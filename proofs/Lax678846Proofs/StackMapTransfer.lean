import Lax979537Proofs.StackProgram

namespace Lax678846Proofs.StackMapTransfer

open Lax979537Proofs.StackProgram

variable {K Aux : Type} {Γ : K → Type} [DecidableEq K]

def read (src : K) : Program Γ (Aux × Option (Γ src)) :=
  .atom (.pop src (fun s b => (s.1, b)))

def body (src dst : K) (f : Γ src → Γ dst) (zero : Γ dst) :
    Program Γ (Aux × Option (Γ src)) :=
  .seq (.atom (.push dst (fun s => s.2.elim zero f))) (read src)

def loop (src dst : K) (f : Γ src → Γ dst) (zero : Γ dst) :
    Program Γ (Aux × Option (Γ src)) :=
  .loop (fun s => s.2.isSome) (body src dst f zero)

/-- Move a stack through a letter map, reversing its order. In particular,
this converts Boolean input to the verifier's own input alphabet. -/
def transfer (src dst : K) (f : Γ src → Γ dst) (zero : Γ dst) :
    Program Γ (Aux × Option (Γ src)) :=
  .seq (read src) (loop src dst f zero)

def working (base : ∀ k, List (Γ k)) (src dst : K)
    (xs : List (Γ src)) (ys : List (Γ dst)) (a : Aux) (scratch : Option (Γ src)) :
    Store Γ (Aux × Option (Γ src)) :=
  ⟨(a, scratch), Function.update (Function.update base src xs) dst ys⟩

theorem pop_working (base : ∀ k, List (Γ k)) (src dst : K)
    (hne : src ≠ dst) (xs : List (Γ src)) (ys : List (Γ dst))
    (a : Aux) (scratch : Option (Γ src)) :
    Op.apply (.pop src (fun s : Aux × Option (Γ src) => fun b => (s.1, b)))
      (working base src dst xs ys a scratch) =
      working base src dst xs.tail ys a xs.head? := by
  apply Store.ext
  · simp [Op.apply, working, hne]
  · funext k
    by_cases hs : k = src
    · subst k; simp [Op.apply, working, hne]
    · by_cases hd : k = dst
      · subst k; simp [Op.apply, working, Ne.symm hne]
      · simp [Op.apply, working, hs, hd, hne]

theorem push_working (base : ∀ k, List (Γ k)) (src dst : K)
    (f : Γ src → Γ dst) (zero : Γ dst)
    (xs : List (Γ src)) (ys : List (Γ dst)) (a : Aux) (b : Γ src) :
    Op.apply (.push dst (fun s : Aux × Option (Γ src) => s.2.elim zero f))
      (working base src dst xs ys a (some b)) =
      working base src dst xs (f b :: ys) a (some b) := by
  apply Store.ext
  · rfl
  · funext k
    by_cases hd : k = dst
    · subst k; simp [Op.apply, working]
    · simp [Op.apply, working, hd]

theorem loop_executes (base : ∀ k, List (Γ k)) (src dst : K)
    (hne : src ≠ dst) (f : Γ src → Γ dst) (zero : Γ dst)
    (xs : List (Γ src)) (ys : List (Γ dst)) (a : Aux) :
    Executes (loop src dst f zero)
      (working base src dst xs.tail ys a xs.head?)
      (working base src dst [] (xs.reverse.map f ++ ys) a none) (3 * xs.length + 1) := by
  induction xs generalizing ys with
  | nil => exact Executes.loop_false rfl
  | cons b bs ih =>
      have hp := Executes.atom (.push dst (fun s : Aux × Option (Γ src) => s.2.elim zero f))
        (working base src dst bs ys a (some b))
      rw [push_working] at hp
      have hr := Executes.atom (.pop src (fun s : Aux × Option (Γ src) => fun b => (s.1, b)))
        (working base src dst bs (f b :: ys) a (some b))
      rw [pop_working base src dst hne] at hr
      have hh := Executes.loop_true (p := body src dst f zero)
        (b := fun s : Aux × Option (Γ src) => s.2.isSome) rfl
        (Executes.seq hp hr) (ih (f b :: ys))
      have ht : (1 + 1) + (3 * bs.length + 1) + 1 = 3 * (bs.length + 1) + 1 := by omega
      simpa only [List.tail_cons, List.head?_cons, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.length_cons, List.append_assoc, List.singleton_append, ht] using hh

theorem transfer_executes (base : ∀ k, List (Γ k)) (src dst : K)
    (hne : src ≠ dst) (f : Γ src → Γ dst) (zero : Γ dst)
    (xs : List (Γ src)) (ys : List (Γ dst)) (a : Aux) (scratch : Option (Γ src)) :
    Executes (transfer src dst f zero) (working base src dst xs ys a scratch)
      (working base src dst [] (xs.reverse.map f ++ ys) a none) (3 * xs.length + 2) := by
  have hr := Executes.atom (.pop src (fun s : Aux × Option (Γ src) => fun b => (s.1, b)))
    (working base src dst xs ys a scratch)
  rw [pop_working base src dst hne] at hr
  have h := Executes.seq hr (loop_executes base src dst hne f zero xs ys a)
  have ht : 1 + (3 * xs.length + 1) = 3 * xs.length + 2 := by omega
  simpa only [ht] using h

theorem transfer_store (src dst : K) (hne : src ≠ dst) (f : Γ src → Γ dst) (zero : Γ dst)
    (s : Store Γ (Aux × Option (Γ src))) :
    Executes (transfer src dst f zero) s
      ⟨(s.state.1, none), Function.update (Function.update s.stk src []) dst
        ((s.stk src).reverse.map f ++ s.stk dst)⟩ (3 * (s.stk src).length + 2) := by
  simpa only [working, Function.update_eq_self, Prod.mk.eta] using
    transfer_executes s.stk src dst hne f zero (s.stk src) (s.stk dst) s.state.1 s.state.2

end Lax678846Proofs.StackMapTransfer
