import Lax751879Proofs.StackCopy
import Lax988886Proofs.PairEncoding

namespace Lax988886Proofs.StackTag

open Lax751879Proofs.StackProgram Lax751879Proofs.StackTransfer

variable {K Aux : Type} [DecidableEq K]

def tagged (xs : List Bool) : List Bool := xs.flatMap (fun b => [true, b])

def body (src dst : K) : BitProgram K Aux :=
  .seq (.atom (.push dst (fun s => s.2.getD false)))
    (.seq (.atom (.push dst (fun _ => true))) (read src))

def loop (src dst : K) : BitProgram K Aux :=
  .loop (fun s => s.2.isSome) (body src dst)

def transfer (src dst : K) : BitProgram K Aux := .seq (read src) (loop src dst)

theorem push_true (base : K → List Bool) (src dst : K)
    (xs ys : List Bool) (a : Aux) (scratch : Option Bool) :
    Op.apply (.push dst (fun _ : Aux × Option Bool => true))
      (working base src dst xs ys a scratch) =
      working base src dst xs (true :: ys) a scratch := by
  apply Store.ext
  · rfl
  · funext key
    by_cases h : key = dst <;> simp_all [Op.apply, working, Function.update_apply]

theorem loop_executes (base : K → List Bool) (src dst : K) (hne : src ≠ dst)
    (xs ys : List Bool) (a : Aux) :
    Executes (loop src dst) (working base src dst xs.tail ys a xs.head?)
      (working base src dst [] (tagged xs.reverse ++ ys) a none) (4 * xs.length + 1) := by
  induction xs generalizing ys with
  | nil => exact Executes.loop_false rfl
  | cons b bs ih =>
    have h1 := Executes.atom (.push dst (fun s : Aux × Option Bool => s.2.getD false))
      (working base src dst bs ys a (some b))
    rw [push_working] at h1
    have h2 := Executes.atom (.push dst (fun _ : Aux × Option Bool => true))
      (working base src dst bs (b :: ys) a (some b))
    rw [push_true] at h2
    have h3 := Executes.atom (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
      (working base src dst bs (true :: b :: ys) a (some b))
    rw [pop_working base src dst hne] at h3
    have h := Executes.loop_true (p := body src dst) (b := fun s : Aux × Option Bool => s.2.isSome)
      rfl (Executes.seq h1 (Executes.seq h2 h3)) (ih (true :: b :: ys))
    have ht : (1 + (1 + 1)) + (4 * bs.length + 1) + 1 = 4 * (bs.length + 1) + 1 := by omega
    simpa only [List.tail_cons, List.head?_cons, List.length_cons, List.reverse_cons,
      tagged, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc, List.cons_append, List.nil_append, ht] using h

theorem transfer_store (src dst : K) (hne : src ≠ dst) (s : BitStore K Aux) :
    Executes (transfer src dst) s
      ⟨(s.state.1, none), Function.update (Function.update s.stk src []) dst
        (tagged (s.stk src).reverse ++ s.stk dst)⟩ (4 * (s.stk src).length + 2) := by
  have h1 := Executes.atom (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
    (working s.stk src dst (s.stk src) (s.stk dst) s.state.1 s.state.2)
  rw [pop_working s.stk src dst hne] at h1
  have h2 := loop_executes s.stk src dst hne (s.stk src) (s.stk dst) s.state.1
  have h := Executes.seq h1 h2
  have ht : 1 + (4 * (s.stk src).length + 1) = 4 * (s.stk src).length + 2 := by omega
  simpa only [working, Function.update_eq_self, Prod.mk.eta, ht] using h

/-- Form the exact tagged pair encoding used in the standard NP concept.
The destination initially holds the certificate; the word is consumed. -/
def join (word dst tmp : K) : BitProgram K Aux :=
  .seq (Lax751879Proofs.StackTransfer.transfer word tmp)
    (.seq (.atom (.push dst (fun _ => false))) (transfer tmp dst))

theorem join_store (word dst tmp : K) (hwd : word ≠ dst) (hwt : word ≠ tmp) (hdt : dst ≠ tmp)
    (s : BitStore K Aux) (htmp : s.stk tmp = []) :
    Executes (join word dst tmp) s
      ⟨(s.state.1, none), Function.update (Function.update s.stk word []) dst
        (Lax988886.NondeterministicPolynomialTime.encodePair (s.stk word, s.stk dst))⟩
      (7 * (s.stk word).length + 5) := by
  let u : BitStore K Aux :=
    ⟨(s.state.1, none), Function.update (Function.update s.stk word []) tmp (s.stk word).reverse⟩
  let v : BitStore K Aux := ⟨u.state, Function.update u.stk dst (false :: s.stk dst)⟩
  have h1 := Lax751879Proofs.StackTransfer.transfer_store word tmp hwt s
  rw [htmp, List.append_nil] at h1
  have h2 := Executes.atom (.push dst (fun _ : Aux × Option Bool => false)) u
  have he : Op.apply (.push dst (fun _ : Aux × Option Bool => false)) u = v := by
    simp [u, v, Op.apply, hdt, Ne.symm hwd]
  rw [he] at h2
  have h3 := transfer_store tmp dst (Ne.symm hdt) v
  have hvt : v.stk tmp = (s.stk word).reverse := by simp [v, u, Ne.symm hdt]
  have hvd : v.stk dst = false :: s.stk dst := by simp [v]
  rw [hvt, hvd, List.reverse_reverse, List.length_reverse] at h3
  have ho : (⟨(v.state.1, none), Function.update (Function.update v.stk tmp []) dst
      (tagged (s.stk word) ++ false :: s.stk dst)⟩ : BitStore K Aux) =
      ⟨(s.state.1, none), Function.update (Function.update s.stk word []) dst
        (Lax988886.NondeterministicPolynomialTime.encodePair (s.stk word, s.stk dst))⟩ := by
    apply Store.ext
    · rfl
    · funext key
      by_cases hd : key = dst
      · subst key; simp [Lax988886.NondeterministicPolynomialTime.encodePair, tagged]
      · by_cases ht : key = tmp
        · subst key; simp [hd, htmp, Ne.symm hwt]
        · simp [v, u, hd, ht]
  rw [ho] at h3
  have h := Executes.seq h1 (Executes.seq h2 h3)
  have ht : (3 * (s.stk word).length + 2) + (1 + (4 * (s.stk word).length + 2)) =
      7 * (s.stk word).length + 5 := by omega
  simpa only [ht] using h

end Lax988886Proofs.StackTag
