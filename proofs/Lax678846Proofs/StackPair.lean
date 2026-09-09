import Lax678846Proofs.PairEncoding
import Lax979537Proofs.StackTransfer

namespace Lax678846Proofs.StackPair

open Lax678846.NondeterministicPolynomialTime
open Lax979537Proofs.StackProgram Lax979537Proofs.StackTransfer

variable {K Aux : Type} [DecidableEq K]

def body (input rev : K) : BitProgram K Aux :=
  .seq (read input) (.seq (.atom (.push rev (fun s => s.2.getD false))) (read input))

def loop (input rev : K) : BitProgram K Aux :=
  .loop (fun s => s.2.getD false) (body input rev)

/-- Consume the tagged input word, leaving the certificate on its original
stack and accumulating the input word in reverse on a temporary stack. -/
def extract (input rev : K) : BitProgram K Aux := .seq (read input) (loop input rev)

theorem loop_executes (base : K → List Bool) (input rev : K) (hne : input ≠ rev)
    (w c ys : List Bool) (a : Aux) :
    Executes (loop input rev)
      (working base input rev (encodePair (w,c)).tail ys a (encodePair (w,c)).head?)
      (working base input rev c (w.reverse ++ ys) a (some false)) (4 * w.length + 1) := by
  induction w generalizing ys with
  | nil => exact Executes.loop_false rfl
  | cons b w ih =>
    have hr := Executes.atom (.pop input (fun s : Aux × Option Bool => fun b => (s.1,b)))
      (working base input rev (b :: encodePair (w,c)) ys a (some true))
    rw [pop_working base input rev hne] at hr
    have hp := Executes.atom (.push rev (fun s : Aux × Option Bool => s.2.getD false))
      (working base input rev (encodePair (w,c)) ys a (some b))
    rw [push_working] at hp
    have ht := Executes.atom (.pop input (fun s : Aux × Option Bool => fun b => (s.1,b)))
      (working base input rev (encodePair (w,c)) (b :: ys) a (some b))
    rw [pop_working base input rev hne] at ht
    have h := Executes.loop_true (p := body input rev)
      (b := fun s : Aux × Option Bool => s.2.getD false) rfl
      (Executes.seq hr (Executes.seq hp ht)) (ih (b :: ys))
    have hc : (1 + (1 + 1)) + (4 * w.length + 1) + 1 = 4 * (w.length + 1) + 1 := by omega
    simpa only [encodePair, List.flatMap_cons, List.cons_append, List.nil_append,
      List.tail_cons, List.head?_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons, hc] using h

theorem extract_executes (base : K → List Bool) (input rev : K) (hne : input ≠ rev)
    (w c ys : List Bool) (a : Aux) (scratch : Option Bool) :
    Executes (extract input rev) (working base input rev (encodePair (w,c)) ys a scratch)
      (working base input rev c (w.reverse ++ ys) a (some false)) (4 * w.length + 2) := by
  have hr := Executes.atom (.pop input (fun s : Aux × Option Bool => fun b => (s.1,b)))
    (working base input rev (encodePair (w,c)) ys a scratch)
  rw [pop_working base input rev hne] at hr
  have h := Executes.seq hr (loop_executes base input rev hne w c ys a)
  convert h using 1 <;> omega

/-- Separate the two words in the NP pair encoding. All other stacks and
the auxiliary finite state are preserved; the scratch register is reset. -/
def split (input rev word : K) : BitProgram K Aux :=
  .seq (extract input rev) (transfer rev word)

def result (s : BitStore K Aux) (input rev word : K) (w c : List Bool) : BitStore K Aux :=
  ⟨(s.state.1, none), Function.update (Function.update (Function.update s.stk input c) rev []) word w⟩

theorem split_executes (input rev word : K) (hir : input ≠ rev)
    (hiw : input ≠ word) (hrw : rev ≠ word) (w c : List Bool)
    (s : BitStore K Aux) (hin : s.stk input = encodePair (w,c))
    (hrev : s.stk rev = []) (hword : s.stk word = []) :
    Executes (split input rev word) s (result s input rev word w c) (7 * w.length + 4) := by
  have hs : working s.stk input rev (encodePair (w,c)) [] s.state.1 s.state.2 = s := by
    rw [← hin, ← hrev]
    simp only [working, Function.update_eq_self, Prod.mk.eta]
  have he := extract_executes s.stk input rev hir w c [] s.state.1 s.state.2
  rw [hs, List.append_nil] at he
  let u := working s.stk input rev c w.reverse s.state.1 (some false)
  have ht := transfer_store rev word hrw u
  have hu : u.stk rev = w.reverse := by simp [u, working]
  have hw : u.stk word = [] := by simp [u, working, Ne.symm hiw, Ne.symm hrw, hword]
  rw [hu, hw, List.append_nil, List.reverse_reverse, List.length_reverse] at ht
  have hf : (⟨(u.state.1, none), Function.update (Function.update u.stk rev []) word w⟩ :
      BitStore K Aux) = result s input rev word w c := by
    apply Store.ext
    · rfl
    · simp only [u, working, result, Function.update_idem]
  rw [hf] at ht
  have h := Executes.seq he ht
  convert h using 1 <;> omega

end Lax678846Proofs.StackPair
