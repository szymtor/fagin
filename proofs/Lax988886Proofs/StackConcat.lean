import Lax751879Proofs.StackCopy

namespace Lax988886Proofs.StackConcat

open Lax751879Proofs.StackProgram Lax751879Proofs.StackTransfer

variable {K Aux : Type} [DecidableEq K]

/-- Concatenate a fixed list of input tables onto an output stack. All
source tables are preserved; one empty temporary stack is reused. -/
def copy (out tmp : K) : List K → BitProgram K Aux
  | [] => .atom (.load (fun s => (s.1, none)))
  | key :: keys => .seq (copy out tmp keys) (Lax751879Proofs.StackCopy.copy key out tmp)

def result (keys : List K) (out : K) (s : BitStore K Aux) : BitStore K Aux :=
  ⟨(s.state.1, none), Function.update s.stk out (keys.flatMap s.stk ++ s.stk out)⟩

theorem copy_executes (out tmp : K) (hot : out ≠ tmp) (keys : List K)
    (hkeys : ∀ key ∈ keys, key ≠ out ∧ key ≠ tmp)
    (s : BitStore K Aux) (ht : s.stk tmp = []) :
    Executes (copy out tmp keys) s (result keys out s)
      (7 * (keys.flatMap s.stk).length + 4 * keys.length + 1) := by
  induction keys with
  | nil =>
    simpa [copy, result] using Executes.atom (.load (fun s : Aux × Option Bool => (s.1, none))) s
  | cons key keys ih =>
    have hk := hkeys key (by simp)
    have hr : ∀ j ∈ keys, j ≠ out ∧ j ≠ tmp := fun j hj => hkeys j (by simp [hj])
    have h1 := ih hr
    have h2 := Lax751879Proofs.StackCopy.copy_store key out tmp hk.1 hk.2 hot
      (result keys out s) (by simp [result, Ne.symm hot, ht])
    have hkey : (result keys out s).stk key = s.stk key := by simp [result, hk.1]
    rw [hkey] at h2
    have he : (⟨((result keys out s).state.1, none),
        Function.update (result keys out s).stk out
          (s.stk key ++ (result keys out s).stk out)⟩ : BitStore K Aux) = result (key :: keys) out s := by
      simp [result, Function.update_idem, List.append_assoc]
    rw [he] at h2
    have hh := Executes.seq h1 h2
    have hc : (7 * (keys.flatMap s.stk).length + 4 * keys.length + 1) +
        (7 * (s.stk key).length + 4) =
        7 * ((key :: keys).flatMap s.stk).length + 4 * (key :: keys).length + 1 := by
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
    simpa only [hc] using hh

end Lax988886Proofs.StackConcat
