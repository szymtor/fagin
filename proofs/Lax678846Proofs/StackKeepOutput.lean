import Lax979537Proofs.StackOutput

namespace Lax678846Proofs.StackKeepOutput

open Lax979537Proofs.StackProgram Lax979537Proofs.StackTransfer

variable {K Aux : Type} [DecidableEq K]

/-- Clear all work stacks while preserving an already constructed output
word, then restore the initial finite control. -/
def clean (keys : List K) (out : K) (initial : Aux × Option Bool) : BitProgram K Aux :=
  .seq (Lax979537Proofs.StackOutput.clearPorts (keys.filter (fun k => decide (k ≠ out))))
    (.atom (.load (fun _ => initial)))

theorem clean_executes (keys : List K) (hall : ∀ key, key ∈ keys) (out : K)
    (initial : Aux × Option Bool) (s : BitStore K Aux) (M : Nat)
    (hs : ∀ key, (s.stk key).length ≤ M) :
    ∃ c, c ≤ (2 * M + 2) * keys.length + 2 ∧
      Executes (clean keys out initial) s (ioStore out initial (s.stk out)) c := by
  let ks := keys.filter (fun k => decide (k ≠ out))
  obtain ⟨c, hc, hp⟩ := Lax979537Proofs.StackOutput.clearPorts_executes ks s M hs
  have hr := Executes.atom (.load (fun _ : Aux × Option Bool => initial))
    (Lax979537Proofs.StackOutput.cleared ks s)
  have he : Op.apply (.load (fun _ : Aux × Option Bool => initial))
      (Lax979537Proofs.StackOutput.cleared ks s) = ioStore out initial (s.stk out) := by
    apply Store.ext
    · rfl
    · funext key
      by_cases hk : key = out
      · subst key; simp [Op.apply, Lax979537Proofs.StackOutput.cleared, ks, ioStore]
      · simp [Op.apply, Lax979537Proofs.StackOutput.cleared, ks, ioStore, hk, hall key]
  rw [he] at hr
  have hlen : ks.length ≤ keys.length := List.length_filter_le _ _
  have hmul := Nat.mul_le_mul_left (2 * M + 2) hlen
  exact ⟨c + 1, by omega, Executes.seq hp hr⟩

end Lax678846Proofs.StackKeepOutput
