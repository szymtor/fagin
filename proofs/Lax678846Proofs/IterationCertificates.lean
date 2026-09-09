import Lax979537Proofs.LeastFixedPoints

namespace Lax678846Proofs.IterationCertificates

open Lax979537.LeastFixedPoints

/-- A finite table records the empty stage and every exact successor stage. -/
def IsIteration {α : Type} (F : Set α → Set α) (N : Nat)
    (H : Fin (N + 1) → Set α) : Prop :=
  H 0 = ∅ ∧ ∀ t : Fin N, H t.succ = F (H t.castSucc)

theorem unique {α : Type} {F : Set α → Set α} {N : Nat}
    {H : Fin (N + 1) → Set α} (hH : IsIteration F N H)
    (t : Fin (N + 1)) : H t = stage F t.val := by
  induction t using Fin.induction with
  | zero => exact hH.1
  | succ t ih => rw [hH.2 t, ih]; rfl

theorem exists_table {α : Type} (F : Set α → Set α) (N : Nat) :
    ∃ H : Fin (N + 1) → Set α, IsIteration F N H := by
  exact ⟨fun t => stage F t.val, rfl, fun _ => rfl⟩

theorem stable_after {α : Type} [Fintype α] (F : Set α → Set α)
    (hF : Monotone F) {N : Nat} (hN : Fintype.card α ≤ N) :
    stage F N = leastFixedPoint F := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  clear hN
  induction d with
  | zero => exact Lax979537Proofs.LeastFixedPoints.finiteConvergence F hF
  | succ d ih =>
      rw [Nat.add_succ, stage, ih]
      exact Lax979537Proofs.LeastFixedPoints.fixedPoint F hF

theorem certificate_iff_of_le {α : Type} [Fintype α] (F : Set α → Set α)
    (hF : Monotone F) {N : Nat} (hN : Fintype.card α ≤ N) (R : Set α) :
    (∃ H : Fin (N + 1) → Set α, IsIteration F N H ∧ H (Fin.last N) = R) ↔
      R = leastFixedPoint F := by
  constructor
  · rintro ⟨H, hH, hR⟩
    rw [← hR, unique hH]
    exact stable_after F hF hN
  · intro hR
    exact ⟨fun t => stage F t.val, ⟨rfl, fun _ => rfl⟩,
      (stable_after F hF hN).trans hR.symm⟩

/-- Checking the complete iteration certifies leastness, including negative
queries about the final relation. This is the semantic foundation of the
syntactic ∃SO translation, not yet that translation itself. -/
theorem certificate_iff {α : Type} [Fintype α] (F : Set α → Set α)
    (hF : Monotone F) (R : Set α) :
    (∃ H : Fin (Fintype.card α + 1) → Set α,
      IsIteration F (Fintype.card α) H ∧ H (Fin.last _) = R) ↔
    R = leastFixedPoint F := by
  constructor
  · rintro ⟨H, hH, hR⟩
    rw [← hR, unique hH]
    exact Lax979537Proofs.LeastFixedPoints.finiteConvergence F hF
  · intro hR
    refine ⟨fun t => stage F t.val, ⟨rfl, fun _ => rfl⟩, ?_⟩
    exact (Lax979537Proofs.LeastFixedPoints.finiteConvergence F hF).trans hR.symm

end Lax678846Proofs.IterationCertificates
