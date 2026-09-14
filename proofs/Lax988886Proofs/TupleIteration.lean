import Lax988886Proofs.IterationCertificates
import Lax751879Proofs.TupleAddresses

namespace Lax988886Proofs.TupleIteration

open Lax751879.LeastFixedPoints
open Lax751879Proofs.TupleAddresses

def OrdinalChecks {α : Type} (F : Set α → Set α) {T : Nat}
    (H : Fin T → Set α) : Prop :=
  (∀ t, t.val = 0 → H t = ∅) ∧
  ∀ s t, t.val = s.val + 1 → H t = F (H s)

theorem ordinal_unique {α : Type} {F : Set α → Set α} {T : Nat}
    {H : Fin T → Set α} (hH : OrdinalChecks F H) (t : Fin T) :
    H t = stage F t.val := by
  cases T with
  | zero => exact Fin.elim0 t
  | succ T =>
      induction t using Fin.induction with
      | zero => exact hH.1 _ rfl
      | succ t ih => rw [hH.2 t.castSucc t.succ rfl, ih]; rfl

def Checks {α : Type} (F : Set α → Set α) {n d : Nat}
    (H : (Fin d → Fin n) → Set α) : Prop :=
  (∀ t, (address n d t).val = 0 → H t = ∅) ∧
  ∀ s t, (address n d t).val = (address n d s).val + 1 → H t = F (H s)

theorem unique {α : Type} {F : Set α → Set α} {n d : Nat}
    {H : (Fin d → Fin n) → Set α} (hH : Checks F H) (t : Fin d → Fin n) :
    H t = stage F (address n d t).val := by
  have h : OrdinalChecks F (fun i => H ((address n d).symm i)) := by
    constructor
    · intro i hi
      apply hH.1
      simpa using hi
    · intro i j hij
      apply hH.2
      simpa using hij
  simpa using ordinal_unique h (address n d t)

theorem canonical_checks {α : Type} (F : Set α → Set α) (n d : Nat) :
    Checks F (fun t => stage F (address n d t).val) := by
  constructor
  · intro t ht
    change stage F (address n d t).val = ∅
    rw [ht]
    rfl
  · intro s t hst
    change stage F (address n d t).val = F (stage F (address n d s).val)
    rw [hst]
    rfl

theorem final_row {α : Type} [Fintype α] {F : Set α → Set α} (hF : Monotone F)
    {n d : Nat} {H : (Fin d → Fin n) → Set α} (hH : Checks F H)
    (t : Fin d → Fin n) (ht : Fintype.card α ≤ (address n d t).val) :
    H t = leastFixedPoint F :=
  (unique hH t).trans (IterationCertificates.stable_after F hF ht)

/-- One extra clock coordinate accommodates every stage, including stage zero. -/
theorem clock_capacity {n : Nat} (hn : 2 ≤ n) (r : Nat) : n ^ r + 1 ≤ n ^ (r + 1) := by
  have hp : 0 < n ^ r := Nat.pow_pos (by omega)
  have hm := Nat.mul_le_mul_left (n ^ r) hn
  rw [Nat.pow_succ]
  omega

end Lax988886Proofs.TupleIteration
