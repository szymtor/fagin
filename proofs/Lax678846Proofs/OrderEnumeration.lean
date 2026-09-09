import Lax678846.FiniteStructures
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.RelClasses

namespace Lax678846Proofs.OrderEnumeration

/-- The three first-order conditions imposed on a guessed strict order. -/
def StrictTotal {α : Type} (r : α → α → Prop) : Prop :=
  (∀ x, ¬ r x x) ∧ (∀ x y z, r x y → r y z → r x z) ∧
    ∀ x y, r x y ∨ x = y ∨ r y x

/-- A copy with no inherited order instances. -/
structure Point (n : Nat) where
  value : Fin n

def pointEquiv (n : Nat) : Fin n ≃ Point n where
  toFun := Point.mk
  invFun := Point.value
  left_inv _ := rfl
  right_inv _ := rfl

theorem enumerate {n : Nat} (r : Fin n → Fin n → Prop) (hr : StrictTotal r) :
    ∃ e : Fin n ≃ Fin n, ∀ i j, r (e i) (e j) ↔ i < j := by
  classical
  letI : Fintype (Point n) := Fintype.ofEquiv (Fin n) (pointEquiv n)
  let lifted : Point n → Point n → Prop := fun x y => r x.value y.value
  letI : IsStrictTotalOrder (Point n) lifted := {
    irrefl := fun x => hr.1 x.value
    trans := fun x y z => hr.2.1 x.value y.value z.value
    trichotomous := fun x y hxy hyx => by
      rcases hr.2.2 x.value y.value with h | h | h
      · exact False.elim (hxy h)
      · exact (pointEquiv n).symm.injective h
      · exact False.elim (hyx h) }
  letI : LinearOrder (Point n) := linearOrderOfSTO lifted
  let e : Fin n ≃o Point n := Fintype.orderIsoFinOfCardEq (Point n)
    ((Fintype.card_congr (pointEquiv n).symm).trans (Fintype.card_fin n))
  refine ⟨e.toEquiv.trans (pointEquiv n).symm, fun i j => ?_⟩
  exact e.lt_iff_lt

end Lax678846Proofs.OrderEnumeration
