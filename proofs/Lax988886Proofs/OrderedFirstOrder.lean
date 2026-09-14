import Lax988886.ExistentialSecondOrder
import Lax751879.FixedPointSemantics

-- Preserve Lean 4.30 definition unfolding during elaboration.
set_option backward.isDefEq.respectTransparency false

namespace Lax988886Proofs.OrderedFirstOrder

open Lax988886.FiniteStructures Lax988886.ExistentialSecondOrder
open Lax751879.FixedPointSyntax

/-- First-order syntax may use free relation parameters, but no fixed points. -/
def NoFixedPoints {σ : Vocabulary} {m : Nat} {τ : Vocabulary} :
    RawFormula σ m τ → Prop
  | .truth | .equal _ _ | .less _ _ | .relation _ _ | .variable _ _ => True
  | .neg φ | .exists' φ => NoFixedPoints φ
  | .conj φ ψ => NoFixedPoints φ ∧ NoFixedPoints ψ
  | .lfp _ _ _ => False

/-- Replace the distinguished order by the first existential relation.
The fixed-point branch is excluded by the correctness hypothesis. -/
def translate {σ : Vocabulary} {m : Nat} {τ : Vocabulary}
    (φ : RawFormula σ m τ) : FirstOrder σ (2 :: τ) m :=
  match φ with
  | .truth => .truth
  | .equal x y => .equal x y
  | .less x y => .variable 0 (Fin.cons x (Fin.cons y Fin.elim0))
  | .relation r args => .relation r args
  | .variable r args => .variable r.succ args
  | .neg ψ => .neg (translate ψ)
  | .conj ψ χ => .conj (translate ψ) (translate χ)
  | .exists' ψ => .exists' (translate ψ)
  | .lfp _ _ _ => .truth

def withOrder {τ : Vocabulary} {n : Nat} (R : Interpretation τ n) :
    Interpretation (2 :: τ) n :=
  Fin.cons (fun (a : Fin 2 → Fin n) => decide (a 0 < a 1)) R

theorem eval_translate {σ : Vocabulary} {m : Nat} {τ : Vocabulary}
    (φ : RawFormula σ m τ) (hφ : NoFixedPoints φ)
    (A : Structure σ) (R : Interpretation τ A.size) (v : Fin m → Fin A.size) :
    (translate φ).eval A (withOrder R) v ↔
      Lax751879.FixedPointSemantics.eval φ A v (fun r a => R r a = true) := by
  induction φ with
  | truth | equal | relation => rfl
  | less x y => simp [translate, FirstOrder.eval, withOrder,
      Lax751879.FixedPointSemantics.eval, Function.comp_def]
  | «variable» r args => rfl
  | neg φ ih => exact not_congr (ih hφ R v)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ hφ.1 R v) (ihψ hφ.2 R v)
  | exists' φ ih => exact exists_congr fun a => ih hφ R (Fin.cons a v)
  | lfp => exact hφ.elim

end Lax988886Proofs.OrderedFirstOrder
