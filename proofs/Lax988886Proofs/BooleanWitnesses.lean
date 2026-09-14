import Lax988886Proofs.LfpElimination

namespace Lax988886Proofs.BooleanWitnesses

open Lax988886.FiniteStructures Lax988886.ExistentialSecondOrder
open Lax751879.FixedPointSyntax Lax751879.FixedPointSemantics

def toProp {τ : Vocabulary} {n : Nat} (R : Interpretation τ n) : RelationEnv n τ :=
  fun r a => R r a = true

noncomputable def toBool {τ : Vocabulary} {n : Nat} (η : RelationEnv n τ) : Interpretation τ n := by
  classical
  exact fun r a => decide (η r a)

theorem toProp_toBool {τ : Vocabulary} {n : Nat} (η : RelationEnv n τ) :
    toProp (toBool η) = η := by
  classical
  funext r a
  simp [toProp, toBool]

theorem exists_iff {τ : Vocabulary} {n : Nat} (P : RelationEnv n τ → Prop) :
    (∃ R : Interpretation τ n, P (toProp R)) ↔ ∃ η : RelationEnv n τ, P η := by
  constructor
  · rintro ⟨R, hR⟩; exact ⟨toProp R, hR⟩
  · rintro ⟨η, hη⟩
    exact ⟨toBool η, (toProp_toBool η).symm ▸ hη⟩

theorem exists_ordered_matrix_iff {σ τ : Vocabulary} {m : Nat}
    (φ : RawFormula σ m τ) (hφ : OrderedFirstOrder.NoFixedPoints φ)
    (A : Structure σ) (v : Fin m → Fin A.size) :
    (∃ R : Interpretation τ A.size,
      (OrderedFirstOrder.translate φ).eval A (OrderedFirstOrder.withOrder R) v) ↔
      ∃ η : RelationEnv A.size τ, eval φ A v η :=
  (exists_congr fun R => OrderedFirstOrder.eval_translate φ hφ A R v).trans
    (exists_iff (fun η => eval φ A v η))

/-- The stage-table elimination now uses the actual Boolean relation
interpretations and first-order matrix syntax of the ∃SO concepts. The
first relation still denotes the canonical order at this intermediate step. -/
theorem lfp_exists_iff {σ : Vocabulary} {k : Nat} (body : RawFormula σ k [k])
    (query : RawFormula σ 0 [k]) (hb : OrderedFirstOrder.NoFixedPoints body)
    (hq : OrderedFirstOrder.NoFixedPoints query) (A : Structure σ) (hn : 2 ≤ A.size)
    (hF : Monotone (StageFormulas.operator body A)) :
    (∃ R : Interpretation [(k + 1) + k] A.size,
      (OrderedFirstOrder.translate (LfpElimination.matrix body query (k + 1))).eval
        A (OrderedFirstOrder.withOrder R) Fin.elim0) ↔
      eval query A Fin.elim0
        (Fin.cons (Lax751879.LeastFixedPoints.leastFixedPoint (StageFormulas.operator body A))
          (fun r => Fin.elim0 r)) :=
  (exists_ordered_matrix_iff _ (LfpElimination.noFixedPoints body query hb hq (k + 1)) A
    Fin.elim0).trans (LfpElimination.exists_matrix_iff body query hb hq A hn hF)

end Lax988886Proofs.BooleanWitnesses
