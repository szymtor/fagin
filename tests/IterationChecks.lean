import Lax678846Proofs.LfpElimination
import Lax678846Proofs.Isomorphism

open Lax678846Proofs Lax979537.LeastFixedPoints

/-- The identity operator has many fixed points. A table beginning at the
empty set must reject the spurious nonempty fixed point. -/
example : ¬ ∃ H : Fin 2 → Set Unit,
    IterationCertificates.IsIteration id 1 H ∧ H 1 = Set.univ := by
  rintro ⟨H, hH, hfull⟩
  have he := IterationCertificates.unique hH (1 : Fin 2)
  change H 1 = ∅ at he
  have hf : (∅ : Set Unit) = Set.univ := he.symm.trans hfull
  have : () ∈ (∅ : Set Unit) := hf.symm ▸ Set.mem_univ ()
  exact this

#print axioms Isomorphism.satisfiesInvariant
#print axioms IterationCertificates.certificate_iff_of_le
#print axioms RelationSlices.eval_translate
#print axioms IterationFormula.eval_formula
#print axioms LfpElimination.exists_matrix_iff
