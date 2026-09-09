import Lax678846Proofs

open Lax678846Proofs Lax678846.FiniteStructures

/-- Nullary relations still require one certificate bit on an empty domain. -/
example (b : Bool) :
    RelationCertificates.encode (τ := [0]) (n := 0) (fun _ _ => b) = [b] := rfl

example : RelationCertificates.decode [0] 0 [] = none := rfl

/-- A positive-arity relation has no tuples on an empty domain. -/
example : RelationCertificates.encode (τ := [1]) (n := 0) (fun _ _ => true) = [] := rfl

example : PairEncoding.decode [true] = none := rfl

example {σ : Vocabulary} (φ : Lax678846.ExistentialSecondOrder.Sentence σ) (c : List Bool) :
    CertificateVerifier.verify φ ([], c) = false := rfl

#print axioms OrderFormula.eval_formula
#print axioms OrderRemoval.definable
#print axioms SmallDomains.definable_of_above
#print axioms RuleMatrices.exists_matrix_iff
#print axioms PtimeExistential.of_machine
#print axioms ExistentialProjection.definable
#print axioms FirstOrderEvaluation.executes
#print axioms RelationCertificates.length_bound
#print axioms CertificateVerifier.language_iff
#print axioms PairEncoding.encode_injective
