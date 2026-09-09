import Lax678846Proofs.PreprocessorMachine

namespace Lax678846Proofs.ExpandedVerifier

open Lax678846.FiniteStructures Lax678846.NondeterministicPolynomialTime

/-- The expanded verifier has an ordered existential definition. The
preprocessor supplies the original certificate bound as a guard and the
original input/certificate pair; the guarded NP verifier is composed with
it by the proved polynomial machine-composition construction. -/
theorem ordered_definable {σ : Vocabulary} (V : List Bool × List Bool → Bool)
    (p : Polynomial Nat) (k : Nat)
    (hV : Turing.TM2ComputableInPolyTime encodePair (fun b => [b]) V) :
    OrderedDefinitions.Definable (RelationalVerifier.verified (σ := σ) V p k) := by
  obtain ⟨hp⟩ := PreprocessorMachine.computable σ k p
  obtain ⟨hg⟩ := GuardedVerifier.computable hV
  obtain ⟨h⟩ := PolynomialComposition.comp hp hg
  apply OrderedDefinitions.of_machine (RelationalVerifier.verified V p k) h
  intro B
  change RelationalVerifier.verified V p k B ↔
    ((PreprocessorMachine.prepare σ k p (encode B)).1 &&
      V (PreprocessorMachine.prepare σ k p (encode B)).2) = true
  rw [PreprocessorMachine.prepare_encode]
  simp only [RelationalVerifier.verified, PreprocessorCheck.accepts,
    PreprocessorCertificate.bits, Bool.and_eq_true, decide_eq_true_eq]

end Lax678846Proofs.ExpandedVerifier
