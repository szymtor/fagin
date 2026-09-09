import Lax678846Proofs.VerifierMachine
import Lax678846.Fagin

namespace Lax678846Proofs.Fagin

open Lax678846.FiniteStructures Lax678846.ExistentialSecondOrder
open Lax678846.NondeterministicPolynomialTime

/--
---
conclusion: Lax678846.Fagin.definableInNP
---
Guess the characteristic tables of the existential relations. Their total
length is polynomial in the original input length. The concrete verifier
splits and decodes the pair, uses the Immerman–Vardi first-order evaluator,
rejects malformed encodings, and returns its answer in polynomial TM2 time.
-/
theorem definableInNP {σ : Vocabulary} (Q : Property σ) : Definable Q → InNP Q := by
  rintro ⟨φ, hφ⟩
  have hQ : Q = fun A => Satisfies A φ := funext fun A => propext (hφ A)
  rw [hQ]
  exact CertificateVerifier.inNP_of_computable φ (VerifierMachine.computableInPolyTime φ)

end Lax678846Proofs.Fagin
