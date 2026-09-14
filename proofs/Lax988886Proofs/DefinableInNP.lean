import Lax988886Proofs.VerifierMachine
import Lax988886.Fagin

namespace Lax988886Proofs.Fagin

open Lax988886.FiniteStructures Lax988886.ExistentialSecondOrder
open Lax988886.NondeterministicPolynomialTime

/--
---
conclusion: Lax988886.Fagin.definableInNP
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

end Lax988886Proofs.Fagin
