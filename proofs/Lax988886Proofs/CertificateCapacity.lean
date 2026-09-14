import Lax988886.FiniteStructures
import Lax751879Proofs.InputSize
import Lax751879Proofs.PolynomialBounds

namespace Lax988886Proofs.CertificateCapacity

open Lax988886.FiniteStructures Lax751879Proofs

/-- A fixed tuple arity provides room for every polynomially bounded
certificate. Only polynomial growth is used, with no precise runtime bound. -/
theorem exists_arity (σ : Vocabulary) (p : Polynomial Nat) :
    ∃ k : Nat, ∀ A : Structure σ, 2 ≤ A.size → p.eval (encode A).length < A.size ^ k := by
  obtain ⟨k, hk⟩ := PolynomialBounds.exists_power (p.comp (InputSize.encodingPolynomial σ 0))
  refine ⟨k, fun A hA => ?_⟩
  have he := InputSize.encoding_length_le
    (⟨A, Fin.elim0⟩ : Lax751879.OrderedStructures.PointedStructure σ 0)
  have hp := PolynomialBounds.eval_mono p he
  have hb := hk A.size hA
  simp only [Polynomial.eval_comp] at hb
  exact hp.trans_lt hb

end Lax988886Proofs.CertificateCapacity
