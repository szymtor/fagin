import Lax988886Proofs.FirstOrderEvaluation
import Lax988886Proofs.RelationCertificates
import Lax988886.NondeterministicPolynomialTime

namespace Lax988886Proofs.CertificateVerifier

open Lax988886.FiniteStructures Lax988886.ExistentialSecondOrder
open Lax751879Proofs

/-- Reject malformed structure encodings and witness tables; otherwise run
the existing first-order evaluator with the decoded relations as parameters. -/
def verify {σ : Vocabulary} (φ : Sentence σ) (p : List Bool × List Bool) : Bool :=
  match Decoding.decode σ 0 p.1 with
  | none => false
  | some A => match RelationCertificates.decode φ.witnesses A.structureValue.size p.2 with
    | none => false
    | some R => TableEvaluation.evaluate (FirstOrderEvaluation.raw φ.matrix)
        A.structureValue Fin.elim0 (FirstOrderEvaluation.tables R)

theorem verify_encoded {σ : Vocabulary} (φ : Sentence σ) (A : Structure σ)
    (R : Interpretation φ.witnesses A.size) :
    verify φ (encode A, RelationCertificates.encode R) = true ↔
      φ.matrix.eval A R Fin.elim0 := by
  have hd := Decoding.decode_encode
    (⟨A, Fin.elim0⟩ : Lax751879.OrderedStructures.PointedStructure σ 0)
  change Decoding.decode σ 0 (encode A) = some ⟨A, Fin.elim0⟩ at hd
  simp only [verify, hd, RelationCertificates.decode_encode]
  exact FirstOrderEvaluation.evaluate_iff φ.matrix A R Fin.elim0

theorem verify_sound {σ : Vocabulary} (φ : Sentence σ) (w c : List Bool)
    (h : verify φ (w, c) = true) : language (fun A => Satisfies A φ) w := by
  unfold verify at h
  cases hd : Decoding.decode σ 0 w with
  | none => simp [hd] at h
  | some A =>
    cases hr : RelationCertificates.decode φ.witnesses A.structureValue.size c with
    | none => simp [hd, hr] at h
    | some R =>
      simp only [hd, hr] at h
      refine ⟨A.structureValue, ?_, R,
        (FirstOrderEvaluation.evaluate_iff φ.matrix A.structureValue R Fin.elim0).mp h⟩
      have he := DecoderSoundness.decode_sound σ 0 w A hd
      have hA : A = ⟨A.structureValue, Fin.elim0⟩ := by
        cases A with
        | mk B v =>
          have hv : v = Fin.elim0 := Subsingleton.elim _ _
          cases hv
          rfl
      exact hA ▸ he

/-- Semantic NP certificate characterization, with the actual certificate
polynomial and a fixed verifier. Machine-time verification is separate. -/
theorem language_iff {σ : Vocabulary} (φ : Sentence σ) (w : List Bool) :
    language (fun A => Satisfies A φ) w ↔
      ∃ c, c.length ≤ (InputSize.tablePolynomial φ.witnesses).eval w.length ∧
        verify φ (w, c) = true := by
  constructor
  · rintro ⟨A, rfl, R, hR⟩
    exact ⟨RelationCertificates.encode R, RelationCertificates.length_bound A R,
      (verify_encoded φ A R).mpr hR⟩
  · rintro ⟨c, _, hc⟩
    exact verify_sound φ w c hc

/-- The remaining obligation for this direction is the concrete polynomial
machine implementing `verify`, including its input-decoding wrapper. -/
theorem inNP_of_computable {σ : Vocabulary} (φ : Sentence σ)
    (h : Nonempty (Turing.TM2ComputableInPolyTime
      Lax988886.NondeterministicPolynomialTime.encodePair (fun b => [b]) (verify φ))) :
    Lax988886.NondeterministicPolynomialTime.InNP (fun A => Satisfies A φ) :=
  ⟨verify φ, InputSize.tablePolynomial φ.witnesses, h, language_iff φ⟩

end Lax988886Proofs.CertificateVerifier
