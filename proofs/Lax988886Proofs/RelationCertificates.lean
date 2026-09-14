import Lax988886.FiniteStructures
import Lax751879Proofs.DecoderSoundness
import Lax751879Proofs.InputSize
import Lax751879Proofs.PolynomialBounds

-- Preserve Lean 4.30 definition unfolding during elaboration.
set_option backward.isDefEq.respectTransparency false

namespace Lax988886Proofs.RelationCertificates

open Lax988886.FiniteStructures
open Lax751879Proofs

/-- The certificate consists of the characteristic tables of the guessed
relations, with boundaries determined by the domain size and vocabulary. -/
def encode {τ : Vocabulary} {n : Nat} (R : Interpretation τ n) : List Bool :=
  Decoding.relationBits n R

def decode (τ : Vocabulary) (n : Nat) (c : List Bool) : Option (Interpretation τ n) := do
  let (R, rest) ← Decoding.readRelations n τ c
  if rest = [] then some R else none

theorem decode_encode {τ : Vocabulary} {n : Nat} (R : Interpretation τ n) :
    decode τ n (encode R) = some R := by
  have h := Decoding.readRelations_correct n τ R []
  simp only [List.append_nil] at h
  simp [decode, encode, h]

theorem encode_length {τ : Vocabulary} {n : Nat} (R : Interpretation τ n) :
    (encode R).length = (InputSize.tablePolynomial τ).eval n := by
  rw [InputSize.tablePolynomial_eval]
  induction τ with
  | nil => rfl
  | cons k τ ih =>
    change (Decoding.relationBits n R).length = _
    rw [Decoding.relationBits_cons]
    simpa [StructureEncoding.tuples_length] using!
      congrArg (n ^ k + ·) (ih (fun r => R r.succ))

/-- Fixed relation arities give a polynomial certificate bound in the
original input length, also for empty domains and nullary relations. -/
theorem length_bound {σ τ : Vocabulary} (A : Structure σ) (R : Interpretation τ A.size) :
    (encode R).length ≤ (InputSize.tablePolynomial τ).eval
      (Lax988886.FiniteStructures.encode A).length := by
  rw [encode_length]
  apply PolynomialBounds.eval_mono
  have h := InputSize.domain_size_le_encoding
    (⟨A, Fin.elim0⟩ : Lax751879.OrderedStructures.PointedStructure σ 0)
  exact Nat.le_trans (Nat.le_succ _) h

theorem encode_of_decode {τ : Vocabulary} {n : Nat} {c : List Bool}
    {R : Interpretation τ n} (h : decode τ n c = some R) : encode R = c := by
  unfold decode at h
  cases hd : Decoding.readRelations n τ c with
  | none => simp [hd] at h
  | some p =>
    obtain ⟨S, rest⟩ := p
    by_cases hr : rest = []
    · subst rest
      simp [hd] at h
      subst S
      simpa [encode] using DecoderSoundness.readRelations_sound n τ c R [] hd
    · simp [hd, hr] at h

end Lax988886Proofs.RelationCertificates
