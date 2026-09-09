import Lax678846Proofs.PreprocessorPost
import Lax678846Proofs.StackKeepOutput
import Lax678846Proofs.PolynomialComposition

namespace Lax678846Proofs.PreprocessorMachine

open Lax678846.FiniteStructures Lax979537Proofs
open StackProgram StackBoolean PreprocessorLayout

noncomputable def prepare (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) (xs : List Bool) :
    Bool × (List Bool × List Bool) :=
  match Decoding.decode (k :: k :: σ) 0 xs with
  | none => (false, ([], []))
  | some B => (PreprocessorCheck.accepts p B.structureValue,
      (encode (RelationalVerifier.base B.structureValue), PreprocessorCertificate.bits B.structureValue))

theorem prepare_encode {σ : Vocabulary} (k : Nat) (p : Polynomial Nat) (B : Structure (k :: k :: σ)) :
    prepare σ k p (encode B) = (PreprocessorCheck.accepts p B,
      (encode (RelationalVerifier.base B), PreprocessorCertificate.bits B)) := by
  have h := Decoding.decode_encode (⟨B, Fin.elim0⟩ : Lax979537.OrderedStructures.PointedStructure (k :: k :: σ) 0)
  unfold prepare
  erw [h]

def reject (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : EvalProgram (Port σ k p) Unit :=
  .seq (.atom (.push (pair σ k p) (fun _ => false))) (.atom (.push (pair σ k p) (fun _ => false)))

noncomputable def rejected {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (s : EvalStore (Port σ k p) Unit) : EvalStore (Port σ k p) Unit :=
  ⟨s.state, Function.update s.stk (pair σ k p) [false, false]⟩

theorem reject_executes (σ : Vocabulary) (k : Nat) (p : Polynomial Nat)
    (s : EvalStore (Port σ k p) Unit) (hs : s.stk (pair σ k p) = []) :
    Executes (reject σ k p) s (rejected s) 2 := by
  let push : Op (fun _ : Port σ k p => Bool) FiniteDecoder.Control := .push (pair σ k p) (fun _ => false)
  have h := Executes.seq (Executes.atom push s) (Executes.atom push (push.apply s))
  have he : push.apply (push.apply s) = rejected s := by simp [push, Op.apply, rejected, hs]
  rwa [he] at h

noncomputable def compute (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : EvalProgram (Port σ k p) Unit :=
  .seq (decoder σ k p) (.branch (fun s => s.1.2) (PreprocessorPost.program σ k p) (reject σ k p))

noncomputable def computeCost (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : Polynomial Nat :=
  StackDecoder.costPolynomial (FiniteDecoder.layout (k :: k :: σ) 0) + PreprocessorPost.cost σ k p + 3

/-- Every input, including a malformed encoding, produces a guarded verifier
input in polynomial time. Malformed encodings receive a false guard. -/
theorem compute_executes (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) (xs : List Bool) :
    ∃ d t, d ≤ (computeCost σ k p).eval xs.length ∧
      Executes (compute σ k p) (ioStore (input σ k p) FiniteDecoder.initial xs) t d ∧
      t.stk (pair σ k p) = GuardedVerifier.encode Lax678846.NondeterministicPolynomialTime.encodePair
        (prepare σ k p xs) := by
  obtain ⟨d, hd, hdec⟩ := decoder_executes σ k p xs
  have hv := decoded_validity σ k p xs
  cases hparse : Decoding.decode (k :: k :: σ) 0 xs with
  | none =>
    have hfalse : (decoded σ k p xs).state.1.2 = false := by simpa [hparse] using hv
    have hr := reject_executes σ k p (decoded σ k p xs) rfl
    have hb := Executes.branch_false (b := fun s : FiniteDecoder.Control => s.1.2)
      (p := PreprocessorPost.program σ k p) hfalse hr
    refine ⟨d + (2 + 1), rejected (decoded σ k p xs), ?_, Executes.seq hdec hb, ?_⟩
    · simp only [computeCost, Polynomial.eval_add, Polynomial.eval_ofNat]
      omega
    · simp [rejected, prepare, hparse, GuardedVerifier.encode, Lax678846.NondeterministicPolynomialTime.encodePair]
  | some B =>
    have htrue : (decoded σ k p xs).state.1.2 = true := by simpa [hparse] using hv
    obtain ⟨e, he, hp⟩ := PreprocessorPost.program_executes B.structureValue (decoded σ k p xs)
      (decoded_ready σ k p xs B hparse)
    have hb := Executes.branch_true (b := fun s : FiniteDecoder.Control => s.1.2)
      (q := reject σ k p) htrue hp
    refine ⟨d + (e + 1), PreprocessorPost.result B.structureValue (decoded σ k p xs), ?_,
      Executes.seq hdec hb, ?_⟩
    · have hsize := InputSize.domain_size_le_encoding B
      have henc := DecoderSoundness.decode_sound (k :: k :: σ) 0 xs B hparse
      rw [henc] at hsize
      have hm := PolynomialBounds.eval_mono (PreprocessorPost.cost σ k p)
        (show B.structureValue.size ≤ xs.length by omega)
      simp only [computeCost, Polynomial.eval_add, Polynomial.eval_ofNat]
      omega
    · rw [PreprocessorPost.result_output]
      simp only [prepare, hparse]
      rfl

noncomputable def keys (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : List (Port σ k p) :=
  Finset.univ.toList

theorem mem_keys (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) (key : Port σ k p) : key ∈ keys σ k p := by
  simp [keys]

noncomputable def program (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : EvalProgram (Port σ k p) Unit :=
  .seq (compute σ k p) (StackKeepOutput.clean (keys σ k p) (pair σ k p) FiniteDecoder.initial)

noncomputable def cost (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : Polynomial Nat :=
  computeCost σ k p + (2 * (Polynomial.X + computeCost σ k p) + 2) * Polynomial.C (keys σ k p).length + 2

theorem program_executes (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) (xs : List Bool) :
    ∃ d, d ≤ (cost σ k p).eval xs.length ∧
      Executes (program σ k p) (ioStore (input σ k p) FiniteDecoder.initial xs)
        (ioStore (pair σ k p) FiniteDecoder.initial
          (GuardedVerifier.encode Lax678846.NondeterministicPolynomialTime.encodePair (prepare σ k p xs))) d := by
  obtain ⟨d, t, hd, hp, hout⟩ := compute_executes σ k p xs
  have hs : ∀ key, (t.stk key).length ≤ xs.length + (computeCost σ k p).eval xs.length := by
    intro key
    have hh := StackOutput.length_executes hp key
    have hi := PolynomialComposition.ioStore_length_le (Γ := fun _ : Port σ k p => Bool)
      (input σ k p) FiniteDecoder.initial xs key
    omega
  obtain ⟨e, he, hq⟩ := StackKeepOutput.clean_executes (keys σ k p) (mem_keys σ k p) (pair σ k p)
    FiniteDecoder.initial t (xs.length + (computeCost σ k p).eval xs.length) hs
  rw [hout] at hq
  refine ⟨d + e, ?_, Executes.seq hp hq⟩
  simp only [cost, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_C]
  omega

theorem computable (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) :
    Nonempty (Turing.TM2ComputableInPolyTime id
      (GuardedVerifier.encode Lax678846.NondeterministicPolynomialTime.encodePair) (prepare σ k p)) := by
  apply program_polytime (program σ k p) (input σ k p) (pair σ k p) FiniteDecoder.initial
    id (GuardedVerifier.encode Lax678846.NondeterministicPolynomialTime.encodePair) (prepare σ k p) (cost σ k p)
  exact program_executes σ k p

end Lax678846Proofs.PreprocessorMachine
