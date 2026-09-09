import Lax678846Proofs.VerifierEvaluation
import Lax979537Proofs.FormulaPorts

namespace Lax678846Proofs.VerifierMachine

open Lax678846.FiniteStructures Lax678846.ExistentialSecondOrder
open Lax678846.NondeterministicPolynomialTime
open Lax979537Proofs
open StackProgram StackBoolean VerifierLayout

variable {σ : Vocabulary}

def check (φ : Sentence σ) : EvalProgram (Port φ) Unit :=
  .branch (fun s => s.1.2)
    (.seq (prepare φ)
      (.seq (StackRename.rename (witnessPort φ) (FiniteDecoder.program φ.witnesses 0))
        (VerifierEvaluation.evaluate φ)))
    (answer false)

noncomputable def checkCost (φ : Sentence σ) : Polynomial Nat :=
  7 * Polynomial.X + StackDecoder.costPolynomial (FiniteDecoder.layout φ.witnesses 0) +
    FormulaProgram.costPolynomial (FirstOrderEvaluation.raw φ.matrix) + 10

theorem check_executes (φ : Sentence σ) (w c : List Bool) :
    ∃ d s, d ≤ (checkCost φ).eval (encodePair (w,c)).length ∧
      Executes (check φ) (afterBase φ w c) s d ∧
      s.state.1.2 = CertificateVerifier.verify φ (w,c) := by
  have hv := VerifierEvaluation.base_validity φ w c
  cases hd : Decoding.decode σ 0 w with
  | none =>
    have hf : (afterBase φ w c).state.1.2 = false := by simpa [hd] using hv
    have hp := Executes.branch_false (b := fun s => s.1.2)
      (p := .seq (prepare φ)
        (.seq (StackRename.rename (witnessPort φ) (FiniteDecoder.program φ.witnesses 0))
          (VerifierEvaluation.evaluate φ))) hf (answer_returns false (afterBase φ w c))
    refine ⟨2, result false (afterBase φ w c), ?_, hp, ?_⟩
    · simp [checkCost]
    · simp [result, CertificateVerifier.verify, hd]
  | some A =>
    have ht : (afterBase φ w c).state.1.2 = true := by simpa [hd] using hv
    have he := DecoderSoundness.decode_sound σ 0 w A hd
    have hn : A.structureValue.size ≤ w.length := by
      have h := InputSize.domain_size_le_encoding A
      rw [he] at h
      omega
    have hr := DecoderCorrectness.result_represents σ 0 w A hd
    have hp := prepare_executes φ w c A.structureValue.size hr.ready.1
    obtain ⟨d, hb, hw⟩ := witness_executes φ w c A.structureValue.size
    obtain ⟨e, hc, hv⟩ := VerifierEvaluation.evaluate_executes φ w c A hd
    have h := Executes.branch_true (b := fun s => s.1.2) (q := answer false) ht
      (Executes.seq hp (Executes.seq hw hv))
    refine ⟨(7 * A.structureValue.size + 6) + (d + e) + 1,
      result (CertificateVerifier.verify φ (w,c)) (afterWitness φ w A.structureValue.size c),
      ?_, h, rfl⟩
    have hN : A.structureValue.size ≤ (encodePair (w,c)).length := by
      rw [PairEncoding.length_encode]; omega
    have hL : (Lax979537.StructureEncoding.unary A.structureValue.size ++ c).length ≤
        (encodePair (w,c)).length := by
      simp only [Lax979537.StructureEncoding.unary, List.length_append, List.length_replicate,
        List.length_singleton, PairEncoding.length_encode]
      omega
    have hdBound := PolynomialBounds.eval_mono
      (StackDecoder.costPolynomial (FiniteDecoder.layout φ.witnesses 0)) hL
    have heBound := PolynomialBounds.eval_mono
      (FormulaProgram.costPolynomial (FirstOrderEvaluation.raw φ.matrix)) hN
    simp only [checkCost, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    omega

def compute (φ : Sentence σ) : EvalProgram (Port φ) Unit :=
  .seq (StackPair.split (input φ) (tmp φ) (word φ))
    (.seq (StackRename.rename (basePort φ) (FiniteDecoder.program σ 0)) (check φ))

noncomputable def prefixCost (φ : Sentence σ) : Polynomial Nat :=
  7 * Polynomial.X + 4 + StackDecoder.costPolynomial (FiniteDecoder.layout σ 0) + checkCost φ

theorem prefix_executes (φ : Sentence σ) (w c : List Bool) :
    ∃ d s, d ≤ (prefixCost φ).eval (encodePair (w,c)).length ∧
      Executes (compute φ) (ioStore (input φ) FiniteDecoder.initial (encodePair (w,c))) s d ∧
      s.state.1.2 = CertificateVerifier.verify φ (w,c) := by
  have hp := split_executes φ w c
  obtain ⟨d, hd, hb⟩ := base_executes φ w c
  obtain ⟨e, s, he, hc, hs⟩ := check_executes φ w c
  refine ⟨(7 * w.length + 4) + (d + e), s, ?_, Executes.seq hp (Executes.seq hb hc), hs⟩
  have hlen : w.length ≤ (encodePair (w,c)).length := by rw [PairEncoding.length_encode]; omega
  have hD := PolynomialBounds.eval_mono (StackDecoder.costPolynomial (FiniteDecoder.layout σ 0)) hlen
  simp only [prefixCost, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]
  omega

def keys (φ : Sentence σ) : List (Port φ) :=
  (FormulaPorts.decoderPorts σ 0).map (basePort φ) ++
    (FormulaPorts.decoderPorts φ.witnesses 0).map (witnessPort φ) ++
      [tmp φ] ++ (FormulaPorts.workPorts (FirstOrderEvaluation.raw φ.matrix)).map (workPort φ)

theorem mem_keys (φ : Sentence σ) (p : Port φ) : p ∈ keys φ := by
  rcases p with p | (p | (p | p))
  · simp [keys, basePort, witnessPort, tmp, workPort, FormulaPorts.mem_decoderPorts]
  · simp [keys, basePort, witnessPort, tmp, workPort, FormulaPorts.mem_decoderPorts]
  · cases p; simp [keys, tmp]
  · simp [keys, basePort, witnessPort, tmp, workPort, FormulaPorts.mem_workPorts]

def program (φ : Sentence σ) : EvalProgram (Port φ) Unit :=
  .seq (compute φ) (StackOutput.output (keys φ) (input φ) FiniteDecoder.initial)

noncomputable def costPolynomial (φ : Sentence σ) : Polynomial Nat :=
  prefixCost φ + (2 * (Polynomial.X + prefixCost φ) + 2) * Polynomial.C (keys φ).length + 3

/-- The complete verifier runs on the tagged input/certificate pair,
rejects malformed encodings, emits one bit, clears all work stacks, and
resets finite control, with a polynomial bound on actual execution steps. -/
theorem program_executes (φ : Sentence σ) (p : List Bool × List Bool) :
    ∃ d, d ≤ (costPolynomial φ).eval (encodePair p).length ∧
      Executes (program φ) (ioStore (input φ) FiniteDecoder.initial (encodePair p))
        (ioStore (input φ) FiniteDecoder.initial [CertificateVerifier.verify φ p]) d := by
  obtain ⟨w, c⟩ := p
  obtain ⟨d, s, hd, hp, hs⟩ := prefix_executes φ w c
  have hspace (key : Port φ) :
      (s.stk key).length ≤ (encodePair (w,c)).length + (prefixCost φ).eval (encodePair (w,c)).length := by
    have h := StackOutput.length_executes hp key
    have hi : ((ioStore (Γ := fun _ : Port φ => Bool) (input φ) FiniteDecoder.initial
        (encodePair (w,c))).stk key).length ≤ (encodePair (w,c)).length := by
      by_cases hk : key = input φ
      · subst key; simp [ioStore]
      · simp [ioStore, hk]
    omega
  obtain ⟨e, he, hout⟩ := StackOutput.output_executes (keys φ) (mem_keys φ) (input φ)
    FiniteDecoder.initial s _ hspace
  rw [hs] at hout
  refine ⟨d + e, ?_, Executes.seq hp hout⟩
  simp only [costPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_C]
  omega

theorem computableInPolyTime (φ : Sentence σ) :
    Nonempty (Turing.TM2ComputableInPolyTime encodePair (fun b => [b]) (CertificateVerifier.verify φ)) :=
  program_polytime (program φ) (input φ) (input φ) FiniteDecoder.initial encodePair (fun b => [b])
    (CertificateVerifier.verify φ) (costPolynomial φ) (program_executes φ)

end Lax678846Proofs.VerifierMachine
