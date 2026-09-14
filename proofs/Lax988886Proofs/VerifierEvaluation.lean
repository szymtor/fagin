import Lax988886Proofs.VerifierLayout

namespace Lax988886Proofs.VerifierEvaluation

open Lax988886.FiniteStructures Lax988886.ExistentialSecondOrder
open Lax751879Proofs
open StackProgram StackBoolean VerifierLayout

variable {σ : Vocabulary}

theorem base_validity (φ : Sentence σ) (w c : List Bool) :
    (afterBase φ w c).state.1.2 = (Decoding.decode σ 0 w).isSome := by
  simpa [afterBase, baseResult, StackRename.sumStore] using DecoderAgreement.finite_validity σ 0 w

theorem witness_validity (φ : Sentence σ) (w c : List Bool) (n : Nat) :
    (afterWitness φ w n c).state.1.2 = (RelationCertificates.decode φ.witnesses n c).isSome := by
  have h := DecoderAgreement.finite_validity φ.witnesses 0
    (Lax751879.StructureEncoding.unary n ++ c)
  rw [WitnessStructure.decode_header] at h
  simpa [afterWitness, StackEmbedding.rightStore, StackRename.sumStore] using h

theorem dense_tables {τ : Vocabulary} {n : Nat} (R : Interpretation τ n) (r : Symbol τ) :
    DenseTables.dense (FirstOrderEvaluation.tables R r) =
      (Lax751879.StructureEncoding.tuples n (τ.get r)).map (R r) := by
  apply List.map_congr_left
  intro a _
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using FirstOrderEvaluation.mem_tables R r a

theorem represents (φ : Sentence σ) (w c : List Bool)
    (A : Lax751879.OrderedStructures.PointedStructure σ 0)
    (R : Interpretation φ.witnesses A.structureValue.size)
    (hd : Decoding.decode σ 0 w = some A)
    (hr : RelationCertificates.decode φ.witnesses A.structureValue.size c = some R) :
    FormulaProgram.Represents (inputs φ) A.structureValue Fin.elim0
      (FirstOrderEvaluation.tables R) (afterWitness φ w A.structureValue.size c) := by
  have hb := DecoderCorrectness.result_represents σ 0 w A hd
  have hw : Decoding.decode φ.witnesses 0
      (Lax751879.StructureEncoding.unary A.structureValue.size ++ c) =
      some ⟨WitnessStructure.structureOf R, Fin.elim0⟩ := by
    rw [WitnessStructure.decode_header, hr]
    rfl
  have ht := DecoderCorrectness.result_represents φ.witnesses 0 _ _ hw
  refine ⟨hb.ready.1, fun i => Fin.elim0 i, hb.tables, ?_⟩
  intro r
  rw [dense_tables]
  exact ht.tables r

def evaluate (φ : Sentence σ) : EvalProgram (Port φ) Unit :=
  .branch (fun s => s.1.2)
    (FormulaProgram.compile (FirstOrderEvaluation.raw φ.matrix) (inputs φ) (workPort φ))
    (answer false)

theorem evaluate_executes (φ : Sentence σ) (w c : List Bool)
    (A : Lax751879.OrderedStructures.PointedStructure σ 0)
    (hd : Decoding.decode σ 0 w = some A) :
    ∃ d, d ≤ (FormulaProgram.costPolynomial (FirstOrderEvaluation.raw φ.matrix)).eval
        A.structureValue.size + 2 ∧
      Returns (evaluate φ) (afterWitness φ w A.structureValue.size c)
        (CertificateVerifier.verify φ (w,c)) d := by
  have hv := witness_validity φ w c A.structureValue.size
  cases hr : RelationCertificates.decode φ.witnesses A.structureValue.size c with
  | none =>
    have hf : (afterWitness φ w A.structureValue.size c).state.1.2 = false := by
      simpa [hr] using hv
    refine ⟨2, by omega, ?_⟩
    have h := Executes.branch_false (b := fun s => s.1.2)
      (p := FormulaProgram.compile (FirstOrderEvaluation.raw φ.matrix) (inputs φ) (workPort φ))
      hf (answer_returns false (afterWitness φ w A.structureValue.size c))
    simpa [evaluate, CertificateVerifier.verify, hd, hr] using h
  | some R =>
    have ht : (afterWitness φ w A.structureValue.size c).state.1.2 = true := by
      simpa [hr] using hv
    obtain ⟨d, hb, hp⟩ := FirstOrderEvaluation.compile_correct φ.matrix
      (inputs φ) (workPort φ) (inputs_safe φ) (work_valid φ) A.structureValue Fin.elim0
      (FirstOrderEvaluation.tables R) (afterWitness φ w A.structureValue.size c)
      (fun _ => rfl) (represents φ w c A R hd hr)
    refine ⟨d + 1, by omega, ?_⟩
    have h := Executes.branch_true (b := fun s => s.1.2) (q := answer false) ht hp
    simpa [evaluate, CertificateVerifier.verify, hd, hr] using h

end Lax988886Proofs.VerifierEvaluation
