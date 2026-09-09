import Lax678846Proofs.CertificateVerifier
import Lax678846Proofs.StackPair
import Lax678846Proofs.StackCertificateHeader
import Lax678846Proofs.StackEmbedding
import Lax678846Proofs.WitnessStructure
import Lax979537Proofs.DecoderCorrectness
import Lax979537Proofs.StackOutput

namespace Lax678846Proofs.VerifierLayout

open Lax678846.FiniteStructures Lax678846.ExistentialSecondOrder
open Lax979537Proofs
open StackProgram StackBoolean

variable {σ : Vocabulary}

abbrev Extra (φ : Sentence σ) := Unit ⊕ FormulaProgram.Work (FirstOrderEvaluation.raw φ.matrix)
abbrev Port (φ : Sentence σ) := FiniteDecoder.Port σ 0 ⊕
  (FiniteDecoder.Port φ.witnesses 0 ⊕ Extra φ)

instance extraDecidableEq (φ : Sentence σ) : DecidableEq (Extra φ) :=
  @instDecidableEqSum Unit (FormulaProgram.Work (FirstOrderEvaluation.raw φ.matrix))
    inferInstance (FormulaProgram.workDecidableEq (FirstOrderEvaluation.raw φ.matrix))

instance portDecidableEq (φ : Sentence σ) : DecidableEq (Port φ) :=
  @instDecidableEqSum (FiniteDecoder.Port σ 0) (FiniteDecoder.Port φ.witnesses 0 ⊕ Extra φ)
    inferInstance (@instDecidableEqSum (FiniteDecoder.Port φ.witnesses 0) (Extra φ)
      inferInstance (extraDecidableEq φ))

instance (φ : Sentence σ) : Fintype (Extra φ) := by
  letI : Fintype (FormulaProgram.Work (FirstOrderEvaluation.raw φ.matrix)) :=
    FormulaProgram.workFintype (FirstOrderEvaluation.raw φ.matrix)
  exact inferInstanceAs (Fintype (Unit ⊕ FormulaProgram.Work (FirstOrderEvaluation.raw φ.matrix)))

def basePort (φ : Sentence σ) (p : FiniteDecoder.Port σ 0) : Port φ := .inl p
def witnessPort (φ : Sentence σ) (p : FiniteDecoder.Port φ.witnesses 0) : Port φ := .inr (.inl p)
def workPort (φ : Sentence σ) (p : FormulaProgram.Work (FirstOrderEvaluation.raw φ.matrix)) :
    Port φ := .inr (.inr (.inr p))
def tmp (φ : Sentence σ) : Port φ := .inr (.inr (.inl ()))
def input (φ : Sentence σ) : Port φ := witnessPort φ (FiniteDecoder.work φ.witnesses 0).input
def word (φ : Sentence σ) : Port φ := basePort φ (FiniteDecoder.work σ 0).input
def domain (φ : Sentence σ) : Port φ := basePort φ (FiniteDecoder.work σ 0).domain

def inputs (φ : Sentence σ) : FormulaProgram.Inputs (Port φ) σ 0 φ.witnesses :=
  ⟨domain φ, Fin.elim0, fun r => basePort φ (FiniteDecoder.tablePort σ 0 r),
    fun r => witnessPort φ (FiniteDecoder.tablePort φ.witnesses 0 r)⟩

theorem inputs_safe (φ : Sentence σ) : (inputs φ).Safe := by
  constructor <;> intro r <;> simp [inputs, domain, basePort, witnessPort,
    FiniteDecoder.work, FiniteDecoder.tablePort]

theorem work_valid (φ : Sentence σ) : FormulaProgram.ValidWork (inputs φ) (workPort φ) := by
  refine ⟨by intro p q h; simpa [workPort] using h, ?_⟩
  intro p
  refine ⟨by simp [inputs, domain, basePort, workPort], ?_, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro r; simp [inputs, basePort, workPort]
  · intro r; simp [inputs, witnessPort, workPort]

def baseResult (φ : Sentence σ) (w : List Bool) :=
  StackDecoder.result (FiniteDecoder.layout σ 0) (FiniteDecoder.inputStore σ 0 w)

def afterSplit (φ : Sentence σ) (w c : List Bool) : EvalStore (Port φ) Unit :=
  StackRename.sumStore (FiniteDecoder.inputStore σ 0 w)
    (Sum.elim (FiniteDecoder.inputStore φ.witnesses 0 c).stk (fun _ : Extra φ => []))

def afterBase (φ : Sentence σ) (w c : List Bool) : EvalStore (Port φ) Unit :=
  StackRename.sumStore (baseResult φ w)
    (Sum.elim (FiniteDecoder.inputStore φ.witnesses 0 c).stk (fun _ : Extra φ => []))

def beforeWitness (φ : Sentence σ) (w : List Bool) (n : Nat) (c : List Bool) :
    EvalStore (Port φ) Unit :=
  StackEmbedding.rightStore (baseResult φ w).stk
    (StackRename.sumStore (FiniteDecoder.inputStore φ.witnesses 0
      (Lax979537.StructureEncoding.unary n ++ c)) (fun _ : Extra φ => []))

def afterWitness (φ : Sentence σ) (w : List Bool) (n : Nat) (c : List Bool) :
    EvalStore (Port φ) Unit :=
  StackEmbedding.rightStore (baseResult φ w).stk
    (StackRename.sumStore (StackDecoder.result (FiniteDecoder.layout φ.witnesses 0)
      (FiniteDecoder.inputStore φ.witnesses 0 (Lax979537.StructureEncoding.unary n ++ c)))
      (fun _ : Extra φ => []))

theorem split_executes (φ : Sentence σ) (w c : List Bool) :
    Executes (StackPair.split (input φ) (tmp φ) (word φ))
      (ioStore (input φ) FiniteDecoder.initial
        (Lax678846.NondeterministicPolynomialTime.encodePair (w,c)))
      (afterSplit φ w c) (7 * w.length + 4) := by
  have h := StackPair.split_executes (input φ) (tmp φ) (word φ)
    (by simp [input, tmp, witnessPort]) (by simp [input, word, basePort, witnessPort])
    (by simp [tmp, word, basePort]) w c
    (ioStore (input φ) FiniteDecoder.initial
      (Lax678846.NondeterministicPolynomialTime.encodePair (w,c)))
    (by simp [ioStore]) (by simp [ioStore, input, tmp, witnessPort])
    (by simp [ioStore, input, word, basePort, witnessPort])
  convert h using 1
  apply Store.ext
  · rfl
  · funext p
    cases p with
    | inl p => simp [StackPair.result, afterSplit, StackRename.sumStore, ioStore,
        FiniteDecoder.inputStore, input, word, tmp, basePort, witnessPort, Function.update_apply,
        Function.comp_def]
    | inr p =>
      cases p with
      | inl p =>
        by_cases hp : p = (FiniteDecoder.work φ.witnesses 0).input <;>
          simp [StackPair.result, afterSplit, StackRename.sumStore, ioStore,
            FiniteDecoder.inputStore, input, word, tmp, basePort, witnessPort,
            Function.update_apply, hp]
      | inr p => simp [StackPair.result, afterSplit, StackRename.sumStore,
          ioStore, FiniteDecoder.inputStore, input, word, tmp, basePort, witnessPort,
          Function.update_apply]

theorem base_executes (φ : Sentence σ) (w c : List Bool) :
    ∃ d, d ≤ (StackDecoder.costPolynomial (FiniteDecoder.layout σ 0)).eval w.length ∧
      Executes (StackRename.rename (basePort φ) (FiniteDecoder.program σ 0))
        (afterSplit φ w c) (afterBase φ w c) d := by
  letI : DecidableEq (Extra φ) := extraDecidableEq φ
  obtain ⟨d, hd, hp⟩ := FiniteDecoder.program_executes σ 0 w
  exact ⟨d, hd, StackRename.executes_in_sum hp _⟩

def prepare (φ : Sentence σ) : EvalProgram (Port φ) Unit :=
  .seq (StackCertificateHeader.prepend (domain φ) (input φ) (tmp φ))
    (.atom (.load (fun _ => FiniteDecoder.initial)))

theorem prepare_executes (φ : Sentence σ) (w c : List Bool) (n : Nat)
    (hn : (baseResult φ w).stk (FiniteDecoder.work σ 0).domain = List.replicate n true) :
    Executes (prepare φ) (afterBase φ w c) (beforeWitness φ w n c) (7 * n + 6) := by
  have hp := StackCertificateHeader.prepend_executes (domain φ) (input φ) (tmp φ)
    (by simp [domain, input, basePort, witnessPort]) (by simp [domain, tmp, basePort])
    (by simp [input, tmp, witnessPort]) (afterBase φ w c) n hn rfl
  have hl := Executes.atom (.load (fun _ : FiniteDecoder.Control => FiniteDecoder.initial))
    (⟨((afterBase φ w c).state.1, none), Function.update (afterBase φ w c).stk (input φ)
      (Lax979537.StructureEncoding.unary n ++ (afterBase φ w c).stk (input φ))⟩ : EvalStore (Port φ) Unit)
  have hf : Op.apply (.load (fun _ : FiniteDecoder.Control => FiniteDecoder.initial))
      (⟨((afterBase φ w c).state.1, none), Function.update (afterBase φ w c).stk (input φ)
        (Lax979537.StructureEncoding.unary n ++ (afterBase φ w c).stk (input φ))⟩ : EvalStore (Port φ) Unit) =
      beforeWitness φ w n c := by
    apply Store.ext
    · rfl
    · change Function.update (afterBase φ w c).stk (input φ)
        (Lax979537.StructureEncoding.unary n ++ (afterBase φ w c).stk (input φ)) =
        (beforeWitness φ w n c).stk
      have hinput : (afterBase φ w c).stk (input φ) = c := by
        simp [afterBase, StackRename.sumStore, input, witnessPort, FiniteDecoder.inputStore, ioStore]
      rw [hinput]
      funext p
      cases p with
      | inl p =>
        rw [Function.update_of_ne (show (Sum.inl p : Port φ) ≠ input φ by
          simp [input, witnessPort])]
        rfl
      | inr p =>
        cases p with
        | inl p =>
          by_cases hp : p = (FiniteDecoder.work φ.witnesses 0).input <;>
            simp [afterBase, beforeWitness, StackRename.sumStore, StackEmbedding.rightStore,
              input, witnessPort, FiniteDecoder.inputStore, ioStore, Function.update_apply, hp]
        | inr p =>
          rw [Function.update_of_ne (show (Sum.inr (Sum.inr p) : Port φ) ≠ input φ by
            simp [input, witnessPort])]
          rfl
  rw [hf] at hl
  have h := Executes.seq hp hl
  convert h using 1 <;> omega

theorem witness_executes (φ : Sentence σ) (w c : List Bool) (n : Nat) :
    ∃ d, d ≤ (StackDecoder.costPolynomial (FiniteDecoder.layout φ.witnesses 0)).eval
        (Lax979537.StructureEncoding.unary n ++ c).length ∧
      Executes (StackRename.rename (witnessPort φ) (FiniteDecoder.program φ.witnesses 0))
        (beforeWitness φ w n c) (afterWitness φ w n c) d := by
  letI : DecidableEq (Extra φ) := extraDecidableEq φ
  obtain ⟨d, hd, hp⟩ := FiniteDecoder.program_executes φ.witnesses 0
    (Lax979537.StructureEncoding.unary n ++ c)
  have h := StackEmbedding.executes_right
    (StackRename.executes_in_sum hp (fun _ : Extra φ => [])) (baseResult φ w).stk
  refine ⟨d, hd, ?_⟩
  simpa only [StackEmbedding.rename_comp] using h

end Lax678846Proofs.VerifierLayout
