import Lax988886.ExistentialSecondOrder
import Lax751879Proofs.FormulaCorrectness

namespace Lax988886Proofs.FirstOrderEvaluation

open Lax988886.FiniteStructures Lax988886.ExistentialSecondOrder
open Lax751879.FixedPointSyntax Lax751879.FixedPointSemantics
open Lax751879Proofs

/-- The ∃SO matrix uses the same first-order constructors as the verified
Immerman–Vardi evaluator, with guessed relations supplied as table inputs. -/
def raw {σ τ : Vocabulary} {m : Nat} : FirstOrder σ τ m → RawFormula σ m τ
  | .truth => .truth
  | .equal x y => .equal x y
  | .relation r args => .relation r args
  | .variable r args => .variable r args
  | .neg φ => .neg (raw φ)
  | .conj φ ψ => .conj (raw φ) (raw ψ)
  | .exists' φ => .exists' (raw φ)

theorem raw_admissible {σ τ : Vocabulary} {m : Nat} (φ : FirstOrder σ τ m) :
    (raw φ).Admissible := by
  induction φ with
  | truth | equal | relation | «variable» => trivial
  | neg φ ih | exists' φ ih => exact ih
  | conj φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩

def tables {τ : Vocabulary} {n : Nat} (R : Interpretation τ n) : TableEvaluation.TableEnv n τ :=
  fun r => (Lax751879.StructureEncoding.tuples n (τ.get r)).filter (R r)

theorem mem_tables {τ : Vocabulary} {n : Nat} (R : Interpretation τ n)
    (r : Symbol τ) (a : Fin (τ.get r) → Fin n) :
    a ∈ tables R r ↔ R r a = true := by
  simp [tables, StructureEncoding.mem_tuples]

theorem eval_raw {σ τ : Vocabulary} {m : Nat} (φ : FirstOrder σ τ m)
    (A : Structure σ) (R : Interpretation τ A.size) (v : Fin m → Fin A.size) :
    eval (raw φ) A v (TableEvaluation.denote (tables R)) ↔ φ.eval A R v := by
  induction φ with
  | truth | equal | relation => rfl
  | «variable» r args => exact mem_tables R r (v ∘ args)
  | neg φ ih => exact not_congr (ih v)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ v) (ihψ v)
  | exists' φ ih => exact exists_congr fun a => ih (Fin.cons a v)

theorem evaluate_iff {σ τ : Vocabulary} {m : Nat} (φ : FirstOrder σ τ m)
    (A : Structure σ) (R : Interpretation τ A.size) (v : Fin m → Fin A.size) :
    TableEvaluation.evaluate (raw φ) A v (tables R) = true ↔ φ.eval A R v :=
  (TableEvaluation.evaluate_correct _ (raw_admissible φ) A v (tables R)).trans
    (eval_raw φ A R v)

/-- Reuse only the first-order cases of the existing compiler proof.
The bound counts actual stack-program steps and is polynomial in domain size. -/
theorem compile_correct {K Aux : Type} [DecidableEq K] {σ τ : Vocabulary} {m : Nat}
    (φ : FirstOrder σ τ m) : FormulaProgram.Correct (K := K) (Aux := Aux) (raw φ) := by
  induction φ with
  | truth => exact FormulaProgram.correct_truth
  | equal x y => exact FormulaProgram.correct_equal x y
  | relation r args => exact FormulaProgram.correct_relation r args
  | «variable» r args => exact FormulaProgram.correct_variable r args
  | neg φ ih => exact FormulaProgram.correct_neg ih
  | conj φ ψ ihφ ihψ => exact FormulaProgram.correct_conj ihφ ihψ
  | exists' φ ih => exact FormulaProgram.correct_exists ih

/-- A verified execution of the FO matrix on materialized witness tables.
The input-decoding wrapper is a separate part of the NP verifier. -/
theorem executes {K Aux : Type} [DecidableEq K] {σ τ : Vocabulary} {m : Nat}
    (φ : FirstOrder σ τ m) (input : FormulaProgram.Inputs K σ m τ)
    (work : FormulaProgram.Work (raw φ) → K) (hs : input.Safe)
    (hw : FormulaProgram.ValidWork input work) (A : Structure σ)
    (R : Interpretation τ A.size) (v : Fin m → Fin A.size)
    (s : StackBoolean.EvalStore K Aux) (hc : FormulaProgram.Clean work s)
    (hr : FormulaProgram.Represents input A v (tables R) s) :
    ∃ c b, c ≤ (FormulaProgram.costPolynomial (raw φ)).eval A.size ∧
      StackBoolean.Returns (FormulaProgram.compile (raw φ) input work) s b c ∧
      (b = true ↔ φ.eval A R v) := by
  obtain ⟨c, hb, hp⟩ := compile_correct φ input work hs hw A v (tables R) s hc hr
  exact ⟨c, _, hb, hp, evaluate_iff φ A R v⟩

end Lax988886Proofs.FirstOrderEvaluation
