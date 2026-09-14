import Lax988886Proofs.IterationFormula
import Lax751879Proofs.ClockLast

namespace Lax988886Proofs.LfpElimination

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics Lax751879.LeastFixedPoints
open Lax751879Proofs.SyntaxOperations Lax751879Proofs.FormulaMacros
open Lax751879Proofs.TupleAddresses
open Lax988886Proofs.OrderedFirstOrder Lax988886Proofs.FirstOrderMacros
open Lax988886Proofs.StageFormulas

def readLast {σ : Vocabulary} {k : Nat} (query : RawFormula σ 0 [k]) (d : Nat) :
    RawFormula σ 0 [d + k] :=
  existsBlock d (.conj (Lax751879Proofs.ClockLast.formula id)
    (RelationSlices.translate (rename query (Fin.elim0 : Fin 0 → Fin d)) id))

def matrix {σ : Vocabulary} {k : Nat} (body : RawFormula σ k [k])
    (query : RawFormula σ 0 [k]) (d : Nat) : RawFormula σ 0 [d + k] :=
  .conj (IterationFormula.formula body d) (readLast query d)

theorem noFixedPoints {σ : Vocabulary} {k : Nat} (body : RawFormula σ k [k])
    (query : RawFormula σ 0 [k]) (hb : NoFixedPoints body) (hq : NoFixedPoints query)
    (d : Nat) : NoFixedPoints (matrix body query d) := by
  refine ⟨IterationFormula.noFixedPoints body hb d, ?_⟩
  apply (noFixedPoints_existsBlock _ _).mpr
  exact ⟨noFixedPoints_of_firstOrder _ (Lax751879Proofs.ClockLast.firstOrder id),
    RelationSlices.noFixedPoints _ ((noFixedPoints_rename query _).mpr hq) id⟩

theorem eval_readLast {σ : Vocabulary} {k : Nat} (query : RawFormula σ 0 [k])
    (hq : NoFixedPoints query) (d : Nat) (A : OrderedStructure σ)
    (η : RelationEnv A.size [d + k]) :
    eval (readLast query d) A Fin.elim0 η ↔
      ∃ t : Fin d → Fin A.size, (address A.size d t).val + 1 = A.size ^ d ∧
        eval query A Fin.elim0 (Fin.cons (row η t) (fun r => Fin.elim0 r)) := by
  rw [readLast, eval_existsBlock]
  apply exists_congr
  intro t
  simp only [Fin.append_elim0, Fin.cast_refl, Function.comp_id, eval]
  have hs := RelationSlices.eval_translate (rename query (Fin.elim0 : Fin 0 → Fin d))
    ((noFixedPoints_rename query _).mpr hq) id A t η
  rw [eval_rename, sliced_environment] at hs
  have hempty : t ∘ (Fin.elim0 : Fin 0 → Fin d) = Fin.elim0 := funext fun i => Fin.elim0 i
  simpa only [Function.comp_id, hempty] using!
    and_congr (Lax751879Proofs.ClockLast.eval_formula id A t η) hs

def table {n d k : Nat} (H : (Fin d → Fin n) → Set (Fin k → Fin n)) :
    RelationEnv n [d + k] :=
  Fin.cons (fun (z : Fin (d + k) → Fin n) => H (z ∘ Fin.castAdd k) (z ∘ Fin.natAdd d))
    (fun r => Fin.elim0 r)

theorem row_table {n d k : Nat} (H : (Fin d → Fin n) → Set (Fin k → Fin n))
    (t : Fin d → Fin n) : row (table H) t = H t := by
  ext a
  change H (Fin.append t a ∘ Fin.castAdd k) (Fin.append t a ∘ Fin.natAdd d) ↔ H t a
  rw [IterationFormula.append_left_comp, IterationFormula.append_right_comp]

theorem last_exists {n : Nat} (hn : 0 < n) (d : Nat) :
    ∃ t : Fin d → Fin n, (address n d t).val + 1 = n ^ d := by
  have hp : 0 < n ^ d := Nat.pow_pos hn
  refine ⟨(address n d).symm ⟨n ^ d - 1, by omega⟩, ?_⟩
  simp only [Equiv.apply_symm_apply]
  omega

/-- A single existential relation table eliminates the positive closure.
The first-order query may use that closure negatively. The remaining
distinguished order is converted to a relation by `OrderedFirstOrder`. -/
theorem exists_matrix_iff {σ : Vocabulary} {k : Nat} (body : RawFormula σ k [k])
    (query : RawFormula σ 0 [k]) (hb : NoFixedPoints body) (hq : NoFixedPoints query)
    (A : OrderedStructure σ) (hn : 2 ≤ A.size) (hF : Monotone (operator body A)) :
    (∃ η : RelationEnv A.size [(k + 1) + k], eval (matrix body query (k + 1)) A Fin.elim0 η) ↔
      eval query A Fin.elim0
        (Fin.cons (leastFixedPoint (operator body A)) (fun r => Fin.elim0 r)) := by
  have hbound (t : Fin (k + 1) → Fin A.size)
      (ht : (address A.size (k + 1) t).val + 1 = A.size ^ (k + 1)) :
      Fintype.card (Fin k → Fin A.size) ≤ (address A.size (k + 1) t).val := by
    have hc := TupleIteration.clock_capacity hn k
    rw [Fintype.card_congr (address A.size k), Fintype.card_fin]
    omega
  constructor
  · rintro ⟨η, hi, hq'⟩
    have hc := (IterationFormula.eval_formula body hb (k + 1) A η).mp hi
    obtain ⟨t, ht, hread⟩ := (eval_readLast query hq (k + 1) A η).mp hq'
    have hr := TupleIteration.final_row hF hc t (hbound t ht)
    exact congrArg (fun R => eval query A Fin.elim0
      (Fin.cons R (fun r => Fin.elim0 r))) hr ▸ hread
  · intro h
    let H := fun t => stage (operator body A) (address A.size (k + 1) t).val
    have hr : row (table H) = H := funext (row_table H)
    have hc : TupleIteration.Checks (operator body A) (row (table H)) := by
      rw [hr]
      exact TupleIteration.canonical_checks _ _ _
    refine ⟨table H, (IterationFormula.eval_formula body hb (k + 1) A (table H)).mpr hc, ?_⟩
    obtain ⟨t, ht⟩ := last_exists (by omega : 0 < A.size) (k + 1)
    apply (eval_readLast query hq (k + 1) A (table H)).mpr
    refine ⟨t, ht, ?_⟩
    have hf := TupleIteration.final_row hF hc t (hbound t ht)
    exact (congrArg (fun R => eval query A Fin.elim0
      (Fin.cons R (fun r => Fin.elim0 r))) hf).symm ▸ h

end Lax988886Proofs.LfpElimination
