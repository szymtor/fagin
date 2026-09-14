import Lax988886Proofs.SmallDomains
import Lax751879Proofs.RuleQuery

-- Preserve Lean 4.30 definition unfolding during elaboration.
set_option backward.isDefEq.respectTransparency false

namespace Lax988886Proofs.RuleMatrices

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics Lax751879.LeastFixedPoints
open Lax751879Proofs.ParameterizedRules Lax751879Proofs.SyntaxOperations
open Lax751879Proofs.TupleOrder Lax751879Proofs.FormulaMacros
open Lax988886Proofs.OrderedFirstOrder Lax988886Proofs.FirstOrderMacros

theorem noFixedPoints_allOf {σ : Vocabulary} {m : Nat} {τ : List Nat}
    (fs : List (RawFormula σ m τ)) :
    NoFixedPoints (allOf fs) ↔ ∀ φ ∈ fs, NoFixedPoints φ := by
  induction fs with
  | nil => simp [allOf, NoFixedPoints]
  | cons φ fs ih => simp [allOf, NoFixedPoints, ih]

theorem noFixedPoints_anyOf {σ : Vocabulary} {m : Nat} {τ : List Nat}
    (fs : List (RawFormula σ m τ)) :
    NoFixedPoints (anyOf fs) ↔ ∀ φ ∈ fs, NoFixedPoints φ := by
  induction fs with
  | nil => simp [anyOf, NoFixedPoints]
  | cons φ fs ih => simp [anyOf, disj, NoFixedPoints, ih]

theorem rule_noFixedPoints {σ : Vocabulary} {m k : Nat} (r : Rule σ m k) :
    NoFixedPoints r.formula := by
  apply (noFixedPoints_existsBlock _ _).mpr
  have hg : NoFixedPoints (copyFO r.guard [k]) :=
    noFixedPoints_of_firstOrder _ (SmallDomains.copy_firstOrder _ _)
  simp [Rule.matrix, NoFixedPoints, noFixedPoints_rename, noFixedPoints_allOf, hg]

theorem body_noFixedPoints {σ : Vocabulary} {m k : Nat} (rs : List (Rule σ m k)) :
    NoFixedPoints (Lax751879Proofs.ParameterizedRules.body rs) := by
  simp only [Lax751879Proofs.ParameterizedRules.body, noFixedPoints_anyOf, List.forall_mem_map]
  exact fun r _ => rule_noFixedPoints r

theorem operator_eq {σ : Vocabulary} {k : Nat} (rs : List (Rule σ 0 k)) (A : OrderedStructure σ) :
    StageFormulas.operator (Lax751879Proofs.ParameterizedRules.body rs) A =
      operator rs A Fin.elim0 := by
  funext R
  ext a
  have ha : Fin.append a (Fin.elim0 : Fin 0 → Fin A.size) = a := by simp
  change eval (Lax751879Proofs.ParameterizedRules.body rs) A a
    (Fin.cons R (fun r => Fin.elim0 r)) ↔ _
  rw [← ha]
  simp only [Lax751879Proofs.ParameterizedRules.body, eval_anyOf, exists_map, Rule.eval_formula,
    operator, Set.mem_setOf_eq, Fin.cons_zero]
  change (∃ r ∈ rs, r.holds A Fin.elim0 R a) ↔
    (∃ r ∈ rs, r.holds A Fin.elim0 R (Fin.append a Fin.elim0))
  rw [ha]

def query {σ : Vocabulary} {k : Nat} (r : Rule σ 0 k) : RawFormula σ 0 [k] :=
  existsBlock r.numVars (.conj (copyFO r.guard [k])
    (allOf (r.premises.map fun b => .variable 0 b)))

theorem query_noFixedPoints {σ : Vocabulary} {k : Nat} (r : Rule σ 0 k) :
    NoFixedPoints (query r) := by
  apply (noFixedPoints_existsBlock _ _).mpr
  refine ⟨noFixedPoints_of_firstOrder _ (SmallDomains.copy_firstOrder _ _), ?_⟩
  simp [noFixedPoints_allOf, NoFixedPoints]

theorem eval_query {σ : Vocabulary} {k : Nat} (r : Rule σ 0 k) (A : OrderedStructure σ)
    (η : RelationEnv A.size [k]) :
    eval (query r) A Fin.elim0 η ↔ ∃ out, r.holds A Fin.elim0 (η 0) out := by
  rw [query, eval_existsBlock]
  simp only [Fin.append_elim0, Fin.cast_refl, Function.comp_id, eval,
    eval_copyFO r.guard r.guard_firstOrder [k] A _ (fun i => Fin.elim0 i),
    eval_allOf, List.forall_mem_map]
  constructor
  · rintro ⟨v, hg, hp⟩
    exact ⟨v ∘ r.head, v, hg, funext (fun i => Fin.elim0 i), rfl, hp⟩
  · rintro ⟨out, v, hg, _, _, hp⟩
    exact ⟨v, hg, hp⟩

def queries {σ : Vocabulary} {k : Nat} (qs : List (Rule σ 0 k)) : RawFormula σ 0 [k] :=
  anyOf (qs.map query)

theorem queries_noFixedPoints {σ : Vocabulary} {k : Nat} (qs : List (Rule σ 0 k)) :
    NoFixedPoints (queries qs) := by
  simp only [queries, noFixedPoints_anyOf, List.forall_mem_map]
  exact fun r _ => query_noFixedPoints r

theorem eval_queries {σ : Vocabulary} {k : Nat} (qs rs : List (Rule σ 0 k))
    (A : OrderedStructure σ) :
    eval (queries qs) A Fin.elim0
      (Fin.cons (leastFixedPoint (operator rs A Fin.elim0)) (fun r => Fin.elim0 r)) ↔
    eval (anyOf (qs.map fun r => Lax751879Proofs.RuleQuery.formula r rs)) A Fin.elim0
      (fun r => Fin.elim0 r) := by
  simp only [queries, eval_anyOf, exists_map, eval_query,
    Lax751879Proofs.RuleQuery.eval_formula, Fin.cons_zero]

theorem exists_matrix_iff {σ : Vocabulary} {k : Nat} (qs rs : List (Rule σ 0 k))
    (A : OrderedStructure σ) (hn : 2 ≤ A.size) :
    (∃ η : RelationEnv A.size [(k + 1) + k],
      eval (LfpElimination.matrix (Lax751879Proofs.ParameterizedRules.body rs) (queries qs) (k + 1))
        A Fin.elim0 η) ↔
      eval (anyOf (qs.map fun r => Lax751879Proofs.RuleQuery.formula r rs)) A Fin.elim0
        (fun r => Fin.elim0 r) := by
  have hop := operator_eq rs A
  have hm : Monotone (StageFormulas.operator (Lax751879Proofs.ParameterizedRules.body rs) A) :=
    hop.symm ▸ operator_monotone rs A Fin.elim0
  have he := LfpElimination.exists_matrix_iff (Lax751879Proofs.ParameterizedRules.body rs)
    (queries qs) (body_noFixedPoints rs) (queries_noFixedPoints qs) A hn hm
  have hs := Iff.of_eq (congrArg (fun F => eval (queries qs) A Fin.elim0
    (Fin.cons (leastFixedPoint F) (fun r => Fin.elim0 r))) hop)
  exact he.trans (hs.trans (eval_queries qs rs A))

end Lax988886Proofs.RuleMatrices
