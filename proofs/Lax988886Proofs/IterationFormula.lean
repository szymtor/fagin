import Lax988886Proofs.StageFormulas
import Lax988886Proofs.TupleIteration

namespace Lax988886Proofs.IterationFormula

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics
open Lax988886Proofs.OrderedFirstOrder Lax988886Proofs.FirstOrderMacros
open Lax988886Proofs.StageFormulas
open Lax751879Proofs.TupleAddresses

def previous (d k : Nat) : Fin d → Fin (d + d + k) := fun i => (i.castAdd d).castAdd k
def next (d k : Nat) : Fin d → Fin (d + d + k) := fun i => (Fin.natAdd d i).castAdd k
def data (d k : Nat) : Fin k → Fin (d + d + k) := Fin.natAdd (d + d)

def initial {σ : Vocabulary} (d k : Nat) : RawFormula σ 0 [d + k] :=
  forallBlock (d + k) (initialAt (Fin.castAdd k) (Fin.natAdd d))

def successors {σ : Vocabulary} {k : Nat} (body : RawFormula σ k [k]) (d : Nat) :
    RawFormula σ 0 [d + k] :=
  forallBlock (d + d + k) (successorAt body (previous d k) (next d k) (data d k))

/-- A single first-order sentence checks the entire existential stage table. -/
def formula {σ : Vocabulary} {k : Nat} (body : RawFormula σ k [k]) (d : Nat) :
    RawFormula σ 0 [d + k] := .conj (initial d k) (successors body d)

theorem noFixedPoints {σ : Vocabulary} {k : Nat} (body : RawFormula σ k [k])
    (hbody : NoFixedPoints body) (d : Nat) : NoFixedPoints (formula body d) := by
  exact ⟨(noFixedPoints_forallBlock _ _).mpr (initialAt_noFixedPoints _ _),
    (noFixedPoints_forallBlock _ _).mpr (successorAt_noFixedPoints body hbody _ _ _)⟩

theorem forall_append {α : Type} {m n : Nat} (P : (Fin (m + n) → α) → Prop) :
    (∀ v, P v) ↔ ∀ a b, P (Fin.append a b) := by
  constructor
  · intro h a b; exact h _
  · intro h v
    have hv : Fin.append (v ∘ Fin.castAdd n) (v ∘ Fin.natAdd m) = v := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp only [Fin.append_left, Function.comp_apply]
      · intro j; simp only [Fin.append_right, Function.comp_apply]
    exact hv ▸ h (v ∘ Fin.castAdd n) (v ∘ Fin.natAdd m)

theorem append_left_comp {α : Type} {m n : Nat} (a : Fin m → α) (b : Fin n → α) :
    Fin.append a b ∘ Fin.castAdd n = a := by funext i; simp

theorem append_right_comp {α : Type} {m n : Nat} (a : Fin m → α) (b : Fin n → α) :
    Fin.append a b ∘ Fin.natAdd m = b := by funext i; simp

theorem eval_initial {σ : Vocabulary} (d k : Nat) (A : OrderedStructure σ)
    (η : RelationEnv A.size [d + k]) :
    eval (initial d k) A Fin.elim0 η ↔
      ∀ t, (address A.size d t).val = 0 → row η t = ∅ := by
  rw [initial, eval_forallBlock, forall_append]
  simp only [Fin.append_elim0, Fin.cast_refl, Function.comp_id, eval_initialAt,
    append_left_comp, append_right_comp]
  constructor
  · intro h t ht
    ext a
    exact iff_false_intro (h t a ht)
  · intro h t a ht
    rw [h t ht]
    exact Set.notMem_empty a

theorem previous_comp {n d k : Nat} (s t : Fin d → Fin n) (a : Fin k → Fin n) :
    Fin.append (Fin.append s t) a ∘ previous d k = s := by
  funext i
  simp only [previous, Function.comp_apply, Fin.append_left]

theorem next_comp {n d k : Nat} (s t : Fin d → Fin n) (a : Fin k → Fin n) :
    Fin.append (Fin.append s t) a ∘ next d k = t := by
  funext i
  simp only [next, Function.comp_apply, Fin.append_left, Fin.append_right]

theorem data_comp {n d k : Nat} (s t : Fin d → Fin n) (a : Fin k → Fin n) :
    Fin.append (Fin.append s t) a ∘ data d k = a := append_right_comp _ _

theorem eval_successors {σ : Vocabulary} {k : Nat} (body : RawFormula σ k [k])
    (hbody : NoFixedPoints body) (d : Nat) (A : OrderedStructure σ)
    (η : RelationEnv A.size [d + k]) :
    eval (successors body d) A Fin.elim0 η ↔
      ∀ s t, (address A.size d t).val = (address A.size d s).val + 1 →
        row η t = operator body A (row η s) := by
  rw [successors, eval_forallBlock, forall_append]
  rw [forall_append]
  simp only [Fin.append_elim0, Fin.cast_refl, Function.comp_id,
    eval_successorAt body hbody, previous_comp, next_comp, data_comp]
  constructor
  · intro h s t ht
    exact Set.ext fun a => h s t a ht.symm
  · intro h s t a ht
    exact Set.ext_iff.mp (h s t ht.symm) a

theorem eval_formula {σ : Vocabulary} {k : Nat} (body : RawFormula σ k [k])
    (hbody : NoFixedPoints body) (d : Nat) (A : OrderedStructure σ)
    (η : RelationEnv A.size [d + k]) :
    eval (formula body d) A Fin.elim0 η ↔ TupleIteration.Checks (operator body A) (row η) := by
  exact and_congr (eval_initial d k A η) (eval_successors body hbody d A η)

end Lax988886Proofs.IterationFormula
