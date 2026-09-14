import Lax988886Proofs.FirstOrderMacros
import Lax988886Proofs.RelationSlices
import Lax751879Proofs.AddressFormulas

-- Preserve Lean 4.30 definition unfolding during elaboration.
set_option backward.isDefEq.respectTransparency false

namespace Lax988886Proofs.StageFormulas

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics
open Lax751879Proofs.SyntaxOperations Lax751879Proofs.AddressFormulas
open Lax751879Proofs.TupleAddresses
open Lax988886Proofs.OrderedFirstOrder Lax988886Proofs.FirstOrderMacros

def row {n d k : Nat} (η : RelationEnv n [d + k]) (t : Fin d → Fin n) :
    Set (Fin k → Fin n) := fun a => η 0 (Fin.append t a)

def operator {σ : Vocabulary} {k : Nat} (body : RawFormula σ k [k])
    (A : OrderedStructure σ) (R : Set (Fin k → Fin A.size)) : Set (Fin k → Fin A.size) :=
  fun a => eval body A a (Fin.cons R (fun r => Fin.elim0 r))

def initialAt {σ : Vocabulary} {m d k : Nat} (t : Fin d → Fin m)
    (a : Fin k → Fin m) : RawFormula σ m [d + k] :=
  implies (first t) (.neg (.variable 0 (Fin.append t a)))

def successorAt {σ : Vocabulary} {m d k : Nat} (body : RawFormula σ k [k])
    (s t : Fin d → Fin m) (a : Fin k → Fin m) : RawFormula σ m [d + k] :=
  implies (successor s t)
    (equivalent (.variable 0 (Fin.append t a))
      (RelationSlices.translate (rename body a) s))

theorem compose_append {d k m n : Nat} (t : Fin d → Fin m) (a : Fin k → Fin m)
    (v : Fin m → Fin n) :
    v ∘ Fin.append t a = Fin.append (v ∘ t) (v ∘ a) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp only [Function.comp_apply, Fin.append_left]
  · intro j; simp only [Function.comp_apply, Fin.append_right]

theorem sliced_environment {n d k : Nat} (η : RelationEnv n [d + k])
    (t : Fin d → Fin n) :
    RelationSlices.environment (τ := [k]) t η = Fin.cons (row η t) (fun r => Fin.elim0 r) := by
  funext r
  have hr : r = 0 := by
    apply Fin.ext
    change r.val = 0
    have h : r.val < 1 := r.isLt
    omega
  subst r
  rfl

theorem eval_initialAt {σ : Vocabulary} {m d k : Nat} (t : Fin d → Fin m)
    (a : Fin k → Fin m) (A : OrderedStructure σ) (v : Fin m → Fin A.size)
    (η : RelationEnv A.size [d + k]) :
    eval (initialAt t a) A v η ↔
      ((address A.size d (v ∘ t)).val = 0 → ¬ row η (v ∘ t) (v ∘ a)) := by
  rw [initialAt, eval_implies, eval_first]
  change (_ → ¬ η 0 (v ∘ Fin.append t a)) ↔
    (_ → ¬ η 0 (Fin.append (v ∘ t) (v ∘ a)))
  exact imp_congr_right fun _ => not_congr
    (Iff.of_eq (congrArg (η 0) (compose_append t a v)))

theorem eval_successorAt {σ : Vocabulary} {m d k : Nat} (body : RawFormula σ k [k])
    (hbody : NoFixedPoints body) (s t : Fin d → Fin m) (a : Fin k → Fin m)
    (A : OrderedStructure σ) (v : Fin m → Fin A.size) (η : RelationEnv A.size [d + k]) :
    eval (successorAt body s t a) A v η ↔
      ((address A.size d (v ∘ s)).val + 1 = (address A.size d (v ∘ t)).val →
        (row η (v ∘ t) (v ∘ a) ↔ operator body A (row η (v ∘ s)) (v ∘ a))) := by
  have hb := RelationSlices.eval_translate (rename body a)
    ((noFixedPoints_rename body a).mpr hbody) s A v η
  rw [eval_rename, sliced_environment] at hb
  rw [successorAt, eval_implies, eval_successor, eval_equivalent]
  apply imp_congr_right
  intro _
  exact iff_congr (Iff.of_eq (congrArg (η 0) (compose_append t a v))) hb

theorem initialAt_noFixedPoints {σ : Vocabulary} {m d k : Nat} (t : Fin d → Fin m)
    (a : Fin k → Fin m) : NoFixedPoints (initialAt (σ := σ) t a) :=
  ⟨noFixedPoints_of_firstOrder _ (first_firstOrder t), trivial⟩

theorem successorAt_noFixedPoints {σ : Vocabulary} {m d k : Nat}
    (body : RawFormula σ k [k]) (hbody : NoFixedPoints body)
    (s t : Fin d → Fin m) (a : Fin k → Fin m) :
    NoFixedPoints (successorAt body s t a) := by
  have hb := RelationSlices.noFixedPoints (rename body a)
    ((noFixedPoints_rename body a).mpr hbody) s
  exact ⟨noFixedPoints_of_firstOrder _ (successor_firstOrder s t),
    ⟨⟨trivial, hb⟩, ⟨hb, trivial⟩⟩⟩

end Lax988886Proofs.StageFormulas
