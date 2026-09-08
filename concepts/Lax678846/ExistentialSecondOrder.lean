import Lax678846.FiniteStructures

/-!
---
title: Existential second-order logic
type: definition and theorem
---
An existential second-order sentence has the form
$\exists R_1\cdots\exists R_s\,\varphi$, where each relation has a fixed
arity and the matrix $\varphi$ is first-order. Witness relations range over
all relations of their arities on the existing universe.

The first-order basis consists of truth, equality, input-relation and
witness-relation atoms, negation, conjunction, and existential element
quantification. There is no built-in order or fixed-point operator.
Element quantification binds variable zero. The witness vocabulary records
the finite second-order quantifier prefix.
-/

namespace Lax678846.ExistentialSecondOrder

open Lax678846.FiniteStructures

inductive FirstOrder (σ τ : Vocabulary) : Nat → Type
  | truth {m} : FirstOrder σ τ m
  | equal {m} (x y : Fin m) : FirstOrder σ τ m
  | relation {m} (r : Symbol σ) (args : Fin (σ.get r) → Fin m) : FirstOrder σ τ m
  | variable {m} (r : Symbol τ) (args : Fin (τ.get r) → Fin m) : FirstOrder σ τ m
  | neg {m} (φ : FirstOrder σ τ m) : FirstOrder σ τ m
  | conj {m} (φ ψ : FirstOrder σ τ m) : FirstOrder σ τ m
  | exists' {m} (φ : FirstOrder σ τ (m + 1)) : FirstOrder σ τ m

def FirstOrder.eval {σ τ : Vocabulary} {m : Nat} (φ : FirstOrder σ τ m)
    (A : Structure σ) (R : Interpretation τ A.size) (v : Fin m → Fin A.size) : Prop :=
  match φ with
  | .truth => True
  | .equal x y => v x = v y
  | .relation r args => A.relation r (v ∘ args) = true
  | .variable r args => R r (v ∘ args) = true
  | .neg ψ => ¬ ψ.eval A R v
  | .conj ψ χ => ψ.eval A R v ∧ χ.eval A R v
  | .exists' ψ => ∃ a : Fin A.size, ψ.eval A R (Fin.cons a v)

structure Sentence (σ : Vocabulary) where
  witnesses : Vocabulary
  matrix : FirstOrder σ witnesses 0

def Satisfies {σ : Vocabulary} (A : Structure σ) (φ : Sentence σ) : Prop :=
  ∃ R : Interpretation φ.witnesses A.size, φ.matrix.eval A R Fin.elim0

def Definable {σ : Vocabulary} (Q : Property σ) : Prop :=
  ∃ φ : Sentence σ, ∀ A : Structure σ, Q A ↔ Satisfies A φ

axiom satisfiesInvariant {σ : Vocabulary} (φ : Sentence σ) :
  IsomorphismInvariant (fun A => Satisfies A φ)

end Lax678846.ExistentialSecondOrder
