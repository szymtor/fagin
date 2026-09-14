import Lax751879.OrderedStructures
import Lax751879.StructureEncoding

/-!
---
title: Finite relational structures and their properties
type: definition
---
A finite relational vocabulary is a finite list of relation arities. A
structure has universe `Fin n` and an interpretation of each relation.
The numbering is used for binary input encodings; it is not available as
an order predicate in the logic. Properties are required to be invariant
under isomorphism, so they do not depend on the numbering.

The representation and dense binary encoding are reused from the
Immerman–Vardi submission. Here we forget its distinguished order. Empty
universes and nullary relations are allowed.
-/

namespace Lax988886.FiniteStructures

abbrev Vocabulary := Lax751879.OrderedStructures.Vocabulary
abbrev Symbol := Lax751879.OrderedStructures.Symbol
abbrev Structure := Lax751879.OrderedStructures.OrderedStructure
abbrev Interpretation (σ : Vocabulary) (n : Nat) :=
  (r : Symbol σ) → (Fin (σ.get r) → Fin n) → Bool
abbrev Property (σ : Vocabulary) := Structure σ → Prop

structure Isomorphism {σ : Vocabulary} (A B : Structure σ) where
  equivalence : Fin A.size ≃ Fin B.size
  preserves : ∀ (r : Symbol σ) (a : Fin (σ.get r) → Fin A.size),
    B.relation r (equivalence ∘ a) = A.relation r a

def IsomorphismInvariant {σ : Vocabulary} (Q : Property σ) : Prop :=
  ∀ A B : Structure σ, Nonempty (Isomorphism A B) → (Q A ↔ Q B)

def encode {σ : Vocabulary} (A : Structure σ) : List Bool :=
  Lax751879.StructureEncoding.encode ⟨A, Fin.elim0⟩

def language {σ : Vocabulary} (Q : Property σ) (w : List Bool) : Prop :=
  ∃ A : Structure σ, encode A = w ∧ Q A

end Lax988886.FiniteStructures
