import Lax678846Proofs.OrderRemoval
import Lax678846Proofs.BooleanWitnesses
import Lax979537Proofs.FiniteExceptions

namespace Lax678846Proofs.SmallDomains

open Lax678846.FiniteStructures
open Lax979537.FixedPointSyntax Lax979537.FixedPointSemantics
open Lax979537Proofs.TupleOrder Lax979537Proofs.FormulaMacros
open Lax979537Proofs.FiniteExceptions Lax979537Proofs.AddressFormulas
open Lax678846Proofs.OrderedFirstOrder

theorem bounded_firstOrder {σ : Vocabulary} (Q : Property σ) (N : Nat) :
    FirstOrder (boundedFormula (fun A : Lax979537.OrderedStructures.PointedStructure σ 0 =>
      Q A.structureValue) N).val := by
  classical
  apply (firstOrder_anyOf _).mpr
  simp only [List.forall_mem_map]
  exact fun A _ => diagramRaw_firstOrder A

theorem copy_firstOrder {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (τ : List Nat) : FirstOrder (copyFO φ τ) := by
  induction φ with
  | truth | equal | less | relation | «variable» | lfp => trivial
  | neg φ ih | exists' φ ih => exact ih
  | conj φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩

noncomputable def patch {σ τ : Vocabulary} (Q : Property σ) (N : Nat)
    (φ : RawFormula σ 0 τ) : RawFormula σ 0 τ :=
  disj (copyFO (boundedFormula (fun A => Q A.structureValue) N).val τ)
    (.conj (.neg (sizeAtMost N)) φ)

theorem patch_noFixedPoints {σ τ : Vocabulary} (Q : Property σ) (N : Nat)
    (φ : RawFormula σ 0 τ) (hφ : NoFixedPoints φ) : NoFixedPoints (patch Q N φ) :=
  ⟨FirstOrderMacros.noFixedPoints_of_firstOrder _ (copy_firstOrder _ _),
    FirstOrderMacros.noFixedPoints_of_firstOrder _ (numeral_firstOrder N 0), hφ⟩

theorem eval_patch {σ τ : Vocabulary} (Q : Property σ) (N : Nat)
    (φ : RawFormula σ 0 τ) (A : Structure σ) (η : RelationEnv A.size τ) :
    eval (patch Q N φ) A Fin.elim0 η ↔
      (A.size ≤ N ∧ Q A) ∨ (N < A.size ∧ eval φ A Fin.elim0 η) := by
  rw [patch, eval_disj,
    eval_copyFO _ (bounded_firstOrder Q N) τ A Fin.elim0 (fun r => Fin.elim0 r)]
  have hb := satisfies_boundedFormula (fun B => Q B.structureValue) N
    (⟨A, Fin.elim0⟩ : Lax979537.OrderedStructures.PointedStructure σ 0)
  change eval _ A Fin.elim0 _ ↔ A.size ≤ N ∧ Q A at hb
  rw [hb]
  simp only [eval, eval_sizeAtMost, not_le]

theorem exists_patch {σ τ : Vocabulary} (Q : Property σ) (N : Nat)
    (φ : RawFormula σ 0 τ)
    (hφ : ∀ A, N < A.size → (Q A ↔ ∃ η : RelationEnv A.size τ, eval φ A Fin.elim0 η))
    (A : Structure σ) :
    Q A ↔ ∃ η : RelationEnv A.size τ, eval (patch Q N φ) A Fin.elim0 η := by
  constructor
  · intro h
    by_cases hn : A.size ≤ N
    · exact ⟨fun _ => ∅, (eval_patch Q N φ A _).mpr (Or.inl ⟨hn, h⟩)⟩
    · have hn' : N < A.size := Nat.lt_of_not_ge hn
      obtain ⟨η, hη⟩ := (hφ A hn').mp h
      exact ⟨η, (eval_patch Q N φ A η).mpr (Or.inr ⟨hn', hη⟩)⟩
  · rintro ⟨η, hη⟩
    rcases (eval_patch Q N φ A η).mp hη with h | ⟨hn, h⟩
    · exact h.2
    · exact (hφ A hn).mpr ⟨η, h⟩

/-- Patch finitely many domain sizes, then existentially choose and check
the auxiliary order. The resulting sentence is ordinary unordered ∃SO. -/
theorem definable_of_above {σ τ : Vocabulary} (Q : Property σ) (hQ : IsomorphismInvariant Q)
    (N : Nat) (φ : RawFormula σ 0 τ) (hφ : NoFixedPoints φ)
    (hcorrect : ∀ A, N < A.size →
      (Q A ↔ ∃ η : RelationEnv A.size τ, eval φ A Fin.elim0 η)) :
    Lax678846.ExistentialSecondOrder.Definable Q := by
  apply OrderRemoval.definable Q hQ (OrderedFirstOrder.translate (patch Q N φ))
  intro A
  exact (exists_patch Q N φ hcorrect A).trans
    (BooleanWitnesses.exists_ordered_matrix_iff _ (patch_noFixedPoints Q N φ hφ) A Fin.elim0).symm

end Lax678846Proofs.SmallDomains
