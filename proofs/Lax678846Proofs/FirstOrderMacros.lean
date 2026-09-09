import Lax678846Proofs.OrderedFirstOrder
import Lax979537Proofs.FormulaMacros

namespace Lax678846Proofs.FirstOrderMacros

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax
open Lax979537.FixedPointSemantics
open Lax979537Proofs.SyntaxOperations Lax979537Proofs.FormulaMacros
open Lax678846Proofs.OrderedFirstOrder

theorem noFixedPoints_rename {σ : Vocabulary} {m : Nat} {τ : List Nat}
    (φ : RawFormula σ m τ) {l : Nat} (f : Fin m → Fin l) :
    NoFixedPoints (rename φ f) ↔ NoFixedPoints φ := by
  induction φ generalizing l with
  | truth | equal | less | relation | «variable» | lfp => rfl
  | neg φ ih | exists' φ ih => exact ih _
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ _) (ihψ _)

theorem noFixedPoints_existsBlock {σ : Vocabulary} {τ : List Nat} (k : Nat)
    {m : Nat} (φ : RawFormula σ (k + m) τ) :
    NoFixedPoints (existsBlock k φ) ↔ NoFixedPoints φ := by
  induction k with
  | zero => exact noFixedPoints_rename _ _
  | succ k ih => exact (ih _).trans (noFixedPoints_rename φ _)

theorem noFixedPoints_of_firstOrder {σ : Vocabulary} {m : Nat} {τ : List Nat}
    (φ : RawFormula σ m τ) (hφ : FirstOrder φ) : NoFixedPoints φ := by
  induction φ with
  | truth | equal | less | relation => trivial
  | «variable» | lfp => exact hφ.elim
  | neg φ ih | exists' φ ih => exact ih hφ
  | conj φ ψ ihφ ihψ => exact ⟨ihφ hφ.1, ihψ hφ.2⟩

def implies {σ : Vocabulary} {m : Nat} {τ : List Nat}
    (φ ψ : RawFormula σ m τ) : RawFormula σ m τ := .neg (.conj φ (.neg ψ))

def equivalent {σ : Vocabulary} {m : Nat} {τ : List Nat}
    (φ ψ : RawFormula σ m τ) : RawFormula σ m τ :=
  .conj (implies φ ψ) (implies ψ φ)

def forallBlock {σ : Vocabulary} {τ : List Nat} (k : Nat) {m : Nat}
    (φ : RawFormula σ (k + m) τ) : RawFormula σ m τ :=
  .neg (existsBlock k (.neg φ))

theorem eval_implies {σ : Vocabulary} {m : Nat} {τ : List Nat}
    (φ ψ : RawFormula σ m τ) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size τ) :
    eval (implies φ ψ) A v η ↔ (eval φ A v η → eval ψ A v η) := by
  classical
  simp [implies, eval]

theorem eval_equivalent {σ : Vocabulary} {m : Nat} {τ : List Nat}
    (φ ψ : RawFormula σ m τ) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size τ) :
    eval (equivalent φ ψ) A v η ↔ (eval φ A v η ↔ eval ψ A v η) := by
  simp only [equivalent, eval, eval_implies]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem eval_forallBlock {σ : Vocabulary} {τ : List Nat} (k : Nat) {m : Nat}
    (φ : RawFormula σ (k + m) τ) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size τ) :
    eval (forallBlock k φ) A v η ↔
      ∀ a : Fin k → Fin A.size, eval φ A (Fin.append a v) η := by
  classical
  simp [forallBlock, eval, eval_existsBlock]

theorem noFixedPoints_forallBlock {σ : Vocabulary} {τ : List Nat} (k : Nat)
    {m : Nat} (φ : RawFormula σ (k + m) τ) :
    NoFixedPoints (forallBlock k φ) ↔ NoFixedPoints φ :=
  noFixedPoints_existsBlock k (.neg φ)

end Lax678846Proofs.FirstOrderMacros
