import Lax988886Proofs.OrderEnumeration
import Lax988886Proofs.OrderedFirstOrder

-- Preserve Lean 4.30 definition unfolding during elaboration.
set_option backward.isDefEq.respectTransparency false

namespace Lax988886Proofs.OrderFormula

open Lax988886.FiniteStructures Lax988886.ExistentialSecondOrder

def pair {α : Type} (a b : α) : Fin 2 → α := Fin.cons a (Fin.cons b Fin.elim0)

def relation {τ : Vocabulary} {n : Nat} (R : Interpretation (2 :: τ) n)
    (a b : Fin n) : Prop := R 0 (pair a b) = true

def atom {σ τ : Vocabulary} {m : Nat} (a b : Fin m) : FirstOrder σ (2 :: τ) m :=
  .variable 0 (pair a b)

def all {σ τ : Vocabulary} {m : Nat} (φ : FirstOrder σ τ (m + 1)) : FirstOrder σ τ m :=
  .neg (.exists' (.neg φ))

def implies {σ τ : Vocabulary} {m : Nat} (φ ψ : FirstOrder σ τ m) : FirstOrder σ τ m :=
  .neg (.conj φ (.neg ψ))

def disj {σ τ : Vocabulary} {m : Nat} (φ ψ : FirstOrder σ τ m) : FirstOrder σ τ m :=
  .neg (.conj (.neg φ) (.neg ψ))

/-- The first witness relation is a strict total order on the entire domain. -/
def formula {σ τ : Vocabulary} : FirstOrder σ (2 :: τ) 0 :=
  .conj (all (.neg (atom 0 0)))
    (.conj (all (all (all (implies (.conj (atom 0 1) (atom 1 2)) (atom 0 2)))))
      (all (all (disj (atom 0 1) (disj (.equal 0 1) (atom 1 0))))))

theorem comp_pair {α β : Type} (f : α → β) (a b : α) :
    f ∘ pair a b = pair (f a) (f b) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun j => Fin.elim0 j) j

theorem eval_atom {σ τ : Vocabulary} {m : Nat} (a b : Fin m) (A : Structure σ)
    (R : Interpretation (2 :: τ) A.size) (v : Fin m → Fin A.size) :
    (atom a b).eval A R v ↔ relation R (v a) (v b) := by
  exact Iff.of_eq (congrArg (fun t => R 0 t = true) (comp_pair v a b))

theorem eval_all {σ τ : Vocabulary} {m : Nat} (φ : FirstOrder σ τ (m + 1))
    (A : Structure σ) (R : Interpretation τ A.size) (v : Fin m → Fin A.size) :
    (all φ).eval A R v ↔ ∀ a, φ.eval A R (Fin.cons a v) := by
  classical
  simp [all, FirstOrder.eval]

theorem eval_implies {σ τ : Vocabulary} {m : Nat} (φ ψ : FirstOrder σ τ m)
    (A : Structure σ) (R : Interpretation τ A.size) (v : Fin m → Fin A.size) :
    (implies φ ψ).eval A R v ↔ (φ.eval A R v → ψ.eval A R v) := by
  classical
  simp [implies, FirstOrder.eval]

theorem eval_disj {σ τ : Vocabulary} {m : Nat} (φ ψ : FirstOrder σ τ m)
    (A : Structure σ) (R : Interpretation τ A.size) (v : Fin m → Fin A.size) :
    (disj φ ψ).eval A R v ↔ (φ.eval A R v ∨ ψ.eval A R v) := by
  classical
  by_cases h : φ.eval A R v <;> simp [disj, FirstOrder.eval, h]

theorem eval_formula {σ τ : Vocabulary} (A : Structure σ)
    (R : Interpretation (2 :: τ) A.size) :
    formula.eval A R Fin.elim0 ↔ OrderEnumeration.StrictTotal (relation R) := by
  simp only [formula, FirstOrder.eval, eval_all, eval_implies, eval_disj, eval_atom,
    Fin.cons_zero]
  constructor
  · rintro ⟨hi, ht, hc⟩
    exact ⟨hi, fun a b c hab hbc => ht c b a ⟨hab, hbc⟩, fun a b => hc b a⟩
  · rintro ⟨hi, ht, hc⟩
    exact ⟨hi, fun a b c h => ht c b a h.1 h.2, fun a b => hc b a⟩

theorem canonical {τ : Vocabulary} {n : Nat} (R : Interpretation τ n) :
    OrderEnumeration.StrictTotal (relation (OrderedFirstOrder.withOrder R)) := by
  have h (a b : Fin n) : relation (OrderedFirstOrder.withOrder R) a b ↔ a < b := by
    simp [relation, OrderedFirstOrder.withOrder, pair]
  refine ⟨fun a ha => (lt_irrefl a) ((h a a).mp ha), ?_, ?_⟩
  · intro a b c hab hbc
    exact (h a c).mpr (lt_trans ((h a b).mp hab) ((h b c).mp hbc))
  · intro a b
    rcases lt_trichotomy a b with hab | hab | hab
    · exact Or.inl ((h a b).mpr hab)
    · exact Or.inr (Or.inl hab)
    · exact Or.inr (Or.inr ((h b a).mpr hab))

end Lax988886Proofs.OrderFormula
