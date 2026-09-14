import Lax988886.ExistentialSecondOrder

-- Preserve Lean 4.30 definition unfolding during elaboration.
set_option backward.isDefEq.respectTransparency false

namespace Lax988886Proofs.ExistentialProjection

open Lax988886.FiniteStructures Lax988886.ExistentialSecondOrder

/-- Expand a structure by one relation on its existing universe. -/
def expand {σ : Vocabulary} {k : Nat} (A : Structure σ)
    (S : (Fin k → Fin A.size) → Bool) : Structure (k :: σ) :=
  ⟨A.size, Fin.cons S A.relation⟩

/-- Move the first input relation into the existential witness vocabulary.
Element variables, and therefore the behavior on empty domains, are unchanged. -/
def matrix {σ τ : Vocabulary} {k m : Nat} :
    FirstOrder (k :: σ) τ m → FirstOrder σ (k :: τ) m
  | .truth => .truth
  | .equal x y => .equal x y
  | .relation r args => Fin.cases (fun args => .variable 0 args)
      (fun r args => .relation r args) r args
  | .variable r args => .variable r.succ args
  | .neg φ => .neg (matrix φ)
  | .conj φ ψ => .conj (matrix φ) (matrix ψ)
  | .exists' φ => .exists' (matrix φ)

theorem eval_matrix {σ τ : Vocabulary} {k m : Nat}
    (φ : FirstOrder (k :: σ) τ m) (A : Structure σ)
    (S : (Fin k → Fin A.size) → Bool) (R : Interpretation τ A.size)
    (v : Fin m → Fin A.size) :
    (matrix φ).eval A (Fin.cons S R) v ↔ φ.eval (expand A S) R v := by
  induction φ with
  | truth => rfl
  | equal => rfl
  | relation r args =>
    cases r using Fin.cases <;> simp [matrix, FirstOrder.eval, expand]
  | «variable» => rfl
  | neg φ ih => exact not_congr (ih v)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ v) (ihψ v)
  | exists' φ ih => exact exists_congr fun a => ih (Fin.cons a v)

def sentence {σ : Vocabulary} {k : Nat} (φ : Sentence (k :: σ)) : Sentence σ :=
  ⟨k :: φ.witnesses, matrix φ.matrix⟩

theorem satisfies_sentence {σ : Vocabulary} {k : Nat}
    (φ : Sentence (k :: σ)) (A : Structure σ) :
    Satisfies A (sentence φ) ↔
      ∃ S : (Fin k → Fin A.size) → Bool, Satisfies (expand A S) φ := by
  change (∃ R : Interpretation (k :: φ.witnesses) A.size,
    (matrix φ.matrix).eval A R Fin.elim0) ↔ _
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨R 0, (fun r => R r.succ), ?_⟩
    have hη : Fin.cons (R 0) (fun r => R r.succ) = R := by
      funext r; cases r using Fin.cases <;> rfl
    exact (eval_matrix φ.matrix A (R 0) (fun r => R r.succ) Fin.elim0).mp (hη.symm ▸ hR)
  · rintro ⟨S, R, hR⟩
    exact ⟨Fin.cons S R, (eval_matrix φ.matrix A S R Fin.elim0).mpr hR⟩

/-- Existential projection preserves ordinary ∃SO definability. Repeating
this construction handles any finite list of guessed input relations. -/
theorem definable {σ : Vocabulary} {k : Nat} (Q : Property (k :: σ))
    (hQ : Definable Q) :
    Definable (fun A : Structure σ => ∃ S, Q (expand A S)) := by
  obtain ⟨φ, hφ⟩ := hQ
  refine ⟨sentence φ, fun A => ?_⟩
  exact (exists_congr fun S => hφ (expand A S)).trans (satisfies_sentence φ A).symm

end Lax988886Proofs.ExistentialProjection
