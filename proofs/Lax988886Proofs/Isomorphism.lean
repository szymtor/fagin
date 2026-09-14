import Lax988886.ExistentialSecondOrder

namespace Lax988886Proofs.Isomorphism

open Lax988886.FiniteStructures Lax988886.ExistentialSecondOrder

def inverse {σ : Vocabulary} {A B : Structure σ} (e : Isomorphism A B) :
    Isomorphism B A where
  equivalence := e.equivalence.symm
  preserves r a := by
    have h := e.preserves r (e.equivalence.symm ∘ a)
    simpa [Function.comp_def] using h.symm

def transport {τ : Vocabulary} {n m : Nat} (e : Fin n ≃ Fin m)
    (R : Interpretation τ n) : Interpretation τ m :=
  fun r a => R r (e.symm ∘ a)

theorem map_cons {n m k : Nat} (e : Fin n ≃ Fin m) (a : Fin n)
    (v : Fin k → Fin n) :
    e ∘ Fin.cons a v = Fin.cons (e a) (e ∘ v) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem eval_transport {σ τ : Vocabulary} {m : Nat} (φ : FirstOrder σ τ m)
    {A B : Structure σ} (e : Isomorphism A B) (R : Interpretation τ A.size)
    (v : Fin m → Fin A.size) :
    φ.eval B (transport e.equivalence R) (e.equivalence ∘ v) ↔ φ.eval A R v := by
  induction φ with
  | truth => rfl
  | equal x y => exact e.equivalence.injective.eq_iff
  | relation r args =>
      change B.relation r (e.equivalence ∘ (v ∘ args)) = true ↔ _
      rw [e.preserves]
      rfl
  | «variable» r args => simp [FirstOrder.eval, transport, Function.comp_def]
  | neg φ ih => exact not_congr (ih v)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ v) (ihψ v)
  | exists' φ ih =>
      constructor
      · rintro ⟨b, hb⟩
        refine ⟨e.equivalence.symm b, (ih (Fin.cons (e.equivalence.symm b) v)).mp ?_⟩
        simpa [map_cons] using hb
      · rintro ⟨a, ha⟩
        refine ⟨e.equivalence a, ?_⟩
        simpa [map_cons] using (ih (Fin.cons a v)).mpr ha

theorem satisfies_transfer {σ : Vocabulary} (φ : Sentence σ)
    {A B : Structure σ} (e : Isomorphism A B) (h : Satisfies A φ) : Satisfies B φ := by
  obtain ⟨R, hR⟩ := h
  refine ⟨transport e.equivalence R, ?_⟩
  have hv : e.equivalence ∘ (Fin.elim0 : Fin 0 → Fin A.size) = Fin.elim0 :=
    funext fun i => Fin.elim0 i
  simpa [hv] using (eval_transport φ.matrix e R Fin.elim0).mpr hR

/--
---
conclusion: Lax988886.ExistentialSecondOrder.satisfiesInvariant
---
Transport both input tuples and existential witness relations along the
isomorphism; induction on the first-order matrix preserves satisfaction.
-/
theorem satisfiesInvariant {σ : Vocabulary} (φ : Sentence σ) :
    IsomorphismInvariant (fun A => Satisfies A φ) := by
  rintro A B ⟨e⟩
  exact ⟨satisfies_transfer φ e, satisfies_transfer φ (inverse e)⟩

theorem definable_invariant {σ : Vocabulary} {Q : Property σ} (hQ : Definable Q) :
    IsomorphismInvariant Q := by
  obtain ⟨φ, hφ⟩ := hQ
  intro A B e
  exact (hφ A).trans ((satisfiesInvariant φ A B e).trans (hφ B).symm)

end Lax988886Proofs.Isomorphism
