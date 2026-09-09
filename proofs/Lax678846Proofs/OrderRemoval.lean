import Lax678846Proofs.OrderFormula
import Lax678846Proofs.Isomorphism

namespace Lax678846Proofs.OrderRemoval

open Lax678846.FiniteStructures Lax678846.ExistentialSecondOrder

def relabel {σ : Vocabulary} (A : Structure σ) (e : Fin A.size ≃ Fin A.size) : Structure σ where
  size := A.size
  relation r a := A.relation r (e ∘ a)

def relabelIso {σ : Vocabulary} (A : Structure σ) (e : Fin A.size ≃ Fin A.size) :
    Isomorphism (relabel A e) A where
  equivalence := e
  preserves _ _ := rfl

def pull {τ : Vocabulary} {n : Nat} (e : Fin n ≃ Fin n)
    (R : Interpretation τ n) : Interpretation τ n := fun r a => R r (e ∘ a)

def tail {τ : Vocabulary} {n : Nat} (R : Interpretation (2 :: τ) n) : Interpretation τ n :=
  fun r => R r.succ

theorem pull_order {τ : Vocabulary} {n : Nat} (R : Interpretation (2 :: τ) n)
    (e : Fin n ≃ Fin n) (he : ∀ i j, OrderFormula.relation R (e i) (e j) ↔ i < j) :
    pull e R = OrderedFirstOrder.withOrder (tail (pull e R)) := by
  funext r
  refine Fin.cases ?_ (fun r => rfl) r
  change (fun a : Fin 2 → Fin n => R 0 (e ∘ a)) =
    (fun a : Fin 2 → Fin n => decide (a 0 < a 1))
  funext a
  change R 0 (e ∘ a) = decide (a 0 < a 1)
  apply Bool.eq_iff_iff.mpr
  have hpair : e ∘ a = OrderFormula.pair (e (a 0)) (e (a 1)) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have hrel := (Iff.of_eq (congrArg (fun t => R 0 t = true) hpair)).trans (he (a 0) (a 1))
  simpa only [decide_eq_true_eq] using hrel

theorem eval_relabel {σ τ : Vocabulary} {m : Nat} (φ : FirstOrder σ τ m)
    (A : Structure σ) (e : Fin A.size ≃ Fin A.size) (R : Interpretation τ A.size)
    (v : Fin m → Fin A.size) :
    φ.eval (relabel A e) (pull e R) (e.symm ∘ v) ↔ φ.eval A R v :=
  Isomorphism.eval_transport φ (Isomorphism.inverse (relabelIso A e)) R v

def sentence {σ τ : Vocabulary} (φ : FirstOrder σ (2 :: τ) 0) : Sentence σ :=
  ⟨2 :: τ, .conj OrderFormula.formula φ⟩

/-- An ordered existential definition of an invariant property becomes an
ordinary ∃SO definition by guessing and checking an auxiliary order. -/
theorem satisfies_iff {σ τ : Vocabulary} (Q : Property σ) (hQ : IsomorphismInvariant Q)
    (φ : FirstOrder σ (2 :: τ) 0)
    (hφ : ∀ A, Q A ↔ ∃ R : Interpretation τ A.size,
      φ.eval A (OrderedFirstOrder.withOrder R) Fin.elim0) (A : Structure σ) :
    Satisfies A (sentence φ) ↔ Q A := by
  constructor
  · rintro ⟨R, horder, hmatrix⟩
    have ho := (OrderFormula.eval_formula A R).mp horder
    obtain ⟨e, he⟩ := OrderEnumeration.enumerate (OrderFormula.relation R) ho
    have hnorm := (eval_relabel φ A e R Fin.elim0).mpr hmatrix
    have hv : e.symm ∘ (Fin.elim0 : Fin 0 → Fin A.size) = Fin.elim0 :=
      funext fun i => Fin.elim0 i
    have hn0 : φ.eval (relabel A e) (pull e R) Fin.elim0 :=
      congrArg (fun v => φ.eval (relabel A e) (pull e R) v) hv ▸ hnorm
    have hn1 : φ.eval (relabel A e) (OrderedFirstOrder.withOrder (tail (pull e R))) Fin.elim0 :=
      congrArg (fun W => φ.eval (relabel A e) W Fin.elim0) (pull_order R e he) ▸ hn0
    have hb : Q (relabel A e) := (hφ (relabel A e)).mpr ⟨tail (pull e R), hn1⟩
    exact (hQ (relabel A e) A ⟨relabelIso A e⟩).mp hb
  · intro h
    obtain ⟨R, hR⟩ := (hφ A).mp h
    exact ⟨OrderedFirstOrder.withOrder R,
      (OrderFormula.eval_formula A _).mpr (OrderFormula.canonical R), hR⟩

theorem definable {σ τ : Vocabulary} (Q : Property σ) (hQ : IsomorphismInvariant Q)
    (φ : FirstOrder σ (2 :: τ) 0)
    (hφ : ∀ A, Q A ↔ ∃ R : Interpretation τ A.size,
      φ.eval A (OrderedFirstOrder.withOrder R) Fin.elim0) : Definable Q :=
  ⟨sentence φ, fun A => (satisfies_iff Q hQ φ hφ A).symm⟩

end Lax678846Proofs.OrderRemoval
