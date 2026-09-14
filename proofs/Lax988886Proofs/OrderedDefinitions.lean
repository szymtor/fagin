import Lax988886Proofs.PtimeExistential
import Lax988886Proofs.ExistentialProjection

namespace Lax988886Proofs.OrderedDefinitions

open Lax988886.FiniteStructures
open Lax751879.FixedPointSyntax Lax751879.FixedPointSemantics
open OrderedFirstOrder

/-- An intermediate ordered existential definition. This is used only
inside the proof: NP itself retains its standard machine definition. -/
def Definable {σ : Vocabulary} (Q : Property σ) : Prop :=
  ∃ (τ : Vocabulary) (φ : RawFormula σ 0 τ), NoFixedPoints φ ∧
    ∀ A, Q A ↔ ∃ η : RelationEnv A.size τ, eval φ A Fin.elim0 η

theorem of_above {σ τ : Vocabulary} (Q : Property σ) (N : Nat)
    (φ : RawFormula σ 0 τ) (hφ : NoFixedPoints φ)
    (hcorrect : ∀ A, N < A.size →
      (Q A ↔ ∃ η : RelationEnv A.size τ, eval φ A Fin.elim0 η)) : Definable Q :=
  ⟨τ, SmallDomains.patch Q N φ, SmallDomains.patch_noFixedPoints Q N φ hφ,
    SmallDomains.exists_patch Q N φ hcorrect⟩

theorem remove_order {σ : Vocabulary} (Q : Property σ) (hQ : IsomorphismInvariant Q)
    (h : Definable Q) : Lax988886.ExistentialSecondOrder.Definable Q := by
  obtain ⟨τ, φ, hφ, hc⟩ := h
  apply OrderRemoval.definable Q hQ (OrderedFirstOrder.translate φ)
  intro A
  exact (hc A).trans (BooleanWitnesses.exists_ordered_matrix_iff φ hφ A Fin.elim0).symm

/-- Keep the auxiliary order until after existential projection. In
particular, no invariance of the expanded verifier property is assumed. -/
theorem of_machine {σ : Vocabulary} (Q : Property σ) {f : List Bool → Bool}
    (h : Turing.TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
    (hf : ∀ A : Structure σ, Q A ↔ f (encode A) = true) : Definable Q := by
  obtain ⟨d, hd⟩ := Lax751879Proofs.SimulationHorizon.exists_deciding_horizon h σ 0
  let rs := Lax751879Proofs.CompiledRun.rules h.tm h.inputAlphabet σ 0 d
  let qs := PtimeExistential.acceptingRules h.tm (h.outputAlphabet.symm true) σ d
  let k := Lax751879Proofs.TraceCodes.arity h.tm σ d
  let φ := LfpElimination.matrix (Lax751879Proofs.ParameterizedRules.body rs)
    (RuleMatrices.queries qs) (k + 1)
  apply of_above Q (Lax751879Proofs.TraceCodes.threshold h.tm σ 0) φ
    (LfpElimination.noFixedPoints _ _ (RuleMatrices.body_noFixedPoints rs)
      (RuleMatrices.queries_noFixedPoints qs) (k + 1))
  intro A hA
  have hn : Lax751879Proofs.TraceCodes.threshold h.tm σ 0 ≤ A.size := Nat.le_of_lt hA
  have htwo : 2 ≤ A.size := by unfold Lax751879Proofs.TraceCodes.threshold at hA; omega
  let P : Lax751879.OrderedStructures.PointedStructure σ 0 := ⟨A, Fin.elim0⟩
  have he := RuleMatrices.exists_matrix_iff qs rs A htwo
  rw [PtimeExistential.acceptance_eq] at he
  have hc := Lax751879Proofs.AcceptanceCorrectness.eval_iff h d P hn (h.outputAlphabet.symm true)
  have hh := (hd P htwo true).trans eq_comm
  exact (hf A).trans (he.trans (hc.trans hh)).symm

/-- Move the first input relation into the witness prefix while keeping
the canonical order available. The fixed-point branch is excluded below. -/
def project {σ τ : Vocabulary} {k m : Nat} : RawFormula (k :: σ) m τ → RawFormula σ m (k :: τ)
  | .truth => .truth
  | .equal x y => .equal x y
  | .less x y => .less x y
  | .relation r args => Fin.cases (fun args => .variable 0 args)
      (fun r args => .relation r args) r args
  | .variable r args => .variable r.succ args
  | .neg φ => .neg (project φ)
  | .conj φ ψ => .conj (project φ) (project ψ)
  | .exists' φ => .exists' (project φ)
  | .lfp _ _ _ => .truth

theorem project_noFixedPoints {σ τ : Vocabulary} {k m : Nat}
    (φ : RawFormula (k :: σ) m τ) (hφ : NoFixedPoints φ) : NoFixedPoints (project φ) := by
  induction φ with
  | truth | equal | less | «variable» | lfp => trivial
  | relation r args => cases r using Fin.cases <;> trivial
  | neg φ ih | exists' φ ih => exact ih hφ
  | conj φ ψ ihφ ihψ => exact ⟨ihφ hφ.1, ihψ hφ.2⟩

theorem eval_project {σ τ : Vocabulary} {k m : Nat}
    (φ : RawFormula (k :: σ) m τ) (hφ : NoFixedPoints φ) (A : Structure σ)
    (S : (Fin k → Fin A.size) → Bool) (η : RelationEnv A.size τ) (v : Fin m → Fin A.size) :
    eval (project φ) A v (Fin.cons (fun a => S a = true) η) ↔
      eval φ (ExistentialProjection.expand A S) v η := by
  induction φ with
  | truth | equal | less | «variable» => rfl
  | relation r args => cases r using Fin.cases <;> rfl
  | neg φ ih => exact not_congr (ih hφ η v)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ hφ.1 η v) (ihψ hφ.2 η v)
  | exists' φ ih => exact exists_congr fun a => ih hφ η (Fin.cons a v)
  | lfp => exact hφ.elim

theorem projection {σ : Vocabulary} {k : Nat} (Q : Property (k :: σ)) (hQ : Definable Q) :
    Definable (fun A : Structure σ => ∃ S, Q (ExistentialProjection.expand A S)) := by
  classical
  obtain ⟨τ, φ, hφ, hc⟩ := hQ
  refine ⟨k :: τ, project φ, project_noFixedPoints φ hφ, fun A => ?_⟩
  constructor
  · rintro ⟨S, hS⟩
    obtain ⟨η, hη⟩ := (hc (ExistentialProjection.expand A S)).mp hS
    exact ⟨Fin.cons (fun a => S a = true) η, (eval_project φ hφ A S η Fin.elim0).mpr hη⟩
  · rintro ⟨η, hη⟩
    let S : (Fin k → Fin A.size) → Bool := fun a => decide (η 0 a)
    have he : Fin.cons (fun a => S a = true) (fun r => η r.succ) = η := by
      funext r
      refine Fin.cases ?_ (fun _ => rfl) r
      funext a
      simp [S]
    refine ⟨S, (hc (ExistentialProjection.expand A S)).mpr ⟨(fun r => η r.succ), ?_⟩⟩
    exact (eval_project φ hφ A S (fun r => η r.succ) Fin.elim0).mp (he.symm ▸ hη)

end Lax988886Proofs.OrderedDefinitions
