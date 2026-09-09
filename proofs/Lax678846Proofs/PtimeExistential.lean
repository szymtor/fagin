import Lax678846Proofs.RuleMatrices
import Lax979537Proofs.AcceptanceCorrectness

namespace Lax678846Proofs.PtimeExistential

open Turing Lax678846.FiniteStructures
open Lax979537.FixedPointSyntax Lax979537.FixedPointSemantics
open Lax979537Proofs.TupleOrder

noncomputable def acceptingRules (tm : FinTM2) (answer : tm.Γ tm.k₁)
    (σ : Vocabulary) (d : Nat) :
    List (Lax979537Proofs.ParameterizedRules.Rule σ 0 (Lax979537Proofs.TraceCodes.arity tm σ d)) := by
  letI := tm.σFin
  exact (Finset.univ : Finset tm.σ).toList.map fun state =>
    Lax979537Proofs.RuleConstants.compile
      (Lax979537Proofs.AcceptRule.template tm answer σ 0 d
        (Lax979537Proofs.TraceCodes.nodeWidth σ d) state)

theorem acceptance_eq (tm : FinTM2) (input : tm.Γ tm.k₀ ≃ Bool) (answer : tm.Γ tm.k₁)
    (σ : Vocabulary) (d : Nat) :
    anyOf ((acceptingRules tm answer σ d).map fun r =>
      Lax979537Proofs.RuleQuery.formula r (Lax979537Proofs.CompiledRun.rules tm input σ 0 d)) =
      Lax979537Proofs.AcceptanceFormula.formula tm input answer σ 0 d := by
  simp [acceptingRules, Lax979537Proofs.AcceptanceFormula.formula, List.map_map]
  rfl

/-- Reuse the concrete Immerman–Vardi computation closure, eliminate its
LFP by an existential stage table, patch small domains, and remove order.
This is the deterministic-verifier component of the Fagin proof. -/
theorem of_machine {σ : Vocabulary} (Q : Property σ) (hQ : IsomorphismInvariant Q)
    {f : List Bool → Bool} (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
    (hf : ∀ A : Structure σ, Q A ↔ f (encode A) = true) :
    Lax678846.ExistentialSecondOrder.Definable Q := by
  obtain ⟨d, hd⟩ := Lax979537Proofs.SimulationHorizon.exists_deciding_horizon h σ 0
  let rs := Lax979537Proofs.CompiledRun.rules h.tm h.inputAlphabet σ 0 d
  let qs := acceptingRules h.tm (h.outputAlphabet.symm true) σ d
  let k := Lax979537Proofs.TraceCodes.arity h.tm σ d
  let φ := LfpElimination.matrix (Lax979537Proofs.ParameterizedRules.body rs)
    (RuleMatrices.queries qs) (k + 1)
  apply SmallDomains.definable_of_above Q hQ (Lax979537Proofs.TraceCodes.threshold h.tm σ 0) φ
    (LfpElimination.noFixedPoints _ _ (RuleMatrices.body_noFixedPoints rs)
      (RuleMatrices.queries_noFixedPoints qs) (k + 1))
  intro A hA
  have hn : Lax979537Proofs.TraceCodes.threshold h.tm σ 0 ≤ A.size := Nat.le_of_lt hA
  have htwo : 2 ≤ A.size := by unfold Lax979537Proofs.TraceCodes.threshold at hA; omega
  let P : Lax979537.OrderedStructures.PointedStructure σ 0 := ⟨A, Fin.elim0⟩
  have he := RuleMatrices.exists_matrix_iff qs rs A htwo
  rw [acceptance_eq] at he
  have hc := Lax979537Proofs.AcceptanceCorrectness.eval_iff h d P hn (h.outputAlphabet.symm true)
  have hh := (hd P htwo true).trans eq_comm
  exact (hf A).trans (he.trans (hc.trans hh)).symm

end Lax678846Proofs.PtimeExistential
