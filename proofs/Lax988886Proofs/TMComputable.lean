import Lax988886Proofs.TMInterpreter

namespace Lax988886Proofs.TMComputable

open Turing Lax751879Proofs.StackProgram

noncomputable def labels (tm : FinTM2) : List tm.Λ := by
  letI := tm.ΛFin
  exact Finset.univ.toList

theorem mem_labels (tm : FinTM2) (l : tm.Λ) : l ∈ labels tm := by
  letI := tm.ΛFin
  simp [labels]

def initial (tm : FinTM2) : tm.σ × Option tm.Λ := (tm.initialState, some tm.main)

/-- An arbitrary finite machine as a structured program, with its original
stack alphabets and a reset of the extra program-counter register at the end. -/
noncomputable def program (tm : FinTM2) : Program tm.Γ (tm.σ × Option tm.Λ) := by
  classical
  exact .seq (TMInterpreter.run tm.m (labels tm)) (.atom (.load (fun _ => initial tm)))

noncomputable def factor (tm : FinTM2) : Nat := TMInterpreter.dispatchCost tm.m (labels tm) + 1

theorem executes (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) (ys : List (tm.Γ tm.k₁)) (time : Nat)
    (h : TM2OutputsInTime tm xs (some ys) time) :
    ∃ d, d ≤ factor tm * time + 2 ∧
      Executes (program tm) (ioStore tm.k₀ (initial tm) xs) (ioStore tm.k₁ (initial tm) ys) d := by
  classical
  have he := h.evals_in_steps
  change (fun c : Option (TM2.Cfg tm.Γ tm.Λ tm.σ) => c.bind (TM2.step tm.m))^[h.steps]
    (some (initList tm xs)) = some (haltList tm ys) at he
  obtain ⟨d, hd, hp⟩ := TMInterpreter.run_executes tm.m (labels tm) (mem_labels tm)
    h.steps (initList tm xs) (haltList tm ys) rfl he
  have hin : TMStatements.view (initList tm xs) = ioStore tm.k₀ (initial tm) xs := rfl
  rw [hin] at hp
  have hl := Executes.atom (.load (fun _ : tm.σ × Option tm.Λ => initial tm))
    (TMStatements.view (haltList tm ys))
  have hout : Op.apply (.load (fun _ : tm.σ × Option tm.Λ => initial tm))
      (TMStatements.view (haltList tm ys)) = ioStore tm.k₁ (initial tm) ys := rfl
  rw [hout] at hl
  refine ⟨d + 1, ?_, Executes.seq hp hl⟩
  have hb := Nat.mul_le_mul_left (factor tm) h.steps_le_m
  change d ≤ factor tm * h.steps + 1 at hd
  omega

noncomputable def costPolynomial (tm : FinTM2) (p : Polynomial Nat) : Polynomial Nat :=
  Polynomial.C (factor tm) * p + 2

/-- Reuse a verifier supplied by the standard NP hypothesis inside a
structured program. Its polynomial time bound is preserved. -/
theorem of_machine {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    ∃ d, d ≤ (costPolynomial h.tm h.time).eval (ea a).length ∧
      Executes (program h.tm)
        (ioStore h.tm.k₀ (initial h.tm) ((ea a).map h.inputAlphabet.symm))
        (ioStore h.tm.k₁ (initial h.tm) ((eb (f a)).map h.outputAlphabet.symm)) d := by
  obtain ⟨d, hd, hp⟩ := executes h.tm _ _ _ (h.outputsFun a)
  exact ⟨d, by simpa [costPolynomial] using hd, hp⟩

end Lax988886Proofs.TMComputable
