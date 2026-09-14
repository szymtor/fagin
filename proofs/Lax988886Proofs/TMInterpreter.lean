import Lax988886Proofs.TMStatements

namespace Lax988886Proofs.TMInterpreter

open Lax751879Proofs.StackProgram

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K] [DecidableEq Λ]

/-- Select a machine instruction using its finite list of labels. -/
def dispatch (code : Λ → Turing.TM2.Stmt Γ Λ σ) : List Λ → Program Γ (σ × Option Λ)
  | [] => .atom (.load id)
  | l :: labels => .branch (fun s => decide (s.2 = some l))
      (TMStatements.compile (code l)) (dispatch code labels)

def dispatchCost (code : Λ → Turing.TM2.Stmt Γ Λ σ) : List Λ → Nat
  | [] => 1
  | l :: labels => TMStatements.weight (code l) + dispatchCost code labels + 1

theorem dispatch_executes (code : Λ → Turing.TM2.Stmt Γ Λ σ) (labels : List Λ)
    (l : Λ) (hl : l ∈ labels) (v : σ) (s : ∀ k, List (Γ k)) :
    ∃ d, d ≤ dispatchCost code labels ∧ Executes (dispatch code labels) ⟨(v,some l),s⟩
      (TMStatements.view (Turing.TM2.stepAux (code l) v s)) d := by
  induction labels with
  | nil => simp at hl
  | cons a labels ih =>
    by_cases ha : a = l
    · subst a
      obtain ⟨d, hd, hp⟩ := TMStatements.compile_executes (code l) v (some l) s
      refine ⟨d + 1, by simp only [dispatchCost]; omega, ?_⟩
      exact Executes.branch_true (b := fun s => decide (s.2 = some l))
        (q := dispatch code labels) (by simp) hp
    · have hm : l ∈ labels := (List.mem_cons.mp hl).resolve_left (Ne.symm ha)
      obtain ⟨d, hd, hp⟩ := ih hm
      refine ⟨d + 1, by simp only [dispatchCost]; omega, ?_⟩
      exact Executes.branch_false (b := fun s => decide (s.2 = some a))
        (p := TMStatements.compile (code a)) (by simp [Ne.symm ha]) hp

/-- An arbitrary finite TM2 program can run inside the structured language
used for preprocessing. Its counter is part of finite control. -/
def run (code : Λ → Turing.TM2.Stmt Γ Λ σ) (labels : List Λ) : Program Γ (σ × Option Λ) :=
  .loop (fun s => s.2.isSome) (dispatch code labels)

theorem iterate_none (code : Λ → Turing.TM2.Stmt Γ Λ σ) (n : Nat) :
    (fun c : Option (Turing.TM2.Cfg Γ Λ σ) => c.bind (Turing.TM2.step code))^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply, Option.bind_none] using ih

/-- The interpreter has only constant overhead per original machine step.
The constant depends on the finite code, never on the input or its length. -/
theorem run_executes (code : Λ → Turing.TM2.Stmt Γ Λ σ) (labels : List Λ)
    (hall : ∀ l, l ∈ labels) (n : Nat) (c t : Turing.TM2.Cfg Γ Λ σ) (ht : t.l = none)
    (h : (fun c : Option (Turing.TM2.Cfg Γ Λ σ) => c.bind (Turing.TM2.step code))^[n]
      (some c) = some t) :
    ∃ d, d ≤ (dispatchCost code labels + 1) * n + 1 ∧
      Executes (run code labels) (TMStatements.view c) (TMStatements.view t) d := by
  induction n generalizing c with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
    subst c
    exact ⟨1, by simp, Executes.loop_false (by simp [TMStatements.view, ht])⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply, Option.bind_some] at h
    cases c with
    | mk pc v s =>
      cases pc with
      | none =>
        change (fun c : Option (Turing.TM2.Cfg Γ Λ σ) => c.bind (Turing.TM2.step code))^[n]
          none = some t at h
        rw [iterate_none] at h
        cases h
      | some l =>
        change (fun c : Option (Turing.TM2.Cfg Γ Λ σ) => c.bind (Turing.TM2.step code))^[n]
          (some (Turing.TM2.stepAux (code l) v s)) = some t at h
        obtain ⟨d, hd, hp⟩ := dispatch_executes code labels l (hall l) v s
        obtain ⟨e, he, hq⟩ := ih (Turing.TM2.stepAux (code l) v s) h
        refine ⟨d + e + 1, ?_, Executes.loop_true
          (b := fun s : σ × Option Λ => s.2.isSome) rfl hp hq⟩
        rw [Nat.mul_succ]
        omega

end Lax988886Proofs.TMInterpreter
