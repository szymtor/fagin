import Lax979537Proofs.StackProgram

namespace Lax678846Proofs.TMStatements

open Lax979537Proofs.StackProgram

variable {K Λ σ : Type} {Γ : K → Type}

/-- Store the arbitrary machine's program counter in finite control. This
lets its code run after a verified structured preprocessing program. -/
def compile : Turing.TM2.Stmt Γ Λ σ → Program Γ (σ × Option Λ)
  | .push k f q => .seq (.atom (.push k (fun s => f s.1))) (compile q)
  | .peek k f q => .seq (.atom (.peek k (fun s b => (f s.1 b, s.2)))) (compile q)
  | .pop k f q => .seq (.atom (.pop k (fun s b => (f s.1 b, s.2)))) (compile q)
  | .load f q => .seq (.atom (.load (fun s => (f s.1, s.2)))) (compile q)
  | .branch b q r => .branch (fun s => b s.1) (compile q) (compile r)
  | .goto f => .atom (.load (fun s => (s.1, some (f s.1))))
  | .halt => .atom (.load (fun s => (s.1, none)))

def weight : Turing.TM2.Stmt Γ Λ σ → Nat
  | .push _ _ q | .peek _ _ q | .pop _ _ q | .load _ q => weight q + 1
  | .branch _ q r => weight q + weight r + 1
  | .goto _ | .halt => 1

def view (c : Turing.TM2.Cfg Γ Λ σ) : Store Γ (σ × Option Λ) := ⟨(c.var, c.l), c.stk⟩

/-- Every machine statement is implemented with a constant cost depending
only on its finite syntax. The stack operations have their original meaning. -/
theorem compile_executes [DecidableEq K] (q : Turing.TM2.Stmt Γ Λ σ)
    (v : σ) (pc : Option Λ) (s : ∀ k, List (Γ k)) :
    ∃ d, d ≤ weight q ∧ Executes (compile q) ⟨(v,pc),s⟩ (view (Turing.TM2.stepAux q v s)) d := by
  induction q generalizing v pc s with
  | push k f q ih =>
    obtain ⟨d, hd, hp⟩ := ih v pc (Function.update s k (f v :: s k))
    have h := Executes.seq (Executes.atom (.push k (fun s => f s.1)) ⟨(v,pc),s⟩) hp
    exact ⟨1 + d, by simp only [weight]; omega, h⟩
  | peek k f q ih =>
    obtain ⟨d, hd, hp⟩ := ih (f v (s k).head?) pc s
    have h := Executes.seq (Executes.atom (.peek k (fun s b => (f s.1 b, s.2))) ⟨(v,pc),s⟩) hp
    exact ⟨1 + d, by simp only [weight]; omega, h⟩
  | pop k f q ih =>
    obtain ⟨d, hd, hp⟩ := ih (f v (s k).head?) pc (Function.update s k (s k).tail)
    have h := Executes.seq (Executes.atom (.pop k (fun s b => (f s.1 b, s.2))) ⟨(v,pc),s⟩) hp
    exact ⟨1 + d, by simp only [weight]; omega, h⟩
  | load f q ih =>
    obtain ⟨d, hd, hp⟩ := ih (f v) pc s
    have h := Executes.seq (Executes.atom (.load (fun s => (f s.1, s.2))) ⟨(v,pc),s⟩) hp
    exact ⟨1 + d, by simp only [weight]; omega, h⟩
  | branch b q r ihq ihr =>
    cases hb : b v with
    | true =>
      obtain ⟨d, hd, hp⟩ := ihq v pc s
      refine ⟨d + 1, by simp only [weight]; omega, ?_⟩
      simpa only [compile, Turing.TM2.stepAux, hb, Bool.cond_true] using
        Executes.branch_true (b := fun s => b s.1) (q := compile r) hb hp
    | false =>
      obtain ⟨d, hd, hp⟩ := ihr v pc s
      refine ⟨d + 1, by simp only [weight]; omega, ?_⟩
      simpa only [compile, Turing.TM2.stepAux, hb, Bool.cond_false] using
        Executes.branch_false (b := fun s => b s.1) (p := compile q) hb hp
  | goto f => exact ⟨1, le_rfl, Executes.atom _ _⟩
  | halt => exact ⟨1, le_rfl, Executes.atom _ _⟩

end Lax678846Proofs.TMStatements
