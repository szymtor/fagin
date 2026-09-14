import Lax751879Proofs.StackProgram

namespace Lax988886Proofs.StackControl

open Lax751879Proofs.StackProgram

variable {K σ τ : Type} {Γ : K → Type} [DecidableEq K]

def extendOp : Op Γ σ → Op Γ (σ × τ)
  | .push k f => .push k (fun s => f s.1)
  | .pop k f => .pop k (fun s b => (f s.1 b, s.2))
  | .peek k f => .peek k (fun s b => (f s.1 b, s.2))
  | .load f => .load (fun s => (f s.1, s.2))

/-- Extra finite control is preserved throughout a structured execution. -/
def extend : Program Γ σ → Program Γ (σ × τ)
  | .atom o => .atom (extendOp o)
  | .seq p q => .seq (extend p) (extend q)
  | .branch b p q => .branch (fun s => b s.1) (extend p) (extend q)
  | .loop b p => .loop (fun s => b s.1) (extend p)

def store (s : Store Γ σ) (extra : τ) : Store Γ (σ × τ) :=
  ⟨(s.state, extra), s.stk⟩

theorem store_ioStore (port : K) (initial : σ) (w : List (Γ port)) (extra : τ) :
    store (ioStore port initial w) extra = ioStore port (initial, extra) w := rfl

theorem extendOp_apply (o : Op Γ σ) (s : Store Γ σ) (extra : τ) :
    (extendOp o).apply (store s extra) = store (o.apply s) extra := by
  cases o <;> rfl

theorem executes_extend {p : Program Γ σ} {s t : Store Γ σ} {d : Nat}
    (h : Executes p s t d) (extra : τ) :
    Executes (extend p) (store s extra) (store t extra) d := by
  induction h with
  | atom o s => simpa only [extend, extendOp_apply] using Executes.atom (extendOp o) (store s extra)
  | seq _ _ ihp ihq => exact Executes.seq ihp ihq
  | branch_true hb _ ih => exact Executes.branch_true hb ih
  | branch_false hb _ ih => exact Executes.branch_false hb ih
  | loop_false hb => exact Executes.loop_false hb
  | loop_true hb _ _ ihp ihq => exact Executes.loop_true hb ihp ihq

def mapOp (e : σ ≃ τ) : Op Γ σ → Op Γ τ
  | .push k f => .push k (f ∘ e.symm)
  | .pop k f => .pop k (fun s b => e (f (e.symm s) b))
  | .peek k f => .peek k (fun s b => e (f (e.symm s) b))
  | .load f => .load (e ∘ f ∘ e.symm)

def map (e : σ ≃ τ) : Program Γ σ → Program Γ τ
  | .atom o => .atom (mapOp e o)
  | .seq p q => .seq (map e p) (map e q)
  | .branch b p q => .branch (b ∘ e.symm) (map e p) (map e q)
  | .loop b p => .loop (b ∘ e.symm) (map e p)

def mapStore (e : σ ≃ τ) (s : Store Γ σ) : Store Γ τ := ⟨e s.state, s.stk⟩

theorem mapOp_apply (e : σ ≃ τ) (o : Op Γ σ) (s : Store Γ σ) :
    (mapOp e o).apply (mapStore e s) = mapStore e (o.apply s) := by
  cases o <;> simp [mapOp, mapStore, Op.apply, Function.comp_def]

theorem executes_map (e : σ ≃ τ) {p : Program Γ σ} {s t : Store Γ σ} {d : Nat}
    (h : Executes p s t d) : Executes (map e p) (mapStore e s) (mapStore e t) d := by
  induction h with
  | atom o s => simpa only [map, mapOp_apply] using Executes.atom (mapOp e o) (mapStore e s)
  | seq _ _ ihp ihq => exact Executes.seq ihp ihq
  | branch_true hb _ ih => exact Executes.branch_true (by simpa [mapStore] using hb) ih
  | branch_false hb _ ih => exact Executes.branch_false (by simpa [mapStore] using hb) ih
  | loop_false hb => exact Executes.loop_false (by simpa [mapStore] using hb)
  | loop_true hb _ _ ihp ihq => exact Executes.loop_true (by simpa [mapStore] using hb) ihp ihq

def right (p : Program Γ σ) : Program Γ (τ × σ) :=
  map (Equiv.prodComm σ τ) (extend p)

theorem executes_right {p : Program Γ σ} {s t : Store Γ σ} {d : Nat}
    (h : Executes p s t d) (extra : τ) :
    Executes (right p) ⟨(extra, s.state), s.stk⟩ ⟨(extra, t.state), t.stk⟩ d :=
  executes_map (Equiv.prodComm σ τ) (executes_extend h extra)

end Lax988886Proofs.StackControl
