import Lax678846Proofs.TMComputable
import Lax678846Proofs.StackControl
import Lax979537Proofs.PolynomialBounds

namespace Lax678846Proofs.GuardedVerifier

open Turing Lax979537Proofs.StackProgram

def encode {α : Type} (ea : α → List Bool) (a : Bool × α) : List Bool := a.1 :: ea a.2

variable {α : Type} {ea : α → List Bool} {V : α → Bool}

def initial (h : TM2ComputableInPolyTime ea (fun b => [b]) V) := (TMComputable.initial h.tm, true)

def readFlag (h : TM2ComputableInPolyTime ea (fun b => [b]) V) :
    Program h.tm.Γ ((h.tm.σ × Option h.tm.Λ) × Bool) :=
  .atom (.pop h.tm.k₀ (fun s b => (s.1, (b.map h.inputAlphabet).getD false)))

def finish (h : TM2ComputableInPolyTime ea (fun b => [b]) V) :
    Program h.tm.Γ ((h.tm.σ × Option h.tm.Λ) × Bool) :=
  .seq (.atom (.pop h.tm.k₁ (fun s b => (s.1, s.2 && (b.map h.outputAlphabet).getD false))))
    (.seq (.atom (.push h.tm.k₁ (fun s => h.outputAlphabet.symm s.2)))
      (.atom (.load (fun _ => initial h))))

noncomputable def program (h : TM2ComputableInPolyTime ea (fun b => [b]) V) :
    Program h.tm.Γ ((h.tm.σ × Option h.tm.Λ) × Bool) :=
  .seq (readFlag h) (.seq (StackControl.extend (TMComputable.program h.tm)) (finish h))

theorem readFlag_executes (h : TM2ComputableInPolyTime ea (fun b => [b]) V) (a : α) (flag : Bool) :
    Executes (readFlag h) (ioStore h.tm.k₀ (initial h) ((encode ea (flag,a)).map h.inputAlphabet.symm))
      (ioStore h.tm.k₀ (TMComputable.initial h.tm, flag) ((ea a).map h.inputAlphabet.symm)) 1 := by
  have he : Op.apply (.pop h.tm.k₀
      (fun s : (h.tm.σ × Option h.tm.Λ) × Bool => fun b => (s.1, (b.map h.inputAlphabet).getD false)))
      (ioStore h.tm.k₀ (initial h) ((encode ea (flag,a)).map h.inputAlphabet.symm)) =
      ioStore h.tm.k₀ (TMComputable.initial h.tm, flag) ((ea a).map h.inputAlphabet.symm) := by
    apply Store.ext
    · simp [Op.apply, ioStore, encode, initial]
    · funext key
      by_cases hk : key = h.tm.k₀
      · subst key; simp [Op.apply, ioStore, encode]
      · simp [Op.apply, ioStore, hk]
  rw [← he]
  exact Executes.atom _ _

theorem finish_executes (h : TM2ComputableInPolyTime ea (fun b => [b]) V) (flag answer : Bool) :
    Executes (finish h)
      (ioStore h.tm.k₁ (TMComputable.initial h.tm, flag) [h.outputAlphabet.symm answer])
      (ioStore h.tm.k₁ (initial h) [h.outputAlphabet.symm (flag && answer)]) 3 := by
  let s := ioStore h.tm.k₁ (TMComputable.initial h.tm, flag) [h.outputAlphabet.symm answer]
  let pop : Op h.tm.Γ ((h.tm.σ × Option h.tm.Λ) × Bool) :=
    .pop h.tm.k₁ (fun s b => (s.1, s.2 && (b.map h.outputAlphabet).getD false))
  let push : Op h.tm.Γ ((h.tm.σ × Option h.tm.Λ) × Bool) :=
    .push h.tm.k₁ (fun s => h.outputAlphabet.symm s.2)
  let reset : Op h.tm.Γ ((h.tm.σ × Option h.tm.Λ) × Bool) := .load (fun _ => initial h)
  have hh := Executes.seq (Executes.atom pop s)
    (Executes.seq (Executes.atom push (pop.apply s)) (Executes.atom reset (push.apply (pop.apply s))))
  have he : reset.apply (push.apply (pop.apply s)) =
      ioStore h.tm.k₁ (initial h) [h.outputAlphabet.symm (flag && answer)] := by
    apply Store.ext
    · rfl
    · funext key
      by_cases hk : key = h.tm.k₁
      · subst key; simp [pop, push, reset, s, Op.apply, ioStore]
      · simp [pop, push, reset, s, Op.apply, ioStore, hk]
  rw [he] at hh
  exact hh

theorem program_executes (h : TM2ComputableInPolyTime ea (fun b => [b]) V) (a : Bool × α) :
    ∃ d, d ≤ (TMComputable.costPolynomial h.tm h.time + 4).eval (encode ea a).length ∧
      Executes (program h) (ioStore h.tm.k₀ (initial h) ((encode ea a).map h.inputAlphabet.symm))
        (ioStore h.tm.k₁ (initial h) [h.outputAlphabet.symm (a.1 && V a.2)]) d := by
  obtain ⟨d, hd, hp⟩ := TMComputable.of_machine h a.2
  have hm := StackControl.executes_extend hp a.1
  simp only [StackControl.store_ioStore, List.map_cons, List.map_nil] at hm
  have hh := Executes.seq (readFlag_executes h a.2 a.1)
    (Executes.seq hm (finish_executes h a.1 (V a.2)))
  have hmono := Lax979537Proofs.PolynomialBounds.eval_mono (TMComputable.costPolynomial h.tm h.time)
    (show (ea a.2).length ≤ (encode ea a).length by simp [encode])
  refine ⟨1 + (d + 3), ?_, hh⟩
  simp only [Polynomial.eval_add, Polynomial.eval_ofNat]
  omega

/-- Add a one-bit guard to the original NP verifier. The preprocessor can
emit its length-check result as that bit, then reuse polynomial composition. -/
theorem computable (h : TM2ComputableInPolyTime ea (fun b => [b]) V) :
    Nonempty (TM2ComputableInPolyTime (encode ea) (fun b => [b]) (fun a => a.1 && V a.2)) := by
  classical
  letI := h.tm.kFin
  letI := h.tm.σFin
  letI := h.tm.ΛFin
  letI := h.tm.Γk₀Fin
  refine ⟨{ tm := machine (program h) h.tm.k₀ h.tm.k₁ (initial h)
            inputAlphabet := h.inputAlphabet
            outputAlphabet := h.outputAlphabet
            time := TMComputable.costPolynomial h.tm h.time + 4
            outputsFun := ?_ }⟩
  intro a
  apply Classical.choice
  obtain ⟨d, hd, hp⟩ := program_executes h a
  refine ⟨⟨⟨d, ?_⟩, hd⟩⟩
  change Runs (compile (program h) id none) (some (entry (program h)))
    (ioStore h.tm.k₀ (initial h) ((encode ea a).map h.inputAlphabet.symm)) none
    (ioStore h.tm.k₁ (initial h) [h.outputAlphabet.symm (a.1 && V a.2)]) d
  exact compile_correct hp (compile (program h) id none) id none (fun _ => rfl)

end Lax678846Proofs.GuardedVerifier
