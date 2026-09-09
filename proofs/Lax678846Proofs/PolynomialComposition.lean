import Lax678846Proofs.MachineComposition
import Lax979537Proofs.PolynomialBounds

namespace Lax678846Proofs.PolynomialComposition

open Turing Lax979537Proofs.StackProgram Lax979537Proofs

theorem ioStore_length_le {K State : Type} {Γ : K → Type} [DecidableEq K]
    (port : K) (initial : State) (xs : List (Γ port)) (key : K) :
    ((ioStore port initial xs).stk key).length ≤ xs.length := by
  by_cases h : key = port
  · subst key; simp [ioStore]
  · simp [ioStore, h]

noncomputable def bound (p q : Polynomial Nat) : Polynomial Nat :=
  p + 6 * (Polynomial.X + p) + 4 + q.comp (Polynomial.X + p)

/-- Polynomial-time composition with a Boolean intermediate encoding.
This supplies the closure property needed for the expanded NP verifier by
an actual machine construction, independently of mathlib's unfinished
general composition theorem. -/
theorem comp {α β γ A C : Type} {ea : α → List A} {eb : β → List Bool} {ec : γ → List C}
    {f : α → β} {g : β → γ}
    (hf : TM2ComputableInPolyTime ea eb f) (hg : TM2ComputableInPolyTime eb ec g) :
    Nonempty (TM2ComputableInPolyTime ea ec (g ∘ f)) := by
  classical
  letI := hf.tm.kFin
  letI := hg.tm.kFin
  letI := hf.tm.σFin
  letI := hg.tm.σFin
  letI := hf.tm.ΛFin
  letI := hg.tm.ΛFin
  letI : Fintype (MachineComposition.Alphabet hf.tm hg.tm (MachineComposition.input hf.tm hg.tm)) :=
    hf.tm.Γk₀Fin
  let p := TMComputable.costPolynomial hf.tm hf.time
  let q := TMComputable.costPolynomial hg.tm hg.time
  let prog := MachineComposition.program hf.tm hg.tm hf.outputAlphabet hg.inputAlphabet
  let tm := machine prog (MachineComposition.input hf.tm hg.tm)
    (MachineComposition.output hf.tm hg.tm) (MachineComposition.initial hf.tm hg.tm)
  refine ⟨{ tm := tm
            inputAlphabet := hf.inputAlphabet
            outputAlphabet := hg.outputAlphabet
            time := bound p q
            outputsFun := ?_ }⟩
  intro a
  apply Classical.choice
  obtain ⟨d, hd, hp⟩ := TMComputable.of_machine hf a
  obtain ⟨e, he, hq⟩ := TMComputable.of_machine hg (f a)
  have hm := StackOutput.length_executes hp hf.tm.k₁
  have hout : ((ioStore hf.tm.k₁ (TMComputable.initial hf.tm)
      ((eb (f a)).map hf.outputAlphabet.symm)).stk hf.tm.k₁).length = (eb (f a)).length := by
    simp [ioStore]
  rw [hout] at hm
  have hin := ioStore_length_le hf.tm.k₀ (TMComputable.initial hf.tm)
    ((ea a).map hf.inputAlphabet.symm) hf.tm.k₁
  simp only [List.length_map] at hin
  have hmid : (eb (f a)).length ≤ (ea a).length + p.eval (ea a).length := by
    dsimp only [p]
    omega
  have hmono := PolynomialBounds.eval_mono q hmid
  have hrun := MachineComposition.executes hf.tm hg.tm hf.outputAlphabet hg.inputAlphabet hp hq
  refine ⟨⟨⟨d + (6 * (eb (f a)).length + 4 + e), ?_⟩, ?_⟩⟩
  · change Runs (compile prog id none) (some (entry prog))
      (ioStore (MachineComposition.input hf.tm hg.tm) (MachineComposition.initial hf.tm hg.tm)
        ((ea a).map hf.inputAlphabet.symm)) none
      (ioStore (MachineComposition.output hf.tm hg.tm) (MachineComposition.initial hf.tm hg.tm)
        ((ec (g (f a))).map hg.outputAlphabet.symm)) _
    exact compile_correct hrun (compile prog id none) id none (fun _ => rfl)
  · simp only [bound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_comp]
    change d ≤ p.eval (ea a).length at hd
    change e ≤ q.eval (eb (f a)).length at he
    omega

end Lax678846Proofs.PolynomialComposition
