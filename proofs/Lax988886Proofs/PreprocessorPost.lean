import Lax988886Proofs.PreprocessorCheck
import Lax988886Proofs.PreprocessorPack

namespace Lax988886Proofs.PreprocessorPost

open Lax988886.FiniteStructures Lax751879Proofs
open StackProgram StackBoolean PreprocessorLayout

noncomputable def program (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : EvalProgram (Port σ k p) Unit :=
  .seq (PreprocessorTables.program σ k p)
    (.seq (PreprocessorCheck.program σ k p) (PreprocessorPack.program σ k p))

noncomputable def cost (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : Polynomial Nat :=
  PreprocessorTables.cost σ k p + PreprocessorCheck.cost σ k p + PreprocessorPack.cost σ k

noncomputable def result {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit) : EvalStore (Port σ k p) Unit :=
  PreprocessorPack.result B (StackBoolean.result (PreprocessorCheck.accepts p B) (PreprocessorTables.result B s))

theorem result_output {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit) :
    (result B s).stk (pair σ k p) = PreprocessorPack.output B (PreprocessorCheck.accepts p B) := by
  simp [result, PreprocessorPack.result, StackBoolean.result]

theorem program_executes {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit) (h : Ready B s) :
    ∃ d, d ≤ (cost σ k p).eval B.size ∧ Executes (program σ k p) s (result B s) d := by
  obtain ⟨d, hd, hp⟩ := PreprocessorTables.program_executes B s h
  have hu := PreprocessorTables.result_prepared B s h
  obtain ⟨e, he, hq⟩ := PreprocessorCheck.program_executes B (PreprocessorTables.result B s) hu
  obtain ⟨f, hf, hr⟩ := PreprocessorPack.program_executes B
    (StackBoolean.result (PreprocessorCheck.accepts p B) (PreprocessorTables.result B s))
    hu.word hu.certificate hu.pair hu.tmp
  refine ⟨d + (e + f), ?_, Executes.seq hp (Executes.seq hq hr)⟩
  simp only [cost, Polynomial.eval_add]
  omega

end Lax988886Proofs.PreprocessorPost
