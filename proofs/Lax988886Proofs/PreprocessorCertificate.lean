import Lax988886Proofs.PreprocessorLayout
import Lax988886Proofs.StackSelect

namespace Lax988886Proofs.PreprocessorCertificate

open Lax988886.FiniteStructures Lax751879Proofs
open StackProgram StackBoolean PreprocessorLayout

def bits {σ : Vocabulary} {k : Nat} (B : Structure (k :: k :: σ)) : List Bool :=
  BinaryCertificates.decode (RelationalVerifier.tables B)

def program (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : EvalProgram (Port σ k p) Unit :=
  StackSelect.select (table σ k p 0) (table σ k p 1) (certificate σ k p)

noncomputable def result {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit) : EvalStore (Port σ k p) Unit :=
  ⟨((s.state.1.1, true), none),
    Function.update (Function.update (Function.update s.stk (table σ k p 0) []) (table σ k p 1) [])
      (certificate σ k p) (bits B).reverse⟩

theorem program_executes {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit)
    (ht : ∀ r, s.stk (table σ k p r) =
      (Lax751879.StructureEncoding.tuples B.size ((k :: k :: σ).get r)).map (B.relation r))
    (hc : s.stk (certificate σ k p) = []) :
    Executes (program σ k p) s (result B s) (5 * B.size ^ k + 3) := by
  have hm : s.stk (table σ k p 0) =
      (Lax751879.StructureEncoding.tuples B.size k).map ((RelationalVerifier.tables B) 0) := ht 0
  have hd : s.stk (table σ k p 1) =
      (Lax751879.StructureEncoding.tuples B.size k).map ((RelationalVerifier.tables B) 1) := ht 1
  have hlen : (s.stk (table σ k p 0)).length = (s.stk (table σ k p 1)).length := by
    rw [hm, hd]
    simp
  have hmd : table σ k p 0 ≠ table σ k p 1 := by
    intro he
    have hf : (0 : Fin (σ.length + 2)) = 1 :=
      Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inl.inj he)))
    exact Fin.zero_ne_one hf
  have hmlen : (s.stk (table σ k p 0)).length = B.size ^ k := by
    rw [hm, List.length_map]
    exact StructureEncoding.tuples_length B.size k
  have hp := StackSelect.select_store (table σ k p 0) (table σ k p 1) (certificate σ k p)
    hmd
    (by simp [table, certificate, slot]) (by simp [table, certificate, slot]) s hlen
  have he : BinaryCertificates.select (s.stk (table σ k p 0)) (s.stk (table σ k p 1)) = bits B := by
    rw [hm, hd]
    rfl
  rw [he, hc, List.append_nil, hmlen] at hp
  exact hp

end Lax988886Proofs.PreprocessorCertificate
