import Lax678846Proofs.PreprocessorLayout
import Lax678846Proofs.StackConcat
import Lax678846Proofs.StackCertificateHeader

namespace Lax678846Proofs.PreprocessorWord

open Lax678846.FiniteStructures Lax979537Proofs
open StackProgram StackBoolean PreprocessorLayout

def program (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : EvalProgram (Port σ k p) Unit :=
  .seq (StackConcat.copy (word σ k p) (tmp σ k p) (baseTables σ k p))
    (StackCertificateHeader.prepend (domain σ k p) (word σ k p) (tmp σ k p))

noncomputable def result {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit) : EvalStore (Port σ k p) Unit :=
  ⟨(s.state.1, none), Function.update s.stk (word σ k p) (encode (RelationalVerifier.base B))⟩

/-- Reconstruct the base structure's exact input, preserving its domain
counter and all relation tables for the remaining preprocessing phases. -/
theorem program_executes {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit) (h : Ready B s) :
    ∃ d, d ≤ 7 * (encode (RelationalVerifier.base B)).length + 4 * σ.length + 6 ∧
      Executes (program σ k p) s (result B s) d := by
  have hwt : word σ k p ≠ tmp σ k p := by simp [word, tmp, slot]
  have hkeys : ∀ key ∈ baseTables σ k p, key ≠ word σ k p ∧ key ≠ tmp σ k p := by
    intro key hm
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hm
    simp [table, word, tmp, slot]
  have hw : s.stk (word σ k p) = [] := h.empty (.inl 0)
  have ht : s.stk (tmp σ k p) = [] := h.empty (.inl 3)
  have h1 := StackConcat.copy_executes (word σ k p) (tmp σ k p) hwt (baseTables σ k p) hkeys s ht
  let u := StackConcat.result (baseTables σ k p) (word σ k p) s
  have hu : u.stk (word σ k p) = ExpandedEncoding.payload (RelationalVerifier.base B) := by
    simp [u, StackConcat.result, baseTables_payload h, hw]
  have hud : u.stk (domain σ k p) = List.replicate B.size true := by
    simpa [u, StackConcat.result, domain, word, slot] using h.domain
  have hut : u.stk (tmp σ k p) = [] := by simp [u, StackConcat.result, Ne.symm hwt, ht]
  have h2 := StackCertificateHeader.prepend_executes (domain σ k p) (word σ k p) (tmp σ k p)
    (by simp [domain, word, slot]) (by simp [domain, tmp, slot]) hwt u B.size hud hut
  rw [hu] at h2
  have he : (⟨(u.state.1, none), Function.update u.stk (word σ k p)
      (Lax979537.StructureEncoding.unary B.size ++ ExpandedEncoding.payload (RelationalVerifier.base B))⟩ :
      EvalStore (Port σ k p) Unit) = result B s := by
    simp [u, StackConcat.result, result, ExpandedEncoding.encode_eq, RelationalVerifier.base]
  rw [he] at h2
  refine ⟨(7 * ((baseTables σ k p).flatMap s.stk).length + 4 * (baseTables σ k p).length + 1) +
    (7 * B.size + 5), ?_, Executes.seq h1 h2⟩
  rw [baseTables_payload h]
  have hlen : (encode (RelationalVerifier.base B)).length =
      B.size + 1 + (ExpandedEncoding.payload (RelationalVerifier.base B)).length := by
    simp [ExpandedEncoding.encode_eq, Lax979537.StructureEncoding.unary, RelationalVerifier.base]
    omega
  simp only [baseTables, List.length_map, List.length_finRange]
  omega

end Lax678846Proofs.PreprocessorWord
