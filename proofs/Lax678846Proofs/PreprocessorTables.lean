import Lax678846Proofs.PreprocessorWord
import Lax678846Proofs.PreprocessorBound
import Lax678846Proofs.PreprocessorCertificate

namespace Lax678846Proofs.PreprocessorTables

open Lax678846.FiniteStructures Lax979537Proofs
open StackProgram StackBoolean PreprocessorLayout

noncomputable def program (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : EvalProgram (Port σ k p) Unit :=
  .seq (PreprocessorWord.program σ k p)
    (.seq (PreprocessorBound.program σ k p) (PreprocessorCertificate.program σ k p))

noncomputable def cost (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : Polynomial Nat :=
  7 * InputSize.encodingPolynomial σ 0 + Polynomial.C (4 * σ.length + 6) +
    PreprocessorBound.cost σ k p + (5 * Polynomial.X ^ k + 3)

noncomputable def result {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit) : EvalStore (Port σ k p) Unit :=
  PreprocessorCertificate.result B (PreprocessorBound.result B (PreprocessorWord.result B s))

structure Prepared {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit) : Prop where
  word : s.stk (word σ k p) = encode (RelationalVerifier.base B)
  certificate : s.stk (certificate σ k p) = (PreprocessorCertificate.bits B).reverse
  bound : s.stk (bound σ k p) = List.replicate (p.eval (encode (RelationalVerifier.base B)).length + 1) true
  pair : s.stk (pair σ k p) = []
  tmp : s.stk (tmp σ k p) = []
  copyCert : s.stk (copyCert σ k p) = []
  copyBound : s.stk (copyBound σ k p) = []
  valid : s.state.1.2 = true

theorem result_prepared {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit) (h : Ready B s) :
    Prepared B (result B s) := by
  constructor <;>
    simp [result, PreprocessorWord.result, PreprocessorBound.result, PreprocessorCertificate.result,
      word, certificate, bound, pair, tmp, copyCert, copyBound, table, slot, h.empty]

theorem program_executes {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit) (h : Ready B s) :
    ∃ d, d ≤ (cost σ k p).eval B.size ∧ Executes (program σ k p) s (result B s) d := by
  obtain ⟨d, hd, hword⟩ := PreprocessorWord.program_executes B s h
  let u := PreprocessorWord.result B s
  have hud : u.stk (domain σ k p) = List.replicate B.size true := by
    simpa [u, PreprocessorWord.result, domain, word, slot] using h.domain
  have hub : u.stk (bound σ k p) = [] := by
    simp [u, PreprocessorWord.result, bound, word, slot, h.empty]
  have hut : u.stk (tmp σ k p) = [] := by
    simp [u, PreprocessorWord.result, tmp, word, slot, h.empty]
  have huc : ∀ c ∈ counters σ k p, u.stk c = [] := by
    intro c hm
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
    simp [u, PreprocessorWord.result, word, slot, h.empty]
  obtain ⟨e, he, hbound⟩ := PreprocessorBound.program_executes B u hud hub hut huc
  let v := PreprocessorBound.result B u
  have hvt : ∀ r, v.stk (table σ k p r) =
      (Lax979537.StructureEncoding.tuples B.size ((k :: k :: σ).get r)).map (B.relation r) := by
    intro r
    simpa [v, u, PreprocessorBound.result, PreprocessorWord.result, table, bound, word, slot] using h.tables r
  have hvc : v.stk (certificate σ k p) = [] := by
    simp [v, u, PreprocessorBound.result, PreprocessorWord.result, certificate, bound, word, slot, h.empty]
  have hcert := PreprocessorCertificate.program_executes B v hvt hvc
  refine ⟨d + (e + (5 * B.size ^ k + 3)), ?_, Executes.seq hword (Executes.seq hbound hcert)⟩
  have hlen := ExpandedEncoding.encode_length (RelationalVerifier.base B)
  change (encode (RelationalVerifier.base B)).length = (InputSize.encodingPolynomial σ 0).eval B.size at hlen
  rw [hlen] at hd
  simp only [cost, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  omega

end Lax678846Proofs.PreprocessorTables
