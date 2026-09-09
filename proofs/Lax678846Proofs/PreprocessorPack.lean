import Lax678846Proofs.PreprocessorCertificate
import Lax678846Proofs.StackTag
import Lax678846Proofs.GuardedVerifier

namespace Lax678846Proofs.PreprocessorPack

open Lax678846.FiniteStructures Lax979537Proofs
open StackProgram StackBoolean PreprocessorLayout

def program (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : EvalProgram (Port σ k p) Unit :=
  .seq (StackTransfer.transfer (certificate σ k p) (pair σ k p))
    (.seq (StackTag.join (word σ k p) (pair σ k p) (tmp σ k p))
      (.atom (.push (pair σ k p) (fun s => s.1.2))))

noncomputable def cost (σ : Vocabulary) (k : Nat) : Polynomial Nat :=
  3 * Polynomial.X ^ k + 7 * InputSize.encodingPolynomial σ 0 + 8

def output {σ : Vocabulary} {k : Nat} (B : Structure (k :: k :: σ)) (flag : Bool) : List Bool :=
  GuardedVerifier.encode Lax678846.NondeterministicPolynomialTime.encodePair
    (flag, (encode (RelationalVerifier.base B), PreprocessorCertificate.bits B))

noncomputable def result {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit) : EvalStore (Port σ k p) Unit :=
  ⟨(s.state.1, none), Function.update (Function.update (Function.update s.stk (certificate σ k p) [])
    (word σ k p) []) (pair σ k p) (output B s.state.1.2)⟩

theorem program_executes {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit)
    (hw : s.stk (word σ k p) = encode (RelationalVerifier.base B))
    (hc : s.stk (certificate σ k p) = (PreprocessorCertificate.bits B).reverse)
    (hp : s.stk (pair σ k p) = []) (ht : s.stk (tmp σ k p) = []) :
    ∃ d, d ≤ (cost σ k).eval B.size ∧ Executes (program σ k p) s (result B s) d := by
  have hcp : certificate σ k p ≠ pair σ k p := by simp [certificate, pair, slot]
  have hwp : word σ k p ≠ pair σ k p := by simp [word, pair, slot]
  have hwt : word σ k p ≠ tmp σ k p := by simp [word, tmp, slot]
  have hpt : pair σ k p ≠ tmp σ k p := by simp [pair, tmp, slot]
  let u : EvalStore (Port σ k p) Unit := ⟨(s.state.1, none),
    Function.update (Function.update s.stk (certificate σ k p) []) (pair σ k p) (PreprocessorCertificate.bits B)⟩
  have h1 := StackTransfer.transfer_store (certificate σ k p) (pair σ k p) hcp s
  rw [hc, hp, List.reverse_reverse, List.append_nil, List.length_reverse] at h1
  have huw : u.stk (word σ k p) = encode (RelationalVerifier.base B) := by
    simpa [u, word, certificate, pair, slot] using hw
  have hup : u.stk (pair σ k p) = PreprocessorCertificate.bits B := by simp [u]
  have hut : u.stk (tmp σ k p) = [] := by simpa [u, tmp, certificate, pair, slot] using ht
  have h2 := StackTag.join_store (word σ k p) (pair σ k p) (tmp σ k p) hwp hwt hpt u hut
  rw [huw, hup] at h2
  let v : EvalStore (Port σ k p) Unit := ⟨(s.state.1, none),
    Function.update (Function.update (Function.update s.stk (certificate σ k p) []) (word σ k p) [])
      (pair σ k p) (Lax678846.NondeterministicPolynomialTime.encodePair
        (encode (RelationalVerifier.base B), PreprocessorCertificate.bits B))⟩
  have he : (⟨(u.state.1, none), Function.update (Function.update u.stk (word σ k p) []) (pair σ k p)
      (Lax678846.NondeterministicPolynomialTime.encodePair
        (encode (RelationalVerifier.base B), PreprocessorCertificate.bits B))⟩ : EvalStore (Port σ k p) Unit) = v := by
    apply Store.ext
    · rfl
    · funext key
      by_cases hp' : key = pair σ k p
      · subst key; simp [u, v]
      · by_cases hw' : key = word σ k p
        · subst key; simp [u, v, hwp]
        · simp [u, v, hp', hw']
  rw [he] at h2
  have h3 := Executes.atom (.push (pair σ k p) (fun s : FiniteDecoder.Control => s.1.2)) v
  have hf : Op.apply (.push (pair σ k p) (fun s : FiniteDecoder.Control => s.1.2)) v = result B s := by
    simp [Op.apply, v, result, output, GuardedVerifier.encode]
  rw [hf] at h3
  refine ⟨(3 * (PreprocessorCertificate.bits B).length + 2) +
    ((7 * (encode (RelationalVerifier.base B)).length + 5) + 1), ?_,
    Executes.seq h1 (Executes.seq h2 h3)⟩
  have hcl := BinaryCertificates.decode_length (RelationalVerifier.tables B)
  change (PreprocessorCertificate.bits B).length ≤ B.size ^ k at hcl
  have hwl := ExpandedEncoding.encode_length (RelationalVerifier.base B)
  change (encode (RelationalVerifier.base B)).length = (InputSize.encodingPolynomial σ 0).eval B.size at hwl
  rw [hwl]
  simp only [cost, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_X]
  omega

end Lax678846Proofs.PreprocessorPack
