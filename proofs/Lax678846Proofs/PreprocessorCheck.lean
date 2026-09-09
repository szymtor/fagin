import Lax678846Proofs.PreprocessorTables
import Lax979537Proofs.StackCheckBound

namespace Lax678846Proofs.PreprocessorCheck

open Lax678846.FiniteStructures Lax979537Proofs
open StackProgram StackBoolean PreprocessorLayout

noncomputable def accepts {σ : Vocabulary} {k : Nat} (p : Polynomial Nat) (B : Structure (k :: k :: σ)) : Bool :=
  decide ((PreprocessorCertificate.bits B).length ≤ p.eval (encode (RelationalVerifier.base B)).length)

def program (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : EvalProgram (Port σ k p) Unit :=
  StackCheckBound.checkBound (certificate σ k p) (bound σ k p) (copyCert σ k p) (copyBound σ k p) (tmp σ k p)

noncomputable def cost (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : Polynomial Nat :=
  12 * (Polynomial.X ^ k + ExpandedEncoding.boundPolynomial σ p) + 18

theorem program_executes {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit)
    (h : PreprocessorTables.Prepared B s) :
    ∃ d, d ≤ (cost σ k p).eval B.size ∧ Returns (program σ k p) s (accepts p B) d := by
  have hsep : [certificate σ k p, bound σ k p, copyCert σ k p, copyBound σ k p, tmp σ k p].Nodup := by
    simp [certificate, bound, copyCert, copyBound, tmp, slot]
  obtain ⟨d, hd, hp⟩ := StackCheckBound.checkBound_executes
    (certificate σ k p) (bound σ k p) (copyCert σ k p) (copyBound σ k p) (tmp σ k p)
    hsep s h.copyCert h.copyBound h.tmp
  have he : StackCheckBound.result (certificate σ k p) (bound σ k p) s =
      StackBoolean.result (accepts p B) s := by
    simp [StackCheckBound.result, StackBoolean.result, h.valid, h.certificate, h.bound, accepts,
      Nat.lt_succ_iff]
  rw [he] at hp
  refine ⟨d, ?_, hp⟩
  rw [h.certificate, h.bound, List.length_reverse, List.length_replicate] at hd
  have hc := BinaryCertificates.decode_length (RelationalVerifier.tables B)
  change (PreprocessorCertificate.bits B).length ≤ B.size ^ k at hc
  have hb := ExpandedEncoding.boundPolynomial_eval p (RelationalVerifier.base B)
  change (ExpandedEncoding.boundPolynomial σ p).eval B.size = _ at hb
  simp only [cost, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_X, hb]
  omega

end Lax678846Proofs.PreprocessorCheck
