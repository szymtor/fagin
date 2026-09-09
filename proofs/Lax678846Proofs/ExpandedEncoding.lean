import Lax678846Proofs.RelationalVerifier
import Lax979537Proofs.InputSize

namespace Lax678846Proofs.ExpandedEncoding

open Lax678846.FiniteStructures Lax979537Proofs

def payload {σ : Vocabulary} (A : Structure σ) : List Bool :=
  (List.finRange σ.length).flatMap (fun r =>
    (Lax979537.StructureEncoding.tuples A.size (σ.get r)).map (A.relation r))

theorem encode_eq {σ : Vocabulary} (A : Structure σ) :
    encode A = Lax979537.StructureEncoding.unary A.size ++ payload A := by
  simp [encode, Lax979537.StructureEncoding.encode, payload]

/-- With no free element tuple, the encoding polynomial is exact. Thus the
original certificate bound can be computed from the unary domain counter. -/
theorem encode_length {σ : Vocabulary} (A : Structure σ) :
    (encode A).length = (InputSize.encodingPolynomial σ 0).eval A.size := by
  rw [show encode A = Lax979537.StructureEncoding.encode ⟨A, Fin.elim0⟩ from rfl,
    StructureEncoding.encodeLength]
  simp [InputSize.encodingPolynomial, InputSize.tablePolynomial_eval]

/-- One extra token lets the existing strict comparison routine test the
non-strict certificate bound from the NP definition. -/
noncomputable def boundPolynomial (σ : Vocabulary) (p : Polynomial Nat) : Polynomial Nat :=
  p.comp (InputSize.encodingPolynomial σ 0) + 1

theorem boundPolynomial_eval {σ : Vocabulary} (p : Polynomial Nat) (A : Structure σ) :
    (boundPolynomial σ p).eval A.size = p.eval (encode A).length + 1 := by
  simp only [boundPolynomial, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_one,
    encode_length]

theorem length_check {σ : Vocabulary} (p : Polynomial Nat) (A : Structure σ) (c : List Bool) :
    c.length < (boundPolynomial σ p).eval A.size ↔ c.length ≤ p.eval (encode A).length := by
  rw [boundPolynomial_eval]
  omega

theorem payload_expand {σ : Vocabulary} {k : Nat} (A : Structure σ)
    (R : Interpretation [k,k] A.size) :
    payload (RelationalVerifier.expand A R) =
      (Lax979537.StructureEncoding.tuples A.size k).map (R 0) ++
      (Lax979537.StructureEncoding.tuples A.size k).map (R 1) ++ payload A := by
  simp [payload, RelationalVerifier.expand, List.finRange_succ, List.flatMap_map,
    Function.comp_def, List.append_assoc]
  rfl

theorem encode_expand {σ : Vocabulary} {k : Nat} (A : Structure σ)
    (R : Interpretation [k,k] A.size) :
    encode (RelationalVerifier.expand A R) =
      Lax979537.StructureEncoding.unary A.size ++
      (Lax979537.StructureEncoding.tuples A.size k).map (R 0) ++
      (Lax979537.StructureEncoding.tuples A.size k).map (R 1) ++ payload A := by
  rw [encode_eq, payload_expand]
  simp [RelationalVerifier.expand, List.append_assoc]

end Lax678846Proofs.ExpandedEncoding
