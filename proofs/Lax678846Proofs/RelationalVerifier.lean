import Lax678846Proofs.BinaryCertificates
import Lax678846Proofs.CertificateCapacity
import Lax678846Proofs.OrderedDefinitions
import Lax678846.NondeterministicPolynomialTime

namespace Lax678846Proofs.RelationalVerifier

open Lax678846.FiniteStructures
open Lax678846.NondeterministicPolynomialTime
open Lax979537Proofs

def base {σ : Vocabulary} {k : Nat} (B : Structure (k :: k :: σ)) : Structure σ :=
  ⟨B.size, fun r => B.relation r.succ.succ⟩

def tables {σ : Vocabulary} {k : Nat} (B : Structure (k :: k :: σ)) : Interpretation [k,k] B.size :=
  Fin.cons (B.relation 0) (Fin.cons (B.relation 1) (fun r => Fin.elim0 r))

def expand {σ : Vocabulary} {k : Nat} (A : Structure σ) (R : Interpretation [k,k] A.size) :
    Structure (k :: k :: σ) := ⟨A.size, Fin.cons (R 0) (Fin.cons (R 1) A.relation)⟩

theorem base_expand {σ : Vocabulary} {k : Nat} (A : Structure σ) (R : Interpretation [k,k] A.size) :
    base (expand A R) = A := by cases A; rfl

theorem tables_expand {σ : Vocabulary} {k : Nat} (A : Structure σ) (R : Interpretation [k,k] A.size) :
    tables (expand A R) = R := by
  funext r
  refine Fin.cases rfl (fun i => ?_) r
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

/-- The expanded ordered query checks the original binary certificate
bound and invokes the original verifier on the decoded certificate. -/
def verified {σ : Vocabulary} (V : List Bool × List Bool → Bool) (p : Polynomial Nat) (k : Nat) :
    Property (k :: k :: σ) := fun B =>
  let c := BinaryCertificates.decode (tables B)
  c.length ≤ p.eval (encode (base B)).length ∧ V (encode (base B), c) = true

theorem verified_expand {σ : Vocabulary} (V : List Bool × List Bool → Bool)
    (p : Polynomial Nat) (k : Nat) (A : Structure σ) (R : Interpretation [k,k] A.size) :
    verified V p k (expand A R) ↔
      (BinaryCertificates.decode R).length ≤ p.eval (encode A).length ∧
        V (encode A, BinaryCertificates.decode R) = true := by
  simp only [verified, base_expand, tables_expand]
  rfl

theorem language_encode_iff {σ : Vocabulary} (Q : Property σ) (A : Structure σ) :
    language Q (encode A) ↔ Q A := by
  constructor
  · rintro ⟨B, hB, hQ⟩
    have he : (⟨B, Fin.elim0⟩ : Lax979537.OrderedStructures.PointedStructure σ 0) = ⟨A, Fin.elim0⟩ :=
      StructureEncoding.encodeInjective σ 0 hB
    have hBA : B = A := congrArg (fun P => P.structureValue) he
    exact hBA ▸ hQ
  · intro hA; exact ⟨A, rfl, hA⟩

/-- The standard NP hypothesis supplies an actual binary verifier and a
fixed arity for two guessed relations. Their projection agrees with the
original property on domains of size at least two. -/
theorem witnesses_of_np {σ : Vocabulary} (Q : Property σ) (h : InNP Q) :
    ∃ (V : List Bool × List Bool → Bool) (p : Polynomial Nat) (k : Nat),
      Nonempty (Turing.TM2ComputableInPolyTime encodePair (fun b => [b]) V) ∧
      ∀ A : Structure σ, 2 ≤ A.size →
        (Q A ↔ ∃ R : Interpretation [k,k] A.size, verified V p k (expand A R)) := by
  obtain ⟨V, p, hV, hc⟩ := h
  obtain ⟨k, hk⟩ := CertificateCapacity.exists_arity σ p
  refine ⟨V, p, k, hV, fun A hA => ?_⟩
  have hword := (language_encode_iff Q A).symm.trans (hc (encode A))
  have hrel := BinaryCertificates.exists_bounded_iff A.size k (p.eval (encode A).length)
    (Nat.le_of_lt (hk A hA)) (fun c => V (encode A, c) = true)
  exact (hword.trans hrel).trans (exists_congr fun R => (verified_expand V p k A R).symm)

theorem projection {σ : Vocabulary} (V : List Bool × List Bool → Bool)
    (p : Polynomial Nat) (k : Nat) (h : OrderedDefinitions.Definable (σ := k :: k :: σ) (verified V p k)) :
    OrderedDefinitions.Definable
      (fun A : Structure σ => ∃ R : Interpretation [k,k] A.size, verified V p k (expand A R)) := by
  have h1 := OrderedDefinitions.projection (verified (σ := σ) V p k) h
  have h2 := OrderedDefinitions.projection _ h1
  obtain ⟨τ, φ, hφ, hc⟩ := h2
  refine ⟨τ, φ, hφ, fun A => ?_⟩
  apply Iff.trans ?_ (hc A)
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨R 1, R 0, hR⟩
  · rintro ⟨S1, S0, hS⟩
    exact ⟨Fin.cons S0 (Fin.cons S1 (fun r => Fin.elim0 r)), hS⟩

/-- Once the expanded verifier is implemented in polynomial time, apply
the ordered PTime construction, project away the certificate relations,
patch the small domains, and only then remove the auxiliary order. -/
theorem definable_of_ordered_verifier {σ : Vocabulary} (Q : Property σ) (hQ : IsomorphismInvariant Q)
    (V : List Bool × List Bool → Bool) (p : Polynomial Nat) (k : Nat)
    (hcorrect : ∀ A : Structure σ, 2 ≤ A.size →
      (Q A ↔ ∃ R : Interpretation [k,k] A.size, verified V p k (expand A R)))
    (h : OrderedDefinitions.Definable (σ := k :: k :: σ) (verified V p k)) :
    Lax678846.ExistentialSecondOrder.Definable Q := by
  obtain ⟨τ, φ, hφ, hc⟩ := projection V p k h
  apply OrderedDefinitions.remove_order Q hQ
  apply OrderedDefinitions.of_above Q 1 φ hφ
  intro A hA
  exact (hcorrect A (by omega)).trans (hc A)

end Lax678846Proofs.RelationalVerifier
