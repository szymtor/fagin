import Lax678846Proofs.RelationCertificates

namespace Lax678846Proofs.WitnessStructure

open Lax678846.FiniteStructures
open Lax979537Proofs

def structureOf {τ : Vocabulary} {n : Nat} (R : Interpretation τ n) : Structure τ := ⟨n,R⟩

theorem encode_structureOf {τ : Vocabulary} {n : Nat} (R : Interpretation τ n) :
    encode (structureOf R) = Lax979537.StructureEncoding.unary n ++ RelationCertificates.encode R := by
  simp [encode, structureOf, Lax979537.StructureEncoding.encode,
    RelationCertificates.encode, Decoding.relationBits]

/-- The standard structure decoder, applied after adding the domain header,
is exactly the witness-table decoder used by the verifier. -/
theorem decode_header (τ : Vocabulary) (n : Nat) (c : List Bool) :
    Decoding.decode τ 0 (Lax979537.StructureEncoding.unary n ++ c) =
      (RelationCertificates.decode τ n c).map
        (fun R => (⟨structureOf R, Fin.elim0⟩ : Lax979537.OrderedStructures.PointedStructure τ 0)) := by
  simp only [Decoding.decode, Decoding.readUnary_correct, Option.bind_some,
    RelationCertificates.decode]
  cases hr : Decoding.readRelations n τ c with
  | none => simp [hr]
  | some p =>
    obtain ⟨R, rest⟩ := p
    by_cases h : rest = [] <;> simp [Decoding.readTuple, hr, h, structureOf]

end Lax678846Proofs.WitnessStructure
