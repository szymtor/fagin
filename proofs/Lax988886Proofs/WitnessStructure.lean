import Lax988886Proofs.RelationCertificates

namespace Lax988886Proofs.WitnessStructure

open Lax988886.FiniteStructures
open Lax751879Proofs

def structureOf {τ : Vocabulary} {n : Nat} (R : Interpretation τ n) : Structure τ := ⟨n,R⟩

theorem encode_structureOf {τ : Vocabulary} {n : Nat} (R : Interpretation τ n) :
    encode (structureOf R) = Lax751879.StructureEncoding.unary n ++ RelationCertificates.encode R := by
  simp [encode, structureOf, Lax751879.StructureEncoding.encode,
    RelationCertificates.encode, Decoding.relationBits]

/-- The standard structure decoder, applied after adding the domain header,
is exactly the witness-table decoder used by the verifier. -/
theorem decode_header (τ : Vocabulary) (n : Nat) (c : List Bool) :
    Decoding.decode τ 0 (Lax751879.StructureEncoding.unary n ++ c) =
      (RelationCertificates.decode τ n c).map
        (fun R => (⟨structureOf R, Fin.elim0⟩ : Lax751879.OrderedStructures.PointedStructure τ 0)) := by
  simp only [Decoding.decode, Decoding.readUnary_correct, Option.bind_some,
    RelationCertificates.decode]
  cases hr : Decoding.readRelations n τ c with
  | none => simp [hr]
  | some p =>
    obtain ⟨R, rest⟩ := p
    by_cases h : rest = [] <;> simp [Decoding.readTuple, hr, h, structureOf]

end Lax988886Proofs.WitnessStructure
