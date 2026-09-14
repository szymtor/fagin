import Lax988886Proofs

open Lax988886.FiniteStructures Lax988886Proofs

-- Malformed inputs have a false guard, including an unterminated header.
example (p : Polynomial Nat) : PreprocessorMachine.prepare [] 0 p [] = (false, ([], [])) := rfl
example (p : Polynomial Nat) : PreprocessorMachine.prepare [] 0 p [true] = (false, ([], [])) := rfl

-- An empty universe still has one nullary tuple. A marked false bit is a
-- one-bit certificate, not an empty certificate. The bound is non-strict.
def nullaryWitness : Structure [0, 0] := ⟨0, fun r _ => decide (r = 0)⟩

example : PreprocessorMachine.prepare [] 0 0 (encode nullaryWitness) =
    (false, ([false], [false])) := by
  rw [PreprocessorMachine.prepare_encode]
  simp [PreprocessorCheck.accepts, PreprocessorCertificate.bits, BinaryCertificates.decode,
    BinaryCertificates.select, RelationalVerifier.tables, RelationalVerifier.base, nullaryWitness,
    Lax751879.StructureEncoding.tuples, encode, Lax751879.StructureEncoding.encode,
    Lax751879.StructureEncoding.unary]

example : PreprocessorMachine.prepare [] 0 1 (encode nullaryWitness) =
    (true, ([false], [false])) := by
  rw [PreprocessorMachine.prepare_encode]
  simp [PreprocessorCheck.accepts, PreprocessorCertificate.bits, BinaryCertificates.decode,
    BinaryCertificates.select, RelationalVerifier.tables, RelationalVerifier.base, nullaryWitness,
    Lax751879.StructureEncoding.tuples, encode, Lax751879.StructureEncoding.encode,
    Lax751879.StructureEncoding.unary]

#print axioms StackPolynomial.program_executes
#print axioms GuardedVerifier.computable
#print axioms PreprocessorMachine.computable
#print axioms ExpandedVerifier.ordered_definable
#print axioms Fagin.definableInNP
#print axioms Fagin.npDefinable
#print axioms Fagin.capturesNP
