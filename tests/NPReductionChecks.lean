import Lax678846Proofs

open Lax678846Proofs

-- Non-prefix masks must be accepted: they select a subsequence, while the
-- separate certificate check keeps the original NP length bound.
example : BinaryCertificates.select [false, true, false, true] [true, false, false, true] =
    [false, true] := by decide
example : BinaryCertificates.select [false, false] [true, false] = [] := by decide
example : BinaryCertificates.select [] [] = [] := by decide
example : BinaryCertificates.select [true] [false] = [false] := by decide

-- The two tables can represent the empty certificate even at arity zero,
-- where the tuple table has one entry on every domain.
example (n : Nat) : BinaryCertificates.decode (BinaryCertificates.encode n 0 []) = [] :=
  BinaryCertificates.decode_encode n 0 [] (by simp)

-- Compose two independently compiled machines. Reversing twice restores
-- the original word, so the intermediate alphabet transfer must preserve
-- the order of the output passed from the first machine to the second.
example : Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) id id) := by
  obtain ⟨h⟩ := Lax979537Proofs.StackTransfer.reverse_polytime
  have hh := PolynomialComposition.comp h h
  have he : (List.reverse ∘ List.reverse : List Bool → List Bool) = id := by
    funext xs; simp
  rwa [he] at hh

#print axioms OrderedDefinitions.of_machine
#print axioms RelationalVerifier.witnesses_of_np
#print axioms RelationalVerifier.definable_of_ordered_verifier
#print axioms TMComputable.of_machine
#print axioms MachineComposition.executes
#print axioms PolynomialComposition.comp
#print axioms StackSelect.select_store
