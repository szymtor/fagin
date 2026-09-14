import Lax988886Proofs.DefinableInNP

open Lax988886.ExistentialSecondOrder Lax988886Proofs

/-- On an empty input vocabulary, ask for a true nullary witness relation. -/
def nullaryWitness : Sentence [] := ⟨[0], .variable 0 Fin.elim0⟩

example : CertificateVerifier.verify nullaryWitness ([false], [true]) = true := by decide
example : CertificateVerifier.verify nullaryWitness ([false], [false]) = false := by decide
example : CertificateVerifier.verify nullaryWitness ([false], []) = false := by decide
example : CertificateVerifier.verify nullaryWitness ([false], [true, true]) = false := by decide
example : CertificateVerifier.verify nullaryWitness ([], [true]) = false := by decide

#print axioms StackPair.split_executes
#print axioms StackCertificateHeader.prepend_executes
#print axioms VerifierMachine.computableInPolyTime
#print axioms Fagin.definableInNP
