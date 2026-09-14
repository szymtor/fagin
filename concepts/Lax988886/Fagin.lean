import Lax988886.ExistentialSecondOrder
import Lax988886.NondeterministicPolynomialTime

/-!
---
title: Fagin’s theorem
type: theorem
---
On finite relational structures, existential second-order logic captures NP.
Every existential second-order sentence defines a property in NP; every
isomorphism-invariant property in NP has an existential second-order
definition. No order on the input structure is assumed. The vocabulary is
arbitrary but fixed independently of the input.

The computational and expressive directions are stated separately as well
as together. Their proofs must supply the certificate verifier and the
logical encoding of accepting computations, including any chosen auxiliary
order. None of those constructions is an assumption of the theorem.

References: Fagin, *Generalized first-order spectra and polynomial-time
recognizable sets* (1974); Libkin, *Elements of Finite Model Theory*,
Theorem 9.6 and its proof in Section 9.2.
-/

namespace Lax988886.Fagin

open Lax988886.FiniteStructures Lax988886.ExistentialSecondOrder
open Lax988886.NondeterministicPolynomialTime

axiom definableInNP {σ : Vocabulary} (Q : Property σ) : Definable Q → InNP Q

axiom npDefinable {σ : Vocabulary} (Q : Property σ)
    (hQ : IsomorphismInvariant Q) : InNP Q → Definable Q

axiom capturesNP {σ : Vocabulary} (Q : Property σ)
    (hQ : IsomorphismInvariant Q) : Definable Q ↔ InNP Q

end Lax988886.Fagin
