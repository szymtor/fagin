import Lax988886.FiniteStructures
import Mathlib.Computability.TuringMachine.Computable

/-!
---
title: NP through polynomially bounded certificates
type: definition
---
A bit-string language belongs to NP if membership is equivalent to the
existence of a certificate of polynomially bounded length accepted by a
deterministic polynomial-time verifier. This is the usual certificate
definition of NP. The verifier is a concrete finite multi-stack Turing
machine in mathlib, with its machine-step polynomial bound.

The verifier reads a pair of bit strings: the input and the certificate.
Each input bit is preceded by a one-bit; a zero-bit terminates the input,
and the remaining bits form the certificate. This uniquely decodable
pair encoding has length twice the input length plus the certificate
length plus one. Runtime is polynomial in this total length; certificate
length is bounded by a polynomial in the original input length.

A property belongs to NP when its language of structure encodings does.
The language excludes malformed encodings. No logical definability or
simulation theorem occurs in this definition.
-/

namespace Lax988886.NondeterministicPolynomialTime

open Lax988886.FiniteStructures

def encodePair (p : List Bool × List Bool) : List Bool :=
  p.1.flatMap (fun b => [true, b]) ++ false :: p.2

def LanguageInNP (L : List Bool → Prop) : Prop :=
  ∃ (V : List Bool × List Bool → Bool) (p : Polynomial Nat),
    Nonempty (Turing.TM2ComputableInPolyTime encodePair (fun b => [b]) V) ∧
    ∀ w, L w ↔ ∃ c : List Bool, c.length ≤ p.eval w.length ∧ V (w, c) = true

def InNP {σ : Vocabulary} (Q : Property σ) : Prop :=
  LanguageInNP (language Q)

end Lax988886.NondeterministicPolynomialTime
