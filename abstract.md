This submission formalizes Fagin’s theorem: an isomorphism-invariant property
of finite relational structures is definable in existential second-order
logic if and only if its binary encoding language belongs to NP.

The logic has no built-in order. NP is defined by polynomially bounded
binary certificates checked by a concrete deterministic polynomial-time
Turing machine. Empty universes and nullary relations are included.

Both directions reuse the Immerman–Vardi formalization. To obtain an
existential second-order definition, the proof guesses certificate relations
and an order, simulates the concrete polynomial verifier, and replaces its
least fixed point by exact iteration tables checked by first-order formulas.
It then projects the certificate relations and removes the auxiliary order.
In the other direction, a concrete polynomial-time verifier decodes the
guessed relation tables and runs the existing first-order evaluator.

This is a Lean 4.33 port of [the original Lean 4.30 draft](https://laxarchive.org/lax-678846/).
