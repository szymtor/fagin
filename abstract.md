This submission develops Fagin’s theorem: an isomorphism-invariant property
of finite relational structures is definable in existential second-order
logic if and only if its binary encoding language belongs to NP.

The logic has no built-in order. NP is defined by polynomially bounded
binary certificates checked by a concrete deterministic polynomial-time
Turing machine. Empty universes and nullary relations are included.

The proof is being implemented. It reuses the finite-structure encoding and
computational infrastructure of the Immerman–Vardi submission. The planned
expressive direction existentially chooses certificate relations and an
order, applies the polynomial-time-to-LFP theorem to the verifier, and
eliminates least fixed points using existentially quantified iteration
tables with first-order consistency conditions.
