# Fagin’s theorem

This Lax submission formalizes that an isomorphism-invariant property of
finite relational structures is definable in existential second-order logic
if and only if its binary encoding language belongs to NP. It includes empty
universes and nullary relations and assumes no order on the input structure.

Authors: Szymon Toruńczyk and Codex 6.

The [four concept files](concepts/Lax988886) define finite structures,
ordinary existential second-order syntax, the standard polynomial-certificate
machine definition of NP, and [Fagin’s theorem](concepts/Lax988886/Fagin.lean).
Internal machine layouts and intermediate ordered definitions belong to the
proof package and do not change these concepts.

For [∃SO → NP](proofs/Lax988886Proofs/DefinableInNP.lean), the machine guesses
the characteristic tables of the existential relations, decodes them, and
uses the first-order evaluator from Immerman–Vardi. Its certificate length
and actual Turing-machine runtime have polynomial bounds.

For [NP → ∃SO](proofs/Lax988886Proofs/NPDefinable.lean), two guessed relations
encode a binary certificate. A concrete polynomial preprocessor reconstructs
the original input, checks the original certificate bound, and feeds the
original verifier. The Immerman–Vardi construction gives a positive rule
closure; exact iteration tables eliminate its least fixed point. The proof
projects the certificate relations, handles the two smallest domains, and
uses isomorphism invariance to remove the guessed order.

The proof package reuses the pinned Immerman–Vardi revision
`82ef67e68fab884dc4cff117a1b871567bdaaafd`. Its main theorem audits contain only
Lean’s standard background axioms: `propext`, `Classical.choice`, and
`Quot.sound`. There are no proof placeholders or extra simulation axioms.

Run the complete Lax validation from this directory:

```sh
env LEAN_NUM_THREADS=2 lax build . --replay --no-color
```

The regression files in [tests](tests) cover iteration correctness,
certificate encodings, verifier behavior, machine composition, and boundary
cases for the final preprocessor. Run each with `lake env lean` from the
`proofs` directory. [CURRENT_STATE.md](CURRENT_STATE.md) records validation
results and any running process handles.

The local [concepts preview](http://localhost:8126/lax-988886/index.html) is
served by `lax serve . --port 8126 --no-color`.
