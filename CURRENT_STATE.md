# Fagin formalization

Active goal: formalize Fagin’s theorem and its complete proof.
Created 2026-09-09 in `fagin`, local Lax ID `lax-678846`.

The user authorizes autonomous work and requests approval only for security
permissions. Use `tmp` under the workspace, never `/private/tmp`, for working
files. No subagents are authorized. No token budget was requested.

## Statement and concepts

The main theorem is `Definable Q ↔ InNP Q` for every fixed finite relational
vocabulary and isomorphism-invariant Boolean property. Unlike the ordered
Immerman–Vardi theorem, the logic has no built-in order. The existing `Fin n`
representation is reused only for numberings and input encodings. Empty
universes and nullary relations are included.

Four concept modules define finite structures/isomorphisms, ordinary ∃SO
syntax and semantics, standard polynomial-certificate NP with a concrete
mathlib TM2 verifier, and Fagin’s two directions and equivalence. They are
initial concepts, not yet a completed proof. No proof placeholders are used.

Dependency: Immerman–Vardi `lax-979537`, source
https://github.com/szymtor/immerman-vardi,
commit `82ef67e68fab884dc4cff117a1b871567bdaaafd`.
This revision credits Szymon Toruńczyk and Codex 6. Its archive update passed
(workflow 34283043099, control issue 84), and both names were verified on the
live page at https://laxarchive.org/lax-979537/index.html. The archive was
synchronized and the dependency resolves successfully.

## Proof route requested by the user

1. Represent the usual polynomial binary certificate by finitely many
   witness relations; existentially choose an order on the input domain.
2. Implement the certificate verifier as a polynomial-time query on the
   expanded ordered structure. Reuse Immerman–Vardi for an LFP definition.
3. Prove LFP-to-∃SO elimination separately: existentially quantify exact
   iteration tables, check the empty initial stage and every successor
   equation, and read the stabilized final relation. Arbitrary fixed points
   do not suffice. The constructive Immerman–Vardi proof supplies a single
   positive rule closure, so eliminating that form suffices and avoids a
   general translation for arbitrary nested LFPs. Exact tables also preserve
   negative queries about the final closure. Handle domains of sizes zero
   and one explicitly.
4. Eliminate the auxiliary order using isomorphism invariance, and combine
   the existential relation prefixes.
5. For ∃SO-to-NP, guess relation tables and reuse the concrete polynomial
   evaluator, with proved encoding and certificate-length bounds.
6. Audit every main theorem for unproved axioms, and kernel-replay the full
   dependency closure. Do not report completion while a direction is open.

## Literature

Libkin, *Elements of Finite Model Theory*, §9.2, Theorem 9.6 (pp. 168–172;
PDF pp. 179–183), supplies the classical unordered statement, guessed order,
and input/computation encoding. Immerman, *Descriptive Complexity*, chapter
7, gives a second detailed source. Fagin’s original 1974 paper is referenced
in the manifest. Sources were checked online in this session.

## First proof checkpoint

The four concept modules compile. Nine proof modules compile:

- `Isomorphism`: transport witness relations; ∃SO satisfaction and definable
  properties are invariant under structure isomorphism. The first annotated
  concept obligation is proved.
- `IterationCertificates`: a finite table with empty initial stage and exact
  successor equations equals the actual iteration; at any horizon at least
  the number of tuples its final row is the least fixed point.
- `OrderedFirstOrder`: translate fixed-point-free Raw syntax (including free
  relation parameters) to the new FO matrix syntax, replacing built-in order
  by the first relation parameter. Evaluation preservation is proved when
  that relation is the canonical order.
- `RelationSlices`: replace relation atoms by slices of higher-arity stage
  tables, shifting clock variables beneath element binders. Syntax and
  semantic correctness are proved.
- `FirstOrderMacros`: first-order implication, equivalence, and block
  universal quantification, reusing the existing syntax-renaming machinery.
- `TupleIteration`: exact iterations indexed by tuple addresses; one extra
  clock coordinate supplies at least `n^k + 1` rows for `n ≥ 2`.
- `StageFormulas`: first-order checks for the initial and successor rows.
- `IterationFormula`: one first-order sentence checks the entire table and
  is equivalent to the semantic exact-iteration conditions.
- `LfpElimination.exists_matrix_iff`: for a fixed-point-free body with a
  monotone induced operator, and any fixed-point-free query about its closure
  (including negative queries), an existential table satisfying a concrete
  fixed-point-free matrix is equivalent to evaluating the query at the least
  fixed point, on domains of size at least two. The clock width is `k+1` and
  table arity is `2*k+1`. This currently uses ordered Raw semantics and
  Prop-valued relations; conversion to Boolean witness interpretations and
  elimination of the auxiliary order are still required.

All three Fagin statements remain unproved. The certificate-to-expanded-input
verifier and the ∃SO-to-NP verifier are not yet implemented. The completed
LFP lemma must be connected to the single positive closure produced by the
Immerman–Vardi construction; it does not alone prove Fagin’s theorem.

The combined checkpoint passed `lax build . --replay --no-color`: 2m05s
overall, 1m42s kernel replay; 4 concepts and 1 annotated proof inspected.
`tests/IterationChecks.lean` passed: it excludes a spurious fixed point of the
identity operator, and all five axiom audits show only Lean's standard
background axioms. There are no sorry or new axioms in the proof package.

The full replay is complete, with no running validation processes. Normal
Lax warnings remain for depending on an upstream proof package and a draft
submission. The direct proof dependency is deliberate: it reuses the actual
proved construction rather than adding unproved simulation premises.

Next: convert Prop-valued stage witnesses to the Boolean interpretations
used by the new ∃SO syntax, then add/check the existential auxiliary order.
Use `ULift (Fin n)` for the chosen-order domain when applying mathlib's
`linearOrderOfSTO` and `Fintype.orderIsoFinOfCardEq`; this avoids overriding
the canonical order instance on the target `Fin n`.
