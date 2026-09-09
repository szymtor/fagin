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

## First proof checkpoint (historical)

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

## Boolean witnesses and auxiliary order (checkpoint `fcfe641`)

Two further modules compile after the replayed checkpoint `ec56031`:

- `BooleanWitnesses`: Prop-valued relation tables and Boolean witness
  interpretations are interchangeable. `lfp_exists_iff` expresses the LFP
  elimination using the actual FO syntax and Boolean interpretations in
  the ∃SO concepts, with the order relation fixed canonically for now.
- `OrderEnumeration.enumerate`: every strict total relation on `Fin n` is
  obtained from the canonical strict order by a permutation, including
  empty domains. It uses `linearOrderOfSTO` and
  `Fintype.orderIsoFinOfCardEq` on a dedicated `Point n` wrapper. `ULift`
  was unsuitable because it inherits order instances that conflict with
  the chosen order; the dedicated wrapper has no such inherited instances.

The expanded `IterationChecks.lean` regression test and seven axiom audits
pass; the new lemmas use only the standard background axioms. The full
ordinary Lax build passes in 11s (4 concepts, 1 annotated proof). The earlier
kernel replay covers the central elimination construction; the two newest
modules still need inclusion in the next full replay. No processes are
running at this checkpoint.

Next: write the first-order strict-total-order assertion and use the
enumeration lemma, structure relabeling, and the proved FO isomorphism
invariance to eliminate the auxiliary order. Then connect the single-rule-
closure elimination to Immerman–Vardi's concrete reverse construction and
implement the certificate preprocessing/verification bridges for both
directions. Mathlib's general `TM2ComputableInPolyTime.comp` is still
`proof_wanted`; do not use it as an unproved axiom. The existing
`StackProgram` compiler supports verified sequential composition of its
programs and is a candidate for the preprocessing work.

## Current implementation after `fcfe641`

The user explicitly emphasized reusing Immerman–Vardi in the ∃SO-to-NP
direction too: guess the relation tables, then use the existing polynomial
  first-order evaluator. The implementation follows that instruction. The
concepts still use the standard binary-certificate definition of NP.

New proof modules:

- `OrderFormula`: a first-order strict-total-order assertion, with its
  semantic equivalence and correctness for the canonical order.
- `OrderRemoval`: relabel structures by an enumeration of the guessed
  order; transport all witnesses and use isomorphism invariance. This
  produces ordinary unordered ∃SO sentences, including on empty domains.
- `SmallDomains`: extend an ordered existential definition valid above a
  fixed threshold using the actual first-order finite diagrams from the
  upstream proof, then remove order.
- `RuleMatrices`: translate the concrete parameterized rule closure and
  acceptance rules from Immerman–Vardi into the stage-table elimination.
- `PtimeExistential.of_machine`: an invariant Boolean property decided by
  a concrete polynomial-time TM2 has an ordinary ∃SO definition. This now
  compiles using the actual upstream machine simulation, with no simulation
  assumption or unproved complexity-closure axiom.
- `ExistentialProjection`: move one input relation into the existential
  witness prefix, preserving satisfaction. Repetition handles finite lists
  of guessed input relations.
- `FirstOrderEvaluation`: translate the new FO matrix syntax to the
  existing evaluator; reuse its individual first-order compiler-correctness
  lemmas, retaining the polynomial stack-step bound. Guessed relations are
  supplied as materialized table inputs. This does not yet include the
  input/certificate decoding wrapper.
- `RelationCertificates`: encode witness relations as characteristic
  tables, reuse the upstream relation decoder, prove decoding and encoding
  correctness, and bound certificate length by `tablePolynomial τ` evaluated
  at the original input length. Compiles, including empty/nullary cases.
- `CertificateVerifier`: a specific verifier that rejects malformed input
  encodings and certificates and runs the existing FO evaluator. Its
  semantic certificate characterization and reduction of ∃SO-to-NP to this
  verifier's concrete polynomial machine compile. The machine
  obligation is explicit and remains unproved.
- `PairEncoding`: the tagged pair decoder, round-trip laws, injectivity,
  and length formula for the pair encoding in the NP concepts.

All three Fagin statements remain unproved. In the reverse direction the
remaining computational work is the actual pair-splitting, decoding, and
evaluation wrapper. In NP-to-∃SO the standard verifier must still be
connected to an expanded-structure computation, with certificate and size
checks. Do not infer either NP direction from the deterministic theorem
alone, and do not replace standard NP by a relational-projection definition.

All new modules compile together (`lake build Lax678846Proofs`, 1363 jobs).
`tests/CertificateChecks.lean` passes: nullary/empty-domain and malformed-input
checks, plus ten axiom audits. Every audited theorem depends only on the
standard background axioms (or a subset). No new concept declarations or
proof axioms were added. The previous iteration regression suite and its
seven audits also pass.

`env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passed in 2m18s,
including 2m11s kernel replay, with 4 concepts and 1 annotated proof inspected.
The three remaining warnings are the deliberate upstream proof-package
dependency and the two references to the upstream draft. This validates
the implemented helper proofs; it does not discharge the three main Fagin
obligations. No validation processes remain running at this checkpoint.

Concrete next steps for the ∃SO-to-NP machine wrapper:

1. A small `StackTransfer.BitProgram` splits `encodePair (w,c)` into a stack
   for `w` and a stack for `c`; `PairEncoding` supplies its functional spec.
2. Embed `FiniteDecoder.program σ 0` using `StackRename.executes_in_sum`.
   This preserves the external certificate stack. Reuse its decoded
   domain and input tables; run `StackReadRelations.readTables` for the
   witness vocabulary on the certificate stack and check the end of it.
   `DecoderAgreement.tables_agree` and the existing decoder-correctness
   lemmas are available for this bridge. Ensure the witness decoder has a
   counter pool large enough for the witness arities, not only the input
   vocabulary arities.
3. Apply `FirstOrderEvaluation.executes`, then `StackOutput.output` and
   `StackProgram.program_polytime`. This avoids the unproved general
   mathlib composition theorem entirely. Supply the result to
   `CertificateVerifier.inNP_of_computable` and prove the annotated main
   ∃SO-to-NP obligation for arbitrary definable properties.

For NP-to-∃SO, keep a version of the deterministic construction before
order removal: a certificate verifier query on expanded structures need
not itself be invariant under arbitrary relabelings. Existential projection
must precede the final use of invariance of the original property. Do not
silently assume invariance of the expanded verifier query.
