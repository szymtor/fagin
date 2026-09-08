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
This revision changes authors to Szymon Toruńczyk and Codex 6. Its archive
update was still running when the Fagin project began (session 68781,
workflow 34283043099, control issue 84). Collect its result and verify the
updated public page; no duplicate submission should be launched.

## Proof route requested by the user

1. Represent the usual polynomial binary certificate by finitely many
   witness relations; existentially choose an order on the input domain.
2. Implement the certificate verifier as a polynomial-time query on the
   expanded ordered structure. Reuse Immerman–Vardi for an LFP definition.
3. Prove LFP-to-∃SO elimination separately: existentially quantify exact
   iteration tables, check the empty initial stage and every successor
   equation, and read the stabilized final relation. Arbitrary fixed points
   do not suffice. The translation must preserve nested and negated LFPs
   and parameters. Handle domains of sizes zero and one explicitly.
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
