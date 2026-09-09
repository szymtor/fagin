import Lax678846Proofs.ExpandedVerifier
import Lax678846Proofs.DefinableInNP

namespace Lax678846Proofs.Fagin

open Lax678846.FiniteStructures Lax678846.ExistentialSecondOrder
open Lax678846.NondeterministicPolynomialTime

/--
---
conclusion: Lax678846.Fagin.npDefinable
---
Represent the polynomial binary certificate by two guessed relation tables.
A concrete polynomial preprocessor and the original NP verifier decide the
expanded ordered query. Reuse the Immerman–Vardi computation rules, eliminate
their least fixed point by exact iteration tables, project the certificate
relations, patch the two smallest domains, and remove the guessed order
using isomorphism invariance of the original property.
-/
theorem npDefinable {σ : Vocabulary} (Q : Property σ)
    (hQ : IsomorphismInvariant Q) : InNP Q → Definable Q := by
  intro hNP
  obtain ⟨V, p, k, ⟨hV⟩, hc⟩ := RelationalVerifier.witnesses_of_np Q hNP
  exact RelationalVerifier.definable_of_ordered_verifier Q hQ V p k hc
    (ExpandedVerifier.ordered_definable V p k hV)

/--
---
conclusion: Lax678846.Fagin.capturesNP
---
Combine the concrete nondeterministic certificate verifier with the
existential second-order definition constructed for each NP property.
-/
theorem capturesNP {σ : Vocabulary} (Q : Property σ)
    (hQ : IsomorphismInvariant Q) : Definable Q ↔ InNP Q :=
  ⟨definableInNP Q, npDefinable Q hQ⟩

end Lax678846Proofs.Fagin
