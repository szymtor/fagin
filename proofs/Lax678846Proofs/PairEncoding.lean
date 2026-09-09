import Lax678846.NondeterministicPolynomialTime

namespace Lax678846Proofs.PairEncoding

open Lax678846.NondeterministicPolynomialTime

/-- Decode the tagged first word, leaving the untagged certificate intact. -/
def decode : List Bool → Option (List Bool × List Bool)
  | false :: c => some ([], c)
  | true :: b :: rest => do
      let (w, c) ← decode rest
      some (b :: w, c)
  | _ => none

theorem decode_encode (w c : List Bool) : decode (encodePair (w, c)) = some (w, c) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change (decode (encodePair (w, c))).bind (fun p => some (b :: p.1, p.2)) = _
    rw [ih]
    rfl

theorem encode_injective : Function.Injective encodePair := by
  rintro ⟨w, c⟩ ⟨w', c'⟩ h
  have h' := congrArg decode h
  simpa only [decode_encode, Option.some.injEq] using h'

theorem length_encode (w c : List Bool) :
    (encodePair (w, c)).length = 2 * w.length + c.length + 1 := by
  induction w with
  | nil => simp [encodePair]
  | cons b w ih =>
    change (true :: b :: encodePair (w, c)).length = _
    simp only [List.length_cons, ih]
    omega

theorem encode_decode {xs : List Bool} {p : List Bool × List Bool}
    (h : decode xs = some p) : encodePair p = xs := by
  induction xs using decode.induct generalizing p with
  | case1 c =>
    simp only [decode, Option.some.injEq] at h
    cases h
    rfl
  | case2 b rest ih =>
    cases hd : decode rest with
    | none => simp [decode, hd] at h
    | some q =>
      have hq := ih hd
      simp only [decode, hd] at h
      cases h
      change true :: b :: encodePair q = true :: b :: rest
      rw [hq]
  | case3 xs hxs => simp_all [decode]

end Lax678846Proofs.PairEncoding
