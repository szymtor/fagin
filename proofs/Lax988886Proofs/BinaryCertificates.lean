import Lax988886Proofs.RelationCertificates

namespace Lax988886Proofs.BinaryCertificates

open Lax988886.FiniteStructures Lax751879Proofs

/-- Read one data bit for each selected position. Arbitrary masks are
allowed; all of them decode to words bounded by the table length. -/
def select : List Bool → List Bool → List Bool
  | b :: mask, a :: data => if b then a :: select mask data else select mask data
  | _, _ => []

theorem select_length (mask data : List Bool) : (select mask data).length ≤ data.length := by
  induction mask generalizing data with
  | nil => simp [select]
  | cons b mask ih =>
    cases data with
    | nil => simp [select]
    | cons a data => cases b <;> simp [select] <;> have h := ih data <;> omega

theorem select_false (n : Nat) (data : List Bool) : select (List.replicate n false) data = [] := by
  induction n generalizing data with
  | zero => rfl
  | succ n ih => cases data <;> simp [List.replicate_succ, select, ih]

theorem select_prefix (w mask data : List Bool) :
    select (List.replicate w.length true ++ mask) (w ++ data) = w ++ select mask data := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [List.replicate_succ, select] using congrArg (b :: ·) ih

/-- Two relations of the same fixed arity store a variable-length word:
the first marks positions to retain, and the second gives their bit values. -/
def decode {n k : Nat} (R : Interpretation [k,k] n) : List Bool :=
  select ((Lax751879.StructureEncoding.tuples n k).map (R 0))
    ((Lax751879.StructureEncoding.tuples n k).map (R 1))

def encode (n k : Nat) (c : List Bool) : Interpretation [k,k] n :=
  Fin.cons
    (Decoding.readTable (Lax751879.StructureEncoding.tuples n k)
      (List.replicate c.length true ++ List.replicate (n ^ k - c.length) false))
    (Fin.cons
      (Decoding.readTable (Lax751879.StructureEncoding.tuples n k)
        (c ++ List.replicate (n ^ k - c.length) false))
      (fun r => Fin.elim0 r))

theorem decode_length {n k : Nat} (R : Interpretation [k,k] n) :
    (decode R).length ≤ n ^ k := by
  have h := select_length ((Lax751879.StructureEncoding.tuples n k).map (R 0))
    ((Lax751879.StructureEncoding.tuples n k).map (R 1))
  simpa [decode, StructureEncoding.tuples_length] using h

theorem decode_encode (n k : Nat) (c : List Bool) (hc : c.length ≤ n ^ k) :
    decode (encode n k c) = c := by
  have hm := DecoderSoundness.readTable_map (Lax751879.StructureEncoding.tuples n k)
    (List.replicate c.length true ++ List.replicate (n ^ k - c.length) false)
    (DecoderSoundness.tuples_nodup n k) (by simp [StructureEncoding.tuples_length]; omega)
  have hb := DecoderSoundness.readTable_map (Lax751879.StructureEncoding.tuples n k)
    (c ++ List.replicate (n ^ k - c.length) false)
    (DecoderSoundness.tuples_nodup n k) (by simp [StructureEncoding.tuples_length]; omega)
  change select ((Lax751879.StructureEncoding.tuples n k).map
    (Decoding.readTable (Lax751879.StructureEncoding.tuples n k) _))
    ((Lax751879.StructureEncoding.tuples n k).map
      (Decoding.readTable (Lax751879.StructureEncoding.tuples n k) _)) = c
  rw [hm, hb, select_prefix, select_false, List.append_nil]

/-- Replace a polynomially bounded binary certificate by two guessed
relations, retaining the original certificate-length check exactly. -/
theorem exists_bounded_iff (n k bound : Nat) (hcap : bound ≤ n ^ k) (P : List Bool → Prop) :
    (∃ c : List Bool, c.length ≤ bound ∧ P c) ↔
      ∃ R : Interpretation [k,k] n, (decode R).length ≤ bound ∧ P (decode R) := by
  constructor
  · rintro ⟨c, hc, hp⟩
    refine ⟨encode n k c, ?_⟩
    rw [decode_encode n k c (hc.trans hcap)]
    exact ⟨hc, hp⟩
  · rintro ⟨R, hc, hp⟩
    exact ⟨decode R, hc, hp⟩

end Lax988886Proofs.BinaryCertificates
