import Lax988886Proofs.ExpandedEncoding
import Lax988886Proofs.StackPolynomial
import Lax751879Proofs.DecoderCorrectness
import Lax751879Proofs.StackRename
import Lax751879Proofs.StackBoolean

set_option backward.isDefEq.respectTransparency false

namespace Lax988886Proofs.PreprocessorLayout

open Lax988886.FiniteStructures Lax751879Proofs
open StackProgram StackTransfer StackBoolean

abbrev Extra (σ : Vocabulary) (p : Polynomial Nat) :=
  Fin 7 ⊕ Fin (StackPolynomial.depth (ExpandedEncoding.boundPolynomial σ p))
abbrev Port (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) :=
  FiniteDecoder.Port (k :: k :: σ) 0 ⊕ Extra σ p

def input (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : Port σ k p :=
  .inl (FiniteDecoder.work (k :: k :: σ) 0).input
def domain (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : Port σ k p :=
  .inl (FiniteDecoder.work (k :: k :: σ) 0).domain
def table (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) (r : Symbol (k :: k :: σ)) : Port σ k p :=
  .inl (FiniteDecoder.tablePort (k :: k :: σ) 0 r)
def slot (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) (i : Fin 7) : Port σ k p := .inr (.inl i)
def word (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : Port σ k p := slot σ k p 0
def certificate (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : Port σ k p := slot σ k p 1
def pair (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : Port σ k p := slot σ k p 2
def tmp (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : Port σ k p := slot σ k p 3
def bound (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : Port σ k p := slot σ k p 4
def copyCert (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : Port σ k p := slot σ k p 5
def copyBound (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : Port σ k p := slot σ k p 6

noncomputable def counters (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : List (Port σ k p) :=
  (List.finRange (StackPolynomial.depth (ExpandedEncoding.boundPolynomial σ p))).map
    (fun i => .inr (.inr i))

def baseTables (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : List (Port σ k p) :=
  (List.finRange σ.length).map (fun r => table σ k p r.succ.succ)

def decoder (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : EvalProgram (Port σ k p) Unit :=
  StackRename.rename Sum.inl (FiniteDecoder.program (k :: k :: σ) 0)

def decoded (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) (xs : List Bool) : EvalStore (Port σ k p) Unit :=
  StackRename.sumStore
    (StackDecoder.result (FiniteDecoder.layout (k :: k :: σ) 0)
      (FiniteDecoder.inputStore (k :: k :: σ) 0 xs)) (fun _ => [])

theorem decoder_executes (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) (xs : List Bool) :
    ∃ d, d ≤ (StackDecoder.costPolynomial (FiniteDecoder.layout (k :: k :: σ) 0)).eval xs.length ∧
      Executes (decoder σ k p) (ioStore (input σ k p) FiniteDecoder.initial xs) (decoded σ k p xs) d := by
  obtain ⟨d, hd, hp⟩ := FiniteDecoder.program_executes (k :: k :: σ) 0 xs
  have he : StackRename.sumStore (FiniteDecoder.inputStore (k :: k :: σ) 0 xs)
      (fun _ : Extra σ p => []) = ioStore (input σ k p) FiniteDecoder.initial xs := by
    apply Store.ext
    · rfl
    · funext key
      cases key with
      | inl j => simp [StackRename.sumStore, FiniteDecoder.inputStore, ioStore, input]
      | inr j => simp [StackRename.sumStore, ioStore, input]
  have hh := StackRename.executes_in_sum hp (fun _ : Extra σ p => [])
  rw [he] at hh
  exact ⟨d, hd, hh⟩

theorem decoded_validity (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) (xs : List Bool) :
    (decoded σ k p xs).state.1.2 = (Decoding.decode (k :: k :: σ) 0 xs).isSome :=
  DecoderAgreement.finite_validity (k :: k :: σ) 0 xs

structure Ready {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit) : Prop where
  domain : s.stk (domain σ k p) = List.replicate B.size true
  tables : ∀ r, s.stk (table σ k p r) =
    (Lax751879.StructureEncoding.tuples B.size ((k :: k :: σ).get r)).map (B.relation r)
  empty : ∀ e : Extra σ p, s.stk (.inr e) = []

theorem decoded_ready (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) (xs : List Bool)
    (B : Lax751879.OrderedStructures.PointedStructure (k :: k :: σ) 0)
    (hd : Decoding.decode (k :: k :: σ) 0 xs = some B) : Ready B.structureValue (decoded σ k p xs) := by
  have h := DecoderCorrectness.result_represents (k :: k :: σ) 0 xs B hd
  exact ⟨h.ready.1, h.tables, fun _ => rfl⟩

theorem baseTables_payload {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    {B : Structure (k :: k :: σ)} {s : EvalStore (Port σ k p) Unit} (h : Ready B s) :
    (baseTables σ k p).flatMap s.stk = ExpandedEncoding.payload (RelationalVerifier.base B) := by
  simp only [baseTables, List.flatMap_map, Function.comp_def]
  unfold ExpandedEncoding.payload
  apply congrArg (fun f : Symbol σ → List Bool => (List.finRange σ.length).flatMap f)
  funext r
  exact h.tables r.succ.succ

end Lax988886Proofs.PreprocessorLayout
