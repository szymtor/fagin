import Lax988886Proofs.TMComputable
import Lax988886Proofs.StackSum
import Lax988886Proofs.StackBitTransfer
import Lax751879Proofs.StackOutput

-- Preserve Lean 4.30 definition unfolding during elaboration.
set_option backward.isDefEq.respectTransparency false

namespace Lax988886Proofs.MachineComposition

open Turing Lax751879Proofs.StackProgram

abbrev Port (a b : FinTM2) := a.K ⊕ (Unit ⊕ b.K)
abbrev Alphabet (a b : FinTM2) : Port a b → Type := Sum.elim a.Γ (Sum.elim (fun _ => Bool) b.Γ)
abbrev State (a b : FinTM2) :=
  ((a.σ × Option a.Λ) × (b.σ × Option b.Λ)) × Option Bool

def initial (a b : FinTM2) : State a b := ((TMComputable.initial a, TMComputable.initial b), none)
def input (a b : FinTM2) : Port a b := .inl a.k₀
def middleOut (a b : FinTM2) : Port a b := .inl a.k₁
def buffer (a b : FinTM2) : Port a b := .inr (.inl ())
def middleIn (a b : FinTM2) : Port a b := .inr (.inr b.k₀)
def output (a b : FinTM2) : Port a b := .inr (.inr b.k₁)

noncomputable def first (a b : FinTM2) : Program (Alphabet a b) (State a b) :=
  StackSum.rename Sum.inl (StackControl.extend (StackControl.extend (TMComputable.program a)))

noncomputable def second (a b : FinTM2) : Program (Alphabet a b) (State a b) :=
  StackSum.rename Sum.inr (StackSum.rename Sum.inr
    (StackControl.extend (StackControl.right (TMComputable.program b))))

def move (a b : FinTM2) (ea : a.Γ a.k₁ ≃ Bool) (eb : b.Γ b.k₀ ≃ Bool) :
    Program (Alphabet a b) (State a b) :=
  .seq (StackBitTransfer.transfer (middleOut a b) (buffer a b) ea id)
    (StackBitTransfer.transfer (buffer a b) (middleIn a b) (Equiv.refl Bool) eb.symm)

noncomputable def program (a b : FinTM2) (ea : a.Γ a.k₁ ≃ Bool) (eb : b.Γ b.k₀ ≃ Bool) :
    Program (Alphabet a b) (State a b) :=
  .seq (first a b) (.seq (move a b ea eb) (second a b))

theorem first_executes (a b : FinTM2) {xs : List (a.Γ a.k₀)} {ys : List (a.Γ a.k₁)} {d : Nat}
    (h : Executes (TMComputable.program a) (ioStore a.k₀ (TMComputable.initial a) xs)
      (ioStore a.k₁ (TMComputable.initial a) ys) d) :
    Executes (first a b) (ioStore (input a b) (initial a b) xs)
      (ioStore (middleOut a b) (initial a b) ys) d := by
  have hh := StackControl.executes_extend
    (StackControl.executes_extend h (TMComputable.initial b)) (none : Option Bool)
  simp only [StackControl.store_ioStore] at hh
  simpa only [StackSum.leftStore_ioStore] using!
    StackSum.executes_left (Δ := Sum.elim (fun _ : Unit => Bool) b.Γ) hh (fun _ => [])

theorem second_executes (a b : FinTM2) {xs : List (b.Γ b.k₀)} {ys : List (b.Γ b.k₁)} {d : Nat}
    (h : Executes (TMComputable.program b) (ioStore b.k₀ (TMComputable.initial b) xs)
      (ioStore b.k₁ (TMComputable.initial b) ys) d) :
    Executes (second a b) (ioStore (middleIn a b) (initial a b) xs)
      (ioStore (output a b) (initial a b) ys) d := by
  have hr : Executes (StackControl.right (TMComputable.program b))
      (ioStore b.k₀ (TMComputable.initial a, TMComputable.initial b) xs)
      (ioStore b.k₁ (TMComputable.initial a, TMComputable.initial b) ys) d :=
    StackControl.executes_right h (TMComputable.initial a)
  have hh := StackControl.executes_extend hr (none : Option Bool)
  simp only [StackControl.store_ioStore] at hh
  have hi := StackSum.executes_right (Γ := fun _ : Unit => Bool) hh (fun _ => [])
  simp only [StackSum.rightStore_ioStore] at hi
  simpa only [StackSum.rightStore_ioStore] using!
    StackSum.executes_right (Γ := a.Γ) hi (fun _ => [])

theorem move_executes (a b : FinTM2) (ea : a.Γ a.k₁ ≃ Bool) (eb : b.Γ b.k₀ ≃ Bool)
    (xs : List Bool) :
    Executes (move a b ea eb) (ioStore (middleOut a b) (initial a b) (xs.map ea.symm))
      (ioStore (middleIn a b) (initial a b) (xs.map eb.symm)) (6 * xs.length + 4) := by
  have h1 := StackBitTransfer.transfer_ioStore (Γ := Alphabet a b)
    (middleOut a b) (buffer a b) (by simp [middleOut, buffer]) ea id
    (TMComputable.initial a, TMComputable.initial b) (xs.map ea.symm)
  have h2 := StackBitTransfer.transfer_ioStore (Γ := Alphabet a b)
    (buffer a b) (middleIn a b) (by simp [buffer, middleIn]) (Equiv.refl Bool) eb.symm
    (TMComputable.initial a, TMComputable.initial b) xs.reverse
  have he1 : (xs.map ea.symm).reverse.map (id ∘ ea) = xs.reverse := by
    simp [List.map_map, Function.comp_def]
  have he2 : xs.reverse.reverse.map (eb.symm ∘ Equiv.refl Bool) = xs.map eb.symm := by simp
  dsimp only [middleOut, buffer, middleIn, Alphabet, Sum.elim] at h1 h2
  erw [he1, List.length_map] at h1
  erw [he2, List.length_reverse] at h2
  have hh := Executes.seq h1 h2
  have ht : (3 * xs.length + 2) + (3 * xs.length + 2) = 6 * xs.length + 4 := by omega
  simpa only [ht] using! hh

/-- Concrete composition across a Boolean intermediate alphabet. Both
machines finish with clean work stacks and reset finite control. -/
theorem executes (a b : FinTM2) (ea : a.Γ a.k₁ ≃ Bool) (eb : b.Γ b.k₀ ≃ Bool)
    {xs : List (a.Γ a.k₀)} {mid : List Bool} {ys : List (b.Γ b.k₁)} {d e : Nat}
    (ha : Executes (TMComputable.program a) (ioStore a.k₀ (TMComputable.initial a) xs)
      (ioStore a.k₁ (TMComputable.initial a) (mid.map ea.symm)) d)
    (hb : Executes (TMComputable.program b) (ioStore b.k₀ (TMComputable.initial b) (mid.map eb.symm))
      (ioStore b.k₁ (TMComputable.initial b) ys) e) :
    Executes (program a b ea eb) (ioStore (input a b) (initial a b) xs)
      (ioStore (output a b) (initial a b) ys) (d + (6 * mid.length + 4 + e)) :=
  Executes.seq (first_executes a b ha)
    (Executes.seq (move_executes a b ea eb mid) (second_executes a b hb))

end Lax988886Proofs.MachineComposition
