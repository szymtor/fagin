import Lax988886Proofs.OrderedFirstOrder

namespace Lax988886Proofs.RelationSlices

open Lax988886.FiniteStructures
open Lax751879.FixedPointSyntax Lax751879.FixedPointSemantics
open Lax988886Proofs.OrderedFirstOrder

def vocabulary (d : Nat) (τ : Vocabulary) : Vocabulary := τ.map (d + ·)

def symbol {τ : Vocabulary} (d : Nat) (r : Symbol τ) : Symbol (vocabulary d τ) :=
  ⟨r.val, by simpa [vocabulary] using r.isLt⟩

theorem arity {τ : Vocabulary} (d : Nat) (r : Symbol τ) :
    (vocabulary d τ).get (symbol d r) = d + τ.get r := by
  simp [vocabulary, symbol, List.get_eq_getElem]

def arguments {τ : Vocabulary} {d m : Nat} (r : Symbol τ)
    (clock : Fin d → Fin m) (args : Fin (τ.get r) → Fin m) :
    Fin ((vocabulary d τ).get (symbol d r)) → Fin m :=
  fun i => Fin.append clock args (Fin.cast (arity d r) i)

/-- Every relation parameter is replaced by a slice of its stage table.
The element quantifier shifts the clock indices to avoid capture. -/
def translate {σ τ : Vocabulary} {m d : Nat} (φ : RawFormula σ m τ)
    (clock : Fin d → Fin m) : RawFormula σ m (vocabulary d τ) :=
  match φ with
  | .truth => .truth
  | .equal x y => .equal x y
  | .less x y => .less x y
  | .relation r args => .relation r args
  | .variable r args => .variable (symbol d r) (arguments r clock args)
  | .neg ψ => .neg (translate ψ clock)
  | .conj ψ χ => .conj (translate ψ clock) (translate χ clock)
  | .exists' ψ => .exists' (translate ψ (Fin.succ ∘ clock))
  | .lfp _ _ _ => .truth

def environment {τ : Vocabulary} {d n : Nat} (clock : Fin d → Fin n)
    (η : RelationEnv n (vocabulary d τ)) : RelationEnv n τ :=
  fun r a => η (symbol d r) (arguments r clock a)

theorem compose_arguments {τ : Vocabulary} {d m n : Nat} (r : Symbol τ)
    (clock : Fin d → Fin m) (args : Fin (τ.get r) → Fin m) (v : Fin m → Fin n) :
    v ∘ arguments r clock args = arguments r (v ∘ clock) (v ∘ args) := by
  funext i
  change v (Fin.append clock args (Fin.cast (arity d r) i)) =
    Fin.append (v ∘ clock) (v ∘ args) (Fin.cast (arity d r) i)
  generalize Fin.cast (arity d r) i = j
  refine Fin.addCases ?_ ?_ j
  · intro a
    simp only [Fin.append_left, Function.comp_apply]
  · intro a
    simp only [Fin.append_right, Function.comp_apply]

theorem noFixedPoints {σ τ : Vocabulary} {m d : Nat} (φ : RawFormula σ m τ)
    (hφ : NoFixedPoints φ) (clock : Fin d → Fin m) :
    NoFixedPoints (translate φ clock) := by
  induction φ with
  | truth | equal | less | relation | «variable» => trivial
  | neg φ ih => exact ih hφ clock
  | conj φ ψ ihφ ihψ => exact ⟨ihφ hφ.1 clock, ihψ hφ.2 clock⟩
  | exists' φ ih => exact ih hφ _
  | lfp => exact hφ.elim

theorem eval_translate {σ τ : Vocabulary} {m d : Nat} (φ : RawFormula σ m τ)
    (hφ : NoFixedPoints φ) (clock : Fin d → Fin m)
    (A : Structure σ) (v : Fin m → Fin A.size)
    (η : RelationEnv A.size (vocabulary d τ)) :
    eval (translate φ clock) A v η ↔ eval φ A v (environment (v ∘ clock) η) := by
  induction φ with
  | truth | equal | less | relation => rfl
  | «variable» r args =>
      change η (symbol d r) (v ∘ arguments r clock args) ↔
        η (symbol d r) (arguments r (v ∘ clock) (v ∘ args))
      rw [compose_arguments]
  | neg φ ih => exact not_congr (ih hφ clock v η)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ hφ.1 clock v η) (ihψ hφ.2 clock v η)
  | exists' φ ih =>
      apply exists_congr
      intro a
      simpa only [Function.comp_def, Fin.cons_succ] using
        ih hφ (Fin.succ ∘ clock) (Fin.cons a v) η
  | lfp => exact hφ.elim

end Lax988886Proofs.RelationSlices
