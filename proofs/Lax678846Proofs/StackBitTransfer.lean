import Lax678846Proofs.StackMapTransfer
import Lax678846Proofs.StackControl
import Mathlib.Logic.Equiv.Option

namespace Lax678846Proofs.StackBitTransfer

open Lax979537Proofs.StackProgram

variable {K Aux : Type} {Γ : K → Type} [DecidableEq K]

def control (src : K) (e : Γ src ≃ Bool) :
    (Aux × Option (Γ src)) ≃ (Aux × Option Bool) :=
  Equiv.prodCongr (Equiv.refl Aux) (Equiv.optionCongr e)

/-- Alphabet conversion using only a Boolean scratch register. -/
def transfer (src dst : K) (e : Γ src ≃ Bool) (f : Bool → Γ dst) :
    Program Γ (Aux × Option Bool) :=
  StackControl.map (control src e)
    (StackMapTransfer.transfer src dst (f ∘ e) (f false))

theorem transfer_store (src dst : K) (hne : src ≠ dst) (e : Γ src ≃ Bool) (f : Bool → Γ dst)
    (s : Store Γ (Aux × Option Bool)) :
    Executes (transfer src dst e f) s
      ⟨(s.state.1, none), Function.update (Function.update s.stk src []) dst
        ((s.stk src).reverse.map (f ∘ e) ++ s.stk dst)⟩ (3 * (s.stk src).length + 2) := by
  let u : Store Γ (Aux × Option (Γ src)) :=
    ⟨(s.state.1, s.state.2.map e.symm), s.stk⟩
  have h := StackControl.executes_map (control src e)
    (StackMapTransfer.transfer_store src dst hne (f ∘ e) (f false) u)
  have hin : StackControl.mapStore (control src e) u = s := by
    apply Store.ext
    · simp [StackControl.mapStore, control, u, Equiv.optionCongr, Option.map_map]
    · rfl
  rw [hin] at h
  exact h

theorem transfer_ioStore (src dst : K) (hne : src ≠ dst) (e : Γ src ≃ Bool)
    (f : Bool → Γ dst) (a : Aux) (xs : List (Γ src)) :
    Executes (transfer src dst e f) (ioStore src (a, none) xs)
      (ioStore dst (a, none) (xs.reverse.map (f ∘ e))) (3 * xs.length + 2) := by
  have h := transfer_store src dst hne e f (ioStore src (a, none) xs)
  have he : (⟨(a, none), Function.update
        (Function.update (ioStore src (a, (none : Option Bool)) xs).stk src []) dst
        (xs.reverse.map (f ∘ e))⟩ : Store Γ (Aux × Option Bool)) =
      ioStore dst (a, none) (xs.reverse.map (f ∘ e)) := by
    apply Store.ext
    · rfl
    · funext key
      by_cases hd : key = dst
      · subst key; simp [ioStore]
      · by_cases hs : key = src
        · subst key; simp [ioStore, hne]
        · simp [ioStore, hd, hs]
  have hs : (ioStore src (a, (none : Option Bool)) xs).stk src = xs := by simp [ioStore]
  have hd : (ioStore src (a, (none : Option Bool)) xs).stk dst = [] := by
    simp [ioStore, Ne.symm hne]
  rw [hs, hd, List.append_nil] at h
  change Executes _ _ ⟨(a, none), _⟩ _ at h
  rwa [he] at h

end Lax678846Proofs.StackBitTransfer
