import Lax979537Proofs.StackRename

namespace Lax678846Proofs.StackEmbedding

open Lax979537Proofs.StackProgram Lax979537Proofs.StackRename

variable {K L Γ σ : Type} [DecidableEq K] [DecidableEq L]

def rightStore (extra : L → List Γ) (s : Store (fun _ : K => Γ) σ) :
    Store (fun _ : L ⊕ K => Γ) σ := ⟨s.state, Sum.elim extra s.stk⟩

theorem executes_right {p : Program (fun _ : K => Γ) σ} {s t : Store (fun _ : K => Γ) σ}
    {cost : Nat} (h : Executes p s t cost) (extra : L → List Γ) :
    Executes (rename Sum.inr p) (rightStore extra s) (rightStore extra t) cost := by
  obtain ⟨t', ht, hproj, hframe⟩ := rename_executes (L := L ⊕ K) Sum.inr Sum.inr_injective h
    (rightStore extra s) rfl
  have he : t' = rightStore extra t := by
    apply Store.ext
    · exact congrArg (fun q => q.state) hproj
    · funext key
      cases key with
      | inl k => exact hframe (.inl k) (by simp)
      | inr l => exact congrArg (fun q => q.stk l) hproj
  rwa [he] at ht

theorem rename_comp (f : K → L) {M : Type} (g : L → M)
    (p : Program (fun _ : K => Γ) σ) : rename g (rename f p) = rename (g ∘ f) p := by
  induction p with
  | atom o => cases o <;> rfl
  | seq p q ihp ihq => simp [rename, ihp, ihq]
  | branch b p q ihp ihq => simp [rename, ihp, ihq]
  | loop b p ih => simp [rename, ih]

end Lax678846Proofs.StackEmbedding
