import Lax979537Proofs.StackProgram

namespace Lax678846Proofs.StackSum

open Lax979537Proofs.StackProgram

variable {K L σ : Type} {Δ : L → Type} [DecidableEq K] [DecidableEq L]

/-- Stack renaming also works for heterogeneous alphabets. This is needed
to compose the Boolean preprocessor with an arbitrary NP verifier. -/
def renameOp (f : K → L) : Op (fun k => Δ (f k)) σ → Op Δ σ
  | .push k g => .push (f k) g
  | .pop k g => .pop (f k) g
  | .peek k g => .peek (f k) g
  | .load g => .load g

def rename (f : K → L) : Program (fun k => Δ (f k)) σ → Program Δ σ
  | .atom o => .atom (renameOp f o)
  | .seq p q => .seq (rename f p) (rename f q)
  | .branch b p q => .branch b (rename f p) (rename f q)
  | .loop b p => .loop b (rename f p)

def project (f : K → L) (s : Store Δ σ) : Store (fun k => Δ (f k)) σ :=
  ⟨s.state, fun k => s.stk (f k)⟩

theorem op_project (f : K → L) (hf : Function.Injective f)
    (o : Op (fun k => Δ (f k)) σ) (s : Store Δ σ) :
    project f ((renameOp f o).apply s) = o.apply (project f s) := by
  cases o with
  | push k g | pop k g =>
      apply Store.ext
      · rfl
      · funext j
        by_cases h : j = k
        · subst j; simp [project, renameOp, Op.apply]
        · have hj : f j ≠ f k := fun he => h (hf he)
          simp [project, renameOp, Op.apply, h, hj]
  | peek k g | load g => rfl

omit [DecidableEq K] in
theorem op_frame (f : K → L) (o : Op (fun k => Δ (f k)) σ)
    (s : Store Δ σ) (key : L) (hk : key ∉ Set.range f) :
    ((renameOp f o).apply s).stk key = s.stk key := by
  have hne : ∀ k, key ≠ f k := fun k he => hk ⟨k, he.symm⟩
  cases o <;> simp [renameOp, Op.apply, hne]

theorem rename_executes (f : K → L) (hf : Function.Injective f)
    {p : Program (fun k => Δ (f k)) σ} {s t : Store (fun k => Δ (f k)) σ} {cost : Nat}
    (h : Executes p s t cost) (s' : Store Δ σ) (hs : project f s' = s) :
    ∃ t', Executes (rename f p) s' t' cost ∧ project f t' = t ∧
      ∀ key, key ∉ Set.range f → t'.stk key = s'.stk key := by
  induction h generalizing s' with
  | atom o s =>
      refine ⟨(renameOp f o).apply s', Executes.atom _ _, ?_, ?_⟩
      · rw [op_project f hf, hs]
      · exact op_frame f o s'
  | seq hp hq ihp ihq =>
      obtain ⟨u', hp', hu, hpu⟩ := ihp s' hs
      obtain ⟨t', hq', ht, hqt⟩ := ihq u' hu
      exact ⟨t', Executes.seq hp' hq', ht, fun key hk => (hqt key hk).trans (hpu key hk)⟩
  | branch_true hb hp ih =>
      obtain ⟨t', hp', ht, hpt⟩ := ih s' hs
      have hstate := congrArg (fun q => q.state) hs
      dsimp only [project] at hstate
      exact ⟨t', Executes.branch_true (by rw [hstate]; exact hb) hp', ht, hpt⟩
  | branch_false hb hp ih =>
      obtain ⟨t', hp', ht, hpt⟩ := ih s' hs
      have hstate := congrArg (fun q => q.state) hs
      dsimp only [project] at hstate
      exact ⟨t', Executes.branch_false (by rw [hstate]; exact hb) hp', ht, hpt⟩
  | loop_false hb =>
      have hstate := congrArg (fun q => q.state) hs
      dsimp only [project] at hstate
      exact ⟨s', Executes.loop_false (by rw [hstate]; exact hb), hs, fun _ _ => rfl⟩
  | loop_true hb hp hq ihp ihq =>
      obtain ⟨u', hp', hu, hpu⟩ := ihp s' hs
      obtain ⟨t', hq', ht, hqt⟩ := ihq u' hu
      have hstate := congrArg (fun q => q.state) hs
      dsimp only [project] at hstate
      exact ⟨t', Executes.loop_true (by rw [hstate]; exact hb) hp' hq', ht,
        fun key hk => (hqt key hk).trans (hpu key hk)⟩

variable {Γ : K → Type}

def leftStore (s : Store Γ σ) (extra : ∀ l, List (Δ l)) :
    Store (Sum.elim Γ Δ) σ := ⟨s.state, fun | .inl k => s.stk k | .inr l => extra l⟩

theorem leftStore_ioStore (port : K) (initial : σ) (w : List (Γ port)) :
    leftStore (Δ := Δ) (ioStore port initial w) (fun _ => []) =
      ioStore (.inl port) initial w := by
  apply Store.ext
  · rfl
  · funext key
    cases key with
    | inl k =>
      by_cases h : k = port
      · subst k; simp [leftStore, ioStore]
      · simp [leftStore, ioStore, h]
    | inr l => simp [leftStore, ioStore]

theorem executes_left {p : Program Γ σ} {s t : Store Γ σ}
    {cost : Nat} (h : Executes p s t cost) (extra : ∀ l, List (Δ l)) :
    Executes (rename (Δ := Sum.elim Γ Δ) Sum.inl p)
      (leftStore s extra) (leftStore t extra) cost := by
  obtain ⟨t', ht, hproj, hframe⟩ := rename_executes (Δ := Sum.elim Γ Δ)
    Sum.inl Sum.inl_injective h (leftStore s extra) rfl
  have he : t' = leftStore t extra := by
    apply Store.ext
    · exact congrArg (fun q => q.state) hproj
    · funext key
      cases key with
      | inl k => exact congrArg (fun q => q.stk k) hproj
      | inr l => exact hframe (.inr l) (by simp)
  rwa [he] at ht

def rightStore (extra : ∀ k, List (Γ k)) (s : Store Δ σ) :
    Store (Sum.elim Γ Δ) σ := ⟨s.state, fun | .inl k => extra k | .inr l => s.stk l⟩

theorem rightStore_ioStore (port : L) (initial : σ) (w : List (Δ port)) :
    rightStore (Γ := Γ) (fun _ => []) (ioStore port initial w) =
      ioStore (.inr port) initial w := by
  apply Store.ext
  · rfl
  · funext key
    cases key with
    | inl k => simp [rightStore, ioStore]
    | inr l =>
      by_cases h : l = port
      · subst l; simp [rightStore, ioStore]
      · simp [rightStore, ioStore, h]

theorem executes_right {p : Program Δ σ} {s t : Store Δ σ}
    {cost : Nat} (h : Executes p s t cost) (extra : ∀ k, List (Γ k)) :
    Executes (rename (Δ := Sum.elim Γ Δ) Sum.inr p)
      (rightStore extra s) (rightStore extra t) cost := by
  obtain ⟨t', ht, hproj, hframe⟩ := rename_executes (Δ := Sum.elim Γ Δ)
    Sum.inr Sum.inr_injective h (rightStore extra s) rfl
  have he : t' = rightStore extra t := by
    apply Store.ext
    · exact congrArg (fun q => q.state) hproj
    · funext key
      cases key with
      | inl k => exact hframe (.inl k) (by simp)
      | inr l => exact congrArg (fun q => q.stk l) hproj
  rwa [he] at ht

end Lax678846Proofs.StackSum
