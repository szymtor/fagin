import Lax678846Proofs.PreprocessorLayout

namespace Lax678846Proofs.PreprocessorBound

open Lax678846.FiniteStructures Lax979537Proofs
open StackProgram StackBoolean PreprocessorLayout

noncomputable def program (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : EvalProgram (Port σ k p) Unit :=
  StackPolynomial.program (ExpandedEncoding.boundPolynomial σ p)
    (domain σ k p) (bound σ k p) (tmp σ k p) (counters σ k p)

noncomputable def cost (σ : Vocabulary) (k : Nat) (p : Polynomial Nat) : Polynomial Nat :=
  StackPolynomial.cost (StackPolynomial.powers (ExpandedEncoding.boundPolynomial σ p) (counters σ k p))

noncomputable def result {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit) : EvalStore (Port σ k p) Unit :=
  ⟨(s.state.1, none), Function.update s.stk (bound σ k p)
    (List.replicate (p.eval (encode (RelationalVerifier.base B)).length + 1) true)⟩

theorem program_executes {σ : Vocabulary} {k : Nat} {p : Polynomial Nat}
    (B : Structure (k :: k :: σ)) (s : EvalStore (Port σ k p) Unit)
    (hd : s.stk (domain σ k p) = List.replicate B.size true)
    (hb : s.stk (bound σ k p) = []) (ht : s.stk (tmp σ k p) = [])
    (hc : ∀ c ∈ counters σ k p, s.stk c = []) :
    ∃ d, d ≤ (cost σ k p).eval B.size ∧ Executes (program σ k p) s (result B s) d := by
  have hn : (counters σ k p).Nodup := by
    apply (List.nodup_finRange _).map
    intro i j h
    simpa using h
  have hdepth : StackPolynomial.depth (ExpandedEncoding.boundPolynomial σ p) ≤
      (counters σ k p).length := by simp [counters]
  have hs : ∀ c ∈ counters σ k p, c ≠ domain σ k p ∧ c ≠ bound σ k p ∧ c ≠ tmp σ k p := by
    intro c hm
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
    simp [domain, bound, tmp, slot]
  obtain ⟨d, hd', hp⟩ := StackPolynomial.program_executes (ExpandedEncoding.boundPolynomial σ p)
    (domain σ k p) (bound σ k p) (tmp σ k p)
    (by simp [domain, bound, slot]) (by simp [domain, tmp, slot]) (by simp [bound, tmp, slot])
    (counters σ k p) hn hdepth hs B.size s hd ht hc
  have he : StackPower.addTokens (bound σ k p)
      ((ExpandedEncoding.boundPolynomial σ p).eval B.size) s = result B s := by
    have hv := ExpandedEncoding.boundPolynomial_eval p (RelationalVerifier.base B)
    change (ExpandedEncoding.boundPolynomial σ p).eval B.size = _ at hv
    simp only [StackPower.addTokens, result, hv, hb, List.append_nil]
  rw [he] at hp
  exact ⟨d, hd', hp⟩

end Lax678846Proofs.PreprocessorBound
