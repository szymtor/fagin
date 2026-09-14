import Lax751879Proofs.StackPower
import Lax988886Proofs.CertificateCapacity

namespace Lax988886Proofs.StackPolynomial

open Lax751879Proofs Lax751879Proofs.StackProgram Lax751879Proofs.StackTransfer

variable {K Aux : Type} [DecidableEq K]

def value (powers : List (List K)) (n : Nat) : Nat :=
  (powers.map (fun cs => n ^ cs.length)).sum

noncomputable def cost : List (List K) → Polynomial Nat
  | [] => 1
  | cs :: rest => StackPower.costPolynomial cs.length + cost rest

def sumPowers (domain out tmp : K) : List (List K) → BitProgram K Aux
  | [] => .atom (.load (fun s => (s.1, none)))
  | cs :: rest => .seq (StackPower.power domain out tmp cs) (sumPowers domain out tmp rest)

theorem addTokens_add (out : K) (a b : Nat) (s : BitStore K Aux) :
    StackPower.addTokens out a (StackPower.addTokens out b s) =
      StackPower.addTokens out (a + b) s := by
  simp only [StackPower.addTokens, Function.update_self, Function.update_idem,
    List.replicate_add, List.append_assoc]

/-- A fixed finite sum of unary powers. Counters are reused between terms,
and every stack except the accumulating output is preserved. -/
theorem sumPowers_executes (domain out tmp : K)
    (hdo : domain ≠ out) (hdt : domain ≠ tmp) (hot : out ≠ tmp)
    (powers : List (List K)) (hnodup : ∀ cs ∈ powers, cs.Nodup)
    (hslots : ∀ cs ∈ powers, ∀ c ∈ cs, c ≠ domain ∧ c ≠ out ∧ c ≠ tmp)
    (n : Nat) (s : BitStore K Aux) (hd : s.stk domain = List.replicate n true)
    (ht : s.stk tmp = []) (hc : ∀ cs ∈ powers, ∀ c ∈ cs, s.stk c = []) :
    ∃ t, t ≤ (cost powers).eval n ∧
      Executes (sumPowers domain out tmp powers) s (StackPower.addTokens out (value powers n) s) t := by
  induction powers generalizing s with
  | nil =>
    refine ⟨1, by simp [cost], ?_⟩
    simpa [sumPowers, StackPower.addTokens, value] using!
      Executes.atom (.load (fun s : Aux × Option Bool => (s.1, none))) s
  | cons cs rest ih =>
    obtain ⟨d, hd', hp⟩ := StackPower.power_executes domain out tmp hdo hdt hot cs
      (hnodup cs (by simp)) (hslots cs (by simp)) n s hd ht (hc cs (by simp))
    have hrn : ∀ ds ∈ rest, ds.Nodup := fun ds hm => hnodup ds (by simp [hm])
    have hrs : ∀ ds ∈ rest, ∀ c ∈ ds, c ≠ domain ∧ c ≠ out ∧ c ≠ tmp :=
      fun ds hm => hslots ds (by simp [hm])
    obtain ⟨e, he, hq⟩ := ih hrn hrs (StackPower.addTokens out (n ^ cs.length) s)
      (by simpa [StackPower.addTokens, hdo] using hd)
      (by simpa [StackPower.addTokens, Ne.symm hot] using ht)
      (by
        intro ds hm c hcm
        simpa [StackPower.addTokens, (hrs ds hm c hcm).2.1] using hc ds (by simp [hm]) c hcm)
    rw [addTokens_add, Nat.add_comm (value rest n)] at hq
    refine ⟨d + e, by simpa only [cost, Polynomial.eval_add] using Nat.add_le_add hd' he, ?_⟩
    exact Executes.seq hp hq

/-- Natural polynomial coefficients can be compiled by repeating each
monomial a fixed number of times. No arithmetic precision bound is needed. -/
theorem exists_exponents (p : Polynomial Nat) :
    ∃ es : List Nat, ∀ n, p.eval n = (es.map (fun i => n ^ i)).sum := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    obtain ⟨es, he⟩ := ihp
    obtain ⟨fs, hf⟩ := ihq
    exact ⟨es ++ fs, fun n => by simp [he n, hf n]⟩
  | monomial i c =>
    exact ⟨List.replicate c i, fun n => by simp [Polynomial.eval_monomial]⟩

noncomputable def exponents (p : Polynomial Nat) : List Nat := Classical.choose (exists_exponents p)

theorem exponents_spec (p : Polynomial Nat) (n : Nat) :
    p.eval n = ((exponents p).map (fun i => n ^ i)).sum :=
  Classical.choose_spec (exists_exponents p) n

noncomputable def depth (p : Polynomial Nat) : Nat := (exponents p).sum

theorem exponent_le_depth (p : Polynomial Nat) (i : Nat) (hi : i ∈ exponents p) : i ≤ depth p := by
  exact List.single_le_sum (fun _ _ => Nat.zero_le _) i hi

noncomputable def powers (p : Polynomial Nat) (counters : List K) : List (List K) :=
  (exponents p).map counters.take

theorem value_powers (p : Polynomial Nat) (counters : List K) (h : depth p ≤ counters.length) (n : Nat) :
    value (powers p counters) n = p.eval n := by
  rw [exponents_spec]
  unfold value powers
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp [List.length_take, Nat.min_eq_left ((exponent_le_depth p i hi).trans h)]

noncomputable def program (p : Polynomial Nat) (domain out tmp : K) (counters : List K) :
    BitProgram K Aux := sumPowers domain out tmp (powers p counters)

theorem program_executes (p : Polynomial Nat) (domain out tmp : K)
    (hdo : domain ≠ out) (hdt : domain ≠ tmp) (hot : out ≠ tmp)
    (counters : List K) (hnodup : counters.Nodup) (hdepth : depth p ≤ counters.length)
    (hslots : ∀ c ∈ counters, c ≠ domain ∧ c ≠ out ∧ c ≠ tmp)
    (n : Nat) (s : BitStore K Aux) (hd : s.stk domain = List.replicate n true)
    (ht : s.stk tmp = []) (hc : ∀ c ∈ counters, s.stk c = []) :
    ∃ t, t ≤ (cost (powers p counters)).eval n ∧
      Executes (program p domain out tmp counters) s (StackPower.addTokens out (p.eval n) s) t := by
  have hn : ∀ cs ∈ powers p counters, cs.Nodup := by
    intro cs hm
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
    exact hnodup.take
  have hs : ∀ cs ∈ powers p counters, ∀ c ∈ cs, c ≠ domain ∧ c ≠ out ∧ c ≠ tmp := by
    intro cs hm c hcm
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
    exact hslots c (List.mem_of_mem_take hcm)
  have he : ∀ cs ∈ powers p counters, ∀ c ∈ cs, s.stk c = [] := by
    intro cs hm c hcm
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
    exact hc c (List.mem_of_mem_take hcm)
  obtain ⟨t, ht', hp⟩ := sumPowers_executes domain out tmp hdo hdt hot
    (powers p counters) hn hs n s hd ht he
  rw [value_powers p counters hdepth n] at hp
  exact ⟨t, ht', hp⟩

end Lax988886Proofs.StackPolynomial
