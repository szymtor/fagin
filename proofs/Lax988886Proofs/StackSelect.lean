import Lax988886Proofs.BinaryCertificates
import Lax751879Proofs.StackCopy

namespace Lax988886Proofs.StackSelect

open Lax751879Proofs.StackProgram Lax751879Proofs.StackTransfer

variable {K Aux : Type} [DecidableEq K]

abbrev SelectProgram (K Aux : Type) := BitProgram K (Aux × Bool)
abbrev SelectStore (K Aux : Type) := BitStore K (Aux × Bool)

def readData (data : K) : SelectProgram K Aux :=
  .atom (.pop data (fun s b => ((s.1.1, b.getD false), s.2)))

def emit (dst : K) : SelectProgram K Aux :=
  .branch (fun s => s.2.getD false)
    (.atom (.push dst (fun s => s.1.2))) (.atom (.load id))

def body (mask data dst : K) : SelectProgram K Aux :=
  .seq (readData data) (.seq (emit dst) (read mask))

def loop (mask data dst : K) : SelectProgram K Aux :=
  .loop (fun s => s.2.isSome) (body mask data dst)

/-- Consume the mask and data tables, retaining precisely the marked bits.
The selected word is pushed in reverse order onto the destination. -/
def select (mask data dst : K) : SelectProgram K Aux :=
  .seq (read mask) (.seq (loop mask data dst)
    (.atom (.load (fun s => ((s.1.1, true), none)))))

def working (base : K → List Bool) (mask data dst : K)
    (ms ds ys : List Bool) (a : Aux) (bit : Bool) (marker : Option Bool) : SelectStore K Aux :=
  ⟨((a, bit), marker), Function.update (Function.update (Function.update base mask ms) data ds) dst ys⟩

theorem pop_mask (base : K → List Bool) (mask data dst : K)
    (hmd : mask ≠ data) (hmy : mask ≠ dst) (ms ds ys : List Bool)
    (a : Aux) (bit : Bool) (marker : Option Bool) :
    Op.apply (.pop mask (fun s : (Aux × Bool) × Option Bool => fun b => (s.1, b)))
      (working base mask data dst ms ds ys a bit marker) =
      working base mask data dst ms.tail ds ys a bit ms.head? := by
  apply Store.ext
  · simp [Op.apply, working, hmd, hmy]
  · funext key
    by_cases hm : key = mask <;> by_cases hd : key = data <;> by_cases hy : key = dst <;>
      simp_all [Op.apply, working]

theorem pop_data (base : K → List Bool) (mask data dst : K)
    (hmd : mask ≠ data) (hdy : data ≠ dst) (ms ds ys : List Bool)
    (a : Aux) (bit : Bool) (marker : Option Bool) :
    Op.apply (.pop data (fun s : (Aux × Bool) × Option Bool => fun b => ((s.1.1, b.getD false), s.2)))
      (working base mask data dst ms ds ys a bit marker) =
      working base mask data dst ms ds.tail ys a (ds.head?.getD false) marker := by
  apply Store.ext
  · simp [Op.apply, working, hdy]
  · funext key
    by_cases hm : key = mask <;> by_cases hd : key = data <;> by_cases hy : key = dst <;>
      simp_all [Op.apply, working]

theorem emit_executes (base : K → List Bool) (mask data dst : K)
    (ms ds ys : List Bool) (a : Aux) (b m : Bool) :
    Executes (emit dst) (working base mask data dst ms ds ys a b (some m))
      (working base mask data dst ms ds (if m then b :: ys else ys) a b (some m)) 2 := by
  cases m with
  | false => exact Executes.branch_false rfl (Executes.atom (.load id) _)
  | true =>
    have h := Executes.atom (.push dst (fun s : (Aux × Bool) × Option Bool => s.1.2))
      (working base mask data dst ms ds ys a b (some true))
    have he : Op.apply (.push dst (fun s : (Aux × Bool) × Option Bool => s.1.2))
        (working base mask data dst ms ds ys a b (some true)) =
        working base mask data dst ms ds (b :: ys) a b (some true) := by
      apply Store.ext
      · rfl
      · funext key
        by_cases hy : key = dst <;> simp_all [Op.apply, working, Function.update_apply]
    rw [he] at h
    exact Executes.branch_true rfl h

theorem loop_executes (base : K → List Bool) (mask data dst : K)
    (hmd : mask ≠ data) (hmy : mask ≠ dst) (hdy : data ≠ dst)
    (ms ds ys : List Bool) (hlen : ms.length = ds.length) (a : Aux) (bit : Bool) :
    ∃ last, Executes (loop mask data dst)
      (working base mask data dst ms.tail ds ys a bit ms.head?)
      (working base mask data dst [] [] ((BinaryCertificates.select ms ds).reverse ++ ys) a last none)
      (5 * ms.length + 1) := by
  induction ms generalizing ds ys bit with
  | nil =>
    have hd : ds = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ds
    exact ⟨bit, Executes.loop_false rfl⟩
  | cons m ms ih =>
    cases ds with
    | nil => simp at hlen
    | cons b ds =>
      have hl : ms.length = ds.length := by simpa using hlen
      let ys' := if m then b :: ys else ys
      obtain ⟨last, ht⟩ := ih ds ys' hl b
      have hp := Executes.atom
        (.pop data (fun s : (Aux × Bool) × Option Bool => fun b => ((s.1.1, b.getD false), s.2)))
        (working base mask data dst ms (b :: ds) ys a bit (some m))
      rw [pop_data base mask data dst hmd hdy] at hp
      have he := emit_executes base mask data dst ms ds ys a b m
      have hr := Executes.atom
        (.pop mask (fun s : (Aux × Bool) × Option Bool => fun b => (s.1, b)))
        (working base mask data dst ms ds ys' a b (some m))
      rw [pop_mask base mask data dst hmd hmy] at hr
      have hb := Executes.seq hp (Executes.seq he hr)
      have hh := Executes.loop_true (p := body mask data dst)
        (b := fun s : (Aux × Bool) × Option Bool => s.2.isSome) rfl hb ht
      have ht' : (1 + (2 + 1)) + (5 * ms.length + 1) + 1 = 5 * (ms.length + 1) + 1 := by omega
      refine ⟨last, ?_⟩
      cases m <;> simpa only [List.tail_cons, List.head?_cons, List.length_cons,
        BinaryCertificates.select, Bool.false_eq_true, ↓reduceIte, List.reverse_cons,
        List.append_assoc, List.singleton_append, ys', ht'] using hh

theorem select_executes (base : K → List Bool) (mask data dst : K)
    (hmd : mask ≠ data) (hmy : mask ≠ dst) (hdy : data ≠ dst)
    (ms ds ys : List Bool) (hlen : ms.length = ds.length) (a : Aux) (bit : Bool) (marker : Option Bool) :
    Executes (select mask data dst) (working base mask data dst ms ds ys a bit marker)
      (working base mask data dst [] [] ((BinaryCertificates.select ms ds).reverse ++ ys) a true none)
      (5 * ms.length + 3) := by
  have hp := Executes.atom
    (.pop mask (fun s : (Aux × Bool) × Option Bool => fun b => (s.1, b)))
    (working base mask data dst ms ds ys a bit marker)
  rw [pop_mask base mask data dst hmd hmy] at hp
  obtain ⟨last, hl⟩ := loop_executes base mask data dst hmd hmy hdy ms ds ys hlen a bit
  have hr := Executes.atom (.load (fun s : (Aux × Bool) × Option Bool => ((s.1.1, true), none)))
    (working base mask data dst [] [] ((BinaryCertificates.select ms ds).reverse ++ ys) a last none)
  have hh := Executes.seq hp (Executes.seq hl hr)
  have ht : 1 + ((5 * ms.length + 1) + 1) = 5 * ms.length + 3 := by omega
  simpa only [ht] using hh

theorem select_store (mask data dst : K)
    (hmd : mask ≠ data) (hmy : mask ≠ dst) (hdy : data ≠ dst)
    (s : SelectStore K Aux) (hlen : (s.stk mask).length = (s.stk data).length) :
    Executes (select mask data dst) s
      ⟨((s.state.1.1, true), none),
        Function.update (Function.update (Function.update s.stk mask []) data []) dst
          ((BinaryCertificates.select (s.stk mask) (s.stk data)).reverse ++ s.stk dst)⟩
      (5 * (s.stk mask).length + 3) := by
  simpa only [working, Function.update_eq_self, Prod.mk.eta] using
    select_executes s.stk mask data dst hmd hmy hdy (s.stk mask) (s.stk data) (s.stk dst)
      hlen s.state.1.1 s.state.1.2 s.state.2

end Lax988886Proofs.StackSelect
