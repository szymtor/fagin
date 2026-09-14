import Lax751879Proofs.StackCopy
import Lax751879.StructureEncoding

namespace Lax988886Proofs.StackCertificateHeader

open Lax751879Proofs.StackProgram Lax751879Proofs.StackTransfer

variable {K Aux : Type} [DecidableEq K]

/-- Turn the certificate tables into a structure encoding over the witness
vocabulary, using the already decoded unary domain counter. -/
def prepend (domain certificate tmp : K) : BitProgram K Aux :=
  .seq (.atom (.push certificate (fun _ => false)))
    (Lax751879Proofs.StackCopy.copy domain certificate tmp)

theorem prepend_executes (domain certificate tmp : K)
    (hdc : domain ≠ certificate) (hdt : domain ≠ tmp) (hct : certificate ≠ tmp)
    (s : BitStore K Aux) (n : Nat) (hn : s.stk domain = List.replicate n true)
    (ht : s.stk tmp = []) :
    Executes (prepend domain certificate tmp) s
      ⟨(s.state.1, none), Function.update s.stk certificate
        (Lax751879.StructureEncoding.unary n ++ s.stk certificate)⟩ (7 * n + 5) := by
  let u := Op.apply (.push certificate (fun _ : Aux × Option Bool => false)) s
  have hp : Executes (.atom (.push certificate (fun _ => false))) s u 1 := Executes.atom _ _
  have hu : u.stk domain = List.replicate n true := by simp [u, Op.apply, hdc, hn]
  have hc : u.stk certificate = false :: s.stk certificate := by simp [u, Op.apply]
  have htmp : u.stk tmp = [] := by simp [u, Op.apply, Ne.symm hct, ht]
  have he := Lax751879Proofs.StackCopy.copy_store domain certificate tmp hdc hdt hct u htmp
  rw [hu, hc, List.length_replicate] at he
  have hf : (⟨(u.state.1, none), Function.update u.stk certificate
      (List.replicate n true ++ false :: s.stk certificate)⟩ : BitStore K Aux) =
      ⟨(s.state.1, none), Function.update s.stk certificate
        (Lax751879.StructureEncoding.unary n ++ s.stk certificate)⟩ := by
    apply Store.ext
    · rfl
    · simp [u, Op.apply, Lax751879.StructureEncoding.unary, List.append_assoc]
  rw [hf] at he
  have h := Executes.seq hp he
  convert h using 1 <;> omega

end Lax988886Proofs.StackCertificateHeader
