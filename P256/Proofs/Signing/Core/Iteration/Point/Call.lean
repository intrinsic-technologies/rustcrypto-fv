import P256.Proofs.Signing.Core.Iteration.Call
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Site

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Projective.Multiply.Machine.Loop
open NextNonce (scalarFrame)

theorem call_site [Bindings] {s t : RamState} {boundary : ReturnBoundary} {target : BitVec 64}
    (pre : SignPre s boundary) (frame : Frame s t) (site : CallSite target)
    (targetProg : InProgram target)
    (rip : t.RIP = Extracted.textAddress+BitVec.ofNat 64 site.offset) :
    ∃ v, Advances boundary 1 t v ∧ ReadyToStep v ∧
      (callEffect (fun _ => target) site.returnRip t).Holds t v := by
  have step := ScalarFrame.scalar_call pre.toCalleePre (by decide) (by decide)
    (scalarFrame frame) site.offset site.disp (Nat.le_of_lt site.bounded) site.bytes
    (by rw [site.target_eq]; exact Program.inProgram_low targetProg)
    (by rw [site.target_eq]; exact targetProg) rip
  simpa only [site.target_eq,CallSite.returnRip] using step

theorem call_registers [Bindings] {t v u : RamState} {boundary : ReturnBoundary}
    {target ret : BitVec 64} {outputBytes reserve : Nat}
    (effect : (callEffect (fun _ => target) ret t).Holds t v)
    (result : CalleeResult v u boundary outputBytes reserve) :
    ∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15], u.regValue r = t.regValue r := by
  intro r hr
  apply (result.calleeSaved r hr).trans
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
  · exact effect.agrees.read (n := 64) (r := 3) (by simp)
  · exact effect.agrees.read (n := 64) (r := 5) (by simp)
  · exact effect.agrees.read (n := 64) (r := 12) (by simp)
  · exact effect.agrees.read (n := 64) (r := 13) (by simp)
  · exact effect.agrees.read (n := 64) (r := 14) (by simp)
  · exact effect.agrees.read (n := 64) (r := 15) (by simp)

end P256.Proofs.Signing.Core.Iteration.Point
