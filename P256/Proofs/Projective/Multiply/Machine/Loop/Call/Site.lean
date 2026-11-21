import P256.Proofs.Projective.Multiply.Machine.Loop.Interface
import P256.Proofs.Projective.Preserve
import P256.Proofs.Program.FieldCall.Memory

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Program.FieldCall

structure CallSite (target : BitVec 64) where
  offset : Nat
  disp : BitVec 32
  bounded : offset + 5 < 118431
  bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp
  target_eq : branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
    (disp.signExtend 64) = target

def CallSite.returnRip {target : BitVec 64} (site : CallSite target) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 site.offset + 5

theorem call_site [Bindings] {s t : RamState} {boundary : ReturnBoundary} {target : BitVec 64}
    (pre : Pre s boundary) (state : FrameState s t 96 1400 376)
    (site : CallSite target) (targetProg : InProgram target)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.offset) :
    ∃ v, Advances boundary 1 t v ∧ ReadyToStep v ∧
      (callEffect (fun _ => target) site.returnRip t).Holds t v := by
  have low := Program.inProgram_low targetProg
  have step := scalar_call pre.toCalleePre (by decide) (by decide) state site.offset site.disp (Nat.le_of_lt site.bounded)
    site.bytes (by rw [site.target_eq]; exact low) (by rw [site.target_eq]; exact targetProg) rip
  simpa only [site.target_eq, CallSite.returnRip] using step

theorem call_return_program [Bindings] {t v : RamState} {target : BitVec 64}
    (site : CallSite target)
    (effect : (callEffect (fun _ => target) site.returnRip t).Holds t v) :
    InProgram (returnBoundary v).rip := by
  have ret : (returnBoundary v).rip = site.returnRip := (callEffect_stack effect).1
  rw [ret]
  have h := inProgram_of_textOffset (site.offset + 5) site.bounded
  simpa only [CallSite.returnRip, BitVec.ofNat_add, BitVec.add_assoc,
    show BitVec.ofNat 64 5 = (5 : BitVec 64) from rfl] using h

end P256.Proofs.Projective.Multiply.Machine.Loop
