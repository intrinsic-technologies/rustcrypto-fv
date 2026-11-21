import P256.Proofs.Signing.Core.Iteration.Output.Blocks.Load
import P256.Proofs.Common.Field.SquareRoot.Exponent.ReadDigit.State
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary}

theorem dispatch (pre : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d33e)
    {tag : BitVec 64} (htag : memLoad t.external (frameBase s + 528) 64 = tag) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      u.RIP = (if tag.setWidth 8 = 0 then 0x10d377 else 0x10d358) ∧
      u.regValue .r12 = memLoad t.external (frameBase s + 536) 64 ∧
      u.regValue .rbx = memLoad t.external (frameBase s + 544) 64 ∧
      AgreesExcept [.reg 12, .reg 3, .flags, .rip] t u := by
  obtain ⟨n,a,runA,readyA,_,ea⟩ := Blocks.Load_correct boundary pre.outerBoundary t
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xd33e Blocks.LoadBytes
      (by decide) (by decide +kernel)) ⟨rip,fun off ho => by
        rw [frame.rsp]
        exact local_readable pre frame (by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega)⟩
  have fa := after_registers frame readyA ea.agrees
    (by simp [Blocks.LoadEffect,Effect.components,Component.Covers])
    (by simp [Blocks.LoadEffect,Effect.components]) (by simp [Blocks.LoadEffect,Effect.components])
    (by simp [Blocks.LoadEffect,Effect.components]) (by simp [Blocks.LoadEffect,Effect.components])
  have memoryA := ea.agrees.external (by simp [Blocks.LoadEffect,Effect.components,Component.Covers])
  obtain ⟨b,runB,readyB,eb⟩ :=
    (cmp_m8_imm8_effect_step 0x10d34e (.sib 4 none 0 (.d32 528))
      (by decide) (by decide) (by decide) 0).advances readyA
      (programText_slice (programLoaded_codeIn fa.loaded) 0xd34e _ (by decide) (by decide +kernel))
      ⟨ea.rip,by change MemReadable a (stackPtr a + 528) 1; rw [fa.rsp]; exact local_readable pre fa (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd356 (by decide)))
  have fb := after_registers fa readyB eb.agrees
    (by simp [cmpM8Imm8Effect,Effect.components,Component.Covers])
    (by simp [cmpM8Imm8Effect,Effect.components]) (by simp [cmpM8Imm8Effect,Effect.components])
    (by simp [cmpM8Imm8Effect,Effect.components]) (by simp [cmpM8Imm8Effect,Effect.components])
  have flag : (StatusFlags.ofRFLAGS b.RFLAGS).ZF = (tag.setWidth 8 == 0) := by
    have h := eb.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS b.RFLAGS).ZF =
      (cmpSpec (memLoad a.external (stackPtr a + 528) 8) 0).ZF at h
    rw [h,cmpSpec_ZF,fa.rsp,memoryA,
      ← Common.Field.SquareRoot.memLoad_setWidth_of_le _ _ (by decide : 8 ≤ 64) (by decide),htag]
  obtain ⟨u,stepU,readyU,raw⟩ := jcc_rel8_effect_step 0x10d356 4 0x1f b readyB
    (programText_slice (programLoaded_codeIn fb.loaded) 0xd356 _ (by decide) (by decide +kernel))
    ⟨eb.rip,fun _ => by decide⟩
  have ip : u.RIP = (if tag.setWidth 8 = 0 then 0x10d377 else 0x10d358) := by
    have h := raw.rip
    change u.RIP = if condHolds 4 (StatusFlags.ofRFLAGS b.RFLAGS) then _ else _ at h
    change u.RIP = (if (StatusFlags.ofRFLAGS b.RFLAGS).ZF then 0x10d377 else 0x10d358) at h
    simpa only [flag,beq_iff_eq] using h
  have runU : Advances boundary 1 b u := Advances.of_step stepU (.inl (by
    rw [ip]; split
    · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd377 (by decide))
    · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd358 (by decide))))
  have ag : AgreesExcept [.reg 12,.reg 3,.flags,.rip] t u :=
    ((ea.agrees.trans eb.agrees).trans raw.agrees).mono
      (by simp [Blocks.LoadEffect,cmpM8Imm8Effect,jccEffect,branchEffect,Effect.components])
  have fu := after_registers frame readyU ag (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  refine ⟨n+1+1,u,(runA.trans runB).trans runU,fu,ip,?_,?_,ag⟩
  · exact ((raw.agrees.read (n:=64) (r:=12) (by simp [jccEffect,branchEffect,Effect.components])).trans
      (eb.agrees.read (n:=64) (r:=12) (by simp))).trans (by change a.regValue .r12 = _; have h : a.regValue .r12 = memLoad t.external (stackPtr t + 536) 64 := ea.writes.1; simpa only [frame.rsp] using h)
  · exact ((raw.agrees.read (n:=64) (r:=3) (by simp [jccEffect,branchEffect,Effect.components])).trans
      (eb.agrees.read (n:=64) (r:=3) (by simp))).trans (by change a.regValue .rbx = _; have h : a.regValue .rbx = memLoad t.external (stackPtr t + 544) 64 := ea.writes.2; simpa only [frame.rsp] using h)

end P256.Proofs.Signing.Core.Iteration.Output
