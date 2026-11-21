import P256.Proofs.Verifying.Core.Registers
import P256.Proofs.Program.Code
import P256.Proofs.Verifying.Core.Memory
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Memory.LoadByte
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Scalars

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.ByteOps.ByteOps

theorem inverse_guard [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (frame : Frame s t)
    (rip : t.RIP = 0x10dc8d) (flag : t.external[frameBase s + 160]? = some 1) :
    ∃ u, Advances boundary 4 t u ∧ Frame s u ∧ u.RIP = 0x10dca0 ∧
      AgreesExcept [.reg 0, .mem (frameBase s + 0) 1, .flags, .rip] t u := by
  have outside (offset : Nat) (bound : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program pre.outerBoundary (inProgram_of_textOffset offset bound)
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (movzx_r32_m8_effect_step 0x10dc8d 0 (.sib 4 none 0 (.d32 160))
      (by decide +kernel) rfl rfl).advances (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) 0xdc8d _
        (by decide) (by decide +kernel))
      ⟨rip, by
        change MemReadable t (stackPtr t + 160) 1
        exact stack_readable (frameOffset := 1176) pre.toCalleePre frame (by decide) (by decide)⟩
      (outside 0xdc95 (by decide))
  have agreesA : AgreesExcept [.reg 0, .rip] t a := effectA.agrees
  have frameA := frame.after_registers readyA agreesA
    (by simp [Component.Covers]) (by simp)
  have oneA : (a.regValue .rax).setWidth 8 = 1 := by
    have value := effectA.writes
    change a.regValue .rax = (memLoad t.external (stackPtr t + 160) 8).setWidth 64 at value
    rw [frame.rsp] at value
    change a.regValue .rax = (memLoad t.external (frameBase s+160) 8).setWidth 64 at value
    rw [P256.Proofs.Common.Memory.memLoad8_of_byte flag] at value
    rw [value]
    rfl
  let am := AddrMode.sib 4 none 0 .none
  have addr : storeAddrAt 0x10dc95 am 3 a = frameBase s + 0#64 := by
    change stackPtr a + 0#64 = _
    rw [frameA.rsp]
    rfl
  have write : MemWritable a (frameBase s + 0#64) 1 := by
    have eq : frameBase s + 0#64 = stackPtr s - 1176#64 := by
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [eq]
    exact writable_of_grow (stack_sub_writable pre.stack
      (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
      (offset := 1176) (len := 1) (by decide) (by decide) (by decide)
      (by have := Nat.mod_lt (stackPtr s-1176#64).toNat (by decide : 0<4096); omega)) frameA.allocated
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (mov_m8_r8_legacy_effect_step 0x10dc95 0 (by decide) am (by decide +kernel) rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn frameA.loaded) 0xdc95 _
        (by decide) (by decide +kernel))
      ⟨effectA.rip, addr ▸ write, by
        change RangeApart (storeAddrAt 0x10dc95 am 3 a) 1 0x10dc95 3
        rw [addr]
        have h := stack_code (frameOffset := 1176) pre.toCalleePre frameA (offset := 0) (len := 1)
          (codeOffset := 0xdc95) (codeLen := 3) (by decide) (by decide) (by decide)
        simp only [frameA.rsp,Extracted.textAddress,BitVec.reduceAdd] at h
        exact h⟩
      (outside 0xdc98 (by decide))
  change (storeEffect 0x10dc95 3 (storeAddrAt 0x10dc95 am 3)
    (fun state => (Operand.reg 0 : Operand 8).read state) a).Holds a b at effectB
  have agreesB : AgreesExcept [.mem (frameBase s + 0#64) 1, .rip] a b := by
    simpa only [storeEffect_components, addr, Nat.reduceDiv] using effectB.agrees
  have localB : WritesWithin [.mem (frameBase s + 0#64) 1, .rip]
      #v[registerRegion s .rdi 24,workRegion s 9992] := by
    intro c hc address cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · have addr : frameBase s+0#64 = stackPtr s-1176#64 := by
        simp only [frameBase,BitVec.add_zero]
        rfl
      rw [addr] at cover
      exact ⟨workRegion s 9992,by simp,
        work_contains pre.toCalleePre (by decide) (by decide) cover⟩
    · exact cover.elim
  have frameB := frameA.after_effect pre.toCalleePre (by decide) readyB agreesB localB (by simp)
  obtain ⟨c, runC, readyC, effectC⟩ := (P256.Proofs.Common.Instructions.ByteOps.ByteOps.cmp_al_imm8_effect_step 0x10dc98 1).advances readyB
    (programText_slice (programLoaded_codeIn frameB.loaded) 0xdc98 [0x3c,1]
      (by decide) (by decide +kernel)) effectB.rip (outside 0xdc9a (by decide))
  have agreesC : AgreesExcept [.flags,.rip] b c := effectC.agrees
  have frameC := frameB.after_registers readyC agreesC
    (by simp [Component.Covers]) (by simp)
  have oneB : (b.regValue .rax).setWidth 8 = 1 :=
    (agreesB.read (n := 8) (r := 0) (by simp)).trans oneA
  have zeroFlag : (StatusFlags.ofRFLAGS c.RFLAGS).ZF = true := by
    have h := effectC.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS c.RFLAGS).ZF = (cmpSpec ((b.regValue .rax).setWidth 8) 1).ZF at h
    rw [h, oneB]
    decide +kernel
  have cond : condHolds 5 (StatusFlags.ofRFLAGS c.RFLAGS) = false := by
    change (!(StatusFlags.ofRFLAGS c.RFLAGS).ZF) = false
    rw [zeroFlag]
    rfl
  have next : (jccEffect 0x10dc9a 6 5 ((0x54f : BitVec 32).signExtend 64) c).rip = 0x10dca0 := by
    simp only [jccEffect, cond, branchEffect, Bool.false_eq_true, ↓reduceIte, BitVec.reduceAdd]
    rfl
  obtain ⟨u, runU, readyU, effectU⟩ := (jcc_rel32_effect_step 0x10dc9a 5 0x54f).advances readyC
    (programText_slice (programLoaded_codeIn frameC.loaded) 0xdc9a _
      (by decide) (by decide +kernel))
    ⟨effectC.rip, by rw [cond]; exact Bool.noConfusion⟩
    (by rw [next]; exact outside 0xdca0 (by decide))
  have agreesU : AgreesExcept [.rip] c u := effectU.agrees
  have frameU := frameC.after_registers readyU agreesU
    (by simp [Component.Covers]) (by simp)
  refine ⟨u, ((runA.trans runB).trans runC).trans runU, frameU, effectU.rip.trans next, ?_⟩
  exact (((agreesA.trans agreesB).trans agreesC).trans agreesU).mono (by simp)

end P256.Proofs.Verifying.Core.Scalars
