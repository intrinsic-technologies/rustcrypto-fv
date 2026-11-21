import Hkdf.Proofs.Common.SHA256.Entry.Branch

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine

theorem calleePre_after_flags [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry target : BitVec 64} {inputBytes outputBytes reserve : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    (ready : ReadyToStep t) (frame : AgreesExcept [.flags, .rip] s t)
    (rip : t.RIP = target) : CalleePre t boundary target inputBytes outputBytes reserve := by
  have memory := frame.external (by simp [Component.Covers])
  have si : t.regValue .rsi = s.regValue .rsi := frame.read (n := 64) (r := 6) (by simp)
  have di : t.regValue .rdi = s.regValue .rdi := frame.read (n := 64) (r := 7) (by simp)
  have sp : t.regValue .rsp = s.regValue .rsp := frame.read (n := 64) (r := 4) (by simp)
  have ins : registerRegion t .rsi inputBytes = registerRegion s .rsi inputBytes := by
    simp only [registerRegion, si]
  have outs : registerRegion t .rdi outputBytes = registerRegion s .rdi outputBytes := by
    simp only [registerRegion, di]
  have stacks : Stack.region t reserve = Stack.region s reserve := by
    simp only [Stack.region, sp]
  refine ⟨pre.stride, supportedMachine_of_ready_agrees pre.machine ready frame,
    frame.directionFlagClear (by simp) pre.directionFlag, ?_, rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    pre.outerBoundary, ?_⟩
  · intro a b hb
    rw [memory]
    exact pre.loaded a b hb
  · simpa only [ins] using pre.inputBounded
  · simpa only [ins, memory] using pre.inputAllocated
  · simpa only [outs] using pre.outputBounded
  · simpa only [outs, memory] using pre.outputAllocated
  · simpa only [Stack.Valid, stacks, memory, Stack.NoUnderflow, Stack.returnSlot, registerRegion, sp]
      using pre.stack
  · simpa only [ins, outs, stacks] using pre.separation
  · simpa only [outs, stacks] using pre.avoids
  · have hr : (returnBoundary t).rip = (returnBoundary s).rip := by
      change memLoad t.external (t.regValue .rsp) 64 = memLoad s.external (s.regValue .rsp) 64
      rw [memory, sp]
    rw [hr]
    exact pre.returnInProgram

theorem entry_save [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray} {count : Nat}
    (pre : CompressionPre s boundary hash input count) (positive : 0 < count) :
    ∃ t, Advances boundary 9 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x1095da ∧ stackPtr t = stackPtr s - 336 ∧
      t.external = Hkdf.Proofs.Common.Encoding.Serialize.saveMemory s ∧
      AgreesExcept (Hkdf.Proofs.Common.Encoding.Serialize.saveFrame s ++ [.flags]) s t := by
  obtain ⟨u, branch, ready, rip, frame⟩ := entry_branch pre
  have rip' : u.RIP = 0x1095c9 := by simpa only [ite_eq_right (by omega : count ≠ 0)] using rip
  have cp := calleePre_after_flags pre.toCalleePre ready frame rip'
  have code : Hkdf.Proofs.Common.Encoding.Serialize.SaveCode 0x95c9 := by
    constructor <;> decide +kernel
  obtain ⟨v, run, ready', loaded, ripV, rspV, memoryV, frameV⟩ :=
    Hkdf.Proofs.Common.Encoding.Serialize.save_registers cp (by decide) rfl code
  have rspU : stackPtr u = stackPtr s := frame.read (n := 64) (r := 4) (by simp)
  have frameU : Hkdf.Proofs.Common.Encoding.Serialize.saveFrame u =
      Hkdf.Proofs.Common.Encoding.Serialize.saveFrame s := by
    simp only [Hkdf.Proofs.Common.Encoding.Serialize.saveFrame, rspU]
  have saveU : Hkdf.Proofs.Common.Encoding.Serialize.saveMemory u =
      Hkdf.Proofs.Common.Encoding.Serialize.saveMemory s := by
    have rbp : u.regValue .rbp = s.regValue .rbp := frame.read (n := 64) (r := 5) (by simp)
    have r15 : u.regValue .r15 = s.regValue .r15 := frame.read (n := 64) (r := 15) (by simp)
    have r14 : u.regValue .r14 = s.regValue .r14 := frame.read (n := 64) (r := 14) (by simp)
    have r13 : u.regValue .r13 = s.regValue .r13 := frame.read (n := 64) (r := 13) (by simp)
    have r12 : u.regValue .r12 = s.regValue .r12 := frame.read (n := 64) (r := 12) (by simp)
    have rbx : u.regValue .rbx = s.regValue .rbx := frame.read (n := 64) (r := 3) (by simp)
    rw [Hkdf.Proofs.Common.Encoding.Serialize.saveMemory, rspU, rbp, r15, r14, r13, r12, rbx,
      frame.external (by simp [Component.Covers])]
    rfl
  obtain ⟨t, step, readyT, effect⟩ :=
    (sub_r64_imm32_effect_step 0x1095d3 0x48 0xec 288
      (by constructor <;> decide) (by decide) (by decide)).advances ready'
      (programText_slice (programLoaded_codeIn loaded) 0x95d3
        [0x48,0x81,0xec,0x20,1,0,0] (by decide) (by decide +kernel)) ripV
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95da (by decide)))
  have memoryT : t.external = v.external := effect.agrees.external
    (by simp [subR64Imm32Effect_components, Component.Covers])
  have totalFrame : AgreesExcept
      (Hkdf.Proofs.Common.Encoding.Serialize.saveFrame s ++ [.flags]) s t := by
    rw [frameU] at frameV
    apply ((frame.trans frameV).trans effect.agrees).mono
    simp only [subR64Imm32Effect_components, Hkdf.Proofs.Common.Encoding.Serialize.saveFrame,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with ((rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) |
      (rfl | rfl | rfl) <;> simp [gprNumber, rexB, modrmRm]
  refine ⟨t, (branch.trans run).trans step, readyT, ?_, effect.rip, ?_,
    memoryT.trans (memoryV.trans saveU), totalFrame⟩
  · intro a b hb
    rw [memoryT]
    exact loaded a b hb
  · have hw : stackPtr t = stackPtr v - 288 := effect.writes
    rw [hw, rspV, rspU, BitVec.sub_sub]
    rfl

end Hkdf.Proofs.Common.SHA256
