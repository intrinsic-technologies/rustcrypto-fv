import Sha2.Proofs.Common.SHA512.Entry.Branch
import Sha2.Proofs.Common.SHA256.Entry.Save

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem entry_save [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt64} {input : ByteArray} {count : Nat}
    (pre : CompressionPre s boundary hash input count) (positive : 0 < count) :
    ∃ t, Advances boundary 9 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x10ddaa ∧ stackPtr t = stackPtr s - 416 ∧
      t.external = Sha2.Proofs.Common.Encoding.Serialize.saveMemory s ∧
      AgreesExcept (Sha2.Proofs.Common.Encoding.Serialize.saveFrame s ++ [.flags]) s t := by
  obtain ⟨u, branch, ready, rip, frame⟩ := entry_branch pre
  have rip' : u.RIP = 0x10dd99 := by simpa only [ite_eq_right (by omega : count ≠ 0)] using rip
  have cp := Sha2.Proofs.Common.SHA256.calleePre_after_flags pre.toCalleePre ready frame rip'
  have code : Sha2.Proofs.Common.Encoding.Serialize.SaveCode 0xdd99 := by
    constructor <;> decide +kernel
  obtain ⟨v, run, ready', loaded, ripV, rspV, memoryV, frameV⟩ :=
    Sha2.Proofs.Common.Encoding.Serialize.save_registers cp (by decide) rfl code
  have rspU : stackPtr u = stackPtr s := frame.read (n := 64) (r := 4) (by simp)
  have frameU : Sha2.Proofs.Common.Encoding.Serialize.saveFrame u =
      Sha2.Proofs.Common.Encoding.Serialize.saveFrame s := by
    simp only [Sha2.Proofs.Common.Encoding.Serialize.saveFrame, rspU]
  have saveU : Sha2.Proofs.Common.Encoding.Serialize.saveMemory u =
      Sha2.Proofs.Common.Encoding.Serialize.saveMemory s := by
    have rbp : u.regValue .rbp = s.regValue .rbp := frame.read (n := 64) (r := 5) (by simp)
    have r15 : u.regValue .r15 = s.regValue .r15 := frame.read (n := 64) (r := 15) (by simp)
    have r14 : u.regValue .r14 = s.regValue .r14 := frame.read (n := 64) (r := 14) (by simp)
    have r13 : u.regValue .r13 = s.regValue .r13 := frame.read (n := 64) (r := 13) (by simp)
    have r12 : u.regValue .r12 = s.regValue .r12 := frame.read (n := 64) (r := 12) (by simp)
    have rbx : u.regValue .rbx = s.regValue .rbx := frame.read (n := 64) (r := 3) (by simp)
    rw [Sha2.Proofs.Common.Encoding.Serialize.saveMemory, rspU, rbp, r15, r14, r13, r12, rbx,
      frame.external (by simp [Component.Covers])]
    rfl
  obtain ⟨t, step, readyT, effect⟩ :=
    (sub_r64_imm32_effect_step 0x10dda3 0x48 0xec 368
      (by constructor <;> decide) (by decide) (by decide)).advances ready'
      (programText_slice (programLoaded_codeIn loaded) 0xdda3
        [0x48,0x81,0xec,0x70,1,0,0] (by decide) (by decide +kernel)) ripV
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xddaa (by decide)))
  have memoryT : t.external = v.external := effect.agrees.external
    (by simp [subR64Imm32Effect_components, Component.Covers])
  have totalFrame : AgreesExcept
      (Sha2.Proofs.Common.Encoding.Serialize.saveFrame s ++ [.flags]) s t := by
    rw [frameU] at frameV
    apply ((frame.trans frameV).trans effect.agrees).mono
    simp only [subR64Imm32Effect_components, Sha2.Proofs.Common.Encoding.Serialize.saveFrame,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with ((rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) |
      (rfl | rfl | rfl) <;> simp [gprNumber, rexB, modrmRm]
  refine ⟨t, (branch.trans run).trans step, readyT, ?_, effect.rip, ?_,
    memoryT.trans (memoryV.trans saveU), totalFrame⟩
  · intro a b hb
    rw [memoryT]
    exact loaded a b hb
  · have hw : stackPtr t = stackPtr v - 368 := effect.writes
    rw [hw, rspV, rspU, BitVec.sub_sub]
    rfl

end Sha2.Proofs.Common.SHA512
