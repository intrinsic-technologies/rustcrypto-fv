import Sha2.Proofs.Common.SHA512.Memory
import Sha2.Proofs.Common.SHA512.Compression.Interface
import Sha2.Proofs.Common.Encoding.Parser.LengthCheck.Triple
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Encoding.Parser.LengthCheck (cmp_r64_m64_effect_step)

theorem RegistersAt.after_control {s t : RamState} {hash : Array UInt64}
    (state : RegistersAt s hash) (frame : AgreesExcept [.reg 6, .flags, .rip] s t) :
    RegistersAt t hash := by
  refine ⟨state.size, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (frame.read (n := 64) (r := 11) (by simp)).trans state.a
  · exact (frame.read (n := 64) (r := 1) (by simp)).trans state.b
  · exact (frame.read (n := 64) (r := 10) (by simp)).trans state.c
  · exact (frame.read (n := 64) (r := 0) (by simp)).trans state.d
  · exact (frame.read (n := 64) (r := 3) (by simp)).trans state.e
  · exact (frame.read (n := 64) (r := 9) (by simp)).trans state.f
  · exact (frame.read (n := 64) (r := 8) (by simp)).trans state.g
  · exact (frame.read (n := 64) (r := 13) (by simp)).trans state.h

set_option maxRecDepth 8192 in
theorem loop_control [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
    {initialHash hash : Array UInt64} {input : ByteArray} {index count : Nat}
    (pre : CompressionPre initial boundary initialHash input count)
    (state : LoopState initial current hash index count)
    (rip : current.RIP = 0x111802) (hindex : index < count) :
    ∃ next, Advances boundary 3 current next ∧
      LoopState initial next hash (index + 1) count ∧
      next.RIP = (if index + 1 = count then 0x111814 else 0x10ddf0) := by
  obtain ⟨u, run₁, ready₁, effect₁⟩ :=
    (sub_r64_imm8_effect_step 0x111802 0x48 0xee 0x80
      (by simp [RexWPrefix]) (by decide) (by decide)).advances
      (supportedMachine_readyToStep state.machine)
      (programText_slice (programLoaded_codeIn state.loaded) 0x11802 [0x48,0x83,0xee,0x80]
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x11806 (by decide)))
  have frame₁ : AgreesExcept [.reg 6, .flags, .rip] current u := effect₁.agrees
  have state₁ := state.toFrameState.after_registers ready₁ frame₁
    (by simp [Component.Covers]) (by simp)
  have memory₁ : u.external = current.external := frame₁.external (by simp [Component.Covers])
  have rsp₁ : stackPtr u = stackPtr current := frame₁.read (n := 64) (r := 4) (by simp)
  have input₁ : u.regValue .rsi =
      initial.regValue .rsi + BitVec.ofNat 64 (128 * (index + 1)) := by
    have hw : u.regValue .rsi = current.regValue .rsi - (BitVec.ofNat 8 0x80).signExtend 64 := effect₁.writes
    have hconst : (BitVec.ofNat 8 0x80).signExtend 64 = (0xffffffffffffff80 : BitVec 64) := by decide +kernel
    rw [hw, state.inputPointer, hconst, BitVec.sub_eq_add_neg, Nat.mul_add, Nat.mul_one,
      BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  have end₁ : memLoad u.external (stackPtr u + 0xe8) 64 =
      initial.regValue .rsi + BitVec.ofNat 64 (128 * count) := by
    rw [memory₁, rsp₁]
    exact state.endPointer
  have readable₁ : MemReadable u (stackPtr u + 0xe8) 8 := by
    have haddr : stackPtr u + 0xe8 = stackPtr initial - 184 := by
      rw [state₁.rsp]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [haddr]
    exact Sha2.Proofs.Common.Encoding.Serialize.readable_of_grow
      (Sha2.Proofs.Common.Encoding.Serialize.stack_sub_readable pre.toCalleePre
        (by decide) (by decide)) state₁.allocated
  obtain ⟨v, run₂, ready₂, effect₂⟩ :=
    (cmp_r64_m64_effect_step 0x111806 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d32 0xe8)) (by decide +kernel) rfl rfl).advances ready₁
      (programText_slice (programLoaded_codeIn state₁.loaded) 0x11806
        [0x48,0x3b,0xb4,0x24,0xe8,0,0,0] (by decide) (by decide +kernel))
      ⟨effect₁.rip, readable₁⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1180e (by decide)))
  have frame₂ : AgreesExcept [.flags, .rip] u v := effect₂.agrees
  have state₂ := state₁.after_registers ready₂ frame₂ (by simp [Component.Covers]) (by simp)
  have zf : (StatusFlags.ofRFLAGS v.RFLAGS).ZF = decide (index + 1 = count) := by
    have hz := effect₂.flags.2.2.2.1
    change _ = ((u.regValue .rsi - memLoad u.external (stackPtr u + 0xe8) 64) == 0) at hz
    rw [input₁, end₁] at hz
    rw [hz]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
    rw [show (0 : BitVec 64) + (initial.regValue .rsi + BitVec.ofNat 64 (128 * count)) =
      initial.regValue .rsi + BitVec.ofNat 64 (128 * count) by exact BitVec.zero_add _]
    exact pre.inputPointer_eq_iff (index := index + 1) (by omega)
  have target : (jccEffect 0x11180e 6 5 ((0xffffc5dc : BitVec 32).signExtend 64) v).rip =
      (if index + 1 = count then 0x111814 else 0x10ddf0) := by
    by_cases he : index + 1 = count <;>
      simp [jccEffect, branchEffect, condHolds, branchTarget, zf, he]
  obtain ⟨next, run₃, ready₃, effect₃⟩ :=
    (jcc_rel32_effect_step 0x11180e 5 0xffffc5dc).advances ready₂
      (programText_slice (programLoaded_codeIn state₂.loaded) 0x1180e
        [0x0f,0x85,0xdc,0xc5,0xff,0xff] (by decide) (by decide +kernel))
      ⟨effect₂.rip, by intro _; decide +kernel⟩
      (by rw [target]; split
          · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x11814 (by decide))
          · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xddf0 (by decide)))
  have frame₃ : AgreesExcept [.rip] v next := effect₃.agrees
  have combined : AgreesExcept [.reg 6, .flags, .rip] current next :=
    ((frame₁.trans frame₂).trans frame₃).mono (by simp)
  have nextFrame := state.toFrameState.after_registers ready₃ combined
    (by simp [Component.Covers]) (by simp)
  have memory : next.external = current.external := combined.external (by simp [Component.Covers])
  have rsp : stackPtr next = stackPtr current := combined.read (n := 64) (r := 4) (by simp)
  refine ⟨next, (run₁.trans run₂).trans run₃, ?_, effect₃.rip.trans target⟩
  refine ⟨nextFrame, state.registers.after_control combined, ?_, ?_, ?_⟩
  · exact (frame₃.read (n := 64) (r := 6) (by simp)).trans
      ((frame₂.read (n := 64) (r := 6) (by simp)).trans input₁)
  · rw [memory, rsp]
    exact state.statePointer
  · rw [memory, rsp]
    exact state.endPointer

end Sha2.Proofs.Common.SHA512
