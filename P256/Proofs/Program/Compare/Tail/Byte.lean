import P256.Proofs.Program.Compare.Execution
import P256.Proofs.Program.Compare.Model
import P256.Proofs.Program.Compare.Instructions.TestByte
import P256.Proofs.Program.Compare.Instructions.CmpByte
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

namespace P256.Proofs.Program.Compare.Tail

open X86 X86.Machine X86.UserProcess X86Proofs

private theorem movzxByte_local (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    Effect.Local (movzxR32M8Effect p len dst am) := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ _ h ↦ congrArg some h, fun _ ↦ ?_⟩
  · simp only [movzxR32M8Effect, AddrMode.addr_obs h, h.read_mem]
  · simp [movzxR32M8Effect, Write.Full, Operand.Full]

private theorem cmpByte_local (p : BitVec 64) (len : Nat) (dst src : BitVec 5) :
    Effect.Local (cmpR8R8Effect p len dst src) := by
  refine ⟨fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl,
    fun s t h i _ ↦ ?_, fun _ ↦ by simp [cmpR8R8Effect]⟩
  simp only [cmpR8R8Effect, Effect.flag, h.read_reg]

attribute [local x86_local] movzxByte_local cmpByte_local
attribute [local x86_compose] movzxR32M8Effect cmpR8R8Effect BitVec.add_zero

def lastBitEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 3
    flags := some (testFlags ((Operand.reg 1 : Operand 8).read s &&& 1)) }

theorem test_last_bit_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0xf6, 0xc1, 0x01])
      (lastBitEffect p) := by
  rintro s h hc rfl
  refine ⟨_, Instructions.test_r8_imm8_low_step s h 0xc1 1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hc.bytesAt
    (hc.low (by simp) (by simp)), ReadyToStep.afterStep_writeFlagsOutputs h 3 _ 1 _,
    ⟨afterStep_writeFlagsOutputs_rip h 3 _ 1 _, trivial,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 3 _ 1 _⟩⟩
  exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

private theorem lastBitEffect_local (p : BitVec 64) : Effect.Local (lastBitEffect p) := by
  refine ⟨fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl,
    fun s t h i _ ↦ ?_, fun _ ↦ by simp [lastBitEffect]⟩
  simp only [lastBitEffect, Effect.flag, h.read_reg]

attribute [local x86_local] lastBitEffect_local
attribute [local x86_compose] lastBitEffect

def bytePrepareEffect (s : RamState) : Effect :=
  { rip := 0x11cdf5
    writes := [⟨(Operand.reg 0 : Operand 64), 0⟩]
    flags := some (testFlags ((Operand.reg 1 : Operand 8).read s &&& 1)) }

theorem byte_prepare [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cdf0)
      (codeRange 0x11cdf0 [0x31, 0xc0, 0xf6, 0xc1, 0x01]) bytePrepareEffect := by
  p256_memcmp_run_begin xor_r32_r32_effect_step 0x11cdf0 0xc0 (by decide)
  p256_memcmp_run_then test_last_bit_step 0x11cdf2
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cdf0)
      (all := [0x31, 0xc0, 0xf6, 0xc1, 0x01]) 2 (by decide +kernel)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [bytePrepareEffect]
  · x86_norm [bytePrepareEffect]
    simp [Operand.read, gprNumber, modrmReg, modrmRm]
  · intro i; cases i <;> x86_norm [bytePrepareEffect]
  · x86_norm [bytePrepareEffect]

def lastByteLeft (s : RamState) : BitVec 8 :=
  (Operand.mem ((Operand.reg 6 : Operand 64).read s) : Operand 8).read s

def lastByteRight (s : RamState) : BitVec 8 :=
  (Operand.mem ((Operand.reg 2 : Operand 64).read s) : Operand 8).read s

structure ByteComparePre (s : RamState) : Prop where
  rip : s.RIP = 0x11cdfb
  left : MemReadable s ((Operand.reg 6 : Operand 64).read s) 1
  right : MemReadable s ((Operand.reg 2 : Operand 64).read s) 1

def byteCompareBytes : List UInt8 := [0x0f, 0xb6, 0x0e, 0x0f, 0xb6, 0x12, 0x38, 0xd1]

def byteCompareEffect (s : RamState) : Effect :=
  { rip := 0x11ce03
    writes := [⟨(Operand.reg 1 : Operand 64), (lastByteLeft s).setWidth 64⟩,
      ⟨(Operand.reg 2 : Operand 64), (lastByteRight s).setWidth 64⟩]
    flags := some (.ofStatusFlags (cmpSpec (lastByteLeft s) (lastByteRight s))) }

set_option maxRecDepth 2048 in
theorem byte_compare [Bindings] :
    RegisterBlock ByteComparePre (codeRange 0x11cdfb byteCompareBytes) byteCompareEffect := by
  unfold byteCompareBytes
  p256_memcmp_run_begin movzx_r32_m8_effect_step 0x11cdfb 1 (.base 6 .none)
    (by decide) (by decide) (by decide)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    exact hP.left
  p256_memcmp_run_then movzx_r32_m8_effect_step 0x11cdfe 2 (.base 2 .none)
    (by decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cdfb) (all := byteCompareBytes) 3 (by decide +kernel)
  try (case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact hP.right
    · x86_avoid)
  p256_memcmp_run_then cmp_r8_r8_effect_step 0x11ce01 0xd1
    (by decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cdfb) (all := byteCompareBytes) 6 (by decide +kernel)
  p256_memcmp_run_finish [byteCompareEffect, lastByteLeft, lastByteRight,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

theorem byte_compare_zero_iff [Bindings] {s t : RamState}
    (h : (byteCompareEffect s).Holds s t) :
    (StatusFlags.ofRFLAGS t.RFLAGS).ZF = true ↔
      BytesEqual s ((Operand.reg 6 : Operand 64).read s)
        ((Operand.reg 2 : Operand 64).read s) 1 := by
  have hz := h.flags.2.2.2.1
  change (StatusFlags.ofRFLAGS t.RFLAGS).ZF = ((lastByteLeft s - lastByteRight s) == 0) at hz
  rw [hz, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
  simpa [lastByteLeft, lastByteRight] using bytesEqual_iff_load.symm

def byteDifferenceEffect (s : RamState) : Effect :=
  let difference := (Operand.reg 1 : Operand 32).read s - (Operand.reg 2 : Operand 32).read s
  { rip := 0x11ce0d
    writes := [⟨(Operand.reg 1 : Operand 64), difference.setWidth 64⟩,
      ⟨(Operand.reg 0 : Operand 64), difference.setWidth 64⟩]
    flags := some (.ofStatusFlags (subSpec ((Operand.reg 1 : Operand 32).read s)
      ((Operand.reg 2 : Operand 32).read s)).2) }

attribute [local x86_compose] subR32R32Effect

theorem byte_difference [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11ce09)
      (codeRange 0x11ce09 [0x29, 0xd1, 0x89, 0xc8]) byteDifferenceEffect := by
  p256_memcmp_run_begin sub_r32_r32_effect_step 0x11ce09 0xd1 (by decide)
  p256_memcmp_run_then mov_r32_r32_effect_step 0x11ce0b 0xc8 (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11ce09) (all := [0x29, 0xd1, 0x89, 0xc8]) 2
      (by decide +kernel)
  apply RegisterBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [byteDifferenceEffect]
  · x86_norm [byteDifferenceEffect]
    simp [Operand.read, gprNumber, modrmReg, modrmRm]
  · intro i; cases i <;> x86_norm [byteDifferenceEffect]
    all_goals simp [Operand.read, gprNumber, modrmReg, modrmRm]
  · x86_norm [byteDifferenceEffect]

theorem byte_difference_zero_iff [Bindings] {s t : RamState}
    (h : (byteDifferenceEffect s).Holds s t) :
    (Operand.reg 0 : Operand 32).read t = 0 ↔
      (Operand.reg 1 : Operand 32).read s = (Operand.reg 2 : Operand 32).read s := by
  have hw := h.writes.2
  change (Operand.reg 0 : Operand 64).read t =
    ((Operand.reg 1 : Operand 32).read s - (Operand.reg 2 : Operand 32).read s).setWidth 64 at hw
  have hl : (Operand.reg 0 : Operand 32).read t =
      (Operand.reg 1 : Operand 32).read s - (Operand.reg 2 : Operand 32).read s := by
    simpa [Operand.read] using congrArg (BitVec.setWidth 32) hw
  rw [hl, BitVec.sub_eq_iff_eq_add]
  simp

end P256.Proofs.Program.Compare.Tail
