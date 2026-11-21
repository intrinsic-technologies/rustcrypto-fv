import P256.Proofs.Nonce.Update.Absorb.SeedMemory
import P256.Proofs.Nonce.UpdateValue.Copy

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem seed_callee_pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original : State} {address : BitVec 64} {bytes : ByteArray}
    {offset count outputOffset : Nat}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (frame : ScalarFrame.FrameState initial s 64 1856 688)
    (seed : UpdateSeedAt initial address bytes) (span : offset + count ≤ bytes.size)
    (outputAbove : outputOffset ≤ 680) (outputEnd : count + 48 ≤ outputOffset)
    (input : s.regValue .rsi = address + BitVec.ofNat 64 offset)
    (output : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (rip : s.RIP = 0x11c930) (ret : InProgram (returnBoundary s).rip) :
    CalleePre s boundary 0x11c930 count count 0 := by
  have bounds := stack_bounds pre.stack
  have hsp : (stackPtr s).toNat = (stackPtr initial).toNat - 688 := by
    rw [frame.rsp]
    exact stack_sub_toNat pre.stack (offset := 688) (by decide)
  have hout : (s.regValue .rdi).toNat = (stackPtr initial).toNat - outputOffset := by
    rw [output, stack_sub_toNat pre.stack (by omega)]
  have hin : (s.regValue .rsi).toNat = address.toNat + offset := by
    rw [input, seed_offset_toNat seed (by omega)]
  have sourceLow : address.toNat + bytes.size < 2^32 := seed.bounded
  have stackSub : ∀ a, (Stack.region s 0).Contains a → (Stack.region initial 1856).Contains a := by
    intro a ha
    change (stackPtr s).toNat - 0 ≤ a ∧ a < (Stack.region s 0).start + (Stack.region s 0).size at ha
    rw [stack_region_end, hsp] at ha
    change (stackPtr initial).toNat - 1856 ≤ a ∧
      a < (Stack.region initial 1856).start + (Stack.region initial 1856).size
    rw [stack_region_end]
    constructor <;> omega
  have outputSub : ∀ a, (registerRegion s .rdi count).Contains a → (Stack.region initial 1856).Contains a := by
    intro a ha
    change (MemoryRegion.mk (s.regValue .rdi).toNat count).Contains a at ha
    rw [output] at ha
    exact by
      have bounds := stack_bounds pre.stack
      change (stackPtr initial - BitVec.ofNat 64 outputOffset).toNat ≤ a ∧ a < (stackPtr initial - BitVec.ofNat 64 outputOffset).toNat + count at ha
      rw [stack_sub_toNat pre.stack (by omega)] at ha
      change (stackPtr initial).toNat - 1856 ≤ a ∧ a < (Stack.region initial 1856).start + (Stack.region initial 1856).size
      rw [stack_region_end]
      constructor <;> omega
  have inputSub : ∀ a, (registerRegion s .rsi count).Contains a →
      (MemoryRegion.mk address.toNat bytes.size).Contains a := by
    intro a ha
    change (MemoryRegion.mk (s.regValue .rsi).toNat count).Contains a at ha
    rw [input] at ha
    exact seed_subregion seed span ha
  have allocated (region : MemoryRegion)
      (sub : ∀ a, region.Contains a → (Stack.region initial 1856).Contains a) :
      region.Allocated s.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (frame.allocated a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (sub a.toNat ha))))
  refine {
    bindingsSupported := frame.bindingsSupported
    machine := frame.machine
    directionFlag := frame.directionFlag
    loaded := frame.loaded
    rip := rip
    inputBounded := ?_
    inputAllocated := ?_
    outputBounded := ?_
    outputAllocated := allocated _ outputSub
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := pre.outerBoundary
    returnInProgram := ret }
  · change (s.regValue .rsi).toNat + count < 2^32
    rw [hin]
    omega
  · intro a ha
    exact Option.isSome_iff_exists.mp (frame.allocated a
      (Option.isSome_iff_exists.mpr (seed.allocated a (inputSub a.toNat ha))))
  · change (s.regValue .rdi).toNat + count < 2^32
    rw [hout]
    omega
  · refine ⟨?_, allocated _ stackSub, Nat.zero_le _, ?_⟩
    · change (Stack.region s 0).start + (Stack.region s 0).size < 2^32
      rw [stack_region_end, hsp]
      omega
    · change (stackPtr s).toNat % 16 = 8
      rw [hsp]
      have align : (stackPtr initial).toNat % 16 = 8 := pre.stack.2.2.2
      omega
  · intro i j hij
    have pairs : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases pairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro a ha hb
      exact seed.stackApart a (inputSub a ha) (outputSub a hb)
    · intro a ha hb
      exact seed.stackApart a (inputSub a ha) (stackSub a hb)
    · intro a ha hb
      change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + count at ha
      change (stackPtr s).toNat - 0 ≤ a ∧ a < (Stack.region s 0).start + (Stack.region s 0).size at hb
      rw [hout] at ha
      rw [stack_region_end, hsp] at hb
      omega
  · intro region member a inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact pre.avoids _ (by simp) a (outputSub a.toNat inside)
    · exact pre.avoids _ (by simp) a (stackSub a.toNat inside)

end P256.Proofs.Nonce.Update.Absorb
