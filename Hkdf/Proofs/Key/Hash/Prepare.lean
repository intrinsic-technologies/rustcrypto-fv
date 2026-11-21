import Hkdf.Proofs.Key.Hash.State
import Hkdf.Proofs.Key.Memory
import Hkdf.Proofs.Key.Hash.Initialize
import Hkdf.Proofs.Common.Streaming

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Hash

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program
open Hkdf.Proofs.Common.Machine (supportedMachine_readyToStep)
open Hkdf.Proofs.Common.SHA256

private theorem full_length (n : BitVec 64) (bound : n.toNat < 2^61) :
    0x7fffffffffffffc0 &&& n = BitVec.ofNat 64 (64 * (n.toNat / 64)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have div := Nat.and_div_two_pow (a := 0x7fffffffffffffc0) (b := n.toNat) (n := 6)
  change (0x7fffffffffffffc0 &&& n.toNat) / 64 = (2^57-1) &&& (n.toNat/64) at div
  rw [Nat.and_comm (2^57-1) (n.toNat/64), Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)] at div
  have rem := Nat.and_mod_two_pow (a := 0x7fffffffffffffc0) (b := n.toNat) (n := 6)
  change (0x7fffffffffffffc0 &&& n.toNat) % 64 = 0 &&& (n.toNat%64) at rem
  simp only [Nat.zero_and] at rem
  change (0x7fffffffffffffc0 &&& n.toNat) = (64*(n.toNat/64)) % 2^64
  omega

private theorem tail_length (n : BitVec 64) :
    ((n.setWidth 32) &&& 63).setWidth 64 = BitVec.ofNat 64 (n.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_and]
  change (n.setWidth 32).toNat &&& (2^6-1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have mod := Nat.mod_mod_of_dvd n.toNat (show 64 ∣ 2^32 by decide)
  have bound := Nat.mod_lt n.toNat (by decide : 0 < 64)
  omega

private theorem block_count (n : BitVec 64) : n >>> 6 = BitVec.ofNat 64 (n.toNat / 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.reducePow, BitVec.toNat_ofNat]
  have := n.isLt
  omega

structure InitialBlocks [Bindings] (initial : RamState) (boundary : ReturnBoundary)
    (key : ByteArray) (s : RamState) : Prop extends Working initial boundary s where
  rip : s.RIP = 0x11640e
  hashPointer : s.regValue .rdi = blockAddress initial + 296
  hashWords : HashStateAt s (blockAddress initial + 296) Hkdf.Proofs.NIST.SHA256.initialHash
  inputPointer : s.regValue .rsi = initial.regValue .rsi
  countRegister : s.regValue .rdx = BitVec.ofNat 64 (key.size / 64)
  tailPointer : s.regValue .r14 =
    initial.regValue .rsi + BitVec.ofNat 64 (64 * (key.size / 64))
  tailLength : s.regValue .r15 = BitVec.ofNat 64 (key.size % 64)
  blocks : memLoad s.external (blockAddress initial + 328) 64 =
    BitVec.ofNat 64 (key.size / 64)

theorem initialize_pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key : ByteArray} (ctx : Context initial boundary key)
    (state : Prepared initial boundary s) (rip : s.RIP = 0x11638e) :
    Initialize.Pre s := by
  refine ⟨rip, ?_, ?_⟩
  · intro slot member
    rw [stack_address state.rsp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [BitVec.ofNat_eq_ofNat, BitVec.reduceSub]
    all_goals first
      | exact stack_writable8 ctx state.toState (by decide) (by decide)
      | exact stack_writable1 ctx state.toState (by decide)
  · intro slot member pc len lower upper
    rw [stack_address state.rsp]
    have address : BitVec.ofNat 64 pc =
        Extracted.textAddress + BitVec.ofNat 64 (pc - 0x100000) := by
      change BitVec.ofNat 64 pc = BitVec.ofNat 64 0x100000 + _
      rw [← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    rw [address]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [BitVec.ofNat_eq_ofNat, BitVec.reduceSub]
    all_goals exact stack_codeApart ctx (by decide) (by decide) (by omega)

theorem prepare [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key : ByteArray} (ctx : Context initial boundary key)
    (state : Prepared initial boundary s) (rip : s.RIP = 0x11638e) :
    ∃ t, InitialBlocks initial boundary key t := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Initialize.run boundary ctx.outerBoundary
    s (supportedMachine_readyToStep state.machine) (Initialize.code state.loaded)
    (initialize_pre ctx state rip)
  have writes : LocalWrites initial (Initialize.effect s).components := by
    intro c hc a ha
    simp only [Initialize.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals rw [stack_address state.rsp] at ha
    all_goals simp only [BitVec.ofNat_eq_ofNat, BitVec.reduceSub] at ha
    all_goals exact local_memory (by decide) (by decide) a ha
  have running := state.toRunning.of_agrees run ready effect.agrees (writes.within ctx)
    (by
      intro region member address contains inside
      exact ctx.avoids region (by simpa [writeRegions] using member)
        address contains (.inl inside))
    (by simp [Initialize.effect, Effect.components, Write.component, Operand.component])
  have sameSaved : (Component.mem (stackPtr initial - 40) 48).Agrees s t := by
    intro i hi
    exact effect.agrees.memory _ (fun c hc => writes.saved c hc _ ⟨i, hi, rfl⟩)
  have zero : (⟨(blockAddress initial).toNat, 64⟩ : MemoryRegion).HasBytes t.external
      ⟨Array.replicate 64 0⟩ := by
    refine ⟨state.zeroBlock.1, ?_⟩
    intro i
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    apply (effect.agrees.byte ?_).trans
    · simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        using state.zeroBlock.2 i
    · intro c hc cover
      simp only [Initialize.effect, Effect.components, List.map_cons, List.map_nil,
        Write.component, Operand.component, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact cover.elim
      all_goals rw [show rspOf s = blockAddress initial from state.rsp] at cover
      all_goals obtain ⟨j, hj, he⟩ := cover
      · exact OffsetsApart.ne (c₁ := 0) (len₁ := 64) (c₂ := 320) (len₂ := 8)
          (by unfold OffsetsApart; decide +kernel) (blockAddress initial) i.isLt hj (by decide)
          (by simpa using he)
      · exact OffsetsApart.ne (c₁ := 0) (len₁ := 64) (c₂ := 312) (len₂ := 8)
          (by unfold OffsetsApart; decide +kernel) (blockAddress initial) i.isLt hj (by decide)
          (by simpa using he)
      · exact OffsetsApart.ne (c₁ := 0) (len₁ := 64) (c₂ := 304) (len₂ := 8)
          (by unfold OffsetsApart; decide +kernel) (blockAddress initial) i.isLt hj (by decide)
          (by simpa using he)
      · exact OffsetsApart.ne (c₁ := 0) (len₁ := 64) (c₂ := 296) (len₂ := 8)
          (by unfold OffsetsApart; decide +kernel) (blockAddress initial) i.isLt hj (by decide)
          (by simpa using he)
      · exact OffsetsApart.ne (c₁ := 0) (len₁ := 64) (c₂ := 295) (len₂ := 1)
          (by unfold OffsetsApart; decide +kernel) (blockAddress initial) i.isLt hj (by decide)
          (by simpa using he)
      · exact OffsetsApart.ne (c₁ := 0) (len₁ := 64) (c₂ := 328) (len₂ := 8)
          (by unfold OffsetsApart; decide +kernel) (blockAddress initial) i.isLt hj (by decide)
          (by simpa using he)
  have working := (Prepared.working state).of_observations running sameSaved
    (effect.agrees.read (n := 64) (r := 4) (by
      simp [Initialize.effect, Effect.components, Write.component, Operand.component]))
    (effect.agrees.read (n := 64) (r := 3) (by
      simp [Initialize.effect, Effect.components, Write.component, Operand.component]))
    (effect.agrees.read (n := 64) (r := 5) (by
      simp [Initialize.effect, Effect.components, Write.component, Operand.component]))
    (effect.agrees.mxcsr (by simp [Initialize.effect, Effect.components]))
    (effect.agrees.fcw (by simp [Initialize.effect, Effect.components])) zero
  have length : (s.regValue .rdx).toNat = key.size := by
    rw [state.inputLength]
    exact ctx.length
  have small : key.size < 2 ^ 61 := by
    have bound := ctx.inputBounded
    change (initial.regValue .rsi).toNat + key.size < 2 ^ 32 at bound
    omega
  have count : s.regValue .rdx >>> 6 = BitVec.ofNat 64 (key.size / 64) := by
    rw [block_count, length]
  have stores := effect.writes
  simp only [Initialize.effect, Write.AllHold, Operand.read] at stores
  refine ⟨t, working, effect.rip, ?_, ?_, ?_, stores.2.2.2.2.2.2.2.2.1.trans count,
    ?_, ?_, ?_⟩
  · have pointer : t.regValue .rdi = rspOf s + 296 := effect.writes.1
    simpa only [show rspOf s = blockAddress initial from state.rsp] using pointer
  · have hash := Initialize.hash_words effect (by
      rw [stack_address state.rsp]
      exact stack_readable ctx working.toState (offset := 80) (len := 32) (by decide) (by decide))
    simpa only [show rspOf s = blockAddress initial from state.rsp] using hash
  · exact (effect.agrees.read (n := 64) (r := 6) (by
      simp [Initialize.effect, Effect.components, Write.component, Operand.component])).trans
        state.inputPointer
  · have pointer := stores.2.2.2.2.2.2.2.1
    rw [full_length _ (by rw [length]; exact small),
      length, state.inputPointer, BitVec.add_comm] at pointer
    exact pointer
  · exact stores.2.2.2.2.2.2.2.2.2.2.trans (by
      rw [tail_length, length])
  · have blocks := Initialize.count_word effect
    rw [show rspOf s = blockAddress initial from state.rsp, count] at blocks
    exact blocks

end Hkdf.Proofs.Key.Hash
