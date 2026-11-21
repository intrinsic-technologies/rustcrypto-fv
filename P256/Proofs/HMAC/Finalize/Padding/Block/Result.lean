import P256.Proofs.HMAC.Finalize.Padding.Bytes
import P256.Proofs.HMAC.Key.Output.Bytes
import P256.Proofs.HMAC.Interface
import P256.Proofs.HMAC.Finalize.Padding.Block.Machine
import P256.Proofs.HMAC.Finalize.Padding.Block.Length
import P256.Proofs.HMAC.Finalize.Padding.Memory
import P256.Proofs.SHA256.LengthEncoding
import P256.Proofs.HMAC.Finalize.Frame
import P256.Proofs.Program.CopyBytes

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Padding.Block

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common
open P256.Proofs.Common.Instructions
open P256.Proofs.Program (stack_bounds stack_sub_toNat)

theorem effect_components (p : BitVec 64) (r : BitVec 3) (q : UInt8) (s : RamState) :
    (effect p r q s).components =
      [.mem (rspOf s + 128) 8, .mem (rspOf s + 64) 8, .reg 0, .reg 1,
       .mem (rspOf s + 8) 8, .mem (rspOf s + 16) 8, .mem (rspOf s + 24) 8,
       .mem (rspOf s + 32) 8, .mem (rspOf s + 40) 8, .mem (rspOf s + 48) 8,
       .mem (rspOf s + 56) 8, .reg 6, .reg 2, .reg 7, .rip] := by simp [effect, Effect.components, Write.component, Operand.component]

theorem scratch_local [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (rsp : stackPtr s = stackPtr initial - 328#64)
    {offset len : Nat} {a : BitVec 64} (bound : offset + len ≤ 176)
    (covered : (Component.mem (stackPtr s + BitVec.ofNat 64 offset) len).Covers a) :
    (scratchRegion initial).Contains a.toNat := by
  rw [stack_address rsp (by omega : offset ≤ 328)] at covered
  exact scratch_contains pre (by omega) (by omega) covered

theorem effect_frame [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {p : BitVec 64} {r : BitVec 3} {q : UInt8}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : ScalarFrame.FrameState initial s 0 672 328)
    (ready : ReadyToStep t) (h : (effect p r q s).Holds s t) :
    ScalarFrame.FrameState initial t 0 672 328 ∧ MemoryWriteFrame s t #v[scratchRegion initial] := by
  have agrees := h.agrees
  rw [effect_components] at agrees
  constructor
  · apply state.after_effect (stackPre pre) (by decide) ready agrees ?_ (by simp)
    intro c hc a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact covered.elim
      | exact ⟨workRegion initial 672, by simp, local_work_contains pre state.rsp (by decide) covered⟩
  · apply agrees.memoryWriteFrame
    intro c hc a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact covered.elim
      | exact ⟨scratchRegion initial, by simp, scratch_local pre state.rsp (by decide) covered⟩

theorem hash_apart (base : BitVec 64) {offset i : Nat}
    (bound : offset + 8 ≤ 136) (hi : i < 32) :
    ¬ (Component.mem (base + BitVec.ofNat 64 offset) 8).Covers
      (base + 136 + BitVec.ofNat 64 i) := by
  rintro ⟨j, hj, eq⟩
  exact RangeApart.offsets base (a := offset) (b := 136) (len := 8) (count := 32)
    (by omega) (by decide) (.inl bound) j hj i hi eq.symm

theorem effect_hash {s t : RamState} {p : BitVec 64} {r : BitVec 3} {q : UInt8}
    (h : (effect p r q s).Holds s t) {hash : Array UInt32}
    (state : SHA256.HashStateAt s (rspOf s + 136) hash) :
    SHA256.HashStateAt t (rspOf s + 136) hash := by
  apply state.copy
  intro i hi
  apply h.agrees.byte
  intro c hc covered
  rw [effect_components] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact covered.elim | exact hash_apart _ (by decide) hi covered

theorem effect_words {s t : RamState} {p : BitVec 64} {r : BitVec 3} {q : UInt8}
    (h : (effect p r q s).Holds s t) :
    ∀ j < 7, memLoad t.external (rspOf s + 8 + BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (rspOf s + 72 + BitVec.ofNat 64 (8*j)) 64 := by
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read] at stores
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    BitVec.add_assoc, BitVec.reduceAdd]
  · simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat] using stores.2.2.2.2.1
  · simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat] using stores.2.2.2.2.2.1
  · simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat] using stores.2.2.2.2.2.2.1
  · simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat] using stores.2.2.2.2.2.2.2.1
  · simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat] using stores.2.2.2.2.2.2.2.2.1
  · simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat] using stores.2.2.2.2.2.2.2.2.2.1
  · simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat] using stores.2.2.2.2.2.2.2.2.2.2.1



def storeRegister (outer : Bool) : BitVec 3 := if outer then 4 else 5

def setupRegister (outer : Bool) : UInt8 := if outer then 0xf7 else 0xff

theorem result [Bindings] (outer : Bool)
    {initial s t : RamState} {boundary : ReturnBoundary} {message : ByteArray}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : Encoded initial s message outer) (ready : ReadyToStep t)
    (h : (effect (storeStart outer) (storeRegister outer) (setupRegister outer) s).Holds s t)
    (small : message.size % 64 < 56) :
    BlockReady initial t message ∧ MemoryWriteFrame s t #v[scratchRegion initial] := by
  obtain ⟨frame, memory⟩ := effect_frame pre state.toFrameState ready h
  have sourceAddress : rspOf s + 72 = stackPtr initial - 256#64 :=
    stack_address state.rsp (by decide : 72 ≤ 328)
  have targetAddress : rspOf s + 8 = stackPtr initial - 320#64 :=
    stack_address state.rsp (by decide : 8 ≤ 328)
  have hashAddress : rspOf s + 136 = stackPtr initial - 192#64 :=
    stack_address state.rsp (by decide : 136 ≤ 328)
  have copied : ∀ i < 56, t.external[rspOf s + 8 + BitVec.ofNat 64 i]? =
      s.external[rspOf s + 72 + BitVec.ofNat 64 i]? :=
    Key.Output.bytes_of_words (count := 7)
      (ScalarFrame.stack_readable (stackPre pre) state.toFrameState (by decide) (by decide))
      ((ScalarFrame.stack_readable (stackPre pre) state.toFrameState (offset := 8) (len := 56) (by decide) (by decide)).of_holds h)
      (effect_words h)
  have lengthWord : memLoad t.external (rspOf s + 64) 64 =
      bswap64 (BitVec.ofNat 64 (8 * message.size)) := by
    have written := h.writes.2.1
    change memLoad t.external (rspOf s + 64) 64 =
      (Operand.reg (gprNumber 0 1 (storeRegister outer)) : Operand 64).read s at written
    apply written.trans
    cases outer <;> exact state.length
  have prefixBytes := SHA256.hasBytes_prefix state.buffer
    (count := 56) (by change 56 ≤ 64; decide)
  rw [SHA256.paddedBuffer_prefix message small] at prefixBytes
  have prefixSize : (SHA256.finalPrefix message).size = 56 := prefixBytes.1
  have blockEq : SHA256.tailFirst message = SHA256.finalBlock message := by
    simp only [SHA256.tailFirst, SHA256.finalBlock, SHA256.finalPrefix, small, ite_true]
  refine ⟨⟨frame, ?_, ?_, ?_, ?_, ?_, ?_⟩, memory⟩
  · exact (h.agrees.read (n := 64) (r := 3) (by rw [effect_components]; simp)).trans state.outputPointer
  · have written := h.writes.2.2.2.2.2.2.2.2.2.2.2.1
    exact written.trans targetAddress
  · have written := h.writes.2.2.2.2.2.2.2.2.2.2.2.2.2
    cases outer <;> exact written.trans state.hashPointer
  · exact h.writes.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [blockEq]
    have blockSize := SHA256.finalBlock_size message
    refine ⟨blockSize, fun i => ?_⟩
    have hi : i.val < 64 := by have := i.isLt; omega
    have hi' : i.val < (SHA256.finalPrefix message ++ Standards.SECG.ECC.Encoding.natToOctets 8 (8 * message.size)).size := by
      simpa only [SHA256.finalBlock] using i.isLt
    change t.external[BitVec.ofNat 64 ((stackPtr initial - 320#64).toNat + i.val)]? =
      some ((SHA256.finalPrefix message ++ Standards.SECG.ECC.Encoding.natToOctets 8 (8 * message.size))[i.val]'hi')
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← targetAddress]
    by_cases low : i.val < 56
    · rw [ByteArray.getElem_append_left (by omega), copied i.val low, sourceAddress]
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        using prefixBytes.2 ⟨i.val, by omega⟩
    · rw [ByteArray.getElem_append_right (by omega)]
      have stored := Bytes.of_memLoad (n := 64)
        (((ScalarFrame.stack_readable (stackPre pre) state.toFrameState (offset := 64) (len := 8)
          (by decide) (by decide)).of_holds h).mem)
      change Bytes t.external (rspOf s + 64) 8
        (storedByte (memLoad t.external (rspOf s + 64) 64)) at stored
      rw [lengthWord] at stored
      have byte := stored (i.val - 56) (by omega)
      rw [SHA256.bswap64_ofNat_storedByte _ (by omega)] at byte
      have address : rspOf s + 8 + BitVec.ofNat 64 i.val =
          rspOf s + 64 + BitVec.ofNat 64 (i.val - 56) := by
        change rspOf s + BitVec.ofNat 64 8 + BitVec.ofNat 64 i.val =
          rspOf s + BitVec.ofNat 64 64 + BitVec.ofNat 64 (i.val - 56)
        rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
        congr 2
        omega
      rw [address]
      simpa only [prefixSize] using byte
  · rw [← hashAddress]
    exact effect_hash h (by simpa only [hashAddress] using state.hash)

end P256.Proofs.HMAC.Finalize.Padding.Block
