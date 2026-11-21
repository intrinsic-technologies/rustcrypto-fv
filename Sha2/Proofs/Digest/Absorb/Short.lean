import Sha2.Proofs.Digest.Absorb.Execution
import Sha2.Proofs.Digest.Absorb.Memory
import Sha2.Proofs.Wrapper512.Absorb.Copy
import Sha2.Proofs.Wrapper512.Absorb.Mathematics
import Sha2.Proofs.Common.Machine.MemoryFrame

set_option autoImplicit false

namespace Sha2.Proofs.Digest.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine
  X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper512 Sha2.Proofs.Common.SHA512

 theorem short [Bindings] {v : Variant} {initial s : RamState} {data : ByteArray}
    (ctx : Context v initial #[⟨initial.regValue .rdi, data⟩] .digest)
    (input : Buffered v initial s ByteArray.empty .digest)
    (rip : s.RIP = v.pc 0xd0 .digest) (small : data.size < 128)
    (source : s.regValue .rsi = initial.regValue .rdi)
    (length : s.regValue .r14 = BitVec.ofNat 64 data.size) :
    ∃ t, Buffered v initial t data .digest ∧ t.RIP = v.pc 0x143 .digest := by
  obtain ⟨b,preservedB,setup⟩ := copy_setup ctx input.toPreserved false rip
  have memoryB : b.external = s.external := setup.agrees.external
    (by simp [CopySetup.effect, Effect.components, Write.component, Operand.component, Component.Covers])
  have regs : b.regValue .rdi = rspOf s + 208 ∧ b.regValue .rdx = s.regValue .r14 := setup.writes
  have addr : rspOf s + 208 = stackPtr initial - 392#64 := by
    change stackPtr s + 208 = _
    rw [input.rsp]
    simp only [Form.frameBytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have sourceB : b.regValue .rsi = initial.regValue .rdi :=
    (setup.agrees.read (n := 64) (r := 6)
      (by simp [CopySetup.effect, Effect.components, Write.component, Operand.component])).trans source
  have lengthB : b.regValue .r14 = BitVec.ofNat 64 data.size :=
    (setup.agrees.read (n := 64) (r := 14)
      (by simp [CopySetup.effect, Effect.components, Write.component, Operand.component])).trans length
  have ripB : b.RIP = v.pc 0xdb .digest := setup.rip.trans (Variant.pc_add v 0xd0 11 .digest)
  obtain ⟨c,copied⟩ := Wrapper512.Absorb.Copy.copy ctx preservedB .short
    (⟨0, by simp⟩ : Fin (#[⟨initial.regValue .rdi,data⟩] : Array Input).size)
    (offset := 0) (position := 0) (count := data.size) (by simp) (by simp; omega)
    ripB (by simpa using regs.1.trans addr)
    (by simpa using sourceB) (regs.2.trans length)
  have ripC : c.RIP = v.pc 0xe1 .digest := copied.rip.trans (Variant.pc_add v 0xdb 6 .digest)
  have lengthC : c.regValue .r14 = BitVec.ofNat 64 data.size :=
    (copied.abi.1 .r14 (by simp)).trans lengthB
  obtain ⟨t,preservedT,stored⟩ := tail_length ctx copied.preserved true ripC
  have addrC : rspOf c + 335 = stackPtr initial - 265#64 := by
    change stackPtr c + 335 = _
    rw [copied.preserved.rsp]
    simp only [Form.frameBytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have frameT : AgreesExcept [.mem (stackPtr initial - 265#64) 1,.rip] c t := by
    simpa only [TailLength.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, Nat.reduceDiv, List.cons_append, List.nil_append,
      addrC] using stored.agrees
  have kept (offset len : Nat)
      (apart : OffsetsApart (-265) 1 (-(BitVec.ofNat 64 offset)) len)
      (bound : 1 + len < 2^64) :
      ∀ j < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 j]? =
        c.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 j]? :=
    bytes_of_mem_frame frameT (by simp [Component.Covers]) apart bound
  have hashT : HashStateAt t (hashPointer initial .digest) v.initialHash := by
    apply Wrapper512.Absorb.hashState_of_bytes (s := s) (a := hashPointer initial .digest)
      (by simpa only [compressBlocks, ByteArray.size_empty, Nat.zero_div, compressBlocksFrom]
        using input.hashWords)
    intro j hj
    exact (kept 264 64 (by unfold OffsetsApart; decide +kernel) (by decide) j hj).trans
      (copied.bytes_unchanged ctx (by simp; omega) (offset := 264) (len := 64)
        (by decide) (by decide) (Or.inr (by change 264 + data.size ≤ 392; omega)) j hj |>.trans
        (by simp [memoryB, hashPointer]))
  have counters (offset : Nat) (lo : 192 ≤ offset) (hi : offset ≤ 200)
      (apart : OffsetsApart (-265) 1 (-(BitVec.ofNat 64 offset)) 8) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    rw [← memoryB]
    apply memLoad_congr
    intro j hj
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      ((kept offset 8 apart (by decide) j hj).trans
        (copied.bytes_unchanged ctx (by simp; omega) (offset := offset) (len := 8)
          (by change offset ≤ 600; omega) (by omega)
          (Or.inr (by change offset + data.size ≤ 392; omega)) j hj))
  have tail : (⟨(stackPtr initial - 392#64).toNat,data.size⟩ : MemoryRegion).HasBytes t.external data := by
    have bytes : (⟨(stackPtr initial - 392#64).toNat,data.size⟩ : MemoryRegion).HasBytes c.external data := by
      simpa using copied.bytes
    refine ⟨rfl, fun j => ?_⟩
    have eq := kept 392 data.size
      (by change 1 ≤ 18446744073709551489 ∧ data.size ≤ 127; omega)
      (by omega) j.val j.isLt
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      using eq.trans (by simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using bytes.2 j)
  have tailLength : t.external[stackPtr initial - 265#64]? = some (UInt8.ofNat data.size) := by
    have value : memLoad t.external (rspOf c + 335) 8 = (c.regValue .r14).setWidth 8 := stored.writes
    rw [addrC,lengthC] at value
    have read := stack_frame_readable ctx.stack (frame := 600) (offset := 335) (len := 1)
      (s := t) (by change 600 ≤ 1152; decide) preservedT.allocated (by decide)
    have read' : MemReadable t (stackPtr initial - 265#64) 1 := by
      simpa only [stack_frame_address initial (frame := 600) (offset := 335) (by decide), Nat.reduceSub] using read
    have byte := Bytes.of_memLoad (n := 8) read'.mem 0 (by decide)
    rw [value] at byte
    simpa only [BitVec.add_zero, storedByte, Nat.mul_zero, Nat.shiftRight_zero,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : data.size < 2^64),
      Nat.mod_eq_of_lt (by omega : data.size < 2^8)] using byte
  refine ⟨t, ⟨preservedT, ?_, ?_, ?_, ?_, ?_⟩,
    stored.rip.trans (Variant.pc_add v 0xe1 98 .digest)⟩
  · rw [Wrapper512.Absorb.compressBlocks_short _ _ small]
    exact hashT
  · simpa only [tailRegion, bufferPointer, bufferOffset, tailData,
      Nat.mod_eq_of_lt small, Nat.div_eq_of_lt small, Nat.mul_zero, ByteArray.extract_zero_size] using tail
  · simpa only [tailLengthPointer, tailLengthOffset, Nat.mod_eq_of_lt small] using tailLength
  · simpa only [blockCountPointer, blockCountOffset, blockCountHighPointer, blockCountHighOffset, ByteArray.size_empty, Nat.zero_div, Nat.div_eq_of_lt small] using
      (counters 200 (by decide) (by decide) (by unfold OffsetsApart; decide +kernel)).trans input.blockCount
  · simpa only [blockCountPointer, blockCountOffset, blockCountHighPointer, blockCountHighOffset, ByteArray.size_empty, Nat.zero_div, Nat.div_eq_of_lt small] using
      (counters 192 (by decide) (by decide) (by unfold OffsetsApart; decide +kernel)).trans input.blockCountHigh

end Sha2.Proofs.Digest.Absorb
