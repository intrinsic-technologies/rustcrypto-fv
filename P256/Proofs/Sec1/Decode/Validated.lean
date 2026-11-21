import P256.Proofs.Sec1.Decode.Header.Model
import P256.Proofs.Sec1.Decode.Failure
import P256.Proofs.Program.ScalarFrame.Input
import P256.Proofs.Common.Memory.LoadByte

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ValidatedEntry [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (bytes : ByteArray) : Prop extends Frame initial s where
  execution : ∃ fuel, Advances boundary fuel initial s
  rip : s.RIP = 0x10e522
  output : s.regValue .rdi = initial.regValue .rdi
  source : s.regValue .rsi = initial.regValue .rsi
  length : s.regValue .rdx = BitVec.ofNat 64 bytes.size
  shape : EncodingShape bytes

theorem validate_positive [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : DecodePre s boundary bytes) (positive : 0 < bytes.size) :
    (∃ t, CalleeResult s t boundary 80 3680 ∧
      PublicKeyResultAt t (s.regValue .rdi) (P256.Spec.Points.decodePublicKey bytes)) ∨
    (∃ t, ValidatedEntry s t boundary bytes) := by
  have bound32 : (s.regValue .rsi).toNat + bytes.size < 2^32 := pre.inputBounded
  have bound : bytes.size < 2^64 := by omega
  obtain ⟨a, entry⟩ := prologue pre
  have sa := entry.frame pre
  obtain ⟨b, ab, rb, ib, gb⟩ := length_branch entry.ready entry.loaded pre.outerBoundary entry.rip
  have sb := sa.after_registers pre rb gb (by simp [Component.Covers]) (by simp)
  have total := entry.agrees.trans gb
  have source : b.regValue .rsi = s.regValue .rsi :=
    total.read (n := 64) (r := 6) (by simp [saveComponents, savedRegisters, pushSequenceFrame])
  have output : b.regValue .rdi = s.regValue .rdi :=
    total.read (n := 64) (r := 7) (by simp [saveComponents, savedRegisters, pushSequenceFrame])
  have lengthA : a.regValue .rdx = BitVec.ofNat 64 bytes.size :=
    (entry.agrees.read (n := 64) (r := 2)
      (by simp [saveComponents, savedRegisters, pushSequenceFrame])).trans pre.length
  have lengthB : b.regValue .rdx = BitVec.ofNat 64 bytes.size :=
    (gb.read (n := 64) (r := 2) (by simp)).trans lengthA
  have nonzero : a.regValue .rdx ≠ 0 := by
    rw [lengthA]
    intro h
    have hn := congrArg BitVec.toNat h
    change bytes.size % 2^64 = 0 at hn
    rw [Nat.mod_eq_of_lt bound] at hn
    omega
  have bytesB := ScalarFrame.input_bytes_of_frame pre.toCalleePre sb.frame pre.input
  have first : b.external[s.regValue .rsi]? = some (bytes.data[0]?.getD 0) := by
    have h := bytesB.2 ⟨0, positive⟩
    simpa only [registerRegion, MemoryRegion.start, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Array.getElem?_eq_getElem positive, Option.getD_some, ByteArray.getElem_eq_getElem_data] using h
  have readable : MemReadable b (b.regValue .rsi) 1 := by
    rw [source]
    exact readable_of_grow (memoryRegion_memReadable pre.inputBounded pre.inputAllocated
      (Nat.le_refl _) (by change (s.regValue .rsi).toNat + 1 ≤ (s.regValue .rsi).toNat + bytes.size; omega)) sb.allocated
  have load : memLoad b.external (b.regValue .rsi) 8 = (bytes.data[0]?.getD 0).toBitVec := by
    rw [source]
    exact P256.Proofs.Common.Memory.memLoad8_of_byte first
  obtain ⟨c, bc, rc, ic, _, gc⟩ := header rb sb.loaded pre.outerBoundary
    (by simpa only [nonzero, ite_false] using ib) readable
  have sc := sb.after_registers pre rc gc (by simp [Component.Covers]) (by simp)
  have outC : c.regValue .rdi = s.regValue .rdi :=
    (gc.read (n := 64) (r := 7) (by simp)).trans output
  have run : ∃ fuel, Advances boundary fuel s c := ⟨_, (entry.execution.trans ab).trans bc⟩
  rw [load, lengthB] at ic
  by_cases accepted : Header.accepts (bytes.data[0]?.getD 0).toBitVec
      (BitVec.ofNat 64 bytes.size) = true
  · exact .inr ⟨c, ⟨sc, run, by simpa only [accepted, ite_true] using ic, outC,
      (gc.read (n := 64) (r := 6) (by simp)).trans source,
      (gc.read (n := 64) (r := 2) (by simp)).trans lengthB,
      (Header.accepts_shape positive bound).mp accepted⟩⟩
  · obtain ⟨t, result, tag⟩ := failure pre sc (by simpa only [accepted, Bool.false_eq_true, ite_false] using ic) outC run
    refine .inl ⟨t, result, ?_⟩
    have shape : ¬ EncodingShape bytes := fun h ↦ accepted ((Header.accepts_shape positive bound).mpr h)
    simpa only [P256.Spec.Points.decodePublicKey, decodePoint_invalid_shape shape] using tag

end P256.Proofs.Sec1.Decode
