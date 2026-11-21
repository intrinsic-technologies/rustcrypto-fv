import Md5.Proofs.Buffered.Update.Calls
import Md5.Proofs.Buffered.Stack
import Md5.Proofs.Block.Subroutine
import Md5.Proofs.Block.Bytes
import Md5.Proofs.MemoryRoutines.Ranges

namespace Md5.Proofs.Buffered.FinalizeReset.CompressCall

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def scratchRegion (s : RamState) : MemoryRegion := ⟨(stackPtr s).toNat - 320, 320⟩

structure Pre (buffer : Standards.RFC.MD5.Buffer) (input : ByteArray) (s : RamState) : Prop where
  inputInMemory : Call.Compress.ValidInput s input
  bufferInMemory : Call.Compress.ValidBuffer s buffer
  stackLow : 320 ≤ (stackPtr s).toNat
  stackHigh : (stackPtr s).toNat < userAddressLimit
  stackAligned : (stackPtr s).toNat % 16 = 0
  scratch : MemoryRoutines.WritableRange s (stackPtr s - 320) 320
  inputScratch : (Compress.inputRegion s input).Disjoint (scratchRegion s)
  bufferScratch : (Compress.outputRegion s).Disjoint (scratchRegion s)
  inputBuffer : (Compress.inputRegion s input).Disjoint (Compress.outputRegion s)
  bufferAvoids : (Compress.outputRegion s).Avoids
    (fun address ↦ InProgram address ∨ InPageTables address)

theorem Pre.scratchAddress {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray} {s : RamState}
    (h : Pre buffer input s) : (stackPtr s - 320).toNat = (stackPtr s).toNat - 320 := by
  rw [BitVec.toNat_sub_of_le]
  · rfl
  · exact h.stackLow

theorem Pre.scratchBounded {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray} {s : RamState}
    (h : Pre buffer input s) : (scratchRegion s).Bounded := by
  change (stackPtr s).toNat - 320 + 320 < userAddressLimit
  have := h.stackLow
  have := h.stackHigh
  omega

theorem Pre.scratchIndex {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray} {s : RamState}
    (h : Pre buffer input s) {address : BitVec 64}
    (ha : (scratchRegion s).Contains address.toNat) :
    ∃ i < 320, address = stackPtr s - 320 + BitVec.ofNat 64 i := by
  change (stackPtr s).toNat - 320 ≤ address.toNat ∧
    address.toNat < (stackPtr s).toNat - 320 + 320 at ha
  refine ⟨address.toNat - ((stackPtr s).toNat - 320), by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, h.scratchAddress, BitVec.toNat_ofNat]
  have := address.isLt
  omega

theorem Pre.scratchAllocated {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray} {s : RamState}
    (h : Pre buffer input s) : (scratchRegion s).Allocated s.external := by
  intro address ha
  obtain ⟨i, hi, rfl⟩ := h.scratchIndex ha
  exact Option.isSome_iff_exists.mp (h.scratch.readable.mem i hi)

theorem Pre.scratchAvoids {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray} {s : RamState}
    (h : Pre buffer input s) :
    (scratchRegion s).Avoids (fun address ↦ InProgram address ∨ InPageTables address) := by
  intro address ha
  obtain ⟨i, hi, rfl⟩ := h.scratchIndex ha
  exact fun hp ↦ hp.elim (h.scratch.code i hi) (h.scratch.tables i hi)

theorem Pre.pushAddress {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray} {s : RamState}
    (_h : Pre buffer input s) : pushAddr s = stackPtr s - 320 + 312 := by
  change stackPtr s - 8 = stackPtr s - 320 + 312
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rfl

theorem Pre.pushCover {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray} {s : RamState}
    (h : Pre buffer input s) {address : BitVec 64}
    (ha : Component.Covers (.mem (pushAddr s) 8) address) :
    (scratchRegion s).Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := ha
  rw [h.pushAddress, BitVec.add_assoc]
  apply Block.contains_of_mem_covers h.scratchBounded
  have hs : BitVec.ofNat 64 (scratchRegion s).start = stackPtr s - 320 := by
    have hh : BitVec.ofNat 64 (stackPtr s - 320).toNat = stackPtr s - 320 := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [h.scratchAddress] at hh
    exact hh
  change ∃ j < 320, _ = BitVec.ofNat 64 (scratchRegion s).start + BitVec.ofNat 64 j
  exact ⟨312 + i, by omega, by rw [hs, BitVec.ofNat_add]; rfl⟩

theorem Pre.pushWritable {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray} {s : RamState}
    (h : Pre buffer input s) : Memory.MemWritable s (pushAddr s) 8 := by
  rw [h.pushAddress]
  have hw := h.scratch.slice 312 8 (by decide)
  exact ⟨hw.readable.low, hw.readable.mem, hw.tables⟩

theorem Pre.pushCode {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray} {s : RamState}
    (h : Pre buffer input s) : ∀ i < 8, ¬ InProgram (pushAddr s + BitVec.ofNat 64 i) := by
  intro i hi hp
  exact h.scratchAvoids _ (h.pushCover ⟨i, hi, rfl⟩) (.inl hp)

theorem Pre.callFrame {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    {s u : RamState} {target : RamState → BitVec 64} {ret : BitVec 64}
    (h : Pre buffer input s) (he : (callEffect target ret s).Holds s u) :
    MemoryWriteFrame s u #v[scratchRegion s] := by
  apply he.agrees.memoryWriteFrame
  intro c hc address ha
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ha.elim
  · exact ⟨scratchRegion s, by simp, h.pushCover ha⟩
  · exact ha.elim

set_option maxRecDepth 2048 in
theorem Pre.calleeStackRegion {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    {s u : RamState} {target : RamState → BitVec 64} {ret : BitVec 64}
    (h : Pre buffer input s) (he : (callEffect target ret s).Holds s u) :
    Prelude.Stack.region u Compress.minStackBytes = scratchRegion s := by
  have hsp : (stackPtr u).toNat = (stackPtr s).toNat - 8 := by
    rw [callEffect_rsp he]
    exact BitVec.toNat_sub_of_le (by change 8 ≤ (stackPtr s).toNat; have := h.stackLow; omega)
  rw [show Compress.minStackBytes = 312 by decide +kernel]
  change (⟨(stackPtr u).toNat - 312,
    (stackPtr u).toNat + 8 - ((stackPtr u).toNat - 312)⟩ : MemoryRegion) =
    ⟨(stackPtr s).toNat - 320, 320⟩
  rw [hsp]
  have := h.stackLow
  have hstart : (stackPtr s).toNat - 8 - 312 = (stackPtr s).toNat - 320 := by omega
  have hsize : (stackPtr s).toNat - 8 + 8 - ((stackPtr s).toNat - 8 - 312) = 320 := by omega
  rw [hsize, hstart]

set_option maxRecDepth 2048 in
theorem Pre.after_call {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    {s u : RamState} {target : RamState → BitVec 64} {ret : BitVec 64}
    (h : Pre buffer input s) (he : (callEffect target ret s).Holds s u) :
    Call.Compress.ValidInput u input ∧ Call.Compress.ValidBuffer u buffer ∧
      Prelude.Stack.Valid u Compress.minStackBytes ∧ Call.Compress.MemorySeparation u input := by
  have hdi : u.regValue .rdi = s.regValue .rdi := callEffect_read he (r := 7) (by decide)
  have hsi : u.regValue .rsi = s.regValue .rsi := callEffect_read he (r := 6) (by decide)
  have hdx : u.regValue .rdx = s.regValue .rdx := callEffect_read he (r := 2) (by decide)
  have hInput : Compress.inputRegion u input = Compress.inputRegion s input := by
    simp only [Compress.inputRegion, registerRegion, hsi]
  have hOutput : Compress.outputRegion u = Compress.outputRegion s := by
    simp only [Compress.outputRegion, registerRegion, hdi]
  have hFrame := h.callFrame he
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (Compress.inputRegion u input).Bounded ∧
      (Compress.inputRegion u input).HasLength (64 * (u.regValue .rdx).toNat) ∧ _
    rw [hInput, hdx]
    exact ⟨h.inputInMemory.1, h.inputInMemory.2.1,
      hasBytes_of_memoryWriteFrame hFrame h.inputInMemory.2.2 h.inputInMemory.1 (by
        intro r hr; have hr' : r = scratchRegion s := by simpa using hr
        subst r; exact h.inputScratch)⟩
  · change (Compress.outputRegion u).Bounded ∧ _
    rw [hOutput]
    exact ⟨h.bufferInMemory.1, hasBytes_of_memoryWriteFrame hFrame h.bufferInMemory.2 h.bufferInMemory.1 (by
      intro r hr; have hr' : r = scratchRegion s := by simpa using hr
      subst r; exact h.bufferScratch)⟩
  · have hsp : (stackPtr u).toNat = (stackPtr s).toNat - 8 := by
      rw [callEffect_rsp he]
      exact BitVec.toNat_sub_of_le (by change 8 ≤ (stackPtr s).toNat; have := h.stackLow; omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h.calleeStackRegion he]
      exact h.scratchBounded
    · rw [h.calleeStackRegion he]
      intro address ha
      exact Option.isSome_iff_exists.mp (he.agrees.grow _
        (Option.isSome_iff_exists.mpr (h.scratchAllocated address ha)))
    · rw [show Compress.minStackBytes = 312 by decide +kernel]
      change 312 ≤ (stackPtr u).toNat
      rw [hsp]
      have := h.stackLow
      omega
    · change (stackPtr u).toNat % 16 = 8
      rw [hsp]
      have := h.stackLow
      have := h.stackAligned
      omega
  · change MemoryRegion.PairwiseDisjoint #v[Compress.inputRegion u input,
      Compress.outputRegion u, Prelude.Stack.region u Compress.minStackBytes] ∧ _
    rw [hInput, hOutput, h.calleeStackRegion he]
    constructor
    · intro i j hij
      rcases i with ⟨i, hi⟩
      rcases j with ⟨j, hj⟩
      have hic : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      have hjc : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hic with rfl | rfl | rfl <;> rcases hjc with rfl | rfl | rfl
      all_goals first
        | exact h.inputBuffer
        | exact h.inputScratch
        | exact h.bufferScratch
        | exact False.elim (by simp at hij)
    · intro region hr
      simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.bufferAvoids
      · exact h.scratchAvoids

end Md5.Proofs.Buffered.FinalizeReset.CompressCall
