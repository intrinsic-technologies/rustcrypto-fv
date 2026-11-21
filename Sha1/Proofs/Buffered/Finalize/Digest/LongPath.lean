import Sha1.Proofs.Buffered.Finalize.Digest.Final

namespace Sha1.Proofs.Buffered.Finalize.Digest

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine
open Sha1.Proofs.Buffered.DigestPrepare.Long (CompressionCall)

structure LongPre [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (x : RamState) : Prop extends Storage .digestCopy x where
  ready : ReadyToStep x
  code : CodeIn Extracted.programImage x
  rip : x.RIP = 0x10013c
  boundaryOutside : ¬ InProgram boundary.rip
  df : DirectionFlagClear x.RFLAGS
  long : 56 ≤ message.size % 64
  position : (Operand.reg 15 : Operand 64).read x = BitVec.ofNat 64 (message.size % 64)
  blocks : (Operand.reg 12 : Operand 64).read x = BitVec.ofNat 64 (message.size / 64)
  padded : Bytes x.external (stackPtr x + 24) 64 (fun i ↦ (firstBlock message)[i]!)
  state : (⟨(stackPtr x).toNat, 20⟩ : MemoryRegion).HasBytes x.external
    (absorbedStateBytes message)

theorem long_path [bindings : Bindings] (hBridge : CompressionCall)
    (hStride : UnitStringStride bindings) {boundary : ReturnBoundary} {message : ByteArray}
    {x : RamState} (h : LongPre boundary message x) :
    ∃ y, (∃ fuel, Advances boundary fuel x y) ∧
      LastPre boundary message
        (Wrapper.Absorb.compressBlocks (absorbedHash message) (firstBlock message)) y ∧
      stackPtr y = stackPtr x ∧ AgreesExcept (Kind.digestCopy.changes x) x y := by
  obtain ⟨y1, hy1⟩ := BlockCopy.long_copy h.ready h.code h.boundaryOutside ⟨h.toStorage, h.rip⟩
  have hsp1 := hy1.rsp
  have hs1 := h.toStorage.of_agrees hy1.agrees hsp1
  have hbytes : Bytes y1.external (stackPtr y1 + BitVec.ofNat 64 120) 64
      (fun i ↦ (firstBlock message)[i]!) := by
    intro i hi
    rw [hsp1, stack_offset, hy1.copy i hi, ← stack_offset]
    exact h.padded i hi
  have hblock := hasBytes_of_bytes_size hbytes (size_firstBlock message)
  have hstate1 : (⟨(stackPtr y1).toNat, 20⟩ : MemoryRegion).HasBytes y1.external
      (Wrapper.Hash.Serialize.stateBytes (absorbedHash message)) := by
    apply hasBytes_resize' _ (Wrapper.Hash.Serialize.stateBytes_size _)
    apply hasBytes_of_copy (src := stackPtr x) (dst := stackPtr y1) _
      (hasBytes_resize h.state (Wrapper.Hash.Serialize.stateBytes_size _).symm)
    intro i hi
    rw [absorbedStateBytes_size] at hi
    rw [hsp1]
    apply hy1.agrees.byte
    intro c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    exact covers_apart (base := stackPtr x) (a := 120) (len := 64) (b := i) (count := 1) (i := 0)
      (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) (.inr (by omega)) hcov
  have hdf1 : DirectionFlagClear y1.RFLAGS :=
    (hy1.agrees.directionFlagClear (by simp) ⟨h.df⟩).df
  have hsite : SitePre boundary 0x1001ae (absorbedHash message) (firstBlock message) y1 := by
    refine ⟨hs1, hy1.ready, hy1.code, hy1.rip, h.boundaryOutside, hdf1, ?_, ?_, hy1.rdx,
      size_firstBlock message, hblock, hstate1⟩
    · exact hy1.rdi.trans hsp1.symm
    · rw [hsp1]
      exact hy1.rsi
  obtain ⟨y2, hy2⟩ := compress_site (disp := 0x232d) (off := 0x1ae) hBridge hStride hsite rfl
    (by decide +kernel) (by decide)
    (Sha1.Proofs.Compress.Machine.program_text_slice hy1.code 0x1ae 5 (by decide +kernel))
    (by decide) (text_address_ne_return h.boundaryOutside 0x1b3 (by decide +kernel))
  have hsp2 := hy2.rsp.trans hsp1
  have hs2 := hs1.of_agrees hy2.agrees hy2.rsp
  have hdf2 : DirectionFlagClear y2.RFLAGS :=
    (hy2.agrees.directionFlagClear (by simp [Kind.changes, Kind.workRegisters, Kind.localChanges])
      ⟨hdf1⟩).df
  obtain ⟨n3, y3, h3, hr3, hc3, hC⟩ := BlockCopy.clear_run hy2.ready hy2.code h.boundaryOutside
    ⟨hs2, hy2.rip.trans (by decide)⟩
  have hsp3 := BlockCopy.clear_rsp hC
  have hs3 := hs2.of_agrees hC.agrees hsp3
  have hwC := hC.writes
  simp only [BlockCopy.clearEffect, Write.AllHold] at hwC
  have hreg (r : BitVec 5) (hr : r = 12 ∨ r = 15) :
      (Operand.reg r : Operand 64).read y3 = (Operand.reg r : Operand 64).read x := by
    have h3r : (Operand.reg r : Operand 64).read y3 = (Operand.reg r : Operand 64).read y2 :=
      hC.agrees.read (by rcases hr with rfl | rfl <;> simp [BlockCopy.clearEffect, Effect.components])
    have h1r : (Operand.reg r : Operand 64).read y1 = (Operand.reg r : Operand 64).read x :=
      hy1.agrees.read (by rcases hr with rfl | rfl <;> simp)
    rcases hr with rfl | rfl
    · exact h3r.trans (hy2.r12.trans h1r)
    · exact h3r.trans (hy2.r15.trans h1r)
  have hz : ∀ d, d + 8 ≤ 280 →
      (Operand.mem (stackPtr y2 + BitVec.ofNat 64 d) : Operand 64).read y3 = 0 →
      ∀ k < 8, y3.external[stackPtr y3 + BitVec.ofNat 64 (d + k)]? = some 0 := by
    intro d hd hv k hk
    have hrd : ∀ i < 64 / 8,
        (y3.external[stackPtr y2 + BitVec.ofNat 64 d + BitVec.ofNat 64 i]?).isSome := by
      intro i hi
      rw [stack_offset, ← hsp3]
      exact BlockCopy.stack_byte_some hs3 (d + i) (by omega)
    have hb := Bytes.of_memLoad hrd k hk
    change memLoad y3.external _ 64 = 0 at hv
    rw [hv, stack_offset, ← hsp3] at hb
    rw [hb]
    simp [storedByte]
  have hzero : ∀ i < 56, y3.external[stackPtr y3 + BitVec.ofNat 64 (24 + i)]? = some 0 := by
    intro i hi
    rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) by omega) with hw | hw | hw | hw | hw | hw | hw
    · have hk : i - 0 < 8 := by omega
      have := hz 24 (by decide) hwC.1 (i - 0) hk
      rwa [show 24 + (i - 0) = 24 + i by omega] at this
    · have hk : i - 8 < 8 := by omega
      have := hz 32 (by decide) hwC.2.1 (i - 8) hk
      rwa [show 32 + (i - 8) = 24 + i by omega] at this
    · have hk : i - 16 < 8 := by omega
      have := hz 40 (by decide) hwC.2.2.1 (i - 16) hk
      rwa [show 40 + (i - 16) = 24 + i by omega] at this
    · have hk : i - 24 < 8 := by omega
      have := hz 48 (by decide) hwC.2.2.2.1 (i - 24) hk
      rwa [show 48 + (i - 24) = 24 + i by omega] at this
    · have hk : i - 32 < 8 := by omega
      have := hz 56 (by decide) hwC.2.2.2.2.1 (i - 32) hk
      rwa [show 56 + (i - 32) = 24 + i by omega] at this
    · have hk : i - 40 < 8 := by omega
      have := hz 64 (by decide) hwC.2.2.2.2.2.1 (i - 40) hk
      rwa [show 64 + (i - 40) = 24 + i by omega] at this
    · have hk : i - 48 < 8 := by omega
      have := hz 72 (by decide) hwC.2.2.2.2.2.2 (i - 48) hk
      rwa [show 72 + (i - 48) = 24 + i by omega] at this
  have hstate3 : (⟨(stackPtr y3).toNat, 20⟩ : MemoryRegion).HasBytes y3.external
      (Wrapper.Hash.Serialize.stateBytes
        (Wrapper.Absorb.compressBlocks (absorbedHash message) (firstBlock message))) := by
    apply hasBytes_resize' _ (Wrapper.Hash.Serialize.stateBytes_size _)
    have h2 := hy2.state
    rw [hsp1] at h2
    apply hasBytes_of_copy (src := stackPtr x) (dst := stackPtr y3) _
      (hasBytes_resize h2 (Wrapper.Hash.Serialize.stateBytes_size _).symm)
    intro i hi
    rw [Wrapper.Hash.Serialize.stateBytes_size] at hi
    rw [hsp3, hy2.rsp, hsp1, ← hsp1, ← hy2.rsp]
    rw [BlockCopy.clear_byte hC i (by omega) (by omega)]
  have hag : AgreesExcept (Kind.digestCopy.changes x) x y3 := by
    have hag1 : AgreesExcept (Kind.digestCopy.changes x) x y1 := by
      apply agrees_changes hy1.agrees
      · intro c hc hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters]
      · intro x' c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcov.elim
        exact h.toStorage.localWithin (offset := 120) (len := 64) (by decide) hcov
    have hag2 := hy2.agrees
    rw [Kind.changes_eq_of_rsp _ hsp1 (by decide)] at hag2
    have hag3 : AgreesExcept (Kind.digestCopy.changes y2) y2 y3 := by
      apply agrees_changes hC.agrees
      · intro c hc hm
        simp only [BlockCopy.clearEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters]
      · intro x' c hc hcov
        simp only [BlockCopy.clearEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcov.elim
        · exact hs2.localWithin (offset := 24) (len := 8) (by decide) hcov
        · exact hs2.localWithin (offset := 32) (len := 8) (by decide) hcov
        · exact hs2.localWithin (offset := 40) (len := 8) (by decide) hcov
        · exact hs2.localWithin (offset := 48) (len := 8) (by decide) hcov
        · exact hs2.localWithin (offset := 56) (len := 8) (by decide) hcov
        · exact hs2.localWithin (offset := 64) (len := 8) (by decide) hcov
        · exact hs2.localWithin (offset := 72) (len := 8) (by decide) hcov
    rw [Kind.changes_eq_of_rsp _ hsp2 (by decide)] at hag3
    exact ((hag1.trans hag2).trans hag3).mono (by simp)
  obtain ⟨n1, h1⟩ := hy1.advances
  obtain ⟨n2, h2⟩ := hy2.advances
  refine ⟨y3, ⟨n1 + (n2 + n3), h1.trans (h2.trans h3)⟩,
    ⟨hs3, hr3, hc3, hC.rip, h.boundaryOutside, ?_, ?_, ?_, ?_, hstate3⟩,
    hsp3.trans hsp2, hag⟩
  · exact (hC.agrees.directionFlagClear (by simp [BlockCopy.clearEffect, Effect.components])
      ⟨hdf2⟩).df
  · rw [hreg 15 (.inr rfl)]
    exact h.position
  · rw [hreg 12 (.inl rfl)]
    exact h.blocks
  · intro i hi
    have hn : ¬ (message.size % 64 < 56) := by have := h.long; omega
    simp only [hn, ite_false]
    exact hzero i hi

end Sha1.Proofs.Buffered.Finalize.Digest
