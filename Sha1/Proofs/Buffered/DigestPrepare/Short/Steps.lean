import Sha1.Proofs.Buffered.DigestPrepare.Position
import Sha1.Proofs.Buffered.DigestPrepare.Short.Invariant
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

namespace Sha1.Proofs.Buffered.DigestPrepare

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return rangeApart_text)

theorem short_copy_prepare [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : ¬ InProgram boundary.rip) (hRip : s.RIP = 0x100078) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x100083 ∧ rdi.read t = stackPtr s + 184 ∧
      MemoryRoutines.rdx.read t = (Operand.reg 15 : Operand 64).read s ∧
      AgreesExcept [.reg 7, .rip, .reg 2, .rip] s t := by
  have hLea := lea_r64_effect_step 0x100078 0x48 (by unfold RexWPrefix; decide) 7
    (.sib 4 none 0 (.d32 184)) (by decide) (by decide) (by decide)
  have hb1 : CodeIn (codeRange 0x100078 [0x48, 0x8d, 0xbc, 0x24, 0xb8, 0, 0, 0]) s :=
    Sha1.Proofs.Compress.Machine.program_text_slice hCode 0x78 8 (by decide +kernel)
  obtain ⟨u, ha, hu, he⟩ := hLea.advances hReady hb1 hRip
    (text_address_ne_return hOutside 0x80 (by decide +kernel))
  have hcu := he.agrees.codeIn (by simp [Component.Covers]) hCode
  have hdi : rdi.read u = stackPtr s + 184 := by
    have hw := he.writes
    change rdi.read u = _ at hw
    rw [hw]
    simp [AddrMode.addr, Disp.value, stackPtr]
    rfl
  have hMov := mov_r64_r64_effect_step 0x100080 0x4c 0xfa (by unfold RexWPrefix; decide)
    (by decide)
  have hb2 : CodeIn (codeRange 0x100080 [0x4c, 0x89, 0xfa]) u :=
    Sha1.Proofs.Compress.Machine.program_text_slice hcu 0x80 3 (by decide +kernel)
  obtain ⟨t, hb, ht, he'⟩ := hMov.advances hu hb2 he.rip
    (text_address_ne_return hOutside 0x83 (by decide +kernel))
  have hct := he'.agrees.codeIn (by simp [Component.Covers]) hcu
  have hdx : MemoryRoutines.rdx.read t = (Operand.reg 15 : Operand 64).read u := he'.writes
  have h15 : (Operand.reg 15 : Operand 64).read u = (Operand.reg 15 : Operand 64).read s :=
    he.agrees.read (by simp; decide)
  have hdi' : rdi.read t = rdi.read u := he'.agrees.read (by simp; decide)
  exact ⟨t, ha.trans hb, ht, hct, he'.rip, hdi'.trans hdi, hdx.trans h15,
    he.agrees.trans he'.agrees⟩

variable [bindings : Bindings] {initial s : RamState} {input : ByteArray}

set_option maxRecDepth 2048 in
theorem short_ready (hCall : Digest.ValidCall bindings initial input)
    (h : Initialized initial (returnBoundary initial) input s) (hShort : input.size < 64) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      Frame initial (returnBoundary initial) t ∧
      t.RIP = 0x100083 ∧ rdi.read t = stackPtr t + 184 ∧
      rsi.read t = initial.regValue .rdi ∧
      MemoryRoutines.rdx.read t = BitVec.ofNat 64 input.size ∧
      (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 input.size ∧
      AgreesExcept [.reg 2, .reg 7, .flags, .rip] s t := by
  have hs := hCall.stackAvailable
  obtain ⟨u, ha, hu, hcu, hurip, hau⟩ := entry_branch h.ready h.code h.boundaryOutside h.rip
    (input_size_bounded hCall) h.inputSize
  have hurip' : u.RIP = 0x100078 := by
    simpa only [ite_eq_right (show ¬64 ≤ input.size by omega)] using hurip
  obtain ⟨t, hat, ht, hct, htrip, hdi, hdx, hag2⟩ :=
    short_copy_prepare hu hcu h.boundaryOutside hurip'
  have hag : AgreesExcept [.reg 2, .reg 7, .flags, .rip] s t := by
    apply (hau.trans hag2).mono
    simp
  have hsp : stackPtr t = stackPtr s := hag.read (n := 64) (r := 4) (by simp)
  have husp : stackPtr u = stackPtr s := hau.read (n := 64) (r := 4) (by simp)
  have hframe : Frame initial (returnBoundary initial) t := by
    apply h.toFrame.preserve hs hag ht hct
    · simp [digestPreparationChanges]
    · simp [Component.Covers]
    · exact hsp
    · exact hag.read (n := 64) (r := 3) (by simp)
    · exact hag.read (n := 64) (r := 14) (by simp)
  refine ⟨2 + 2, t, ha.trans hat, hframe, htrip, ?_, ?_, ?_, ?_, hag⟩
  · rw [hdi, husp, hsp]
  · exact (hag.read (n := 64) (r := 6) (by simp)).trans h.inputPointer
  · exact hdx.trans ((hau.read (n := 64) (r := 15) (by simp)).trans h.inputSize)
  · exact (hag.read (n := 64) (r := 15) (by simp)).trans h.inputSize

set_option maxRecDepth 2048 in
theorem short_copied (hStride : UnitStringStride bindings)
    (hCall : Digest.ValidCall bindings initial input)
    (h : Initialized initial (returnBoundary initial) input s) (hShort : input.size < 64) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      Frame initial (returnBoundary initial) t ∧ t.RIP = 0x100089 ∧
      (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 input.size ∧
      (⟨(stackPtr s).toNat + 184, input.size⟩ : MemoryRegion).HasBytes t.external input ∧
      AgreesExcept (shortChanges s input.size) s t := by
  have hs := hCall.stackAvailable
  obtain ⟨n, u, ha, hu, hip, hdi, hsi, hdx, h15, hau⟩ := short_ready hCall h hShort
  have hspu : stackPtr u = stackPtr s := hau.read (n := 64) (r := 4) (by simp)
  have hb := hu.inputBytes hCall
  have hp : MemcpySitePre (0x100083 + 6) u :=
    memcpy_site_pre hCall hu (offset := 0) (by omega) (by omega) hb hdi
      (by rw [hsi]; simp) hdx (by decide) (by decide)
  have hw := hu.scratchWritable hCall (AgreesExcept.refl [] u) 8 8 (by decide) (by decide)
  obtain ⟨t, hr⟩ := digest_memcpy_call hStride hu.ready hu.code hu.boundaryOutside hip
    (Or.inl rfl) hp ⟨hw.readable.low, hw.readable.mem, hw.tables⟩
  have hlen : (MemoryRoutines.rdx.read u).toNat = input.size := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨m, hradv⟩ := hr.advances
  refine ⟨n + m, t, ha.trans hradv,
    hu.after_memcpy hCall hr hdi (by rw [hlen]; omega), hr.rip, ?_, ?_, ?_⟩
  · exact (hr.agrees.read (n := 64) (r := 15) (by simp [callSiteChanges])).trans h15
  · have hbytes : (⟨(rsi.read u).toNat, input.size⟩ : MemoryRegion).HasBytes u.external
        input := by
      rw [hsi]
      exact hb
    have hout := memcpy_hasBytes hr hlen hbytes
    have hn : (stackPtr u + 184).toNat = (stackPtr u).toNat + 184 :=
      hu.address hs (offset := 184) (by decide)
    rw [hdi, hn, hspu] at hout
    exact hout
  · have hag := hau.trans hr.agrees
    rw [callSiteChanges, hdi, hlen, pushAddr, hspu] at hag
    exact hag.mono (by simp [shortChanges, pushAddr])

end Sha1.Proofs.Buffered.DigestPrepare
