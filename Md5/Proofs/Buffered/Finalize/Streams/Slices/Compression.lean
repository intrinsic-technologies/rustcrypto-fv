import Md5.Proofs.Buffered.Finalize.Compression
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Contracts

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

namespace Compression

theorem first_run {update : Bool} [Bindings] {boundary : ReturnBoundary} {s : RamState}
    {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hp : FinalizeReset.CompressCall.Pre buffer input s) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hout : ¬ InProgram boundary.rip)
    (hip : s.RIP = (BitVec.ofNat 64 (relocated update 0x1004f9))) :
    ∃ t, FinalizeReset.CompressCall.Post boundary (BitVec.ofNat 64 (relocated update 0x1004fe)) buffer input s t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    have hbytes : CodeIn (codeRange (BitVec.ofNat 64 (relocated update 0x1004f9))
        (encodeCallRel32 (if update then 0xf2 else 0x16a2))) s := by
      have hs := program_text_slice hc (relocated update 0x4f9) 5 (by decide +kernel)
      have he : Extracted.textBytes.toListFrom (relocated update 0x4f9) 5 =
          encodeCallRel32 (if update then 0xf2 else 0x16a2) := by decide +kernel
      rw [he] at hs
      exact hs
    exact FinalizeReset.CompressCall.run_of_step
      (Buffered.Stack.call_rel32_effect_step (BitVec.ofNat 64 (relocated update 0x1004f9)) (if update then 0xf2 else 0x16a2) (by decide +kernel)) hr hc
      hbytes ⟨hip, hp.pushWritable⟩ hp
      (by decide +kernel) (by decide) (Or.inl (by decide)) hout
      (text_address_ne_return hout (relocated update 0x4fe) (by decide +kernel))

theorem final_run {update : Bool} [Bindings] {boundary : ReturnBoundary} {s : RamState}
    {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hp : FinalizeReset.CompressCall.Pre buffer input s) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hout : ¬ InProgram boundary.rip)
    (hip : s.RIP = (BitVec.ofNat 64 (relocated update 0x1005b4))) :
    ∃ t, FinalizeReset.CompressCall.Post boundary (BitVec.ofNat 64 (relocated update 0x1005b9)) buffer input s t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    have hbytes : CodeIn (codeRange (BitVec.ofNat 64 (relocated update 0x1005b4))
        (encodeCallRel32 (if update then 0x37 else 0x15e7))) s := by
      have hs := program_text_slice hc (relocated update 0x5b4) 5 (by decide +kernel)
      have he : Extracted.textBytes.toListFrom (relocated update 0x5b4) 5 =
          encodeCallRel32 (if update then 0x37 else 0x15e7) := by decide +kernel
      rw [he] at hs
      exact hs
    exact FinalizeReset.CompressCall.run_of_step
      (Buffered.Stack.call_rel32_effect_step (BitVec.ofNat 64 (relocated update 0x1005b4)) (if update then 0x37 else 0x15e7) (by decide +kernel)) hr hc
      hbytes ⟨hip, hp.pushWritable⟩ hp
      (by decide +kernel) (by decide) (Or.inl (by decide)) hout
      (text_address_ne_return hout (relocated update 0x5b9) (by decide +kernel))

theorem agrees {update : Bool} {s t : RamState} (hdi : s.regValue .rdi = stackPtr s)
    (ha : AgreesExcept (FinalizeReset.CompressCall.changes s) s t) :
    AgreesExcept ((streamKind update).changes s) s t := by
  apply ha.widen
  · intro c hc hm
    simp only [FinalizeReset.CompressCall.changes, hdi, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases update <;> simp_all [streamKind, Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
  · intro address c hc ha
    simp only [FinalizeReset.CompressCall.changes, hdi, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · obtain ⟨i, hi, he⟩ := ha
      exact ⟨.mem (stackPtr s) 168, by cases update <;> simp [streamKind, Kind.changes, Kind.localChanges],
        i, by omega, he⟩
    · exact ⟨.mem (stackPtr s - 320) 320, by simp [Kind.changes], ha⟩

theorem finish {update : Bool} [Bindings] {boundary : ReturnBoundary} {message : ByteArray} {s : RamState}
    (hOutside : ¬ InProgram boundary.rip) (h : CallReady (update := update) message s) :
    ∃ t, Post (streamKind update) boundary message s t := by
  have hdst : s.regValue .rdi = stackPtr s + BitVec.ofNat 64 0 := by
    change (.reg 7 : Operand 64).read s = stackPtr s + 0
    simpa using h.destination
  have hp := h.toStorage.compressCallPre (src := 104) (dst := 0)
    (input := lastBlock message) (buffer := paddedBuffer message)
    h.source hdst (by
      change 64 * ((.reg 2 : Operand 64).read s).toNat = _
      rw [h.count, size_lastBlock]
      rfl)
    (by rw [size_lastBlock]; cases update <;> decide) (by cases update <;> decide) (Or.inr (by cases update <;> decide))
    (by simpa only [size_lastBlock] using h.input) (by simpa using h.buffer)
  obtain ⟨t, ht⟩ := final_run (update := update) hp h.ready h.code hOutside h.rip
  refine ⟨t, ht.advances, ht.ready, ht.code, (by cases update <;> exact ht.rip), ?_, agrees h.destination ht.agrees⟩
  have hb := ht.output
  have hdi : s.regValue .rdi = stackPtr s := h.destination
  simp only [Compress.outputRegion, registerRegion, hdi] at hb
  cases update <;> simpa only [streamKind, Bool.false_eq_true, ↓reduceIte, Kind.resultRegion, Kind.resultOffset, Nat.add_zero,
    messageDigest_paddedBuffer] using hb

end Compression

end Md5.Proofs.Buffered.Finalize.Streams.Slices
