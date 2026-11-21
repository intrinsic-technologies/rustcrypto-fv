import Md5.Proofs.Buffered.Finalize.Streams.Slices.Padding
import Md5.Proofs.Buffered.Finalize.MemoryCalls
import Md5.Proofs.Buffered.FinalizeReset.Arithmetic
import Md5.Proofs.Buffered.Stack
import Md5.Proofs.Buffered.Update.Rodata

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem padding_rsp {update : Bool} {s t : RamState} (h : (paddingEffect (update := update) s).Holds s t) :
    stackPtr t = stackPtr s := h.agrees.read (n := 64) (r := 4)
      (by simp [paddingEffect, Effect.components])

theorem padding_avoids {update : Bool} {s : RamState} (hs : Storage (streamKind update) s)
    (hp : ((.reg 15 : Operand 64).read s).toNat < 64) :
    (paddingEffect (update := update) s).Avoids Extracted.programImage := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    intro x hx c hc hcover
    simp only [paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    apply hs.stackAvoids x.1 _ (.inl ⟨x.2, hx⟩)
    apply hs.stackCover (offset := ((.reg 15 : Operand 64).read s).toNat + 16)
      (len := 1) (by cases update <;> change _ ≤ 280 <;> omega)
    simpa [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc] using hcover

theorem padding_run {update : Bool} [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hStorage : Storage (streamKind update) s) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = (BitVec.ofNat 64 (relocated update 0x100463))) (hPosition : ((.reg 15 : Operand 64).read s).toNat < 64) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (paddingEffect (update := update) s).Holds s t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    have hbytes : CodeIn (codeRange (BitVec.ofNat 64 (relocated update 0x100463)) paddingBytes) s := by
      have hc := program_text_slice hCode (relocated update 0x463) 26 (by decide +kernel)
      have hb : Extracted.textBytes.toListFrom (relocated update 0x463) 26 = paddingBytes := by
        decide +kernel
      rw [hb] at hc
      exact hc
    obtain ⟨fuel, t, hrun, hready, _, he⟩ := padding_execution (update := update) boundary hOutside s hReady
      hbytes ⟨hStorage, hRip, hPosition⟩
    exact ⟨fuel, t, hrun, hready, he.codeIn (padding_avoids (update := update) hStorage hPosition) hCode, he⟩

theorem padding_memset_pre {update : Bool} {s t : RamState} {n : Nat} (hs : Storage (streamKind update) s)
    (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 n) (hn : n < 64)
    (hdf : DirectionFlagClear s.RFLAGS) (he : (paddingEffect (update := update) s).Holds s t) :
    MemsetSitePre (BitVec.ofNat 64 (relocated update 0x100483)) t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    have hsp := padding_rsp he
    have hdi : rdi.read t = stackPtr t + BitVec.ofNat 64 (n + 17) := by
      rw [he.writes.2.2.1, hp, hsp]
      change stackPtr s + BitVec.ofNat 64 n + BitVec.ofNat 64 17 = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have hdx : MemoryRoutines.rdx.read t = BitVec.ofNat 64 (63 - n) := by
      rw [he.writes.2.2.2.2, hp, FinalizeReset.remainingBytes n hn]
    have hlen : (MemoryRoutines.rdx.read t).toNat = 63 - n := by
      rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact (hs.of_agrees he.agrees hsp).memsetSitePre
      (he.agrees.directionFlagClear (by simp [paddingEffect, Effect.components]) ⟨hdf⟩).df
      hdi hlen (by cases update <;> change _ ≤ 280 <;> omega)
      (by decide) (Or.inl (by decide))

theorem memset_run {update : Bool} [bindings : Bindings] (hstride : UnitStringStride bindings)
    {boundary : ReturnBoundary} {s v : RamState} {n : Nat}
    (hs : Storage (streamKind update) s) (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 n)
    (hn : n < 64) (hdf : DirectionFlagClear s.RFLAGS)
    (he : (paddingEffect (update := update) s).Holds s v) (hr : ReadyToStep v)
    (hc : CodeIn Extracted.programImage v) (hout : ¬ InProgram boundary.rip) :
    ∃ t, MemsetSiteResult boundary (BitVec.ofNat 64 (relocated update 0x100483)) v t := by
  cases update with
  | false =>
    have hsite := padding_memset_pre (update := false) hs hp hn hdf he
    have hsv := hs.of_agrees he.agrees (padding_rsp he)
    have htarget : callMemPtr 0x10047d (.rip 0xffb85) v = 0x102460 := by
      change (Operand.mem 0x200008 : Operand 64).read v = _
      exact memset_pointer hc
    have hpre : Stack.CallMemPre 0x10047d (.rip 0xffb85) v := by
      exact ⟨⟨⟨he.rip, hsv.pushWritable⟩, by rw [htarget]; decide⟩,
        memset_pointer_readable hc⟩
    have hbytes : CodeIn (codeRange 0x10047d (encodeCallM64 (.rip 0xffb85))) v :=
      by
        have hb := program_text_slice hc 0x47d 6 (by decide +kernel)
        have heq : Extracted.textBytes.toListFrom 0x47d 6 =
            encodeCallM64 (.rip 0xffb85) := by decide +kernel
        rw [heq] at hb
        exact hb
    exact memset_call hstride
      (outside_text_range_of_not_inProgram hout 0x102460 0x1024a5 (by decide) (by decide +kernel))
      (Stack.call_m64_rip_effect_step 0x10047d 0xffb85) hr hc hbytes hpre hsite htarget
      (text_address_ne_return hout 0x483 (by decide +kernel))

  | true =>
    have hsite := padding_memset_pre (update := true) hs hp hn hdf he
    have hsv := hs.of_agrees he.agrees (padding_rsp he)
    have htarget : callMemPtr 0x101a2d (.rip 0xfe5d5) v = 0x102460 := by
      change (Operand.mem 0x200008 : Operand 64).read v = _
      exact memset_pointer hc
    have hpre : Stack.CallMemPre 0x101a2d (.rip 0xfe5d5) v := by
      exact ⟨⟨⟨he.rip, hsv.pushWritable⟩, by rw [htarget]; decide⟩,
        memset_pointer_readable hc⟩
    have hbytes : CodeIn (codeRange 0x101a2d (encodeCallM64 (.rip 0xfe5d5))) v :=
      by
        have hb := program_text_slice hc 0x1a2d 6 (by decide +kernel)
        have heq : Extracted.textBytes.toListFrom 0x1a2d 6 =
            encodeCallM64 (.rip 0xfe5d5) := by decide +kernel
        rw [heq] at hb
        exact hb
    exact memset_call hstride
      (outside_text_range_of_not_inProgram hout 0x102460 0x1024a5 (by decide) (by decide +kernel))
      (Stack.call_m64_rip_effect_step 0x101a2d 0xfe5d5) hr hc hbytes hpre hsite htarget
      (text_address_ne_return hout 0x1a33 (by decide +kernel))


end Md5.Proofs.Buffered.Finalize.Streams.Slices
