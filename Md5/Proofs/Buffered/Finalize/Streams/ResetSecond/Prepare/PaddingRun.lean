import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare.Padding
import Md5.Proofs.Buffered.Finalize.MemoryCalls
import Md5.Proofs.Buffered.FinalizeReset.Arithmetic
import Md5.Proofs.Buffered.Stack
import Md5.Proofs.Buffered.Update.Rodata

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem padding_rsp {variant : Variant} {s t : RamState} (h : (paddingEffect s variant).Holds s t) :
    stackPtr t = stackPtr s := by
  cases variant with
  | original =>
      exact h.agrees.read (n := 64) (r := 4)
          (by simp [Variant.tailOffset, paddingEffect, Effect.components])
  | finalize =>
      exact h.agrees.read (n := 64) (r := 4)
          (by simp [Variant.tailOffset, paddingEffect, Effect.components])
  | discard =>
      exact h.agrees.read (n := 64) (r := 4)
          (by simp [Variant.tailOffset, paddingEffect, Effect.components])
theorem padding_avoids {variant : Variant} {s : RamState} (hs : Storage variant.toKind s)
    (hp : ((.reg 15 : Operand 64).read s).toNat < 64) :
    (paddingEffect s variant).Avoids Extracted.programImage := by
  cases variant with
  | original =>
      intro x hx c hc hcover
      simp only [Variant.tailOffset, paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      apply hs.stackAvoids x.1 _ (.inl ⟨x.2, hx⟩)
      apply hs.stackCover (offset := ((.reg 15 : Operand 64).read s).toNat + 96)
        (len := 1) (by change _ ≤ 296; omega)
      simpa [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc] using hcover
  | finalize =>
      intro x hx c hc hcover
      simp only [Variant.tailOffset, paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      apply hs.stackAvoids x.1 _ (.inl ⟨x.2, hx⟩)
      apply hs.stackCover (offset := ((.reg 15 : Operand 64).read s).toNat + 96)
        (len := 1) (by change _ ≤ 296; omega)
      simpa [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc] using hcover
  | discard =>
      intro x hx c hc hcover
      simp only [Variant.tailOffset, paddingEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      apply hs.stackAvoids x.1 _ (.inl ⟨x.2, hx⟩)
      apply hs.stackCover (offset := ((.reg 15 : Operand 64).read s).toNat + 136)
        (len := 1) (by change _ ≤ 288; omega)
      simpa [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc] using hcover
theorem padding_run {variant : Variant} [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hStorage : Storage variant.toKind s) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = (match variant with | .original => 0x100acf | .finalize => 0x10115f | .discard => 0x10163c)) (hPosition : ((.reg 15 : Operand 64).read s).toNat < 64) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (paddingEffect s variant).Holds s t := by
  cases variant with
  | original =>
      obtain ⟨fuel, t, hrun, hready, _, he⟩ := (padding_execution (variant := .original)) boundary hOutside s hReady
        (program_text_slice hCode 0xacf 26 (by decide +kernel)) ⟨hStorage, hRip, hPosition⟩
      exact ⟨fuel, t, hrun, hready, he.codeIn ((padding_avoids (variant := .original)) hStorage hPosition) hCode, he⟩
  | finalize =>
      obtain ⟨fuel, t, hrun, hready, _, he⟩ := (padding_execution (variant := .finalize)) boundary hOutside s hReady
        (program_text_slice hCode 0x115f 26 (by decide +kernel)) ⟨hStorage, hRip, hPosition⟩
      exact ⟨fuel, t, hrun, hready, he.codeIn ((padding_avoids (variant := .finalize)) hStorage hPosition) hCode, he⟩
  | discard =>
      obtain ⟨fuel, t, hrun, hready, _, he⟩ := (padding_execution (variant := .discard)) boundary hOutside s hReady
        (program_text_slice hCode 0x163c 32 (by decide +kernel)) ⟨hStorage, hRip, hPosition⟩
      exact ⟨fuel, t, hrun, hready, he.codeIn ((padding_avoids (variant := .discard)) hStorage hPosition) hCode, he⟩
theorem padding_memset_pre {variant : Variant} {s t : RamState} {n : Nat} (hs : Storage variant.toKind s)
    (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 n) (hn : n < 64)
    (hdf : DirectionFlagClear s.RFLAGS) (he : (paddingEffect s variant).Holds s t) :
    MemsetSitePre variant.preparedRip t := by
  cases variant with
  | original =>
      have hsp := (padding_rsp (variant := .original)) he
      have hdi : rdi.read t = stackPtr t + BitVec.ofNat 64 (n + 97) := by
        rw [he.writes.2.2.1, hp, hsp]
        change stackPtr s + BitVec.ofNat 64 n + BitVec.ofNat 64 97 = _
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      have hdx : MemoryRoutines.rdx.read t = BitVec.ofNat 64 (63 - n) := by
        rw [he.writes.2.2.2.2, hp, FinalizeReset.remainingBytes n hn]
      have hlen : (MemoryRoutines.rdx.read t).toNat = 63 - n := by
        rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact (hs.of_agrees he.agrees hsp).memsetSitePre
        (he.agrees.directionFlagClear (by simp [Variant.tailOffset, paddingEffect, Effect.components]) ⟨hdf⟩).df
        hdi hlen (by change _ ≤ 296; omega)
        (by decide) (Or.inl (by decide))
  | finalize =>
      have hsp := (padding_rsp (variant := .finalize)) he
      have hdi : rdi.read t = stackPtr t + BitVec.ofNat 64 (n + 97) := by
        rw [he.writes.2.2.1, hp, hsp]
        change stackPtr s + BitVec.ofNat 64 n + BitVec.ofNat 64 97 = _
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      have hdx : MemoryRoutines.rdx.read t = BitVec.ofNat 64 (63 - n) := by
        rw [he.writes.2.2.2.2, hp, FinalizeReset.remainingBytes n hn]
      have hlen : (MemoryRoutines.rdx.read t).toNat = 63 - n := by
        rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact (hs.of_agrees he.agrees hsp).memsetSitePre
        (he.agrees.directionFlagClear (by simp [Variant.tailOffset, paddingEffect, Effect.components]) ⟨hdf⟩).df
        hdi hlen (by change _ ≤ 296; omega)
        (by decide) (Or.inl (by decide))
  | discard =>
      have hsp := (padding_rsp (variant := .discard)) he
      have hdi : rdi.read t = stackPtr t + BitVec.ofNat 64 (n + 137) := by
        rw [he.writes.2.2.1, hp, hsp]
        change stackPtr s + BitVec.ofNat 64 n + BitVec.ofNat 64 137 = _
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      have hdx : MemoryRoutines.rdx.read t = BitVec.ofNat 64 (63 - n) := by
        rw [he.writes.2.2.2.2, hp, FinalizeReset.remainingBytes n hn]
      have hlen : (MemoryRoutines.rdx.read t).toNat = 63 - n := by
        rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact (hs.of_agrees he.agrees hsp).memsetSitePre
        (he.agrees.directionFlagClear (by simp [Variant.tailOffset, paddingEffect, Effect.components]) ⟨hdf⟩).df
        hdi hlen (by change _ ≤ 288; omega)
        (by decide) (Or.inl (by decide))
theorem memset_run {variant : Variant} [bindings : Bindings] (hstride : UnitStringStride bindings)
    {boundary : ReturnBoundary} {s v : RamState} {n : Nat}
    (hs : Storage variant.toKind s) (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 n)
    (hn : n < 64) (hdf : DirectionFlagClear s.RFLAGS)
    (he : (paddingEffect s variant).Holds s v) (hr : ReadyToStep v)
    (hc : CodeIn Extracted.programImage v) (hout : ¬ InProgram boundary.rip) :
    ∃ t, MemsetSiteResult boundary variant.preparedRip v t := by
  cases variant with
  | original =>
      have hsite := (padding_memset_pre (variant := .original)) hs hp hn hdf he
      have hsv := hs.of_agrees he.agrees ((padding_rsp (variant := .original)) he)
      have htarget : callMemPtr 0x100ae9 (.rip 0xff519) v = 0x102460 := by
        change (Operand.mem 0x200008 : Operand 64).read v = _
        exact memset_pointer hc
      have hpre : Stack.CallMemPre 0x100ae9 (.rip 0xff519) v := by
        exact ⟨⟨⟨he.rip, hsv.pushWritable⟩, by rw [htarget]; decide⟩,
          memset_pointer_readable hc⟩
      have hbytes : CodeIn (codeRange 0x100ae9 (encodeCallM64 (.rip 0xff519))) v :=
        program_text_slice hc 0xae9 6 (by decide +kernel)
      exact memset_call hstride
        (outside_text_range_of_not_inProgram hout 0x102460 0x1024a5 (by decide) (by decide +kernel))
        (Stack.call_m64_rip_effect_step 0x100ae9 0xff519) hr hc hbytes hpre hsite htarget
        (text_address_ne_return hout 0xaef (by decide +kernel))
  | finalize =>
      have hsite := (padding_memset_pre (variant := .finalize)) hs hp hn hdf he
      have hsv := hs.of_agrees he.agrees ((padding_rsp (variant := .finalize)) he)
      have htarget : callMemPtr 0x101179 (.rip 0xfee89) v = 0x102460 := by
        change (Operand.mem 0x200008 : Operand 64).read v = _
        exact memset_pointer hc
      have hpre : Stack.CallMemPre 0x101179 (.rip 0xfee89) v := by
        exact ⟨⟨⟨he.rip, hsv.pushWritable⟩, by rw [htarget]; decide⟩,
          memset_pointer_readable hc⟩
      have hbytes : CodeIn (codeRange 0x101179 (encodeCallM64 (.rip 0xfee89))) v :=
        program_text_slice hc 0x1179 6 (by decide +kernel)
      exact memset_call hstride
        (outside_text_range_of_not_inProgram hout 0x102460 0x1024a5 (by decide) (by decide +kernel))
        (Stack.call_m64_rip_effect_step 0x101179 0xfee89) hr hc hbytes hpre hsite htarget
        (text_address_ne_return hout 0x117f (by decide +kernel))
  | discard =>
      have hsite := (padding_memset_pre (variant := .discard)) hs hp hn hdf he
      have hsv := hs.of_agrees he.agrees ((padding_rsp (variant := .discard)) he)
      have htarget : callMemPtr 0x10165c (.rip 0xfe9a6) v = 0x102460 := by
        change (Operand.mem 0x200008 : Operand 64).read v = _
        exact memset_pointer hc
      have hpre : Stack.CallMemPre 0x10165c (.rip 0xfe9a6) v := by
        exact ⟨⟨⟨he.rip, hsv.pushWritable⟩, by rw [htarget]; decide⟩,
          memset_pointer_readable hc⟩
      have hbytes : CodeIn (codeRange 0x10165c (encodeCallM64 (.rip 0xfe9a6))) v :=
        program_text_slice hc 0x165c 6 (by decide +kernel)
      exact memset_call hstride
        (outside_text_range_of_not_inProgram hout 0x102460 0x1024a5 (by decide) (by decide +kernel))
        (Stack.call_m64_rip_effect_step 0x10165c 0xfe9a6) hr hc hbytes hpre hsite htarget
        (text_address_ne_return hout 0x1662 (by decide +kernel))

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare
