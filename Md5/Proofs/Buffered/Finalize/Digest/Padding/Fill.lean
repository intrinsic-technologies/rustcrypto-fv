import Md5.Proofs.Buffered.Finalize.Digest.Padding
import Md5.Proofs.Buffered.Finalize.MemoryCalls
import Md5.Proofs.Buffered.Finalize.Algebra
import Md5.Proofs.Buffered.FinalizeReset.Arithmetic
import Md5.Proofs.Buffered.Stack
import Md5.Proofs.Buffered.Update.Rodata

namespace Md5.Proofs.Buffered.Finalize.Digest.Padding

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem effect_rsp {s t : RamState} (h : (effect s).Holds s t) :
    stackPtr t = stackPtr s := h.agrees.read (n := 64) (r := 4) (by
  simp [effect, Effect.components])

theorem effect_avoids {s : RamState} (h : RunPre s) :
    (effect s).Avoids Extracted.programImage := by
  intro x hx c hc hcover
  simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨i, hi, he⟩ := hcover
  have hp := h.position
  have hspan : ((Operand.reg 12 : Operand 64).read s).toNat + 24 + 1 ≤
      Kind.digest.stackBytes := by simp only [Kind.stackBytes]; omega
  have hr := h.toStorage.stackRange _ 1 hspan
  apply hr.code i hi
  refine ⟨x.2, ?_⟩
  have heq : stackPtr s + BitVec.ofNat 64 (((Operand.reg 12 : Operand 64).read s).toNat + 24) =
      stackPtr s + (Operand.reg 12 : Operand 64).read s + 24 := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← BitVec.add_assoc]
    rfl
  rw [heq]
  exact he ▸ hx

theorem run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (h : RunPre s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect s).Holds s t := by
  have hb : CodeIn (codeRange 0x100107 bytes) s :=
    program_text_slice hc 0x107 19 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := execution boundary hout s hr hb h
  exact ⟨n, t, ha, ht, he.codeIn (effect_avoids h) hc, he⟩

theorem memset [bindings : Bindings] (hstride : UnitStringStride bindings)
    {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (hs : Storage .digest s) (hip : s.RIP = 0x10011a)
    (hdf : DirectionFlagClear s.RFLAGS) {position : Nat} (hp : position < 64)
    (hdi : rdi.read s = stackPtr s + BitVec.ofNat 64 (position + 25))
    (hdx : MemoryRoutines.rdx.read s = BitVec.ofNat 64 (63 - position)) :
    ∃ t, MemsetSiteResult boundary 0x100120 s t := by
  have htarget : callMemPtr 0x10011a (.rip 0xffee8) s = 0x102460 := memset_pointer hc
  have hpre : Stack.CallMemPre 0x10011a (.rip 0xffee8) s := by
    refine ⟨⟨⟨hip, hs.pushWritable⟩, ?_⟩, ?_⟩
    · rw [htarget]
      decide
    · exact memset_pointer_readable hc
  have hpSite : MemsetSitePre 0x100120 s := hs.memsetSitePre hdf hdi
    (by rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    (by simp only [Kind.stackBytes]; omega) (by decide) (.inl (by decide))
  have hb : CodeIn (codeRange 0x10011a (encodeCallM64 (.rip 0xffee8))) s :=
    program_text_slice hc 0x11a 6 (by decide +kernel)
  exact memset_call hstride
    (outside_text_range_of_not_inProgram hout 0x102460 0x1024a5 (by decide) (by decide +kernel))
    (Stack.call_m64_rip_effect_step 0x10011a 0xffee8) hr hc hb hpre hpSite htarget
    (text_address_ne_return hout 0x120 (by decide +kernel))

end Md5.Proofs.Buffered.Finalize.Digest.Padding
