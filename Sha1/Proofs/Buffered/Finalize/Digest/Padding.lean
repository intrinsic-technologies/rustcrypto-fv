import Sha1.Proofs.Buffered.Finalize.Geometry
import Sha1.Proofs.Buffered.Update.SiteCalls
import Sha1.Proofs.Buffered.Update.Rodata
import Sha1.Proofs.Compress.Machine.Execution
import X86Proofs.Instructions.Xor.Generated.Imm8.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Lea.Triple

namespace Sha1.Proofs.Buffered.Finalize.Digest

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

namespace Prefix

def bytes : List UInt8 := [0x4d, 0x89, 0xfe, 0x49, 0x83, 0xf6, 0x3f]

def effect (s : RamState) : Effect :=
  { rip := 0x100119
    writes := [⟨(.reg 14 : Operand 64), (.reg 15 : Operand 64).read s ^^^ 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100112) (codeRange 0x100112 bytes) effect := by
  unfold bytes
  md5_run_begin mov_r64_r64_effect_step 0x100112 0x4d 0xfe
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x115 (by decide +kernel)
  md5_run_then xor_r64_imm8_effect_step 0x100115 0x49 0xf6 63
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100112) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x119 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [effect]
  · x86_norm [effect]
    rfl
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

theorem run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x100112) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect s).Holds s t := by
  have hb : CodeIn (codeRange 0x100112 bytes) s :=
    program_text_slice hc 0x112 7 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := execution boundary hout s hr hb hip
  refine ⟨n, t, ha, ht, he.codeIn ?_ hc, he⟩
  exact Effect.Avoids.of_noMem (by simp [effect, Effect.components, Component.Covers]) _

end Prefix
namespace Padding

structure RunPre (s : RamState) : Prop extends Storage .digestCopy s where
  rip : s.RIP = 0x100119
  position : ((.reg 15 : Operand 64).read s).toNat < 64

def effect (s : RamState) : Effect :=
  let pos := (.reg 15 : Operand 64).read s
  { rip := 0x10012c
    writes := [⟨(.mem (stackPtr s + pos + 24) : Operand 8), 128⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + pos + 25⟩,
      ⟨(.reg 6 : Operand 64), 0⟩,
      ⟨(.reg 2 : Operand 64), (.reg 14 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def bytes : List UInt8 :=
  [0x42, 0xc6, 0x44, 0x3c, 0x18, 0x80, 0x4a, 0x8d, 0x3c, 0x3c,
    0x48, 0x83, 0xc7, 0x19, 0x31, 0xf6, 0x4c, 0x89, 0xf2]

theorem marker_address {s : RamState} :
    stackPtr s + BitVec.ofNat 64 (((.reg 15 : Operand 64).read s).toNat + 24) =
      stackPtr s + (.reg 15 : Operand 64).read s + 24 := by
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← BitVec.add_assoc]
  rfl

theorem marker_writable {s : RamState} (hs : Storage .digestCopy s)
    (hp : ((.reg 15 : Operand 64).read s).toNat < 64) :
    X86Proofs.MemWritable s (stackPtr s + (.reg 15 : Operand 64).read s + 24) 1 := by
  rw [← marker_address]
  exact hs.x86Writable _ 1 (by decide) (by simp only [Kind.stackBytes]; omega)

theorem marker_apart {s : RamState} (hs : Storage .digestCopy s)
    (hp : ((.reg 15 : Operand 64).read s).toNat < 64) (offset len : Nat)
    (hc : offset + len ≤ Extracted.textBytes.size) :
    RangeApart (stackPtr s + (.reg 15 : Operand 64).read s + 24) 1
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  rw [← marker_address]
  exact hs.stackApart (len := 1) (by simp only [Kind.stackBytes]; omega) hc

theorem execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary RunPre (codeRange 0x100119 bytes) effect := by
  unfold bytes
  md5_run_begin (mov_m8_imm8_rex_effect_step 0x100119 0x42
    (by unfold RexPrefix; decide) (.sib 4 (some 15) 0 (.d8 24))
    (by decide) (by decide) (by decide) 128)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · x86_norm [BitVec.shiftLeft_zero]
      simpa [stackPtr, Operand.read, BitVec.add_assoc] using marker_writable h.toStorage h.position
    · x86_norm [BitVec.shiftLeft_zero]
      simpa [stackPtr, Operand.read, BitVec.add_assoc, Extracted.textAddress] using
        marker_apart h.toStorage h.position 0x119 6 (by decide +kernel)
  case av =>
    intro s h
    apply Effect.avoids_of_components_mem_rip (show
      (movM8Imm8RexEffect 0x100119 (.sib 4 (some 15) 0 (.d8 24)) 128 s).components =
        [.mem (stackPtr s + (.reg 15 : Operand 64).read s + 24) 1, .rip] by
          x86_norm [BitVec.shiftLeft_zero, stackPtr]; rfl)
    exact marker_apart h.toStorage h.position 0x119 19 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x11f (by decide +kernel)
  md5_run_then (lea_r64_effect_step 0x10011f 0x4a (by unfold RexWPrefix; decide)
    7 (.sib 4 (some 15) 0 .none) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100119) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x123 (by decide +kernel)
  md5_run_then (add_r64_imm8_effect_step 0x100123 0x48 0xc7 25
    (by unfold RexWPrefix; decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100119) 10 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x127 (by decide +kernel)
  md5_run_then (xor_r32_r32_effect_step 0x100127 0xf6 (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100119) 14 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x129 (by decide +kernel)
  md5_run_then (mov_r64_r64_effect_step 0x100129 0x4c 0xf2
    (by unfold RexWPrefix; decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x100119) 16 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x12c (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [effect]
  · x86_norm [effect, stackPtr, BitVec.shiftLeft_zero]
    simp [Operand.read, gprNumber, rexB, rexR, modrmRm, modrmReg]
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect, stackPtr, BitVec.shiftLeft_zero]
    rfl

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
  have hr := h.toStorage.stackRange (((Operand.reg 15 : Operand 64).read s).toNat + 24) 1
    (by simp only [Kind.stackBytes]; omega)
  apply hr.code i hi
  refine ⟨x.2, ?_⟩
  rw [marker_address]
  exact he ▸ hx

theorem run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (h : RunPre s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect s).Holds s t := by
  have hb : CodeIn (codeRange 0x100119 bytes) s :=
    program_text_slice hc 0x119 19 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := execution boundary hout s hr hb h
  exact ⟨n, t, ha, ht, he.codeIn (effect_avoids h) hc, he⟩

theorem memsetSitePre {s : RamState} (hs : Storage .digestCopy s) {ret : BitVec 64}
    {offset len : Nat} (hdf : DirectionFlagClear s.RFLAGS)
    (hdst : rdi.read s = stackPtr s + BitVec.ofNat 64 offset)
    (hlen : (MemoryRoutines.rdx.read s).toNat = len)
    (he : offset + len ≤ Kind.digestCopy.stackBytes)
    (hret : ret.toNat < 2^32) (hout : ret.toNat < 0x1036e0 ∨ 0x103725 ≤ ret.toNat) :
    MemsetSitePre ret s := by
  refine ⟨hdf, ?_, hs.pushRange.readable, hs.pushRange.code, ?_, hret, hout⟩
  · rw [hdst, hlen]
    exact hs.stackRange offset len he
  · rw [hdst, hlen]
    exact hs.stackApartPush he

theorem memset [bindings : Bindings] (hstride : UnitStringStride bindings)
    {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (hs : Storage .digestCopy s) (hip : s.RIP = 0x10012c)
    (hdf : DirectionFlagClear s.RFLAGS) {position : Nat} (hp : position < 64)
    (hdi : rdi.read s = stackPtr s + BitVec.ofNat 64 (position + 25))
    (hdx : MemoryRoutines.rdx.read s = BitVec.ofNat 64 (63 - position)) :
    ∃ t, MemsetSiteResult boundary 0x100132 s t := by
  have htarget : callMemPtr 0x10012c (.rip 0xffed6) s = 0x1036e0 := memset_pointer hc
  have hpre : CallMemPre 0x10012c (.rip 0xffed6) s := by
    refine ⟨⟨hs.pushPre hip (codeOffset := 0x12c) rfl (by decide +kernel), ?_⟩, ?_⟩
    · rw [htarget]
      decide
    · exact memset_pointer_readable hc
  have hpSite : MemsetSitePre 0x100132 s := memsetSitePre hs hdf hdi
    (by rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    (by simp only [Kind.stackBytes]; omega) (by decide) (.inl (by decide))
  have hb : CodeIn (codeRange 0x10012c (encodeCallM64 (.rip 0xffed6))) s :=
    program_text_slice hc 0x12c 6 (by decide +kernel)
  exact memset_call hstride
    (outside_text_range hout 0x1036e0 0x103725 (by decide) (by decide +kernel))
    (call_m64_effect_step 0x10012c (.rip 0xffed6) trivial rfl rfl) hr hc hb hpre hpSite htarget
    (text_address_ne_return hout 0x132 (by decide +kernel))

end Padding

end Sha1.Proofs.Buffered.Finalize.Digest
