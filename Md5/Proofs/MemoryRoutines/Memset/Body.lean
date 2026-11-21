import Md5.Proofs.MemoryRoutines.Memset.Stores
import Md5.Proofs.MemoryRoutines.Finish

namespace Md5.Proofs.MemoryRoutines.Memset

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Spec.Program Md5.Proofs.Block

structure StoresPre (s : RamState) (length : Nat) : Prop where
  rip : s.RIP = 0x102494
  df : DirectionFlagClear s.RFLAGS
  dst : WritableRange s (rdi.read s) length
  pattern : rax.read s = broadcast ((rax.read s).setWidth 8)
  head : (rcx.read s).toNat = alignmentPrefix (rdi.read s) length
  words : (rsi.read s).toNat = (length - alignmentPrefix (rdi.read s) length) / 8
  tail : (r8.read s).toNat = (length - alignmentPrefix (rdi.read s) length) % 8

theorem stores_run [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary) (hb : Outside boundary) (s : RamState) (length : Nat)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (hp : StoresPre s length) :
    ∃ fuel t, Advances boundary fuel s t ∧ FillState s t length length ∧ t.RIP = 0x1024a1 := by
  let head := alignmentPrefix (rdi.read s) length
  let words := (length - head) / 8
  let tail := (length - head) % 8
  have hhead : head ≤ length := alignmentPrefix_le_length _ _
  have hsum : head + 8 * words + tail = length := remaining_split _ _ hhead
  have hinit := FillState.initial s length hr hc
  have hcode1 : CodeIn (codeRange 0x102494 Stos.Kind.byte.code) s :=
    program_text_slice hc 0x2494 2 (by decide +kernel)
  obtain ⟨n₁, u, ha₁, hu, hipu⟩ := hinit.store hstride hp.dst hp.pattern hp.df .byte 0x102494
    hp.rip hcode1 (text_address_add 0x2494 2 (by decide +kernel))
    (by simpa only [Stos.Kind.bytes, Nat.one_mul, Nat.zero_add, hp.head] using hhead)
    (by intro _; exact Nat.mod_one _) boundary
    (hb.ne (p := 0x102494) (by decide) (by decide))
    (hb.ne (p := 0x102496) (by decide) (by decide))
  have hu' : FillState s u length head := by
    simpa only [Stos.Kind.bytes, Nat.one_mul, Nat.zero_add, hp.head] using hu
  have hmove1 : StepEffect (fun t ↦ t.RIP = 0x102496)
      (codeRange 0x102496 [0x48, 0x89, 0xf1]) (movR64R64Effect 0x102496 1 6) :=
    mov_r64_r64_effect_step 0x102496 0x48 0xf1 (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨v, ha₂, hrv, hev⟩ := hmove1.advances hu'.ready
    (program_text_slice hu'.code 0x2496 3 (by decide +kernel)) hipu
    (hb.ne (p := 0x102499) (by decide) (by decide))
  have hv := hu'.move hrv 0x102496 6 hev
  have hcountv : (rcx.read v).toNat = words := by
    rw [show rcx.read v = rsi.read u from hev.writes,
      hu'.agrees.read (r := 6) (n := 64) (by simp [storeChanges])]
    exact hp.words
  have hcode2 : CodeIn (codeRange 0x102499 Stos.Kind.qword.code) v :=
    program_text_slice hv.code 0x2499 3 (by decide +kernel)
  obtain ⟨n₃, w, ha₃, hw, hipw⟩ := hv.store hstride hp.dst hp.pattern hp.df .qword 0x102499
    hev.rip hcode2 (text_address_add 0x2499 3 (by decide +kernel))
    (by change head + 8 * (rcx.read v).toNat ≤ length; rw [hcountv]; omega)
    (by
      intro hnonzero
      change (rdi.read v).toNat % 8 = 0
      rw [hv.pointer, toNat_add_ofNat _ _ (by have := hp.dst.readable.low; omega)]
      apply alignmentPrefix_aligned
      have hn : 0 < words := by
        by_cases hn : 0 < words
        · exact hn
        · have hz : (rcx.read v).toNat = 0 := by omega
          exact False.elim (hnonzero (BitVec.eq_of_toNat_eq hz))
      change 0 < (length - head) / 8 at hn
      change head < length
      omega)
    boundary (hb.ne (p := 0x102499) (by decide) (by decide))
    (hb.ne (p := 0x10249c) (by decide) (by decide))
  have hw' : FillState s w length (head + 8 * words) := by
    simpa only [Stos.Kind.bytes, hcountv] using hw
  have hmove2 : StepEffect (fun t ↦ t.RIP = 0x10249c)
      (codeRange 0x10249c [0x4c, 0x89, 0xc1]) (movR64R64Effect 0x10249c 1 8) :=
    mov_r64_r64_effect_step 0x10249c 0x4c 0xc1 (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨x, ha₄, hrx, hex⟩ := hmove2.advances hw'.ready
    (program_text_slice hw'.code 0x249c 3 (by decide +kernel)) hipw
    (hb.ne (p := 0x10249f) (by decide) (by decide))
  have hx := hw'.move hrx 0x10249c 8 hex
  have hcountx : (rcx.read x).toNat = tail := by
    rw [show rcx.read x = r8.read w from hex.writes,
      hw'.agrees.read (r := 8) (n := 64) (by simp [storeChanges])]
    exact hp.tail
  have hcode3 : CodeIn (codeRange 0x10249f Stos.Kind.byte.code) x :=
    program_text_slice hx.code 0x249f 2 (by decide +kernel)
  obtain ⟨n₅, t, ha₅, ht, hipt⟩ := hx.store hstride hp.dst hp.pattern hp.df .byte 0x10249f
    hex.rip hcode3 (text_address_add 0x249f 2 (by decide +kernel))
    (by change head + 8 * words + 1 * (rcx.read x).toNat ≤ length; rw [hcountx]; omega)
    (by intro _; exact Nat.mod_one _) boundary
    (hb.ne (p := 0x10249f) (by decide) (by decide))
    (hb.ne (p := 0x1024a1) (by decide) (by decide))
  refine ⟨n₁ + 1 + n₃ + 1 + n₅, t,
    (((ha₁.trans ha₂).trans ha₃).trans ha₄).trans ha₅, ?_, hipt⟩
  simpa only [Stos.Kind.bytes, Nat.one_mul, hcountx, hsum] using ht

end Md5.Proofs.MemoryRoutines.Memset
