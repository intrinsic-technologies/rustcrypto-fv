import Md5.Proofs.MemoryRoutines.Memcpy.Body.State
import Md5.Proofs.MemoryRoutines.Finish

namespace Md5.Proofs.MemoryRoutines

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Spec.Program Md5.Proofs.Block
open Memcpy

theorem memcpy_body [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x1024b0 ∨ 0x1024df ≤ boundary.rip.toNat)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : MemcpyPre s) :
    ∃ fuel t, Advances boundary fuel s t ∧ CallBodyResult s t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = 0x1024de ∧
      ∀ i < (rdx.read s).toNat, t.external[rdi.read s + BitVec.ofNat 64 i]? =
        s.external[rsi.read s + BitVec.ofNat 64 i]? := by
  let length := (rdx.read s).toNat
  let head := alignmentPrefix (rdi.read s) length
  let words := (length - head) / 8
  let tail := (length - head) % 8
  have hh : head ≤ length := alignmentPrefix_le_length _ _
  have hh8 : head < 8 := alignmentPrefix_lt_eight _ _
  have hsum : head + 8 * words + tail = length := remaining_split _ _ hh
  have hne (pc : BitVec 64) (hl : 0x1024b0 ≤ pc.toNat) (hu : pc.toNat < 0x1024df) :
      pc ≠ boundary.rip := by intro he; subst pc; omega
  obtain ⟨n₀, u, ha₀, hru, hcu, heu⟩ := memcpy_head_prepare boundary hb s hr hc hp.rip
  have hu := CopyState.head hru hcu heu
  have hcountu : (rcx.read u).toNat = head := by
    rw [heu.writes.2.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by change head < 2^64; omega)]
  obtain ⟨n₁, v, ha₁, hv, hipv, hagv⟩ := hu.movsb hstride hp 0x1024c7 heu.rip
    (program_text_slice hu.code 0x24c7 2 (by decide +kernel))
    (text_address_add 0x24c7 2 (by decide +kernel))
    (by rw [hcountu]; omega) boundary
    (hne 0x1024c7 (by decide) (by decide)) (hne 0x1024c9 (by decide) (by decide))
  have hv' : CopyState s v head := by
    simpa only [Nat.zero_add, hcountu] using hv
  have hrdxv : (rdx.read v).toNat = length := by
    rw [hagv.read (by simp), heu.agrees.read (by
      simp [memcpyHeadEffect, Effect.components, r8])]
  have hr8v : (r8.read v).toNat = head := by
    rw [hagv.read (by simp), heu.writes.2.1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by change head < 2^64; omega)]
  have hcwords : CodeIn (codeRange 0x1024c9 memcpyWordsBytes) v :=
    program_text_slice hv'.code 0x24c9 10 (by decide +kernel)
  obtain ⟨n₂, w, ha₂, hrw, _, hew⟩ := memcpy_words_prepare boundary
    (hne 0x1024cc (by decide) (by decide)) (hne 0x1024cf (by decide) (by decide))
    (hne 0x1024d3 (by decide) (by decide)) v hv'.ready hcwords hipv
  have haw : AgreesExcept [.reg 1, .reg 2, .flags, .rip] v w := by
    apply hew.agrees.mono
    simp [memcpyWordsEffect, Effect.components, rdx]
  have hw := hv'.registers hrw haw
  have hremaining : (rdx.read w).toNat = length - head := by
    rw [hew.writes.1,
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hr8v, hrdxv]; exact hh), hrdxv, hr8v]
  have hcountw : (rcx.read w).toNat = words := by
    rw [hew.writes.2, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hr8v, hrdxv]; exact hh), hrdxv, hr8v]
  have halign : 0 < (rcx.read w).toNat → (rdi.read w).toNat % 8 = 0 := by
    intro hpos
    rw [hw.destination, toNat_add_ofNat _ _ (by have := hp.dst.readable.low; omega)]
    apply alignmentPrefix_aligned
    rw [hcountw] at hpos
    change head < length
    omega
  obtain ⟨n₃, x, ha₃, hx, hipx, hagx⟩ := hw.movsq hstride hp 0x1024d3 hew.rip
    (program_text_slice hw.code 0x24d3 3 (by decide +kernel))
    (text_address_add 0x24d3 3 (by decide +kernel))
    (by rw [hcountw]; omega) halign boundary
    (hne 0x1024d3 (by decide) (by decide)) (hne 0x1024d6 (by decide) (by decide))
  have hx' : CopyState s x (head + 8 * words) := by
    simpa only [hcountw] using hx
  have hrdxx : (rdx.read x).toNat = length - head := by
    rw [hagx.read (by simp), hremaining]
  have hctail : CodeIn (codeRange 0x1024d6 memcpyTailBytes) x :=
    program_text_slice hx'.code 0x24d6 6 (by decide +kernel)
  obtain ⟨n₄, y, ha₄, hry, _, hey⟩ := memcpy_tail_prepare boundary
    (hne 0x1024d9 (by decide) (by decide)) (hne 0x1024dc (by decide) (by decide))
    x hx'.ready hctail hipx
  have hay : AgreesExcept [.reg 1, .reg 2, .flags, .rip] x y := by
    apply hey.agrees.mono
    simp [memcpyTailEffect, Effect.components, rdx]
  have hy := hx'.registers hry hay
  have hcounty : (rcx.read y).toNat = tail := by
    rw [hey.writes.2, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64),
      mask7_toNat _ (by decide), BitVec.toNat_setWidth, hrdxx]
    omega
  obtain ⟨n₅, t, ha₅, ht, hipt, _⟩ := hy.movsb hstride hp 0x1024dc hey.rip
    (program_text_slice hy.code 0x24dc 2 (by decide +kernel))
    (text_address_add 0x24dc 2 (by decide +kernel))
    (by rw [hcounty]; omega) boundary
    (hne 0x1024dc (by decide) (by decide)) (hne 0x1024de (by decide) (by decide))
  have ht' : CopyState s t length := by
    simpa only [hcounty, hsum] using ht
  refine ⟨n₀ + n₁ + n₂ + n₃ + n₄ + n₅, t,
    ((((ha₀.trans ha₁).trans ha₂).trans ha₃).trans ha₄).trans ha₅,
    ⟨ht'.ready, ?_, ht'.result, copyChanges_callChanges ht'.agrees⟩,
    ht'.code, hipt, ht'.copy⟩
  exact ht'.agrees.read (r := 4) (n := 64) (by simp [copyChanges])

end Md5.Proofs.MemoryRoutines
