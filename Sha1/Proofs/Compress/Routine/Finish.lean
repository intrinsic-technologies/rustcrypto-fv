import Sha1.Proofs.Compress.Routine.Frame
import X86Proofs.Instructions.Call.Triple
import Sha1.Proofs.Compress.Machine.Segment
import Sha1.Proofs.Compress.Stores
import Sha1.Proofs.Common.OutputFrame
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

namespace Sha1.Proofs.Compress.Routine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Refine
open Sha1.Spec Sha1.Spec.Program Standards.NIST Sha1.Proofs.Compress.Machine

def storesEffect : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (movM32R32Effect 0x1036bc 8 (.base 1 (.d8 4)))
    (movM32R32LowEffect 0x1036c0 2 (.base 1 (.d8 8))))
    (movM32R32Effect 0x1036c3 10 (.base 1 (.d8 12))))
    (movM32R32LowEffect 0x1036c7 0 (.base 1 (.d8 16))))
    (movM32R32Effect 0x1036ca 11 (.base 1 .none))

theorem output_inside {out : BitVec 64} {s : RamState}
    (h : Common.StoreRegion Extracted.programImage s.external ⟨out.toNat,20⟩)
    (off len : Nat) (hb : off + len ≤ 20) :
    InRegion ⟨out.toNat,20⟩ (out + BitVec.ofNat 64 off) len := by
  have hlo : out.toNat + 20 < 2 ^ 32 := h.bounded
  simp only [InRegion, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
  exact ⟨by omega, by omega, by omega⟩

theorem output_region_of_holds {out : BitVec 64} {s t : RamState} {e : Effect}
    (h : Common.StoreRegion Extracted.programImage s.external ⟨out.toNat,20⟩)
    (he : e.Holds s t) :
    Common.StoreRegion Extracted.programImage t.external ⟨out.toNat,20⟩ := by
  refine ⟨h.bounded, ?_, h.avoids⟩
  intro x hx
  exact Option.isSome_iff_exists.mp
    (he.agrees.grow x (Option.isSome_iff_exists.mpr (h.allocated x hx)))

theorem output_pre {out p : BitVec 64} {s : RamState} {addr : RamState → BitVec 64}
    {off codeLen : Nat}
    (h : Common.StoreRegion Extracted.programImage s.external ⟨out.toNat,20⟩)
    (hrip : s.RIP = p) (ha : addr s = out + BitVec.ofNat 64 off) (hb : off + 4 ≤ 20)
    (hc : ∀ i < codeLen, InProgram (p + BitVec.ofNat 64 i)) :
    Common.Instructions.StorePre.StorePre p codeLen addr 4 s := by
  have hin := output_inside h off 4 hb
  refine ⟨hrip, ?_, ?_⟩
  · rw [ha]
    refine ⟨Nat.le_trans hin.2.1 (Nat.le_of_lt h.bounded), ?_, ?_⟩
    · intro i hi
      exact Option.isSome_iff_exists.mpr (h.allocated _ (Common.StoreRegion.contains_byte hin hi))
    · intro i hi ht
      exact h.avoids _ (Common.StoreRegion.contains_byte hin hi) (.inr ht)
  · rw [ha]
    intro i hi j hj he
    exact h.avoids _ (Common.StoreRegion.contains_byte hin hi) (.inl (he ▸ hc j hj))

theorem output_avoid {out : BitVec 64} {s : RamState} {e : Effect} {off : Nat}
    {code : CodeMap}
    (h : Common.StoreRegion Extracted.programImage s.external ⟨out.toNat,20⟩)
    (he : e.components = [.mem (out + BitVec.ofNat 64 off) 4, .rip])
    (hb : off + 4 ≤ 20) (hc : ∀ x ∈ code, x ∈ Extracted.programImage) :
    e.Avoids code := by
  intro x hx c hcc hcov
  rw [he] at hcc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcc
  rcases hcc with rfl | rfl
  · obtain ⟨i, hi, ha⟩ := hcov
    exact h.avoids _ (Common.StoreRegion.contains_byte (output_inside h off 4 hb) hi)
      (.inl ⟨x.2, ha ▸ hc x hx⟩)
  · exact hcov.elim

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
theorem stores_block [Bindings] (boundary : ReturnBoundary)
    (hout : OutsideCompression boundary.rip) (out : BitVec 64) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1036bc ∧ (Operand.reg 1 : Operand 64).read s = out ∧
        Common.StoreRegion Extracted.programImage s.external ⟨out.toNat,20⟩)
      (codeRange 0x1036bc [0x44,0x89,0x41,4,0x89,0x51,8,0x44,0x89,0x51,12,
        0x89,0x41,16,0x44,0x89,0x19]) storesEffect := by
  have hBoundary (i : Nat) (hi : i < 18) :
      (0x1036bc : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip := by
    apply outsideCompression_ne hout
    all_goals simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    all_goals omega
  have hsub : ∀ x ∈ codeRange 0x1036bc
      [0x44,0x89,0x41,4,0x89,0x51,8,0x44,0x89,0x51,12,0x89,0x41,16,0x44,0x89,0x19],
      x ∈ Extracted.programImage :=
    program_text_subset 0x36bc (by decide +kernel) (by decide +kernel)
  unfold storesEffect
  sha1_run_begin_manual (Common.Instructions.MovStore.mov_m32_r32_effect_step
    0x1036bc 0x44 (by decide +kernel) 0 (.base 1 (.d8 4)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  case pre =>
    intro s hP
    refine output_pre hP.2.2 hP.1 (off := 4) ?_ (by decide +kernel) ?_
    · sha1_norm
      change (Operand.reg 1 : Operand 64).read s + 4 = out + 4
      rw [hP.2.1]
    · exact program_text_range 0x36bc 4 (by decide +kernel)
  case av =>
    intro s hP
    apply output_avoid hP.2.2 (off := 4) _ (by decide +kernel) hsub
    sha1_norm
    change [Component.mem ((Operand.reg 1 : Operand 64).read s + 4) 4, Component.rip] = _
    rw [hP.2.1]
    all_goals rfl
  sha1_run_then_manual (Common.Instructions.MovStore.mov_m32_r32_low_effect_step
    0x1036c0 2 (.base 1 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case mid =>
    intro s t hP hH hO
    have hcx : (Operand.reg 1 : Operand 64).read t = out := by
      rw [← (hO true).read_reg]
      sha1_norm
      exact hP.2.1
    have hregion := output_region_of_holds hP.2.2 hH
    refine ⟨?_, ?_⟩
    · refine output_pre hregion (hH.rip_of rfl) (off := 8) ?_ (by decide +kernel) ?_
      · sha1_norm
        change (Operand.reg 1 : Operand 64).read t + 8 = out + 8
        rw [hcx]
      · exact program_text_range 0x36c0 3 (by decide +kernel)
    · apply output_avoid hregion (off := 8) _ (by decide +kernel) hsub
      sha1_norm
      change [Component.mem ((Operand.reg 1 : Operand 64).read t + 8) 4, Component.rip] = _
      rw [hcx]
      all_goals rfl
  sha1_run_then_manual (Common.Instructions.MovStore.mov_m32_r32_effect_step
    0x1036c3 0x44 (by decide +kernel) 2 (.base 1 (.d8 12)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  case mid =>
    intro s t hP hH hO
    have hcx : (Operand.reg 1 : Operand 64).read t = out := by
      rw [← (hO true).read_reg]
      sha1_norm
      exact hP.2.1
    have hregion := output_region_of_holds hP.2.2 hH
    refine ⟨?_, ?_⟩
    · refine output_pre hregion (hH.rip_of rfl) (off := 12) ?_ (by decide +kernel) ?_
      · sha1_norm
        change (Operand.reg 1 : Operand 64).read t + 12 = out + 12
        rw [hcx]
      · exact program_text_range 0x36c3 4 (by decide +kernel)
    · apply output_avoid hregion (off := 12) _ (by decide +kernel) hsub
      sha1_norm
      change [Component.mem ((Operand.reg 1 : Operand 64).read t + 12) 4, Component.rip] = _
      rw [hcx]
      all_goals rfl
  sha1_run_then_manual (Common.Instructions.MovStore.mov_m32_r32_low_effect_step
    0x1036c7 0 (.base 1 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case mid =>
    intro s t hP hH hO
    have hcx : (Operand.reg 1 : Operand 64).read t = out := by
      rw [← (hO true).read_reg]
      sha1_norm
      exact hP.2.1
    have hregion := output_region_of_holds hP.2.2 hH
    refine ⟨?_, ?_⟩
    · refine output_pre hregion (hH.rip_of rfl) (off := 16) ?_ (by decide +kernel) ?_
      · sha1_norm
        change (Operand.reg 1 : Operand 64).read t + 16 = out + 16
        rw [hcx]
      · exact program_text_range 0x36c7 3 (by decide +kernel)
    · apply output_avoid hregion (off := 16) _ (by decide +kernel) hsub
      sha1_norm
      change [Component.mem ((Operand.reg 1 : Operand 64).read t + 16) 4, Component.rip] = _
      rw [hcx]
      all_goals rfl
  sha1_run_then_manual (Common.Instructions.MovStore.mov_m32_r32_effect_step
    0x1036ca 0x44 (by decide +kernel) 3 (.base 1 .none) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  case mid =>
    intro s t hP hH hO
    have hcx : (Operand.reg 1 : Operand 64).read t = out := by
      rw [← (hO true).read_reg]
      sha1_norm
      exact hP.2.1
    have hregion := output_region_of_holds hP.2.2 hH
    refine ⟨?_, ?_⟩
    · refine output_pre hregion (hH.rip_of rfl) (off := 0) ?_ (by decide +kernel) ?_
      · sha1_norm
        change (Operand.reg 1 : Operand 64).read t + 0 = out + 0
        rw [hcx]
      · exact program_text_range 0x36ca 3 (by decide +kernel)
    · apply output_avoid hregion (off := 0) _ (by decide +kernel) hsub
      sha1_norm
      change [Component.mem ((Operand.reg 1 : Operand 64).read t + 0) 4, Component.rip] = _
      rw [hcx]
      all_goals rfl
  intro h
  exact h

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
theorem stores_components {out : BitVec 64} {s : RamState}
    (hcx : (Operand.reg 1 : Operand 64).read s = out) :
    (storesEffect s).components =
      [.mem (out+4) 4,.mem (out+8) 4,.mem (out+12) 4,.mem (out+16) 4,.mem out 4,.rip] := by
  sha1_norm [storesEffect]
  change [Component.mem ((Operand.reg 1 : Operand 64).read s + 4) 4,
    .mem ((Operand.reg 1 : Operand 64).read s + 8) 4,
    .mem ((Operand.reg 1 : Operand 64).read s + 12) 4,
    .mem ((Operand.reg 1 : Operand 64).read s + 16) 4,
    .mem ((Operand.reg 1 : Operand 64).read s + 0) 4,.rip] = _
  rw [hcx]
  rw [show out + (0 : BitVec 64) = out by bv_omega]
  rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
theorem stores_after_memory {out : BitVec 64} {H : Vector (BitVec 32) 5} {s : RamState}
    (hcx : (Operand.reg 1 : Operand 64).read s = out) (hr : LoopRegisters H s) :
    ((storesEffect s).after s true).external = stateMemory s.external out H := by
  obtain ⟨h11,h8,h2,h10,h0⟩ := hr
  change (applyWrites s (storesEffect s).writes).external = _
  sha1_norm [storesEffect]
  simp only [BitVec.add_zero]
  change stateMemory s.external ((Operand.reg 1 : Operand 64).read s)
    #v[(Operand.reg 11 : Operand 32).read s,(Operand.reg 8 : Operand 32).read s,
      (Operand.reg 2 : Operand 32).read s,(Operand.reg 10 : Operand 32).read s,
      (Operand.reg 0 : Operand 32).read s] = _
  rw [hcx,h11,h8,h2,h10,h0]
  congr 1
  apply Vector.ext
  intro i hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
theorem stores_words {out : BitVec 64} {H : Vector (BitVec 32) 5} {s t : RamState}
    (hcx : (Operand.reg 1 : Operand 64).read s = out)
    (hr : LoopRegisters H s) (he : (storesEffect s).Holds s t) :
    ∀ i : Fin 5, memLoad t.external (out + BitVec.ofNat 64 (4*i.val)) 32 = H[i] := by
  have hfull : ∀ w ∈ (storesEffect s).writes, w.Full := by
    apply Effect.Local.full
    unfold storesEffect
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hm := stores_after_memory hcx hr
  intro i
  apply Eq.trans _ (stateMemory_words s.external out H i)
  apply memLoad_congr
  intro j hj
  rw [← hm]
  exact (ho.mem _).symm

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
theorem stores_frame {out : BitVec 64} {s t : RamState}
    (hcx : (Operand.reg 1 : Operand 64).read s = out)
    (hr : Common.StoreRegion Extracted.programImage s.external ⟨out.toNat,20⟩)
    (he : (storesEffect s).Holds s t) :
    RamWriteFrame s.external t.external [⟨out.toNat,20⟩] := by
  refine ⟨?_,he.agrees.grow⟩
  intro x hx
  apply he.agrees.byte
  intro comp hc hcov
  rw [stores_components hcx] at hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  have hs : ∃ off : Nat, off + 4 ≤ 20 ∧ comp = .mem (out + BitVec.ofNat 64 off) 4 := by
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨4,by decide,rfl⟩
    · exact ⟨8,by decide,rfl⟩
    · exact ⟨12,by decide,rfl⟩
    · exact ⟨16,by decide,rfl⟩
    · exact ⟨0,by decide,by rw [BitVec.add_zero]⟩
    · exact hcov.elim
  obtain ⟨off,hb,rfl⟩ := hs
  obtain ⟨i,hi,ha⟩ := hcov
  have hi' := Common.StoreRegion.contains_byte (output_inside hr off 4 hb) hi
  have hx' := hx.2 ⟨out.toNat,20⟩ (List.mem_singleton_self _)
  rw [ha] at hx'
  change (out + BitVec.ofNat 64 off + BitVec.ofNat 64 i).toNat + 1 ≤ out.toNat ∨
    out.toNat + 20 ≤ (out + BitVec.ofNat 64 off + BitVec.ofNat 64 i).toNat at hx'
  change out.toNat ≤ (out + BitVec.ofNat 64 off + BitVec.ofNat 64 i).toNat ∧
    (out + BitVec.ofNat 64 off + BitVec.ofNat 64 i).toNat < out.toNat + 20 at hi'
  rcases hx' with hx' | hx' <;> omega

def restoreEffect : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (addR64Imm32Effect 0x1036cd 4 160)
    (popR64Effect 0x1036d4 1 3))
    (popR64Effect 0x1036d5 2 12))
    (popR64Effect 0x1036d7 2 13))
    (popR64Effect 0x1036d9 2 14))
    (popR64Effect 0x1036db 2 15))
    (popR64Effect 0x1036dd 1 5)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
theorem restore_block [Bindings] (boundary : ReturnBoundary)
    (hout : OutsideCompression boundary.rip) (base : BitVec 64) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1036cd ∧ stackPtr s = base ∧ MemReadable s base 216)
      (codeRange 0x1036cd [0x48,0x81,0xc4,0xa0,0,0,0,0x5b,0x41,0x5c,0x41,0x5d,
        0x41,0x5e,0x41,0x5f,0x5d]) restoreEffect := by
  have hBoundary (i : Nat) (hi : i < 18) :
      (0x1036cd : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip := by
    apply outsideCompression_ne hout
    all_goals simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    all_goals omega
  have hAdd : StepEffect (fun s ↦ s.RIP = 0x1036cd)
      (codeRange 0x1036cd [0x48,0x81,0xc4,0xa0,0,0,0]) (addR64Imm32Effect 0x1036cd 4 160) :=
    add_r64_imm32_effect_step 0x1036cd 0x48 0xc4 160 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hPop3 : StepEffect (PopPre 0x1036d4) (codeRange 0x1036d4 [0x5b])
      (popR64Effect 0x1036d4 1 3) := pop_r64_effect_step 0x1036d4 0x5b (by decide) (by decide)
  have hPop12 : StepEffect (PopPre 0x1036d5) (codeRange 0x1036d5 [0x41,0x5c])
      (popR64Effect 0x1036d5 2 12) := pop_r64_rex_effect_step 0x1036d5 0x41 0x5c (by decide) (by decide) (by decide)
  have hPop13 : StepEffect (PopPre 0x1036d7) (codeRange 0x1036d7 [0x41,0x5d])
      (popR64Effect 0x1036d7 2 13) := pop_r64_rex_effect_step 0x1036d7 0x41 0x5d (by decide) (by decide) (by decide)
  have hPop14 : StepEffect (PopPre 0x1036d9) (codeRange 0x1036d9 [0x41,0x5e])
      (popR64Effect 0x1036d9 2 14) := pop_r64_rex_effect_step 0x1036d9 0x41 0x5e (by decide) (by decide) (by decide)
  have hPop15 : StepEffect (PopPre 0x1036db) (codeRange 0x1036db [0x41,0x5f])
      (popR64Effect 0x1036db 2 15) := pop_r64_rex_effect_step 0x1036db 0x41 0x5f (by decide) (by decide) (by decide)
  have hPop5 : StepEffect (PopPre 0x1036dd) (codeRange 0x1036dd [0x5d])
      (popR64Effect 0x1036dd 1 5) := pop_r64_effect_step 0x1036dd 0x5d (by decide) (by decide)
  unfold restoreEffect
  sha1_run_begin hAdd
  sha1_run_then_manual hPop3
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of rfl, ?_⟩, popR64Effect_avoids _ _ _ _ _⟩
    have hs : stackPtr t = base + 160 := by
      change (Operand.reg 4 : Operand 64).read t = _
      rw [← (hO true).read_reg]
      have hbase : (Operand.reg 4 : Operand 64).read s = base := hP.2.1
      sha1_norm
      change (Operand.reg 4 : Operand 64).read s + 160 = base + 160
      exact congrArg (fun x : BitVec 64 ↦ x + 160) hbase
    rw [hs]
    exact (memReadable_slice hP.2.2 160 8 (by decide)).of_holds hH
  sha1_run_then_manual hPop12
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of rfl, ?_⟩, popR64Effect_avoids _ _ _ _ _⟩
    have hs : stackPtr t = base + 168 := by
      change (Operand.reg 4 : Operand 64).read t = _
      rw [← (hO true).read_reg]
      have hbase : (Operand.reg 4 : Operand 64).read s = base := hP.2.1
      sha1_norm
      change (Operand.reg 4 : Operand 64).read s + 168 = base + 168
      rw [hbase]
    rw [hs]
    exact (memReadable_slice hP.2.2 168 8 (by decide)).of_holds hH
  sha1_run_then_manual hPop13
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of rfl, ?_⟩, popR64Effect_avoids _ _ _ _ _⟩
    have hs : stackPtr t = base + 176 := by
      change (Operand.reg 4 : Operand 64).read t = _
      rw [← (hO true).read_reg]
      have hbase : (Operand.reg 4 : Operand 64).read s = base := hP.2.1
      sha1_norm
      change (Operand.reg 4 : Operand 64).read s + 176 = base + 176
      rw [hbase]
    rw [hs]
    exact (memReadable_slice hP.2.2 176 8 (by decide)).of_holds hH
  sha1_run_then_manual hPop14
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of rfl, ?_⟩, popR64Effect_avoids _ _ _ _ _⟩
    have hs : stackPtr t = base + 184 := by
      change (Operand.reg 4 : Operand 64).read t = _
      rw [← (hO true).read_reg]
      have hbase : (Operand.reg 4 : Operand 64).read s = base := hP.2.1
      sha1_norm
      change (Operand.reg 4 : Operand 64).read s + 184 = base + 184
      rw [hbase]
    rw [hs]
    exact (memReadable_slice hP.2.2 184 8 (by decide)).of_holds hH
  sha1_run_then_manual hPop15
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of rfl, ?_⟩, popR64Effect_avoids _ _ _ _ _⟩
    have hs : stackPtr t = base + 192 := by
      change (Operand.reg 4 : Operand 64).read t = _
      rw [← (hO true).read_reg]
      have hbase : (Operand.reg 4 : Operand 64).read s = base := hP.2.1
      sha1_norm
      change (Operand.reg 4 : Operand 64).read s + 192 = base + 192
      rw [hbase]
    rw [hs]
    exact (memReadable_slice hP.2.2 192 8 (by decide)).of_holds hH
  sha1_run_then_manual hPop5
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of rfl, ?_⟩, popR64Effect_avoids _ _ _ _ _⟩
    have hs : stackPtr t = base + 200 := by
      change (Operand.reg 4 : Operand 64).read t = _
      rw [← (hO true).read_reg]
      have hbase : (Operand.reg 4 : Operand 64).read s = base := hP.2.1
      sha1_norm
      change (Operand.reg 4 : Operand 64).read s + 200 = base + 200
      rw [hbase]
    rw [hs]
    exact (memReadable_slice hP.2.2 200 8 (by decide)).of_holds hH
  intro h
  exact h

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
theorem restore_values {base : BitVec 64} {s t : RamState}
    (hsp : stackPtr s = base) (he : (restoreEffect s).Holds s t) :
    (∀ i : Fin 6, (Operand.reg (#[3,12,13,14,15,5][i.val]) : Operand 64).read t =
      memLoad s.external (base + BitVec.ofNat 64 (160 + 8 * i.val)) 64) ∧
    stackPtr t = base + 208 ∧ t.RIP = 0x1036de ∧
    AgreesExcept [.reg 3,.reg 4,.reg 5,.reg 12,.reg 13,.reg 14,.reg 15,.flags,.rip] s t := by
  have hfull : ∀ w ∈ (restoreEffect s).writes, w.Full := by
    apply Effect.Local.full
    unfold restoreEffect
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  refine ⟨?_, ?_, he.rip.trans rfl, ?_⟩
  · intro ⟨i,hi⟩
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      change (Operand.reg _ : Operand 64).read t = _
      rw [← ho.read_reg]
      sha1_norm [restoreEffect]
    all_goals
      change memLoad s.external ((Operand.reg 4 : Operand 64).read s + _) 64 = _
      change (Operand.reg 4 : Operand 64).read s = base at hsp
      rw [hsp]
    all_goals rfl
  · change (Operand.reg 4 : Operand 64).read t = _
    rw [← ho.read_reg]
    sha1_norm [restoreEffect]
    change (Operand.reg 4 : Operand 64).read s + 208 = base + 208
    exact congrArg (fun x : BitVec 64 ↦ x + 208) hsp
  · apply he.agrees.mono
    intro c hc
    sha1_norm [restoreEffect] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide +kernel

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
theorem memory_eq_stateMemory {out : BitVec 64} {H : Vector (BitVec 32) 5}
    {mem result : Ram} (hbound : out.toNat + 20 ≤ 2 ^ 64)
    (halloc : ∀ i < 20, (mem[out + BitVec.ofNat 64 i]?).isSome)
    (hframe : RamWriteFrame mem result [⟨out.toNat,20⟩])
    (hwords : ∀ i : Fin 5, memLoad result (out + BitVec.ofNat 64 (4*i.val)) 32 = H[i]) :
    result = stateMemory mem out H := by
  have ht : ∀ i < 20, (result[out + BitVec.ofNat 64 i]?).isSome :=
    fun i hi ↦ hframe.present _ (halloc i hi)
  have hb := stateBytes_of_words hwords ht
  have hs := stateMemory_hasBytes mem out H halloc
  have hf := stateMemory_frame mem out H hbound
  apply Std.ExtHashMap.ext_getElem?
  intro x
  by_cases hx : out.toNat ≤ x.toNat ∧ x.toNat < out.toNat + 20
  · let i : Fin 20 := ⟨x.toNat - out.toNat, by omega⟩
    have he : BitVec.ofNat 64 (out.toNat + i.val) = x := by
      rw [show out.toNat + i.val = x.toNat by dsimp [i]; omega]
      rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]
    have hi : i.val < (ByteArray.mk (Hasher.stateBytes H).toArray).size := by
      change i.val < (Hasher.stateBytes H).toArray.size
      rw [Vector.size_toArray]
      exact i.isLt
    have ht' := hb.2 ⟨i.val,hi⟩
    have hs' := hs.2 ⟨i.val,hi⟩
    rw [he] at ht' hs'
    exact ht'.trans hs'.symm
  · have ho : Outside [⟨out.toNat,20⟩] x 1 := by
      refine ⟨?_, ?_⟩
      · have := x.isLt
        omega
      · intro r hr
        obtain rfl := List.mem_singleton.mp hr
        change x.toNat + 1 ≤ out.toNat ∨ out.toNat + 20 ≤ x.toNat
        omega
    exact (hframe.outside x ho).trans (hf.outside x ho).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
theorem finishCorrect : FinishCorrect := by
  intro bindings c hv s hReady hCode hRip hAt
  letI := bindings
  have hf := hAt.frame
  have hLoad : StepEffect
      (LoadPre 0x1036b4 (fun s ↦ (.sib 4 none 0 (.d32 128) : AddrMode).addr s 0x1036bc) 8)
      (codeRange 0x1036b4 [0x48,0x8b,0x8c,0x24,0x80,0,0,0])
      (movR64M64Effect 0x1036b4 1 (.sib 4 none 0 (.d32 128))) :=
    mov_r64_m64_effect_step 0x1036b4 0x48 (by decide +kernel) 1
      (.sib 4 none 0 (.d32 128)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hpre : LoadPre 0x1036b4
      (fun s ↦ (.sib 4 none 0 (.d32 128) : AddrMode).addr s 0x1036bc) 8 s := by
    refine ⟨hRip, ?_⟩
    change MemReadable s (stackPtr s + 128) 8
    rw [hf.stackPointer]
    exact memReadable_slice hf.writable.readable 128 8 (by decide)
  have hCodeLoad : CodeIn (codeRange 0x1036b4 [0x48,0x8b,0x8c,0x24,0x80,0,0,0]) s :=
    program_text_slice hCode 0x36b4 8 (by decide +kernel)
  obtain ⟨s1,ha1,hr1,he1⟩ := hLoad.advances hReady hCodeLoad hpre
    (by
      simpa [movR64M64Effect] using
        (outsideCompression_ne hv.outside (by decide +kernel) (by decide +kernel)))
  have hag1 : AgreesExcept [.reg 1,.rip] s s1 := he1.agrees
  have hm1 : s1.external = s.external := hag1.external (by simp [Component.Covers])
  have hc1 := CodeIn.of_external_eq hm1 hCode
  have hf1 : Frame c s1 := hf.of_agrees hv (hag1.mono (by
    intro comp hcomp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hcomp
    rcases hcomp with rfl | rfl <;> simp [scratchComponents]))
  have hcx : (Operand.reg 1 : Operand 64).read s1 = c.initial.regValue .rdi := by
    have hw := he1.writes
    change (Operand.reg 1 : Operand 64).read s1 = memLoad s.external (stackPtr s+128) 64 at hw
    rw [hf.stackPointer,hf.output] at hw
    exact hw
  have hregs : LoopRegisters (c.state c.count) s1 := by
    obtain ⟨h11,h8,h2,h10,h0⟩ := hAt.registers
    exact ⟨(hag1.read (by decide)).trans h11,(hag1.read (by decide)).trans h8,
      (hag1.read (by decide)).trans h2,(hag1.read (by decide)).trans h10,
      (hag1.read (by decide)).trans h0⟩
  have hstore := hv.outputStoreRegion hf1
  obtain ⟨n2,s2,ha2,hr2,_,he2⟩ :=
    stores_block (returnBoundary c.initial) hv.outside (c.initial.regValue .rdi)
      s1 hr1 (program_text_slice hc1 0x36bc 17 (by decide +kernel)) ⟨he1.rip,hcx,hstore⟩
  have hm2 := stores_frame hcx hstore he2
  have hwords := stores_words hcx hregs he2
  have halloc : ∀ i < 20,
      (s1.external[c.initial.regValue .rdi + BitVec.ofNat 64 i]?).isSome := by
    have hinit := ((stateBytes_hasBytes_iff (m:=c.initial.external)
      (base:=c.initial.regValue .rdi) (H:=c.H)).mp hv.call.outputInMemory.2.2).1
    intro i hi
    exact hf1.memory.present _ (hinit i hi)
  have hbound : (c.initial.regValue .rdi).toNat + 20 ≤ 2 ^ 64 := by
    have hb : (c.initial.regValue .rdi).toNat + 20 < 2 ^ 32 := hstore.bounded
    omega
  have hext : s2.external = stateMemory s1.external (c.initial.regValue .rdi) (c.state c.count) :=
    memory_eq_stateMemory hbound halloc hm2 hwords
  have hc2 : CodeIn Extracted.programImage s2 := by
    intro x hx
    refine ⟨(hc1 x hx).1, ?_⟩
    rw [hm2.outside x.1 ?_]
    · exact (hc1 x hx).2
    · refine ⟨by have := x.1.isLt; omega, ?_⟩
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      have hn : ¬ ((Compress.outputRegion c.initial).Contains x.1.toNat) :=
        fun hin ↦ hstore.avoids _ hin (.inl ⟨x.2,hx⟩)
      change ¬ ((c.initial.regValue .rdi).toNat ≤ x.1.toNat ∧
        x.1.toNat < (c.initial.regValue .rdi).toNat + 20) at hn
      change x.1.toNat + 1 ≤ (c.initial.regValue .rdi).toNat ∨
        (c.initial.regValue .rdi).toNat + 20 ≤ x.1.toNat
      omega
  have hcomponents := stores_components hcx
  have hag2 : AgreesExcept (storesEffect s1).components s1 s2 := he2.agrees
  have hsp2 : stackPtr s2 = c.stack := by
    exact (hag2.read (r:=4) (n:=64) (by rw [hcomponents]; simp)).trans hf1.stackPointer
  have hread2 : MemReadable s2 c.stack 216 := hf1.writable.readable.of_holds he2
  obtain ⟨n3,s3,ha3,hr3,_,he3⟩ := restore_block (returnBoundary c.initial) hv.outside c.stack
    s2 hr2 (program_text_slice hc2 0x36cd 17 (by decide +kernel))
    ⟨he2.rip,hsp2,hread2⟩
  obtain ⟨hvals,hsp3,hip3,hag3⟩ := restore_values hsp2 he3
  have hm3 : s3.external = s2.external := hag3.external (by simp [Component.Covers])
  have hsp3' : stackPtr s3 = c.sp := hsp3.trans (by
    change c.sp - 208 + 208 = c.sp
    bv_omega)
  have htop3 : stackTop s3 = (returnBoundary c.initial).rip := by
    change memLoad s3.external (stackPtr s3) 64 = memLoad c.initial.external c.sp 64
    rw [hm3,hsp3']
    have he : c.sp = c.stack + BitVec.ofNat 64 208 := by
      change c.sp = c.sp - 208 + 208
      bv_omega
    rw [he,hm2.memLoad_eq (k:=64) (a:=c.stack + BitVec.ofNat 64 208)
      (hv.stack_outside_output (off:=208) (len:=8) (by decide)),← he]
    exact hf1.callerReturn
  have hRet : RetPre 0x1036de s3 := by
    refine ⟨⟨hip3, ?_⟩, ?_⟩
    · rw [hsp3']
      have he : c.sp = c.stack + BitVec.ofNat 64 208 := by
        change c.sp = c.sp - 208 + 208
        bv_omega
      rw [he]
      exact (memReadable_slice hread2 208 8 (by decide)).of_external_eq hm3
    · rw [htop3]
      exact hv.returnLow
  have hc3 := CodeIn.of_external_eq hm3 hc2
  obtain ⟨t,hret,hrt,het⟩ := ret_effect_step 0x1036de s3 hr3
    (program_text_slice hc3 0x36de 1 (by decide +kernel)) hRet
  have hReturns : Returns (returnBoundary c.initial) 1 s3 t := by
    apply Returns.of_step hret
    · exact het.rip.trans htop3
    · have hw : stackPtr t = stackPtr s3 + 8 := het.writes
      exact hw.trans (congrArg (fun x : BitVec 64 ↦ x+8) hsp3')
  have hfinalRip : t.RIP = (returnBoundary c.initial).rip := het.rip.trans htop3
  have hfinalRsp : stackPtr t = (returnBoundary c.initial).rsp := by
    have hw : stackPtr t = stackPtr s3 + 8 := het.writes
    exact hw.trans (congrArg (fun x : BitVec 64 ↦ x+8) hsp3')
  have hagt := het.agrees
  have hmt : t.external = s3.external := hagt.external (by simp [Component.Covers])
  have hdf2 : DirectionFlagUnset s2 :=
    hag2.directionFlagClear (by rw [hcomponents]; simp) hf1.directionFlag
  have hagFinal : AgreesExcept (compressionChanges c) c.initial t :=
    (((hAt.agrees.trans hag1).trans hag2).trans hag3).trans hagt |>.mono (by
      intro comp hc
      rw [hcomponents] at hc
      simp [compressionChanges, frameComponents, Machine.scratchComponents] at hc ⊢
      grind)
  refine ⟨_,t,ha1.returns (ha2.returns (ha3.returns hReturns)),hrt,?_⟩
  refine ⟨?_,hagt.directionFlagClear (by simp) (hag3.directionFlagClear (by decide) hdf2),
    ?_,?_,hagt.rest.trans (hag3.rest.trans (hag2.rest.trans hf1.controls)),hagFinal,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    have hsaved (i : Fin 6) :
        (Operand.reg (#[3,12,13,14,15,5][i.val]) : Operand 64).read t =
        (Operand.reg (#[3,12,13,14,15,5][i.val]) : Operand 64).read c.initial := by
      have hn : ∀ j : Fin 6, (Component.reg (#[3,12,13,14,15,5][j.val])) ∉
          [Component.reg 4,Component.rip] := by decide +kernel
      rw [hagt.read (hn i)]
      rw [hvals i,hm2.memLoad_eq (k:=64) (a:=c.stack + BitVec.ofNat 64 (160+8*i.val))
        (hv.stack_outside_output (by have := i.isLt; omega))]
      exact hf1.saved i
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0
    · exact hsaved 5
    · exact hsaved 1
    · exact hsaved 2
    · exact hsaved 3
    · exact hsaved 4
  · have hfStack : RamWriteFrame c.initial.external s1.external
        [Compress.outputRegion c.initial,c.stackRegion] := by
      refine ⟨fun x hx ↦ hf1.memory.outside x ⟨hx.1,?_⟩,hf1.memory.present⟩
      intro r hr
      exact hx.2 r (List.mem_cons_of_mem _ hr)
    have hfAll := hfStack.trans hm2 (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨Compress.outputRegion c.initial,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩)
    have hfFinal : RamWriteFrame c.initial.external t.external
        [Compress.outputRegion c.initial,c.stackRegion] := by
      rw [hmt,hm3]
      exact hfAll
    apply hfFinal.memoryWriteFrame
    intro x hx r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hx _ (by simp)
    · obtain rfl := List.mem_singleton.mp hr
      exact hx _ (by simp)
  · apply stateMemory_readOutput halloc
    rw [hmt,hm3]
    exact hext
  · have hb := stateMemory_hasBytes s1.external (c.initial.regValue .rdi) (c.state c.count) halloc
    rw [hmt, hm3, hext]
    exact ⟨hfinalRip, hfinalRsp, hb⟩


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
theorem finishAdvanceCorrect : FinishAdvanceCorrect := by
  intro bindings boundary c hv hBoundary hDifferent s hReady hCode hRip hAt
  letI := bindings
  have hf := hAt.frame
  have hLoad : StepEffect
      (LoadPre 0x1036b4 (fun s ↦ (.sib 4 none 0 (.d32 128) : AddrMode).addr s 0x1036bc) 8)
      (codeRange 0x1036b4 [0x48,0x8b,0x8c,0x24,0x80,0,0,0])
      (movR64M64Effect 0x1036b4 1 (.sib 4 none 0 (.d32 128))) :=
    mov_r64_m64_effect_step 0x1036b4 0x48 (by decide +kernel) 1
      (.sib 4 none 0 (.d32 128)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hpre : LoadPre 0x1036b4
      (fun s ↦ (.sib 4 none 0 (.d32 128) : AddrMode).addr s 0x1036bc) 8 s := by
    refine ⟨hRip, ?_⟩
    change MemReadable s (stackPtr s + 128) 8
    rw [hf.stackPointer]
    exact memReadable_slice hf.writable.readable 128 8 (by decide)
  have hCodeLoad : CodeIn (codeRange 0x1036b4 [0x48,0x8b,0x8c,0x24,0x80,0,0,0]) s :=
    program_text_slice hCode 0x36b4 8 (by decide +kernel)
  obtain ⟨s1,ha1,hr1,he1⟩ := hLoad.advances (boundary := boundary) hReady hCodeLoad hpre
    (by
      simpa [movR64M64Effect] using
        (outsideCompression_ne hBoundary (by decide +kernel) (by decide +kernel)))
  have hag1 : AgreesExcept [.reg 1,.rip] s s1 := he1.agrees
  have hm1 : s1.external = s.external := hag1.external (by simp [Component.Covers])
  have hc1 := CodeIn.of_external_eq hm1 hCode
  have hf1 : Frame c s1 := hf.of_agrees hv (hag1.mono (by
    intro comp hcomp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hcomp
    rcases hcomp with rfl | rfl <;> simp [scratchComponents]))
  have hcx : (Operand.reg 1 : Operand 64).read s1 = c.initial.regValue .rdi := by
    have hw := he1.writes
    change (Operand.reg 1 : Operand 64).read s1 = memLoad s.external (stackPtr s+128) 64 at hw
    rw [hf.stackPointer,hf.output] at hw
    exact hw
  have hregs : LoopRegisters (c.state c.count) s1 := by
    obtain ⟨h11,h8,h2,h10,h0⟩ := hAt.registers
    exact ⟨(hag1.read (by decide)).trans h11,(hag1.read (by decide)).trans h8,
      (hag1.read (by decide)).trans h2,(hag1.read (by decide)).trans h10,
      (hag1.read (by decide)).trans h0⟩
  have hstore := hv.outputStoreRegion hf1
  obtain ⟨n2,s2,ha2,hr2,_,he2⟩ :=
    stores_block boundary hBoundary (c.initial.regValue .rdi)
      s1 hr1 (program_text_slice hc1 0x36bc 17 (by decide +kernel)) ⟨he1.rip,hcx,hstore⟩
  have hm2 := stores_frame hcx hstore he2
  have hwords := stores_words hcx hregs he2
  have halloc : ∀ i < 20,
      (s1.external[c.initial.regValue .rdi + BitVec.ofNat 64 i]?).isSome := by
    have hinit := ((stateBytes_hasBytes_iff (m:=c.initial.external)
      (base:=c.initial.regValue .rdi) (H:=c.H)).mp hv.call.outputInMemory.2.2).1
    intro i hi
    exact hf1.memory.present _ (hinit i hi)
  have hbound : (c.initial.regValue .rdi).toNat + 20 ≤ 2 ^ 64 := by
    have hb : (c.initial.regValue .rdi).toNat + 20 < 2 ^ 32 := hstore.bounded
    omega
  have hext : s2.external = stateMemory s1.external (c.initial.regValue .rdi) (c.state c.count) :=
    memory_eq_stateMemory hbound halloc hm2 hwords
  have hc2 : CodeIn Extracted.programImage s2 := by
    intro x hx
    refine ⟨(hc1 x hx).1, ?_⟩
    rw [hm2.outside x.1 ?_]
    · exact (hc1 x hx).2
    · refine ⟨by have := x.1.isLt; omega, ?_⟩
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      have hn : ¬ ((Compress.outputRegion c.initial).Contains x.1.toNat) :=
        fun hin ↦ hstore.avoids _ hin (.inl ⟨x.2,hx⟩)
      change ¬ ((c.initial.regValue .rdi).toNat ≤ x.1.toNat ∧
        x.1.toNat < (c.initial.regValue .rdi).toNat + 20) at hn
      change x.1.toNat + 1 ≤ (c.initial.regValue .rdi).toNat ∨
        (c.initial.regValue .rdi).toNat + 20 ≤ x.1.toNat
      omega
  have hcomponents := stores_components hcx
  have hag2 : AgreesExcept (storesEffect s1).components s1 s2 := he2.agrees
  have hsp2 : stackPtr s2 = c.stack := by
    exact (hag2.read (r:=4) (n:=64) (by rw [hcomponents]; simp)).trans hf1.stackPointer
  have hread2 : MemReadable s2 c.stack 216 := hf1.writable.readable.of_holds he2
  obtain ⟨n3,s3,ha3,hr3,_,he3⟩ := restore_block boundary hBoundary c.stack
    s2 hr2 (program_text_slice hc2 0x36cd 17 (by decide +kernel))
    ⟨he2.rip,hsp2,hread2⟩
  obtain ⟨hvals,hsp3,hip3,hag3⟩ := restore_values hsp2 he3
  have hm3 : s3.external = s2.external := hag3.external (by simp [Component.Covers])
  have hsp3' : stackPtr s3 = c.sp := hsp3.trans (by
    change c.sp - 208 + 208 = c.sp
    bv_omega)
  have htop3 : stackTop s3 = (returnBoundary c.initial).rip := by
    change memLoad s3.external (stackPtr s3) 64 = memLoad c.initial.external c.sp 64
    rw [hm3,hsp3']
    have he : c.sp = c.stack + BitVec.ofNat 64 208 := by
      change c.sp = c.sp - 208 + 208
      bv_omega
    rw [he,hm2.memLoad_eq (k:=64) (a:=c.stack + BitVec.ofNat 64 208)
      (hv.stack_outside_output (off:=208) (len:=8) (by decide)),← he]
    exact hf1.callerReturn
  have hRet : RetPre 0x1036de s3 := by
    refine ⟨⟨hip3, ?_⟩, ?_⟩
    · rw [hsp3']
      have he : c.sp = c.stack + BitVec.ofNat 64 208 := by
        change c.sp = c.sp - 208 + 208
        bv_omega
      rw [he]
      exact (memReadable_slice hread2 208 8 (by decide)).of_external_eq hm3
    · rw [htop3]
      exact hv.returnLow
  have hc3 := CodeIn.of_external_eq hm3 hc2
  obtain ⟨t,hret,hrt,het⟩ := ret_effect_step 0x1036de s3 hr3
    (program_text_slice hc3 0x36de 1 (by decide +kernel)) hRet
  have hAdvanceRet : Advances boundary 1 s3 t := by
    apply Advances.of_step hret
    · exact Or.inl (by rw [het.rip.trans htop3]; exact hDifferent.symm)
  have hfinalRip : t.RIP = (returnBoundary c.initial).rip := het.rip.trans htop3
  have hfinalRsp : stackPtr t = (returnBoundary c.initial).rsp := by
    have hw : stackPtr t = stackPtr s3 + 8 := het.writes
    exact hw.trans (congrArg (fun x : BitVec 64 ↦ x + 8) hsp3')
  have hagt := het.agrees
  have hmt : t.external = s3.external := hagt.external (by simp [Component.Covers])
  have hdf2 : DirectionFlagUnset s2 :=
    hag2.directionFlagClear (by rw [hcomponents]; simp) hf1.directionFlag
  have hagFinal : AgreesExcept (compressionChanges c) c.initial t :=
    (((hAt.agrees.trans hag1).trans hag2).trans hag3).trans hagt |>.mono (by
      intro comp hc
      rw [hcomponents] at hc
      simp [compressionChanges, frameComponents, Machine.scratchComponents] at hc ⊢
      grind)
  refine ⟨_,t,ha1.trans (ha2.trans (ha3.trans hAdvanceRet)),hrt,?_⟩
  refine ⟨?_,hagt.directionFlagClear (by simp) (hag3.directionFlagClear (by decide) hdf2),
    ?_,?_,hagt.rest.trans (hag3.rest.trans (hag2.rest.trans hf1.controls)),
    ⟨hagFinal, hfinalRip, hfinalRsp, ?_⟩⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    have hsaved (i : Fin 6) :
        (Operand.reg (#[3,12,13,14,15,5][i.val]) : Operand 64).read t =
        (Operand.reg (#[3,12,13,14,15,5][i.val]) : Operand 64).read c.initial := by
      have hn : ∀ j : Fin 6, (Component.reg (#[3,12,13,14,15,5][j.val])) ∉
          [Component.reg 4,Component.rip] := by decide +kernel
      rw [hagt.read (hn i)]
      rw [hvals i,hm2.memLoad_eq (k:=64) (a:=c.stack + BitVec.ofNat 64 (160+8*i.val))
        (hv.stack_outside_output (by have := i.isLt; omega))]
      exact hf1.saved i
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0
    · exact hsaved 5
    · exact hsaved 1
    · exact hsaved 2
    · exact hsaved 3
    · exact hsaved 4
  · have hfStack : RamWriteFrame c.initial.external s1.external
        [Compress.outputRegion c.initial,c.stackRegion] := by
      refine ⟨fun x hx ↦ hf1.memory.outside x ⟨hx.1,?_⟩,hf1.memory.present⟩
      intro r hr
      exact hx.2 r (List.mem_cons_of_mem _ hr)
    have hfAll := hfStack.trans hm2 (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨Compress.outputRegion c.initial,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩)
    have hfFinal : RamWriteFrame c.initial.external t.external
        [Compress.outputRegion c.initial,c.stackRegion] := by
      rw [hmt,hm3]
      exact hfAll
    apply hfFinal.memoryWriteFrame
    intro x hx r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hx _ (by simp)
    · obtain rfl := List.mem_singleton.mp hr
      exact hx _ (by simp)
  · apply stateMemory_readOutput halloc
    rw [hmt,hm3]
    exact hext
  · have hb := stateMemory_hasBytes s1.external (c.initial.regValue .rdi) (c.state c.count) halloc
    rw [hmt, hm3, hext]
    exact hb

end Sha1.Proofs.Compress.Routine
