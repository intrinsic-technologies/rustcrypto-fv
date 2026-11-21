import Sha1.Proofs.Buffered.DigestFinish.Load
import Sha1.Proofs.Compress.StateMemory
import Sha1.Proofs.Compress.Machine.Code
import Sha1.Proofs.Common.OutputFrame
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import Sha1.Proofs.Common.Refine
import Sha1.Proofs.Compress.Input
import X86Proofs.Instructions.Bswap.Generated.R.Triple

namespace Sha1.Proofs.Buffered.DigestFinish

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec Sha1.Spec.Program Standards.NIST
open Sha1.Proofs.Compress.Machine

theorem stateBytes_bswap_eq_toDigest (H : Vector (BitVec 32) 5) :
    Hasher.stateBytes (H.map bswapSpec) = (SHA1.toDigest H).bytes := by
  apply Vector.ext
  intro i hi
  rw [show (Hasher.stateBytes (H.map bswapSpec))[i] =
      (Hasher.stateBytes (H.map bswapSpec))[(⟨i, hi⟩ : Fin 20)] from rfl,
    Sha1.Proofs.Compress.stateBytes_byte]
  simp only [Vector.getElem_map]
  rw [Sha1.Proofs.Compress.Input.storedByte_bswap32 _ _ (Nat.mod_lt _ (by decide))]
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  simp [SHA1.toDigest, storedByte_eq_extract, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ushiftRight]

def outputChanges (t : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .rip, .mem (t.regValue .rbx) 20]

theorem output_text_ne_return {boundary : ReturnBoundary} (hOutside : ¬ InProgram boundary.rip)
    (offset : Nat) (h : offset < Extracted.textBytes.size) :
    Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip := by
  intro hEq
  exact hOutside (hEq ▸ text_address_in_program offset h)

theorem memLoad32_keep {cs : List Component} {s s' : RamState} (h : AgreesExcept cs s s')
    (a : BitVec 64) (hc : ∀ i < 4, ∀ c ∈ cs, ¬ c.Covers (a + BitVec.ofNat 64 i)) :
    memLoad s'.external a 32 = memLoad s.external a 32 := by
  apply memLoad_congr
  intro i hi
  unfold memByte
  exact congrArg (fun v : Option UInt8 ↦ v.getD 0) (h.byte (hc i (by omega)))

theorem word_apart {a : BitVec 64} {o1 o2 i j : Nat} (ha : a.toNat + 20 < 2 ^ 32)
    (hi : i < 4) (hj : j < 4) (h1 : o1 + 4 ≤ 20) (h2 : o2 + 4 ≤ 20)
    (hd : o1 + 4 ≤ o2 ∨ o2 + 4 ≤ o1) :
    a + BitVec.ofNat 64 o1 + BitVec.ofNat 64 i ≠ a + BitVec.ofNat 64 o2 + BitVec.ofNat 64 j := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

theorem store_keeps {s s' : RamState} {a : BitVec 64} {o1 o2 : Nat}
    {e : Effect} (he : e.Holds s s') (hc : e.components = [.mem (a + BitVec.ofNat 64 o2) 4, .rip])
    (ha : a.toNat + 20 < 2 ^ 32) (h1 : o1 + 4 ≤ 20) (h2 : o2 + 4 ≤ 20)
    (hd : o1 + 4 ≤ o2 ∨ o2 + 4 ≤ o1) :
    memLoad s'.external (a + BitVec.ofNat 64 o1) 32 = memLoad s.external (a + BitVec.ofNat 64 o1) 32 := by
  apply memLoad32_keep he.agrees
  intro i hi c hcm hcov
  rw [hc] at hcm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
  rcases hcm with rfl | rfl
  · obtain ⟨j, hj, heq⟩ := hcov
    exact word_apart ha hi hj h1 h2 hd heq
  · exact hcov

theorem reg_keeps {s s' : RamState} {e : Effect} (he : e.Holds s s') {a : BitVec 64} {len : Nat}
    (hc : e.components = [.mem a len, .rip]) (r : BitVec 5) :
    (Operand.reg r : Operand 64).read s' = (Operand.reg r : Operand 64).read s := by
  have := he.agrees
  rw [hc] at this
  exact this.read (n := 64) (r := r) (by simp)


theorem AgreesExcept.coarsen {cs cs' : List Component} {s s' : RamState}
    (h : AgreesExcept cs s s') (hreg : ∀ c ∈ cs, c.isMem = false → c ∈ cs')
    (hmem : ∀ c ∈ cs, ∀ x, c.Covers x → ∃ c' ∈ cs', c'.Covers x) : AgreesExcept cs' s s' :=
  ⟨fun c hc' hm => h.agree c (fun hc => hc' (hreg c hc hm)) hm,
    fun x hx => h.memory x (fun c hc hcov => by
      obtain ⟨c', hc', hcov'⟩ := hmem c hc x hcov
      exact hx c' hc' hcov'),
    h.rest, h.grow⟩

theorem reg_step_keeps {x y : RamState} {r : BitVec 5} (h : AgreesExcept [.reg r, .rip] x y)
    (h3 : r ≠ 3) (h4 : r ≠ 4) (hc : CodeIn Extracted.programImage x) :
    y.external = x.external ∧ stackPtr y = stackPtr x ∧ y.regValue .rbx = x.regValue .rbx ∧
      CodeIn Extracted.programImage y := by
  have hm : y.external = x.external := h.external (by simp [Component.Covers])
  refine ⟨hm, h.read (n := 64) (r := 4) (by simp; exact fun e => h4 e.symm), ?_,
    hc.of_external_eq hm⟩
  exact h.read (n := 64) (r := 3) (by simp; exact fun e => h3 e.symm)

open Sha1.Proofs.Refine in
theorem output_inside {out : BitVec 64} {s : RamState}
    (h : Common.StoreRegion Extracted.programImage s.external ⟨out.toNat, 20⟩)
    (off len : Nat) (hb : off + len ≤ 20) :
    InRegion ⟨out.toNat, 20⟩ (out + BitVec.ofNat 64 off) len := by
  have hlo : out.toNat + 20 < 2 ^ 32 := h.bounded
  simp only [InRegion, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
  exact ⟨by omega, by omega, by omega⟩

open Sha1.Proofs.Refine in
theorem output_region_of_holds {out : BitVec 64} {s t : RamState} {e : Effect}
    (h : Common.StoreRegion Extracted.programImage s.external ⟨out.toNat, 20⟩)
    (he : e.Holds s t) :
    Common.StoreRegion Extracted.programImage t.external ⟨out.toNat, 20⟩ := by
  refine ⟨h.bounded, ?_, h.avoids⟩
  intro x hx
  exact Option.isSome_iff_exists.mp
    (he.agrees.grow x (Option.isSome_iff_exists.mpr (h.allocated x hx)))

open Sha1.Proofs.Refine in
theorem output_pre {out p : BitVec 64} {s : RamState} {addr : RamState → BitVec 64}
    {off codeLen : Nat}
    (h : Common.StoreRegion Extracted.programImage s.external ⟨out.toNat, 20⟩)
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

open Sha1.Proofs.Refine in
theorem output_avoid {out : BitVec 64} {s : RamState} {e : Effect} {off : Nat}
    {code : CodeMap}
    (h : Common.StoreRegion Extracted.programImage s.external ⟨out.toNat, 20⟩)
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

section Steps

variable [Bindings] {boundary : ReturnBoundary}

theorem load_step {t x : RamState} {H : Vector (BitVec 32) 5}
    (hWord : ∀ i : Fin 5, memLoad t.external (stackPtr t + BitVec.ofNat 64 (4 * i.val)) 32 = H[i])
    (hRead : ∀ i < 5, MemReadable t (stackPtr t + BitVec.ofNat 64 (4 * i)) 4)
    (k : Fin 5) (p : BitVec 64) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0)
    (haddr : ∀ s q, am.addr s q = stackPtr s + BitVec.ofNat 64 (4 * k.val))
    (hReady : ReadyToStep x) (hcode : CodeIn (codeRange p (0x8B :: am.modrm reg :: am.tail)) x)
    (hrip : x.RIP = p) (hne : p + BitVec.ofNat 64 (2 + am.tail.length) ≠ boundary.rip)
    (hsp : stackPtr x = stackPtr t) (hm : x.external = t.external) :
    ∃ y, Advances boundary 1 x y ∧ ReadyToStep y ∧
      y.RIP = p + BitVec.ofNat 64 (2 + am.tail.length) ∧
      AgreesExcept [.reg (gprNumber 0 0 reg), .rip] x y ∧
      (Operand.reg (gprNumber 0 0 reg) : Operand 64).read y = H[k].setWidth 64 := by
  have hpre : LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 4 x := by
    refine ⟨hrip, ?_⟩
    rw [haddr, hsp]
    exact (hRead k.val k.isLt).of_external_eq hm
  obtain ⟨y, hay, hry, hey⟩ :=
    (mov_r32_m32_noRex_effect_step p reg am hv hx hb).advances hReady hcode hpre hne
  refine ⟨y, hay, hry, hey.rip, hey.agrees, ?_⟩
  have hw := hey.writes
  change (Operand.reg (gprNumber 0 0 reg) : Operand 64).read y =
    ((Operand.mem (am.addr x (p + BitVec.ofNat 64 (2 + am.tail.length))) : Operand 32).read x).setWidth 64 at hw
  rw [hw, haddr, hsp]
  change (memLoad x.external _ 32).setWidth 64 = _
  rw [hm, hWord k]

theorem bswap_step {x : RamState} (p : BitVec 64) (op : UInt8)
    (hop : op ∈ [0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF])
    (hReady : ReadyToStep x) (hcode : CodeIn (codeRange p [0x0F, op]) x)
    (hrip : x.RIP = p) (hne : p + BitVec.ofNat 64 2 ≠ boundary.rip) :
    ∃ y, Advances boundary 1 x y ∧ ReadyToStep y ∧ y.RIP = p + BitVec.ofNat 64 2 ∧
      AgreesExcept [.reg (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3)), .rip] x y ∧
      (Operand.reg (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3)) : Operand 64).read y =
        (bswapSpec (((Operand.reg (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3)) : Operand 64).read x).setWidth 32)).setWidth 64 := by
  obtain ⟨y, hay, hry, hey⟩ := (bswap_r32_effect_step p op hop).advances hReady hcode hrip hne
  exact ⟨y, hay, hry, hey.rip, hey.agrees, hey.writes⟩

theorem store_step {x : RamState} {out : BitVec 64} (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (off : Nat)
    (hoff : off + 4 ≤ 20)
    (haddr : ∀ s q, am.addr s q = s.regValue .rbx + BitVec.ofNat 64 off)
    (hReady : ReadyToStep x) (hCode : CodeIn Extracted.programImage x)
    (hcode : CodeIn (codeRange p (0x89 :: am.modrm reg :: am.tail)) x)
    (hInProgram : ∀ i < 2 + am.tail.length, InProgram (p + BitVec.ofNat 64 i))
    (hrip : x.RIP = p) (hne : p + BitVec.ofNat 64 (2 + am.tail.length) ≠ boundary.rip)
    (hrbx : x.regValue .rbx = out)
    (hOut : Common.StoreRegion Extracted.programImage x.external ⟨out.toNat, 20⟩) :
    ∃ y, Advances boundary 1 x y ∧ ReadyToStep y ∧ CodeIn Extracted.programImage y ∧
      y.RIP = p + BitVec.ofNat 64 (2 + am.tail.length) ∧
      (movM32R32LowEffect p (gprNumber 0 0 reg) am x).Holds x y ∧
      (movM32R32LowEffect p (gprNumber 0 0 reg) am x).components =
        [.mem (out + BitVec.ofNat 64 off) 4, .rip] ∧
      memLoad y.external (out + BitVec.ofNat 64 off) 32 =
        (Operand.reg (gprNumber 0 0 reg) : Operand 32).read x ∧
      Common.StoreRegion Extracted.programImage y.external ⟨out.toNat, 20⟩ := by
  have ha : (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) x =
      out + BitVec.ofNat 64 off := by
    simp only [haddr, hrbx]
  have hpre := output_pre (addr := fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length)))
    hOut hrip ha hoff hInProgram
  obtain ⟨y, hay, hry, hey⟩ :=
    (Common.Instructions.MovStore.mov_m32_r32_low_effect_step p reg am hv hx hb).advances
      hReady hcode hpre hne
  have hcomp : (movM32R32LowEffect p (gprNumber 0 0 reg) am x).components =
      [.mem (out + BitVec.ofNat 64 off) 4, .rip] := by
    simp only [movM32R32LowEffect, storeEffect_components, haddr, hrbx]
  refine ⟨y, hay, hry,
    hey.codeIn (output_avoid hOut hcomp hoff (fun _ h => h)) hCode,
    hey.rip, hey, hcomp, ?_, output_region_of_holds hOut hey⟩
  have hw := hey.writes
  change (Operand.mem (am.addr x (p + BitVec.ofNat 64 (2 + am.tail.length))) : Operand 32).read y =
    (Operand.reg (gprNumber 0 0 reg) : Operand 32).read x at hw
  rw [haddr, hrbx] at hw
  exact hw

end Steps

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem digest_output [Bindings] {t : RamState} {boundary : ReturnBoundary}
    {H : Vector (BitVec 32) 5}
    (hReady : ReadyToStep t) (hCode : CodeIn Extracted.programImage t) (hRip : t.RIP = 0x100277)
    (hOutside : ¬ InProgram boundary.rip)
    (hStack : (⟨(stackPtr t).toNat, 20⟩ : MemoryRegion).HasBytes t.external
      ⟨(Hasher.stateBytes H).toArray⟩)
    (hStackLow : (stackPtr t).toNat + 20 ≤ 2 ^ 32)
    (hOut : Common.StoreRegion Extracted.programImage t.external
      ⟨(t.regValue .rbx).toNat, 20⟩) :
    ∃ u, Advances boundary 15 t u ∧ ReadyToStep u ∧ CodeIn Extracted.programImage u ∧
      u.RIP = 0x1002a2 ∧ AgreesExcept (outputChanges t) t u ∧
      (⟨(t.regValue .rbx).toNat, 20⟩ : MemoryRegion).HasBytes u.external
        ⟨(Hasher.stateBytes (H.map bswapSpec)).toArray⟩ := by
  have hWord := Compress.stateBytes_words hStack
  have hRead : ∀ i < 5, MemReadable t (stackPtr t + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    refine ⟨?_, ?_⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · intro j hj
      have he : stackPtr t + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 j =
          BitVec.ofNat 64 ((stackPtr t).toNat + (4 * i + j)) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      rw [he, hStack.2 ⟨4 * i + j, by simp [ByteArray.size]; omega⟩]
      rfl
  have hc0 := hCode
  have hspT0 : stackPtr t = stackPtr t := rfl
  have hmT0 : t.external = t.external := rfl
  have hrbxT0 : t.regValue .rbx = t.regValue .rbx := rfl
  have hr0 := hReady
  have hrip0 : t.RIP = 0x100277 := hRip
  obtain ⟨x1, ha1, hr1, hrip1, hag1, hval1⟩ :=
    load_step (boundary := boundary) hWord hRead ⟨0, by decide⟩ 0x100277 0 (.sib 4 none 0 .none)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun _ _ => by simp [AddrMode.addr, Disp.value]; rfl)
      hr0 (program_text_slice hc0 0x277 3 (by decide +kernel)) (hrip0.trans (by decide +kernel))
      (output_text_ne_return hOutside 0x27a (by decide +kernel)) hspT0 hmT0
  obtain ⟨hm1, hsp1, hrbx1, hc1⟩ := reg_step_keeps hag1 (by decide) (by decide) hc0
  have hspT1 : stackPtr x1 = stackPtr t := hsp1.trans hspT0
  have hmT1 : x1.external = t.external := hm1.trans hmT0
  have hrbxT1 : x1.regValue .rbx = t.regValue .rbx := hrbx1.trans hrbxT0
  obtain ⟨x2, ha2, hr2, hrip2, hag2, hval2⟩ :=
    load_step (boundary := boundary) hWord hRead ⟨1, by decide⟩ 0x10027a 1 (.sib 4 none 0 (.d8 4))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun _ _ => by simp [AddrMode.addr, Disp.value]; rfl)
      hr1 (program_text_slice hc1 0x27a 4 (by decide +kernel)) (hrip1.trans (by decide +kernel))
      (output_text_ne_return hOutside 0x27e (by decide +kernel)) hspT1 hmT1
  obtain ⟨hm2, hsp2, hrbx2, hc2⟩ := reg_step_keeps hag2 (by decide) (by decide) hc1
  have hspT2 : stackPtr x2 = stackPtr t := hsp2.trans hspT1
  have hmT2 : x2.external = t.external := hm2.trans hmT1
  have hrbxT2 : x2.regValue .rbx = t.regValue .rbx := hrbx2.trans hrbxT1
  obtain ⟨x3, ha3, hr3, hrip3, hag3, hval3⟩ :=
    bswap_step (boundary := boundary) 0x10027e 0xc8 (by decide)
      hr2 (program_text_slice hc2 0x27e 2 (by decide +kernel)) (hrip2.trans (by decide +kernel))
      (output_text_ne_return hOutside 0x280 (by decide +kernel))
  obtain ⟨hm3, hsp3, hrbx3, hc3⟩ := reg_step_keeps hag3 (by decide) (by decide) hc2
  have hspT3 : stackPtr x3 = stackPtr t := hsp3.trans hspT2
  have hmT3 : x3.external = t.external := hm3.trans hmT2
  have hrbxT3 : x3.regValue .rbx = t.regValue .rbx := hrbx3.trans hrbxT2
  obtain ⟨x4, ha4, hr4, hrip4, hag4, hval4⟩ :=
    bswap_step (boundary := boundary) 0x100280 0xc9 (by decide)
      hr3 (program_text_slice hc3 0x280 2 (by decide +kernel)) (hrip3.trans (by decide +kernel))
      (output_text_ne_return hOutside 0x282 (by decide +kernel))
  obtain ⟨hm4, hsp4, hrbx4, hc4⟩ := reg_step_keeps hag4 (by decide) (by decide) hc3
  have hspT4 : stackPtr x4 = stackPtr t := hsp4.trans hspT3
  have hmT4 : x4.external = t.external := hm4.trans hmT3
  have hrbxT4 : x4.regValue .rbx = t.regValue .rbx := hrbx4.trans hrbxT3
  obtain ⟨x5, ha5, hr5, hrip5, hag5, hval5⟩ :=
    load_step (boundary := boundary) hWord hRead ⟨2, by decide⟩ 0x100282 2 (.sib 4 none 0 (.d8 8))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun _ _ => by simp [AddrMode.addr, Disp.value]; rfl)
      hr4 (program_text_slice hc4 0x282 4 (by decide +kernel)) (hrip4.trans (by decide +kernel))
      (output_text_ne_return hOutside 0x286 (by decide +kernel)) hspT4 hmT4
  obtain ⟨hm5, hsp5, hrbx5, hc5⟩ := reg_step_keeps hag5 (by decide) (by decide) hc4
  have hspT5 : stackPtr x5 = stackPtr t := hsp5.trans hspT4
  have hmT5 : x5.external = t.external := hm5.trans hmT4
  have hrbxT5 : x5.regValue .rbx = t.regValue .rbx := hrbx5.trans hrbxT4
  obtain ⟨x6, ha6, hr6, hrip6, hag6, hval6⟩ :=
    bswap_step (boundary := boundary) 0x100286 0xca (by decide)
      hr5 (program_text_slice hc5 0x286 2 (by decide +kernel)) (hrip5.trans (by decide +kernel))
      (output_text_ne_return hOutside 0x288 (by decide +kernel))
  obtain ⟨hm6, hsp6, hrbx6, hc6⟩ := reg_step_keeps hag6 (by decide) (by decide) hc5
  have hspT6 : stackPtr x6 = stackPtr t := hsp6.trans hspT5
  have hmT6 : x6.external = t.external := hm6.trans hmT5
  have hrbxT6 : x6.regValue .rbx = t.regValue .rbx := hrbx6.trans hrbxT5
  obtain ⟨x7, ha7, hr7, hrip7, hag7, hval7⟩ :=
    load_step (boundary := boundary) hWord hRead ⟨3, by decide⟩ 0x100288 6 (.sib 4 none 0 (.d8 0xc))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun _ _ => by simp [AddrMode.addr, Disp.value]; rfl)
      hr6 (program_text_slice hc6 0x288 4 (by decide +kernel)) (hrip6.trans (by decide +kernel))
      (output_text_ne_return hOutside 0x28c (by decide +kernel)) hspT6 hmT6
  obtain ⟨hm7, hsp7, hrbx7, hc7⟩ := reg_step_keeps hag7 (by decide) (by decide) hc6
  have hspT7 : stackPtr x7 = stackPtr t := hsp7.trans hspT6
  have hmT7 : x7.external = t.external := hm7.trans hmT6
  have hrbxT7 : x7.regValue .rbx = t.regValue .rbx := hrbx7.trans hrbxT6
  obtain ⟨x8, ha8, hr8, hrip8, hag8, hval8⟩ :=
    bswap_step (boundary := boundary) 0x10028c 0xce (by decide)
      hr7 (program_text_slice hc7 0x28c 2 (by decide +kernel)) (hrip7.trans (by decide +kernel))
      (output_text_ne_return hOutside 0x28e (by decide +kernel))
  obtain ⟨hm8, hsp8, hrbx8, hc8⟩ := reg_step_keeps hag8 (by decide) (by decide) hc7
  have hspT8 : stackPtr x8 = stackPtr t := hsp8.trans hspT7
  have hmT8 : x8.external = t.external := hm8.trans hmT7
  have hrbxT8 : x8.regValue .rbx = t.regValue .rbx := hrbx8.trans hrbxT7
  obtain ⟨x9, ha9, hr9, hrip9, hag9, hval9⟩ :=
    load_step (boundary := boundary) hWord hRead ⟨4, by decide⟩ 0x10028e 7 (.sib 4 none 0 (.d8 0x10))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun _ _ => by simp [AddrMode.addr, Disp.value]; rfl)
      hr8 (program_text_slice hc8 0x28e 4 (by decide +kernel)) (hrip8.trans (by decide +kernel))
      (output_text_ne_return hOutside 0x292 (by decide +kernel)) hspT8 hmT8
  obtain ⟨hm9, hsp9, hrbx9, hc9⟩ := reg_step_keeps hag9 (by decide) (by decide) hc8
  have hspT9 : stackPtr x9 = stackPtr t := hsp9.trans hspT8
  have hmT9 : x9.external = t.external := hm9.trans hmT8
  have hrbxT9 : x9.regValue .rbx = t.regValue .rbx := hrbx9.trans hrbxT8
  obtain ⟨x10, ha10, hr10, hrip10, hag10, hval10⟩ :=
    bswap_step (boundary := boundary) 0x100292 0xcf (by decide)
      hr9 (program_text_slice hc9 0x292 2 (by decide +kernel)) (hrip9.trans (by decide +kernel))
      (output_text_ne_return hOutside 0x294 (by decide +kernel))
  obtain ⟨hm10, hsp10, hrbx10, hc10⟩ := reg_step_keeps hag10 (by decide) (by decide) hc9
  have hspT10 : stackPtr x10 = stackPtr t := hsp10.trans hspT9
  have hmT10 : x10.external = t.external := hm10.trans hmT9
  have hrbxT10 : x10.regValue .rbx = t.regValue .rbx := hrbx10.trans hrbxT9
  have hB0 : (Operand.reg 0 : Operand 64).read x10 = (bswapSpec H[0]).setWidth 64 := by
    rw [((((((hag4.trans hag5).trans hag6).trans hag7).trans hag8).trans hag9).trans hag10).read (n := 64) (r := 0) (by simp <;> decide)]
    have h := hval3
    change (Operand.reg 0 : Operand 64).read x3 = (bswapSpec (((Operand.reg 0 : Operand 64).read x2).setWidth 32)).setWidth 64 at h
    rw [h]
    rw [hag2.read (n := 64) (r := 0) (by simp <;> decide)]
    have hl := hval1
    change (Operand.reg 0 : Operand 64).read x1 = H[0].setWidth 64 at hl
    rw [hl]
    simp
  have hB1 : (Operand.reg 1 : Operand 64).read x10 = (bswapSpec H[1]).setWidth 64 := by
    rw [(((((hag5.trans hag6).trans hag7).trans hag8).trans hag9).trans hag10).read (n := 64) (r := 1) (by simp <;> decide)]
    have h := hval4
    change (Operand.reg 1 : Operand 64).read x4 = (bswapSpec (((Operand.reg 1 : Operand 64).read x3).setWidth 32)).setWidth 64 at h
    rw [h]
    rw [hag3.read (n := 64) (r := 1) (by simp <;> decide)]
    have hl := hval2
    change (Operand.reg 1 : Operand 64).read x2 = H[1].setWidth 64 at hl
    rw [hl]
    simp
  have hB2 : (Operand.reg 2 : Operand 64).read x10 = (bswapSpec H[2]).setWidth 64 := by
    rw [(((hag7.trans hag8).trans hag9).trans hag10).read (n := 64) (r := 2) (by simp <;> decide)]
    have h := hval6
    change (Operand.reg 2 : Operand 64).read x6 = (bswapSpec (((Operand.reg 2 : Operand 64).read x5).setWidth 32)).setWidth 64 at h
    rw [h]
    have hl := hval5
    change (Operand.reg 2 : Operand 64).read x5 = H[2].setWidth 64 at hl
    rw [hl]
    simp
  have hB6 : (Operand.reg 6 : Operand 64).read x10 = (bswapSpec H[3]).setWidth 64 := by
    rw [(hag9.trans hag10).read (n := 64) (r := 6) (by simp <;> decide)]
    have h := hval8
    change (Operand.reg 6 : Operand 64).read x8 = (bswapSpec (((Operand.reg 6 : Operand 64).read x7).setWidth 32)).setWidth 64 at h
    rw [h]
    have hl := hval7
    change (Operand.reg 6 : Operand 64).read x7 = H[3].setWidth 64 at hl
    rw [hl]
    simp
  have hB7 : (Operand.reg 7 : Operand 64).read x10 = (bswapSpec H[4]).setWidth 64 := by
    have h := hval10
    change (Operand.reg 7 : Operand 64).read x10 = (bswapSpec (((Operand.reg 7 : Operand 64).read x9).setWidth 32)).setWidth 64 at h
    rw [h]
    have hl := hval9
    change (Operand.reg 7 : Operand 64).read x9 = H[4].setWidth 64 at hl
    rw [hl]
    simp
  have hO10 : Common.StoreRegion Extracted.programImage x10.external ⟨(t.regValue .rbx).toNat, 20⟩ := by
    rw [hmT10]
    exact hOut
  obtain ⟨x11, ha11, hr11, hc11, hrip11, he11, hcomp11, hw11, hO11⟩ :=
    store_step (boundary := boundary) 0x100294 0 (.base 3 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      0 (by decide) (fun _ _ => by simp [AddrMode.addr, Disp.value]; rfl) hr10 hc10
      (program_text_slice hc10 0x294 2 (by decide +kernel))
      (program_text_range 0x294 2 (by decide +kernel)) (hrip10.trans (by decide +kernel))
      (output_text_ne_return hOutside 0x296 (by decide +kernel)) hrbxT10 hO10
  have hrbxT11 : x11.regValue .rbx = t.regValue .rbx :=
    (reg_keeps he11 hcomp11 3).trans hrbxT10
  obtain ⟨x12, ha12, hr12, hc12, hrip12, he12, hcomp12, hw12, hO12⟩ :=
    store_step (boundary := boundary) 0x100296 1 (.base 3 (.d8 4)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      4 (by decide) (fun _ _ => by simp [AddrMode.addr, Disp.value]; rfl) hr11 hc11
      (program_text_slice hc11 0x296 3 (by decide +kernel))
      (program_text_range 0x296 3 (by decide +kernel)) (hrip11.trans (by decide +kernel))
      (output_text_ne_return hOutside 0x299 (by decide +kernel)) hrbxT11 hO11
  have hrbxT12 : x12.regValue .rbx = t.regValue .rbx :=
    (reg_keeps he12 hcomp12 3).trans hrbxT11
  obtain ⟨x13, ha13, hr13, hc13, hrip13, he13, hcomp13, hw13, hO13⟩ :=
    store_step (boundary := boundary) 0x100299 2 (.base 3 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      8 (by decide) (fun _ _ => by simp [AddrMode.addr, Disp.value]; rfl) hr12 hc12
      (program_text_slice hc12 0x299 3 (by decide +kernel))
      (program_text_range 0x299 3 (by decide +kernel)) (hrip12.trans (by decide +kernel))
      (output_text_ne_return hOutside 0x29c (by decide +kernel)) hrbxT12 hO12
  have hrbxT13 : x13.regValue .rbx = t.regValue .rbx :=
    (reg_keeps he13 hcomp13 3).trans hrbxT12
  obtain ⟨x14, ha14, hr14, hc14, hrip14, he14, hcomp14, hw14, hO14⟩ :=
    store_step (boundary := boundary) 0x10029c 6 (.base 3 (.d8 12)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      12 (by decide) (fun _ _ => by simp [AddrMode.addr, Disp.value]; rfl) hr13 hc13
      (program_text_slice hc13 0x29c 3 (by decide +kernel))
      (program_text_range 0x29c 3 (by decide +kernel)) (hrip13.trans (by decide +kernel))
      (output_text_ne_return hOutside 0x29f (by decide +kernel)) hrbxT13 hO13
  have hrbxT14 : x14.regValue .rbx = t.regValue .rbx :=
    (reg_keeps he14 hcomp14 3).trans hrbxT13
  obtain ⟨x15, ha15, hr15, hc15, hrip15, he15, hcomp15, hw15, hO15⟩ :=
    store_step (boundary := boundary) 0x10029f 7 (.base 3 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      16 (by decide) (fun _ _ => by simp [AddrMode.addr, Disp.value]; rfl) hr14 hc14
      (program_text_slice hc14 0x29f 3 (by decide +kernel))
      (program_text_range 0x29f 3 (by decide +kernel)) (hrip14.trans (by decide +kernel))
      (output_text_ne_return hOutside 0x2a2 (by decide +kernel)) hrbxT14 hO14
  have hrbxT15 : x15.regValue .rbx = t.regValue .rbx :=
    (reg_keeps he15 hcomp15 3).trans hrbxT14
  have hbound : (t.regValue .rbx).toNat + 20 < 2 ^ 32 := hOut.bounded
  have hS0 : (Operand.reg 0 : Operand 32).read x10 = bswapSpec H[0] := by
    change ((Operand.reg 0 : Operand 64).read x10).setWidth 32 = _
    rw [hB0]
    simp
  have hS1 : (Operand.reg 1 : Operand 32).read x11 = bswapSpec H[1] := by
    change ((Operand.reg 1 : Operand 64).read x11).setWidth 32 = _
    rw [reg_keeps he11 hcomp11 1]
    rw [hB1]
    simp
  have hS2 : (Operand.reg 2 : Operand 32).read x12 = bswapSpec H[2] := by
    change ((Operand.reg 2 : Operand 64).read x12).setWidth 32 = _
    rw [reg_keeps he12 hcomp12 2]
    rw [reg_keeps he11 hcomp11 2]
    rw [hB2]
    simp
  have hS6 : (Operand.reg 6 : Operand 32).read x13 = bswapSpec H[3] := by
    change ((Operand.reg 6 : Operand 64).read x13).setWidth 32 = _
    rw [reg_keeps he13 hcomp13 6]
    rw [reg_keeps he12 hcomp12 6]
    rw [reg_keeps he11 hcomp11 6]
    rw [hB6]
    simp
  have hS7 : (Operand.reg 7 : Operand 32).read x14 = bswapSpec H[4] := by
    change ((Operand.reg 7 : Operand 64).read x14).setWidth 32 = _
    rw [reg_keeps he14 hcomp14 7]
    rw [reg_keeps he13 hcomp13 7]
    rw [reg_keeps he12 hcomp12 7]
    rw [reg_keeps he11 hcomp11 7]
    rw [hB7]
    simp
  have hWords : ∀ i : Fin 5, memLoad x15.external
      (t.regValue .rbx + BitVec.ofNat 64 (4 * i.val)) 32 = (H.map bswapSpec)[i] := by
    intro ⟨i, hi⟩
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · show memLoad x15.external (t.regValue .rbx + BitVec.ofNat 64 0) 32 = _
      rw [store_keeps he15 hcomp15 hbound (o1 := 0) (o2 := 16) (by decide) (by decide) (by decide)]
      rw [store_keeps he14 hcomp14 hbound (o1 := 0) (o2 := 12) (by decide) (by decide) (by decide)]
      rw [store_keeps he13 hcomp13 hbound (o1 := 0) (o2 := 8) (by decide) (by decide) (by decide)]
      rw [store_keeps he12 hcomp12 hbound (o1 := 0) (o2 := 4) (by decide) (by decide) (by decide)]
      rw [hw11]
      exact hS0.trans (by simp; try rfl)
    · show memLoad x15.external (t.regValue .rbx + BitVec.ofNat 64 4) 32 = _
      rw [store_keeps he15 hcomp15 hbound (o1 := 4) (o2 := 16) (by decide) (by decide) (by decide)]
      rw [store_keeps he14 hcomp14 hbound (o1 := 4) (o2 := 12) (by decide) (by decide) (by decide)]
      rw [store_keeps he13 hcomp13 hbound (o1 := 4) (o2 := 8) (by decide) (by decide) (by decide)]
      rw [hw12]
      exact hS1.trans (by simp; try rfl)
    · show memLoad x15.external (t.regValue .rbx + BitVec.ofNat 64 8) 32 = _
      rw [store_keeps he15 hcomp15 hbound (o1 := 8) (o2 := 16) (by decide) (by decide) (by decide)]
      rw [store_keeps he14 hcomp14 hbound (o1 := 8) (o2 := 12) (by decide) (by decide) (by decide)]
      rw [hw13]
      exact hS2.trans (by simp; try rfl)
    · show memLoad x15.external (t.regValue .rbx + BitVec.ofNat 64 12) 32 = _
      rw [store_keeps he15 hcomp15 hbound (o1 := 12) (o2 := 16) (by decide) (by decide) (by decide)]
      rw [hw14]
      exact hS6.trans (by simp; try rfl)
    · show memLoad x15.external (t.regValue .rbx + BitVec.ofNat 64 16) 32 = _
      rw [hw15]
      exact hS7.trans (by simp; try rfl)
  have hAlloc : ∀ i < 20, (x15.external[t.regValue .rbx + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    obtain ⟨b, hb⟩ := hO15.allocated (t.regValue .rbx + BitVec.ofNat 64 i) (by
      change (t.regValue .rbx).toNat ≤ _ ∧ _ < (t.regValue .rbx).toNat + 20
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega)
    rw [hb]
    rfl
  have hs11 := he11.agrees
  have hs12 := he12.agrees
  have hs13 := he13.agrees
  have hs14 := he14.agrees
  have hs15 := he15.agrees
  rw [hcomp11] at hs11
  rw [hcomp12] at hs12
  rw [hcomp13] at hs13
  rw [hcomp14] at hs14
  rw [hcomp15] at hs15
  have hAll := ((((((((((((((hag1.trans hag2).trans hag3).trans hag4).trans hag5).trans hag6).trans hag7).trans hag8).trans hag9).trans hag10).trans hs11).trans hs12).trans hs13).trans hs14).trans hs15)
  refine ⟨x15, ?_, hr15, hc15, hrip15.trans (by decide +kernel), ?_,
    Compress.stateBytes_of_words hWords hAlloc⟩
  · exact ((((((((((((((ha1.trans ha2).trans ha3).trans ha4).trans ha5).trans ha6).trans ha7).trans ha8).trans ha9).trans ha10).trans ha11).trans ha12).trans ha13).trans ha14).trans ha15)
  · apply AgreesExcept.coarsen hAll
    · intro c hc hm
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      repeat' (rcases hc with rfl | hc)
      all_goals first
        | (simp [outputChanges] <;> decide)
        | exact absurd hm (by simp [Component.isMem])
    · intro c hc x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      repeat' (rcases hc with rfl | hc)
      all_goals simp only [Component.Covers] at hx
      · obtain ⟨j, hj, rfl⟩ := hx
        exact ⟨.mem (t.regValue .rbx) 20, by simp [outputChanges], j, by omega, by bv_omega⟩
      · obtain ⟨j, hj, rfl⟩ := hx
        exact ⟨.mem (t.regValue .rbx) 20, by simp [outputChanges], 4 + j, by omega, by bv_omega⟩
      · obtain ⟨j, hj, rfl⟩ := hx
        exact ⟨.mem (t.regValue .rbx) 20, by simp [outputChanges], 8 + j, by omega, by bv_omega⟩
      · obtain ⟨j, hj, rfl⟩ := hx
        exact ⟨.mem (t.regValue .rbx) 20, by simp [outputChanges], 12 + j, by omega, by bv_omega⟩
      · obtain ⟨j, hj, rfl⟩ := hx
        exact ⟨.mem (t.regValue .rbx) 20, by simp [outputChanges], 16 + j, by omega, by bv_omega⟩

end Sha1.Proofs.Buffered.DigestFinish
