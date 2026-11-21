import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Control.Instructions

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

variable {alphabet : Base16ct.Proofs.Base16ctUpperDecodeCorrect.RFC4648.Alphabet}
open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

theorem lowByte_test_one (x : BitVec 64) :
    (x.setWidth 8 &&& 1#8 == 0#8) = decide (x.toNat % 2 = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have hnat := congrArg BitVec.toNat h
    change x.toNat % 256 &&& 1 = 0 at hnat
    rw [Nat.and_one_is_mod] at hnat
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    change x.toNat % 256 &&& 1 = 0
    rw [Nat.and_one_is_mod]
    omega

set_option maxRecDepth 100000 in
theorem decode_check_parity [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (he : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet))
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 3 s t ∧ EntryReady programImage t ∧
      t.RIP = (if (AddrMode.reg64 6 s).toNat % 2 = 0
        then (decodeAddress alphabet) + 15#64 else (decodeAddress alphabet) + 240#64) ∧
      AgreesExcept [.reg 0, .flags, .rip] s t ∧ AddrMode.reg64 0 t = 1#64 := by
  obtain ⟨u, hau, hru, hcu, hu⟩ := decode_mov_eax_one he hp hret
  change (movR32Imm32Effect s.RIP 5 0 1 s).Holds s u at hu
  have heu := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter he hru hcu hu.agrees
  have hpu : u.RIP = (decodeAddress alphabet) + 5#64 := by simpa [movR32Imm32Effect, hp] using hu.rip
  obtain ⟨v, hav, hrv, hcv, hv⟩ := decode_test_sil_one heu hpu hret
  change (testR8Imm8Effect u.RIP 6 1 u).Holds u v at hv
  have hev := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter heu hrv hcv hv.agrees
  have hpv : v.RIP = (decodeAddress alphabet) + 9#64 := by
    simpa [testR8Imm8Effect, hpu, BitVec.add_assoc] using hv.rip
  obtain ⟨t, hat, hrt, hct, ht⟩ := decode_jne_after_test hev hpv hret
  have hfu : AgreesExcept [.reg 0, .rip] s u := by simpa using hu.agrees
  have hfv : AgreesExcept [.flags, .rip] u v := hv.agrees
  have hft : AgreesExcept [.rip] v t := by simpa [Effect.components, jccEffect, branchEffect] using ht.agrees
  have hsi : AddrMode.reg64 6 u = AddrMode.reg64 6 s := hfu.read (by simp)
  have hz : (StatusFlags.ofRFLAGS v.RFLAGS).ZF =
      ((AddrMode.reg64 6 s).setWidth 8 &&& 1#8 == 0#8) := by
    have hh := hv.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS v.RFLAGS).ZF =
      ((AddrMode.reg64 6 u).setWidth 8 &&& 1#8 == 0#8) at hh
    rw [hsi] at hh
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hh
  have hx : AddrMode.reg64 0 u = 1#64 := by exact hu.writes
  refine ⟨t, hau.trans (hav.trans hat),
    Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter hev hrt hct ht.agrees, ?_, ?_, ?_⟩
  · have hh := ht.rip
    change t.RIP = (if !(StatusFlags.ofRFLAGS v.RFLAGS).ZF then
      branchTarget v.RIP 6 ((0xe1#32).signExtend 64) else BitVec.add v.RIP (6#64)) at hh
    rw [hz, lowByte_test_one, hpv] at hh
    rw [show branchTarget ((decodeAddress alphabet) + 9#64) 6 ((0xe1#32).signExtend 64) =
        (decodeAddress alphabet) + 240#64 by cases alphabet <;> decide +kernel,
      show BitVec.add ((decodeAddress alphabet) + 9#64) (6#64) = (decodeAddress alphabet) + 15#64 by cases alphabet <;> decide +kernel] at hh
    by_cases heven : (AddrMode.reg64 (6#4) s).toNat % 2 = 0 <;> simpa [heven] using hh
  · exact (hfu.trans (hfv.trans hft)).mono (by simp)
  · exact ((hfv.trans hft).read (by simp)).trans hx

theorem cmpSpec_below_or_equal (x y : BitVec 64) :
    ((cmpSpec x y).CF || (cmpSpec x y).ZF) = decide (x.toNat ≤ y.toNat) := by
  have heq : x - y = 0#64 ↔ x = y := by
    constructor
    · intro h
      exact (BitVec.sub_eq_iff_eq_add.mp h).trans (BitVec.zero_add y)
    · intro h; simp [h]
  apply Bool.eq_iff_iff.mpr
  simp only [cmpSpec, subSpec, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  change (x.toNat < y.toNat ∨ x - y = 0#64) ↔ x.toNat ≤ y.toNat
  rw [heq]
  constructor
  · intro h
    rcases h with h | h
    · omega
    · subst y; exact Nat.le_refl _
  · intro h
    by_cases hl : x.toNat < y.toNat
    · exact Or.inl hl
    · right; apply BitVec.eq_of_toNat_eq; omega

set_option maxRecDepth 100000 in
theorem decode_check_capacity [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {length capacity : Nat}
    (he : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 15#64)
    (hlen : (AddrMode.reg64 6 s).toNat = length)
    (hcap : (AddrMode.reg64 8 s).toNat = capacity)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 4 s t ∧ EntryReady programImage t ∧
      t.RIP = (if length / 2 ≤ capacity then (decodeAddress alphabet) + 30#64
        else (decodeAddress alphabet) + 240#64) ∧
      AgreesExcept [.reg 9, .flags, .rip] s t ∧
      AddrMode.reg64 9 t = BitVec.ofNat 64 (length / 2) := by
  obtain ⟨u, hau, hru, hcu, hu⟩ := decode_mov_r9_rsi he hp hret
  change (movR64R64Effect s.RIP 9 6 s).Holds s u at hu
  have heu := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter he hru hcu hu.agrees
  have hpu : u.RIP = (decodeAddress alphabet) + 18#64 := by
    simpa [movR64R64Effect, hp, BitVec.add_assoc] using hu.rip
  obtain ⟨v, hav, hrv, hcv, hv⟩ := decode_shr_r9_one heu hpu hret
  change (shrR64Effect u.RIP 3 9 1 u).Holds u v at hv
  have hev := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter heu hrv hcv hv.agrees
  have hpv : v.RIP = (decodeAddress alphabet) + 21#64 := by
    simpa [shrR64Effect, hpu, BitVec.add_assoc] using hv.rip
  obtain ⟨w, haw, hrw, hcw, hw⟩ := decode_cmp_r9_r8 hev hpv hret
  change (cmpR64R64Effect v.RIP 9 8 v).Holds v w at hw
  have hew := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter hev hrw hcw hw.agrees
  have hpw : w.RIP = (decodeAddress alphabet) + 24#64 := by
    simpa [cmpR64R64Effect, hpv, BitVec.add_assoc] using hw.rip
  obtain ⟨t, hat, hrt, hct, ht⟩ := decode_ja_after_cmp hew hpw hret
  have hfu : AgreesExcept [.reg 9, .rip] s u := by simpa using hu.agrees
  have hfv : AgreesExcept [.reg 9, .flags, .rip] u v := by simpa using hv.agrees
  have hfw : AgreesExcept [.flags, .rip] v w := hw.agrees
  have hft : AgreesExcept [.rip] w t := by simpa [Effect.components, jccEffect, branchEffect] using ht.agrees
  have haxu : AddrMode.reg64 9 u = AddrMode.reg64 6 s := hu.writes
  have haxv : AddrMode.reg64 9 v = AddrMode.reg64 6 s >>> 1 := by
    have hh := hv.writes
    change AddrMode.reg64 9 v = AddrMode.reg64 9 u >>> 1 at hh
    rw [haxu] at hh
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hh
  have haxnat : (AddrMode.reg64 9 v).toNat = length / 2 := by
    rw [haxv]
    simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using congrArg (fun n => n / 2) hlen
  have hax : AddrMode.reg64 9 v = BitVec.ofNat 64 (length / 2) := by
    simpa using congrArg (BitVec.ofNat 64) haxnat
  have hcxv : AddrMode.reg64 8 v = AddrMode.reg64 8 s := (hfu.trans hfv).read (by simp)
  have hcond : condHolds (7#4) (StatusFlags.ofRFLAGS w.RFLAGS) = !decide (length / 2 ≤ capacity) := by
    have hcf := hw.flags.1
    have hzf := hw.flags.2.2.2.1
    change condHolds (7#4) (StatusFlags.ofRFLAGS w.RFLAGS) = _
    change (Bool.not ((StatusFlags.ofRFLAGS w.RFLAGS).CF || (StatusFlags.ofRFLAGS w.RFLAGS).ZF)) = _
    change (StatusFlags.ofRFLAGS w.RFLAGS).CF = (cmpSpec (AddrMode.reg64 9 v) (AddrMode.reg64 8 v)).CF at hcf
    change (StatusFlags.ofRFLAGS w.RFLAGS).ZF = (cmpSpec (AddrMode.reg64 9 v) (AddrMode.reg64 8 v)).ZF at hzf
    rw [hcf, hzf, cmpSpec_below_or_equal, haxnat, hcxv, hcap]
  refine ⟨t, hau.trans (hav.trans (haw.trans hat)),
    Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter hew hrt hct ht.agrees, ?_, ?_, ?_⟩
  · have hh := ht.rip
    change t.RIP = (if condHolds (7#4) (StatusFlags.ofRFLAGS w.RFLAGS) then
      branchTarget w.RIP 6 ((0xd2#32).signExtend 64) else BitVec.add w.RIP (6#64)) at hh
    rw [hcond, hpw] at hh
    rw [show branchTarget ((decodeAddress alphabet) + 24#64) 6 ((0xd2#32).signExtend 64) =
        (decodeAddress alphabet) + 240#64 by cases alphabet <;> decide +kernel,
      show BitVec.add ((decodeAddress alphabet) + 24#64) (6#64) = (decodeAddress alphabet) + 30#64 by cases alphabet <;> decide +kernel] at hh
    by_cases h : length / 2 ≤ capacity <;> simpa [h] using hh
  · exact (hfu.trans (hfv.trans (hfw.trans hft))).mono (by simp)
  · exact ((hfw.trans hft).read (by simp)).trans hax

set_option maxRecDepth 100000 in
theorem decode_check_empty [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {length : Nat}
    (he : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 30#64)
    (hlen : (AddrMode.reg64 6 s).toNat = length)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ EntryReady programImage t ∧
      t.RIP = (if length = 0 then (decodeAddress alphabet) + 241#64
        else (decodeAddress alphabet) + 39#64) ∧ AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, hau, hru, hcu, hu⟩ := decode_test_rsi_rsi he hp hret
  change (testR64R64Effect s.RIP 6 6 s).Holds s u at hu
  have heu := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter he hru hcu hu.agrees
  have hpu : u.RIP = (decodeAddress alphabet) + 33#64 := by
    simpa [testR64R64Effect, hp, BitVec.add_assoc] using hu.rip
  obtain ⟨t, hat, hrt, hct, ht⟩ := decode_je_empty heu hpu hret
  have hfu : AgreesExcept [.flags, .rip] s u := hu.agrees
  have hft : AgreesExcept [.rip] u t := by simpa [Effect.components, jccEffect, branchEffect] using ht.agrees
  have hzf : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (AddrMode.reg64 6 s == 0#64) := by
    have hh := hu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (AddrMode.reg64 6 s &&& AddrMode.reg64 6 s == 0#64) at hh
    simpa using hh
  have hzero : (AddrMode.reg64 6 s == 0#64) = decide (length = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro hz
      have hh := congrArg BitVec.toNat hz
      change (AddrMode.reg64 6 s).toNat = 0 at hh
      exact hlen.symm.trans hh
    · intro hz
      apply BitVec.eq_of_toNat_eq
      exact hlen.trans hz
  refine ⟨t, hau.trans hat, Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter heu hrt hct ht.agrees, ?_,
    (hfu.trans hft).mono (by simp)⟩
  have hh := ht.rip
  change t.RIP = (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then
    branchTarget u.RIP 6 ((0xca#32).signExtend 64) else BitVec.add u.RIP (6#64)) at hh
  rw [hzf, hzero, hpu] at hh
  rw [show branchTarget ((decodeAddress alphabet) + 33#64) 6 ((0xca#32).signExtend 64) =
      (decodeAddress alphabet) + 241#64 by cases alphabet <;> decide +kernel,
    show BitVec.add ((decodeAddress alphabet) + 33#64) (6#64) = (decodeAddress alphabet) + 39#64 by cases alphabet <;> decide +kernel] at hh
  simpa only [decide_eq_true_eq] using hh

set_option maxRecDepth 100000 in
theorem decode_empty_prepare [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (he : EntryReady programImage s) (hp : s.RIP = decodeAddress alphabet + 241#64)
    (hnonnull : AddrMode.reg64 1 s ≠ 0#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ EntryReady programImage t ∧
      t.RIP = decodeAddress alphabet + 246#64 ∧ AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, hau, hru, hcu, hu⟩ := decode_empty_test_rcx he hp hret
  change (testR64R64Effect s.RIP 1 1 s).Holds s u at hu
  have heu := entryReadyAfter he hru hcu hu.agrees
  have hpu : u.RIP = decodeAddress alphabet + 244#64 := by
    simpa [testR64R64Effect, hp, BitVec.add_assoc] using hu.rip
  obtain ⟨t, hat, hrt, hct, ht⟩ := decode_empty_je_null heu hpu hret
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := by
    have hh := hu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (AddrMode.reg64 1 s &&& AddrMode.reg64 1 s == 0#64) at hh
    have hfalse : (AddrMode.reg64 1 s == 0#64) = false := by
      apply Bool.eq_false_iff.mpr
      intro hx
      exact hnonnull (beq_iff_eq.mp hx)
    simpa only [BitVec.and_self, hfalse] using hh
  refine ⟨t, hau.trans hat, entryReadyAfter heu hrt hct ht.agrees, ?_, ?_⟩
  · have hh := ht.rip
    change t.RIP = (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then
      branchTarget u.RIP 2 ((0x06#8).signExtend 64) else BitVec.add u.RIP 2#64) at hh
    simp only [hz, Bool.false_eq_true, ite_false, hpu] at hh
    cases alphabet <;> exact hh
  · exact (hu.agrees.trans ht.agrees).mono (by simp [Effect.components,
      testR64R64Effect, jccEffect, branchEffect])

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
