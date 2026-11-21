import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.LoopTailParts
namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

variable {alphabet : Base16ct.Proofs.Base16ctUpperDecodeCorrect.RFC4648.Alphabet}
open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86.Helpers
open Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

theorem decode_store_memory [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s)
    (hpre : StorePre ((decodeAddress alphabet) + 208#64) 3
      (fun u => lowerStoreAM.addrAt u 3) 1 s)
    (hret : ¬ InProgram boundary.rip)
    (ha : Advances boundary 1 s t) :
    t.external = memStore s.external (lowerStoreAM.addrAt s 3)
      ((Operand.reg 3 : Operand 8).read s) := by
  have hcode : CodeIn (codeRange ((decodeAddress alphabet) + 208#64) [0x88, 0x1c, 0x01]) s := by
    apply hentry.code.mono
    exact decode_codeRangeInImage (entry := (decodeAddress alphabet)) (offset := 208)
      (by intro i; change Fin 3 at i; finite_cases i <;> first | decide +kernel | (cases alphabet <;> decide +kernel))
  have hs := mov_lower_store_step_exact _ s hentry.ready hcode hpre
  let u := afterStep s 3 fun v => writeResult (dataAccess v "store")
    (.mem (lowerStoreAM.addrAt s 3) : Operand 8) ((Operand.reg 3 : Operand 8).read s)
    ((decodeAddress alphabet) + 208#64 + 3#64)
  have hpu : u.RIP = (decodeAddress alphabet) + 211#64 := by
    simpa only [u, BitVec.add_assoc, show 208#64 + 3#64 = 211#64 by decide] using
      afterStep_store_rip hentry.ready 3 (lowerStoreAM.addrAt s 3)
        ((Operand.reg 3 : Operand 8).read s) ((decodeAddress alphabet) + 208#64 + 3#64)
  change step s = some (.next u) at hs
  have hau : Advances boundary 1 s u := by
    apply Advances.of_step hs
    left
    intro heq
    apply hret
    rw [← heq, hpu]
    exact ⟨0x48, by first | decide +kernel | (cases alphabet <;> decide +kernel)⟩
  have htu : t = u := by
    have h := Option.some.inj (ha.symm.trans hau)
    injection h
  rw [htu]
  rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
theorem decode_tail_store [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} {value : BitVec 32}
    (hentry : EntryReady programImage s)
    (hpre : StorePre ((decodeAddress alphabet) + 208#64) 3
      (fun u => lowerStoreAM.addrAt u 3) 1 s)
    (hret : ¬ InProgram boundary.rip)
    (havoid : (storeEffect ((decodeAddress alphabet) + 208#64) 3
      (fun u => lowerStoreAM.addrAt u 3) (fun u => (Operand.reg 3 : Operand 8).read u) s).Avoids programImage)
    (hvalue : (Operand.reg 3#5 : Operand 32).read s = value) :
    ∃ t, Advances boundary 6 s t ∧ EntryReady programImage t ∧
      t.RIP = (if AddrMode.reg64 9 s = AddrMode.reg64 0 s + 1#64
        then (decodeAddress alphabet) + 228#64 else (decodeAddress alphabet) + 48#64) ∧
      AgreesExcept [.reg 6, .reg 3, .reg 0, .flags, .rip, .mem (lowerStoreAM.addrAt s 3) 1] s t ∧
      t.external = memStore s.external (lowerStoreAM.addrAt s 3) (value.setWidth 8) ∧
      AddrMode.reg64 0 t = AddrMode.reg64 0 s + 1#64 ∧
      AddrMode.reg64 6 t = (((Operand.reg 6#5 : Operand 32).read s) |||
        (value.extractLsb' 8 8).setWidth 32).setWidth 64 := by
  have hp19 := hpre.rip
  obtain ⟨s20, ha20, hr20, hc20, he20⟩ :=
    Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions.decode_loop_store
      hentry hp19 hpre hret havoid
  have hstored : (Operand.mem (lowerStoreAM.addrAt s 3) : Operand 8).read s20 =
      (Operand.reg 3#5 : Operand 8).read s := by
    have hw := he20.writes
    simp [storeEffect, Write.AllHold] at hw
    exact hw
  have e20 : EntryReady programImage s20 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter hentry hr20 hc20 he20.agrees
  have hp20 : s20.RIP = (decodeAddress alphabet) + 211#64 := by
    have hh := he20.rip
    change s20.RIP = (decodeAddress alphabet) + 208#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 208#64 + 3#64 = (decodeAddress alphabet) + 211#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s21, ha21, hr21, hc21, he21⟩ := decode_loop_inc_rsi e20 hp20 hret
  have h3_21 : (Operand.reg 3#5 : Operand 32).read s21 =
      (Operand.reg 3#5 : Operand 32).read s := by
    have hh := he20.agrees.trans he21.agrees
    exact hh.read (r := 3#5) (n := 32) (by
      simp [Effect.components, storeEffect, incR64Effect, lowerStoreAM] <;> first | decide +kernel | (cases alphabet <;> decide +kernel))
  have e21 : EntryReady programImage s21 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e20 hr21 hc21 he21.agrees
  have hp21 : s21.RIP = (decodeAddress alphabet) + 214#64 := by
    have hh := he21.rip
    rw [hp20] at hh
    change s21.RIP = (decodeAddress alphabet) + 211#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 211#64 + 3#64 = (decodeAddress alphabet) + 214#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s22, ha22, hr22, hc22, he22⟩ := decode_loop_movzx_ebx_bh e21 hp21 hret
  have h3_22 : (Operand.reg 3#5 : Operand 32).read s22 =
      BitVec.setWidth 32 (((Operand.reg 3#5 : Operand 64).read s21).extractLsb' 8 8) := by
    exact tail_movzx_bh_value he22
  have hpairerr22 : (Operand.reg 3#5 : Operand 32).read s22 =
      BitVec.setWidth 32 ((value).extractLsb' 8 8) := by
    rw [h3_22]
    have hh := h3_21.trans hvalue
    change BitVec.setWidth 32 (BitVec.extractLsb' 8 8 s21.GPR[gprIndex 3#5]) =
      BitVec.setWidth 32 ((value).extractLsb' 8 8)
    have hh' := congrArg (fun x : BitVec 32 => x.extractLsb' 8 8) hh
    have hh'' := congrArg (fun x : BitVec 8 => x.setWidth 32) hh'
    change BitVec.setWidth 32 (BitVec.extractLsb' 8 8 (BitVec.setWidth 32 s21.GPR[gprIndex 3#5])) =
      BitVec.setWidth 32 (BitVec.extractLsb' 8 8 (value)) at hh''
    have hnorm64 (x : BitVec 64) :
        BitVec.extractLsb' 8 8 (BitVec.setWidth 32 x) = BitVec.extractLsb' 8 8 x :=
      BitVec.extractLsb'_setWidth_of_le (b := x) (start := 8) (len := 8) (w' := 32) (by decide)
    rw [hnorm64 s21.GPR[gprIndex 3#5]] at hh''
    simpa [Operand.read, BitVec.setWidth_setWidth] using hh''
  have e22 : EntryReady programImage s22 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e21 hr22 hc22 he22.agrees
  have hp22 : s22.RIP = (decodeAddress alphabet) + 217#64 := by
    have hh := he22.rip
    rw [hp21] at hh
    change s22.RIP = (decodeAddress alphabet) + 214#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 214#64 + 3#64 = (decodeAddress alphabet) + 217#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s23, ha23, hr23, hc23, he23⟩ := decode_loop_or_ebx_ecx e22 hp22 hret
  have hrcx23 : (Operand.reg 6#5 : Operand 32).read s23 =
      (Operand.reg 6#5 : Operand 32).read s22 ||| (Operand.reg 3#5 : Operand 32).read s22 := by
    have hh := tail_or_value he23
    change (Operand.reg 6#5 : Operand 32).read s23 =
      (Operand.reg 6#5 : Operand 32).read s22 ||| (Operand.reg 3#5 : Operand 32).read s22 at hh
    exact hh
  have hrcx_keep : (Operand.reg 6#5 : Operand 32).read s22 =
      (Operand.reg 6#5 : Operand 32).read s := by
    have hh20 := he20.agrees.read (r := 6#5) (n := 32) (by
      simp [Effect.components, storeEffect])
    have hh21 := he21.agrees.read (r := 6#5) (n := 32) (by
      simp only [incR64Effect_components]
      first | decide +kernel | (cases alphabet <;> decide +kernel))
    have hh22 := he22.agrees.read (r := 6#5) (n := 32) (by
      simp [Effect.components, movzxEbxBhEffect] <;> first | decide +kernel | (cases alphabet <;> decide +kernel))
    exact hh22.trans (hh21.trans hh20)
  have hrcx23_value : (Operand.reg 6#5 : Operand 32).read s23 =
      (Operand.reg 6#5 : Operand 32).read s ||| BitVec.setWidth 32 ((value).extractLsb' 8 8) := by
    rw [hrcx23, hrcx_keep, hpairerr22]
  have e23 : EntryReady programImage s23 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e22 hr23 hc23 he23.agrees
  have hp23 : s23.RIP = (decodeAddress alphabet) + 219#64 := by
    have hh := he23.rip
    rw [hp22] at hh
    change s23.RIP = (decodeAddress alphabet) + 217#64 + 2#64 at hh
    rw [show (decodeAddress alphabet) + 217#64 + 2#64 = (decodeAddress alphabet) + 219#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s24, ha24, hr24, hc24, he24⟩ := decode_loop_cmp_rax_rsi e23 hp23 hret
  have e24 : EntryReady programImage s24 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e23 hr24 hc24 he24.agrees
  have hp24 : s24.RIP = (decodeAddress alphabet) + 222#64 := by
    have hh := he24.rip
    rw [hp23] at hh
    change s24.RIP = (decodeAddress alphabet) + 219#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 219#64 + 3#64 = (decodeAddress alphabet) + 222#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s25, ha25, hr25, hc25, he25⟩ := decode_loop_jne e24 hp24 hret
  have e25 : EntryReady programImage s25 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e24 hr25 hc25 he25.agrees
  have hmem20 := decode_store_memory hentry hpre hret ha20
  have hbyte : (Operand.reg 3#5 : Operand 8).read s = value.setWidth 8 := by
    have hh := congrArg (BitVec.setWidth 8) hvalue
    simpa [Operand.read, BitVec.setWidth_setWidth] using hh
  change s20.external = memStore s.external (lowerStoreAM.addrAt s 3)
    ((Operand.reg 3#5 : Operand 8).read s) at hmem20
  rw [hbyte] at hmem20
  have hafter := he21.agrees.trans (he22.agrees.trans (he23.agrees.trans
    (he24.agrees.trans he25.agrees)))
  have hmem25 : s25.external = s20.external := by
    apply hafter.external
    intro c hc x
    cases c <;> simp_all [Component.Covers, Effect.components, incR64Effect,
      movzxEbxBhEffect, Instructions.orR32R32Effect, cmpR64R64Effect, jccEffect, branchEffect]
  have hframe : AgreesExcept
      [.reg 6, .reg 3, .reg 0, .flags, .rip, .mem (lowerStoreAM.addrAt s 3) 1] s s25 := by
    apply (he20.agrees.trans hafter).mono
    intro c hc
    simpa [Effect.components, storeEffect, incR64Effect, movzxEbxBhEffect,
      Instructions.orR32R32Effect, cmpR64R64Effect, jccEffect, branchEffect, gprNumber,
      modrmRm, modrmReg, rexB, rexR, or_assoc, or_left_comm, or_comm] using hc
  have hsi20 : AddrMode.reg64 0 s20 = AddrMode.reg64 0 s :=
    he20.agrees.read (by simp [Effect.components, storeEffect])
  have hsi21 : AddrMode.reg64 0 s21 = AddrMode.reg64 0 s + 1#64 := by
    have hw := he21.writes
    change AddrMode.reg64 0 s21 = AddrMode.reg64 0 s20 + 1#64 at hw
    exact hw.trans (congrArg (fun x => x + 1#64) hsi20)
  have hafter21 := he22.agrees.trans (he23.agrees.trans (he24.agrees.trans he25.agrees))
  have hsi25 : AddrMode.reg64 0 s25 = AddrMode.reg64 0 s + 1#64 := by
    exact (hafter21.read (r := 0#5) (n := 64) (by
      simp [Effect.components, movzxEbxBhEffect, Instructions.orR32R32Effect, cmpR64R64Effect,
        jccEffect, branchEffect, gprNumber, modrmRm, modrmReg])).trans hsi21
  have hcx23 : AddrMode.reg64 6 s23 =
      (((Operand.reg 6#5 : Operand 32).read s) ||| (value.extractLsb' 8 8).setWidth 32).setWidth 64 := by
    have hw := he23.writes
    change AddrMode.reg64 6 s23 =
      (((Operand.reg 6#5 : Operand 32).read s22) ||| ((Operand.reg 3#5 : Operand 32).read s22)).setWidth 64 at hw
    rw [hrcx_keep, hpairerr22] at hw
    exact hw
  have hcx25 : AddrMode.reg64 6 s25 =
      (((Operand.reg 6#5 : Operand 32).read s) ||| (value.extractLsb' 8 8).setWidth 32).setWidth 64 := by
    exact ((he24.agrees.trans he25.agrees).read (by
      simp [Effect.components, cmpR64R64Effect, jccEffect, branchEffect])).trans hcx23
  have hsi23 : AddrMode.reg64 0 s23 = AddrMode.reg64 0 s + 1#64 := by
    exact ((he22.agrees.trans he23.agrees).read (by
      simp [Effect.components, movzxEbxBhEffect, Instructions.orR32R32Effect,
        gprNumber, modrmRm, modrmReg])).trans hsi21
  have ha23reg : AddrMode.reg64 9 s23 = AddrMode.reg64 9 s := by
    exact (he20.agrees.trans (he21.agrees.trans (he22.agrees.trans he23.agrees))).read
      (by simp [Effect.components, storeEffect, incR64Effect, movzxEbxBhEffect,
        Instructions.orR32R32Effect, gprNumber, modrmRm, modrmReg, rexB])
  have hz : (StatusFlags.ofRFLAGS s24.RFLAGS).ZF =
      (AddrMode.reg64 9 s23 - AddrMode.reg64 0 s23 == 0#64) := by
    exact he24.flags.2.2.2.1
  have htarget : s25.RIP = (if AddrMode.reg64 9 s = AddrMode.reg64 0 s + 1#64
      then (decodeAddress alphabet) + 228#64 else (decodeAddress alphabet) + 48#64) := by
    have hh := he25.rip
    change s25.RIP = (if !(StatusFlags.ofRFLAGS s24.RFLAGS).ZF then
      branchTarget s24.RIP 6 ((0xffffff4c#32).signExtend 64) else BitVec.add s24.RIP 6#64) at hh
    rw [hz, ha23reg, hsi23, hp24] at hh
    rw [show branchTarget ((decodeAddress alphabet) + 222#64) 6
        ((0xffffff4c#32).signExtend 64) = (decodeAddress alphabet) + 48#64 by first | decide +kernel | (cases alphabet <;> decide +kernel),
      show BitVec.add ((decodeAddress alphabet) + 222#64) 6#64 =
        (decodeAddress alphabet) + 228#64 by first | decide +kernel | (cases alphabet <;> decide +kernel)] at hh
    have hcompare (a b x y : BitVec 64) :
        (if !(a - b == 0#64) then x else y) = if a = b then y else x := by
      by_cases heq : a = b
      · simp [heq]
      · have hnz : a - b ≠ 0#64 := by
          intro hz
          apply heq
          exact (BitVec.sub_eq_iff_eq_add.mp hz).trans (BitVec.zero_add b)
        simp [heq, hnz]
    exact hh.trans (hcompare _ _ _ _)
  exact ⟨s25, ha20.trans (ha21.trans (ha22.trans (ha23.trans (ha24.trans ha25)))),
    e25, htarget, hframe, hmem25.trans hmem20, hsi25, hcx25⟩

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
