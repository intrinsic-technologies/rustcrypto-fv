import P256.Proofs.Program.Compare.Scan
import P256.Proofs.Program.Compare.Setup

namespace P256.Proofs.Program.Compare

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program.Compare.Ranges (memReadable_slice)

def mainLength (s : RamState) : Nat := ((Operand.reg 1 : Operand 64).read s).toNat

def prefixLength (s : RamState) : Nat := 16 * (mainLength s / 16)

def prefixChanges : List Component :=
  [.reg 0, .reg 2, .reg 3, .reg 6, .reg 7, .reg 9, .reg 10,
    .reg 11, .reg 12, .reg 14, .reg 15, .flags, .rip]

structure PrefixPre (s : RamState) : Prop where
  rip : s.RIP = 0x11c87f
  bound : (Operand.reg 8 : Operand 64).read s = BitVec.ofNat 64 (prefixLength s)
  zero : (StatusFlags.ofRFLAGS s.RFLAGS).ZF = ((Operand.reg 8 : Operand 64).read s == 0)
  left : MemReadable s ((Operand.reg 6 : Operand 64).read s) (mainLength s)
  right : MemReadable s ((Operand.reg 2 : Operand 64).read s) (mainLength s)

structure PrefixEqual (s t : RamState) : Prop where
  rip : t.RIP = 0x11c8c2
  left : (Operand.reg 6 : Operand 64).read t =
    (Operand.reg 6 : Operand 64).read s + BitVec.ofNat 64 (prefixLength s)
  right : (Operand.reg 2 : Operand 64).read t =
    (Operand.reg 2 : Operand 64).read s + BitVec.ofNat 64 (prefixLength s)
  equal : BytesEqual s ((Operand.reg 6 : Operand 64).read s)
    ((Operand.reg 2 : Operand 64).read s) (prefixLength s)

def PrefixOutcome (s t : RamState) : Prop := PrefixEqual s t ∨
  (t.RIP = 0x11c8d0 ∧
    ¬ BytesEqual s ((Operand.reg 6 : Operand 64).read s)
      ((Operand.reg 2 : Operand 64).read s) (mainLength s) ∧
    ((Operand.reg 0 : Operand 64).read t ≠ (Operand.reg 7 : Operand 64).read t ∨
      (Operand.reg 3 : Operand 64).read t ≠ (Operand.reg 14 : Operand 64).read t))

theorem prefixLength_le (s : RamState) : prefixLength s ≤ mainLength s := by
  have := Nat.div_mul_le_self (mainLength s) 16
  simpa only [prefixLength, Nat.mul_comm] using this

theorem scan_prefix [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : PrefixPre s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programSections.toCodeMap t ∧
      AgreesExcept prefixChanges s t ∧ PrefixOutcome s t := by
  obtain ⟨n, u, hsu, hru, hcu, heu, hspu⟩ := main_gate boundary s hr hc hp.rip hb
  have hfu : AgreesExcept [.rip] s u := heu.agrees
  have hipu : u.RIP = if (Operand.reg 8 : Operand 64).read s == 0 then 0x11c8c2 else 0x11c881 := by
    rw [heu.rip]
    simp only [jccEffect, condHolds, hp.zero, branchEffect, branchTarget]
    rfl
  by_cases hz : mainLength s / 16 = 0
  · have hl : prefixLength s = 0 := by simp [prefixLength, hz]
    have h8 : (Operand.reg 8 : Operand 64).read s = 0#64 := by simpa only [hl] using hp.bound
    have hi : u.RIP = 0x11c8c2 := by
      rw [h8] at hipu
      simpa only [BitVec.ofNat_eq_ofNat, beq_self_eq_true, ite_true] using hipu
    refine ⟨n, u, hsu, hru, hcu, hfu.mono (by simp [prefixChanges]), Or.inl ⟨hi, ?_, ?_, ?_⟩⟩
    · simpa only [hl, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hfu.read (n := 64) (r := 6) (by simp)
    · simpa only [hl, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hfu.read (n := 64) (r := 2) (by simp)
    · rw [hl]
      exact fun i hi ↦ by omega
  · have h8 : (Operand.reg 8 : Operand 64).read s ≠ 0 := by
      intro he
      have hh := congrArg BitVec.toNat (hp.bound.symm.trans he)
      have hlo := hp.left.low
      have hle := prefixLength_le s
      change prefixLength s % 2^64 = 0 at hh
      rw [Nat.mod_eq_of_lt (by omega)] at hh
      unfold prefixLength at hh
      omega
    have hi : u.RIP = 0x11c881 := by
      have he : ((Operand.reg 8 : Operand 64).read s == 0) = false := by
        exact beq_eq_false_iff_ne.mpr h8
      rw [he] at hipu
      exact hipu
    obtain ⟨m, v, huv, hrv, hcv, hev, hspv⟩ :=
      main_start_program boundary u hru hcu hi (hb.of_stack_eq hspu)
    have hfv : AgreesExcept prefixChanges s v :=
      (hfu.trans hev.agrees).mono (by simp [mainStartEffect, Effect.components, prefixChanges])
    have hexv : v.external = s.external := hfv.external (by simp [prefixChanges, Component.Covers])
    have h6u := hfu.read (n := 64) (r := 6) (by simp)
    have h2u := hfu.read (n := 64) (r := 2) (by simp)
    have h8u := hfu.read (n := 64) (r := 8) (by simp)
    have h6v := hev.agrees.read (n := 64) (r := 6) (by simp [mainStartEffect, Effect.components])
    have h2v := hev.agrees.read (n := 64) (r := 2) (by simp [mainStartEffect, Effect.components])
    have h8v := hev.agrees.read (n := 64) (r := 8) (by simp [mainStartEffect, Effect.components])
    have h11v : (Operand.reg 11 : Operand 64).read v = 0#64 := hev.writes.2.2
    have hlv : leftAddress v = (Operand.reg 6 : Operand 64).read s := by
      simp only [leftAddress, h6v, h6u, h11v, BitVec.add_zero]
    have hrv' : rightAddress v = (Operand.reg 2 : Operand 64).read s := by
      simp only [rightAddress, h2v, h2u, h11v, BitVec.add_zero]
    obtain ⟨count, hn⟩ := Nat.exists_eq_succ_of_ne_zero hz
    have hplen : prefixLength s = 16 * (count + 1) := by simp [prefixLength, hn]
    have hpv : ScanPre (count + 1) v := by
      refine ⟨hev.rip, ?_, ?_, ?_⟩
      · simp only [h8v, h8u, hp.bound, h11v, BitVec.zero_add, hplen]
      · rw [hlv, ← hplen]
        apply MemReadable.of_external_eq _ hexv
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
          memReadable_slice hp.left 0 (prefixLength s) (by simpa only [Nat.zero_add] using prefixLength_le s)
      · rw [hrv', ← hplen]
        apply MemReadable.of_external_eq _ hexv
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
          memReadable_slice hp.right 0 (prefixLength s) (by simpa only [Nat.zero_add] using prefixLength_le s)
    obtain ⟨k, w, hvw, hrw, hcw, hfw, hout⟩ := scan count hrv hcv
      (hb.of_stack_eq (hspv.trans hspu)) hpv
    have hfsw : AgreesExcept prefixChanges s w :=
      (hfv.trans hfw).mono (by simp [prefixChanges, scanChanges])
    have hequiv : BytesEqual v (leftAddress v) (rightAddress v) (16 * (count + 1)) ↔
        BytesEqual s ((Operand.reg 6 : Operand 64).read s)
          ((Operand.reg 2 : Operand 64).read s) (prefixLength s) := by
      simp only [hlv, hrv', hplen, BytesEqual, hexv]
    rcases hout with hout | hout
    · have hspw : stackPtr w = stackPtr s := hfsw.read (n := 64) (r := 4) (by decide)
      obtain ⟨j, t, hwt, hrt, hct, het, _⟩ :=
        main_finish_program boundary w hrw hcw hout.1 (hb.of_stack_eq hspw)
      refine ⟨n + m + k + j, t, ((hsu.trans huv).trans hvw).trans hwt,
        hrt, hct, (hfsw.trans het.agrees).mono ?_, Or.inl ⟨het.rip, ?_, ?_, hequiv.mp hout.2⟩⟩
      · simp [prefixChanges, mainFinishEffect, Effect.components]
      · rw [het.writes.2, hfw.read (n := 64) (r := 9) (by decide), hev.writes.1,
          h6u, h8u, hp.bound]
      · rw [het.writes.1, hfw.read (n := 64) (r := 10) (by decide), hev.writes.2.1,
          h2u, h8u, hp.bound]
    · refine ⟨n + m + k, w, (hsu.trans huv).trans hvw, hrw, hcw, hfsw,
        Or.inr ⟨hout.1, ?_, hout.2.2⟩⟩
      exact fun h ↦ hout.2.1 (hequiv.mpr (bytesEqual_prefix h (prefixLength_le s)))

end P256.Proofs.Program.Compare
