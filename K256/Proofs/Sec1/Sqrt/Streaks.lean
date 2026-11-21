import K256.Proofs.Sec1.Sqrt.Rounds

set_option autoImplicit false

namespace K256.Proofs.Sec1.Sqrt

open X86 X86.Machine X86.UserProcess X86Proofs Prelude K256.Spec.Program
open CFG Refine Common.Field

inductive SquareStreak where
  | at16293 | at1673c | at16bcd | at17034 | at176e7
  | at18d97 | at1924d | at19b89 | at1a105

namespace SquareStreak

def first : SquareStreak → SquareCallSite
  | .at16293 => ⟨0x16293, .rbxR14⟩
  | .at1673c => ⟨0x1673c, .rbxR14⟩
  | .at16bcd => ⟨0x16bcd, .rbxR14⟩
  | .at17034 => ⟨0x17034, .rbpR14⟩
  | .at176e7 => ⟨0x176e7, .rbxR14⟩
  | .at18d97 => ⟨0x18d97, .rbxR14⟩
  | .at1924d => ⟨0x1924d, .rbxR14⟩
  | .at19b89 => ⟨0x19b89, .rbxR14⟩
  | .at1a105 => ⟨0x1a105, .rbxR14⟩

def count : SquareStreak → Nat
  | .at16293 | .at1673c | .at18d97 => 3
  | .at16bcd | .at1a105 => 2
  | .at17034 => 11
  | .at176e7 => 22
  | .at1924d => 23
  | .at19b89 => 6

def siteAt (streak : SquareStreak) (i : Nat) : SquareCallSite :=
  ⟨streak.first.offset + 60 * i, streak.first.regs⟩

def last (streak : SquareStreak) : SquareCallSite :=
  streak.siteAt (streak.count - 1)

private theorem siteAt_zero (streak : SquareStreak) : streak.siteAt 0 = streak.first := by
  simp only [siteAt, Nat.mul_zero, Nat.add_zero]

private theorem siteAt_succ_pc (streak : SquareStreak) (i : Nat) :
    (streak.siteAt (i + 1)).pc = (streak.siteAt i).pc + 60 := by
  change (Extracted.textAddress + BitVec.ofNat 64 (streak.first.offset + 60 * (i + 1))) = _
  rw [Nat.mul_succ, ← Nat.add_assoc, BitVec.ofNat_add, ← BitVec.add_assoc]
  rfl

private abbrev Checked (streak : SquareStreak) (i : Nat) : Prop :=
  streak.siteAt i ∈ squareCallSites ∧ (streak.siteAt i ∈ copySites ↔ i < streak.count - 1)

private theorem checked (streak : SquareStreak) :
    (List.range streak.count).all (fun i => decide (streak.Checked i)) = true := by
  cases streak <;> decide +kernel

theorem site_mem (streak : SquareStreak) (i : Nat) (hi : i < streak.count) :
    streak.siteAt i ∈ squareCallSites :=
  (of_decide_eq_true (List.all_eq_true.mp streak.checked i (List.mem_range.mpr hi)) :
    streak.Checked i).1

theorem copy_mem (streak : SquareStreak) (i : Nat) (hi : i < streak.count) :
    streak.siteAt i ∈ copySites ↔ i < streak.count - 1 :=
  (of_decide_eq_true (List.all_eq_true.mp streak.checked i (List.mem_range.mpr hi)) :
    streak.Checked i).2

private theorem count_pos (streak : SquareStreak) : 0 < streak.count := by
  cases streak <;> decide

theorem last_mem (streak : SquareStreak) : streak.last ∈ squareCallSites :=
  streak.site_mem _ (by have := streak.count_pos; omega)

theorem last_not_copy (streak : SquareStreak) : streak.last ∉ copySites := by
  intro h
  exact (Nat.lt_irrefl _) ((streak.copy_mem _ (by have := streak.count_pos; omega)).mp h)

private theorem copiedFrom [inst : Bindings] (streak : SquareStreak)
    {boundary : ReturnBoundary} {base : BitVec 64} {s : RamState} {words : Limbs}
    (stride : UnitStringStride inst) (hout : ReturnOutside boundary roundCode)
    (hroom : 112 ≤ base.toNat) (halign : base.toNat % 16 = 0)
    (hap : base.toNat + 80 ≤ 0x100000 ∨ 0x12aa00 ≤ base.toNat - 112)
    (hRsp : base ≠ boundary.rsp) (hPush : base - 8 ≠ boundary.rsp)
    (i n : Nat) (hfit : i + n ≤ streak.count - 1)
    (hrip : s.RIP = (streak.siteAt i).pc) (hs : RoundState (streak.siteAt i) base words s) :
    ∃ fuel t, Advances boundary fuel s t ∧ t.RIP = (streak.siteAt (i + n)).pc ∧
      RoundState (streak.siteAt (i + n)) base (SqrtChain.iter squareWords n words) t ∧
      RamWriteFrame s.external t.external [roundStack base] ∧
      (∀ r ∈ Activation.calleeSavedNumbers,
        (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read t =
        (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read s) := by
  cases n with
  | zero =>
    exact ⟨0, s, (advances_zero boundary s s).2 rfl, hrip, hs,
      RamWriteFrame.refl _ _, fun _ _ => rfl⟩
  | succ n =>
    have hc := (streak.copy_mem i (by omega)).mpr (by omega)
    obtain ⟨a, u, hsu, huRip, hu, _, huFrame, huRegs⟩ :=
      (streak.siteAt i).squareCopyRound hc stride hout hroom halign hap hRsp hPush hrip hs
    have hu' : RoundState (streak.siteAt (i + 1)) base (squareWords words) u :=
      ⟨hu.entry, hu.rsp, hu.workspace, hu.inputReg, hu.outputReg, hu.df, hu.input⟩
    have huRip' := huRip.trans (streak.siteAt_succ_pc i).symm
    obtain ⟨b, t, hut, htRip, ht, htFrame, htRegs⟩ :=
      streak.copiedFrom stride hout hroom halign hap hRsp hPush (i + 1) n
        (by omega) huRip' hu'
    rw [show i + 1 + n = i + (n + 1) by omega] at htRip ht
    exact ⟨a+b, t, hsu.trans hut, htRip, ht,
      huFrame.trans htFrame (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩),
      fun r hr => (htRegs r hr).trans (huRegs r hr)⟩
termination_by n

theorem execute [inst : Bindings] (streak : SquareStreak)
    {boundary : ReturnBoundary} {base : BitVec 64} {s : RamState} {words : Limbs}
    (stride : UnitStringStride inst) (hout : ReturnOutside boundary roundCode)
    (hroom : 112 ≤ base.toNat) (halign : base.toNat % 16 = 0)
    (hap : base.toNat + 80 ≤ 0x100000 ∨ 0x12aa00 ≤ base.toNat - 112)
    (hRsp : base ≠ boundary.rsp) (hPush : base - 8 ≠ boundary.rsp)
    (hrip : s.RIP = streak.first.pc) (hs : RoundState streak.first base words s) :
    ∃ fuel t, Advances boundary fuel s t ∧ t.RIP = streak.last.pc + 11#64 ∧
      RoundState streak.last base (SqrtChain.iter squareWords (streak.count - 1) words) t ∧
      WordsAt t.external (base + 40) 64 (SqrtChain.iter squareWords streak.count words) ∧
      RamWriteFrame s.external t.external [roundStack base] ∧
      (∀ r ∈ Activation.calleeSavedNumbers,
        (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read t =
        (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read s) := by
  obtain ⟨a, u, hsu, huRip, hu, huFrame, huRegs⟩ :=
    streak.copiedFrom stride hout hroom halign hap hRsp hPush 0 (streak.count - 1)
      (by omega) (by rwa [siteAt_zero]) (by rwa [siteAt_zero])
  rw [Nat.zero_add] at huRip hu
  obtain ⟨b, t, hut, htRip, ht, htOut, htFrame, htRegs⟩ :=
    streak.last.squareRound streak.last_mem stride hout hroom halign hap hRsp hPush huRip hu
  have hp : streak.count - 1 + 1 = streak.count := by have := streak.count_pos; omega
  have he := SqrtChain.iterate_comm squareWords squareWords squareWords (fun _ => rfl)
    (streak.count - 1) words
  change squareWords (SqrtChain.iter squareWords (streak.count - 1) words) =
    SqrtChain.iter squareWords (streak.count - 1 + 1) words at he
  rw [hp] at he
  rw [he] at htOut
  exact ⟨a+b, t, hsu.trans hut, htRip, ht, htOut,
    huFrame.trans htFrame (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩),
    fun r hr => (htRegs r hr).trans (huRegs r hr)⟩

end SquareStreak

end K256.Proofs.Sec1.Sqrt
