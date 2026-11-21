import K256.Proofs.Sec1.Sqrt.Streaks
import K256.Proofs.Sec1.Sqrt.LiftedStreaks.Resume

set_option autoImplicit false

namespace K256.Proofs.Sec1.Sqrt.SquareStreak

open X86 X86.Machine X86.UserProcess X86Proofs Prelude
open CFG Lift Refine Common.Field LIR

def useRbp : SquareStreak → Bool
  | .at17034 => true
  | _ => false

private def returnLabels : SquareStreak → List Label
  | .at16293 =>
    [.l11629e, .l1162da, .l116316]
  | .at1673c =>
    [.l116747, .l116783, .l1167bf]
  | .at16bcd =>
    [.l116bd8, .l116c14]
  | .at17034 =>
    [.l11703f, .l11707b, .l1170b7, .l1170f3, .l11712f, .l11716b, .l1171a7,
     .l1171e3, .l11721f, .l11725b, .l117297]
  | .at176e7 =>
    [.l1176f2, .l11772e, .l11776a, .l1177a6, .l1177e2, .l11781e, .l11785a,
     .l117896, .l1178d2, .l11790e, .l11794a, .l117986, .l1179c2, .l1179fe,
     .l117a3a, .l117a76, .l117ab2, .l117aee, .l117b2a, .l117b66, .l117ba2,
     .l117bde]
  | .at18d97 =>
    [.l118da2, .l118dde, .l118e1a]
  | .at1924d =>
    [.l119258, .l119294, .l1192d0, .l11930c, .l119348, .l119384, .l1193c0,
     .l1193fc, .l119438, .l119474, .l1194b0, .l1194ec, .l119528, .l119564,
     .l1195a0, .l1195dc, .l119618, .l119654, .l119690, .l1196cc, .l119708,
     .l119744, .l119780]
  | .at19b89 =>
    [.l119b94, .l119bd0, .l119c0c, .l119c48, .l119c84, .l119cc0]
  | .at1a105 =>
    [.l11a110, .l11a14c]

def firstReturn (streak : SquareStreak) : Label :=
  streak.returnLabels.headD .l1145f0

def lastReturn (streak : SquareStreak) : Label :=
  (streak.returnLabels.drop 1).getLastD streak.firstReturn

theorem firstReturn_address (streak : SquareStreak) :
    address streak.firstReturn = streak.first.pc + 11#64 := by
  cases streak <;> rfl

theorem lastReturn_address (streak : SquareStreak) :
    address streak.lastReturn = streak.last.pc + 11#64 := by
  cases streak <;> rfl

private def Linked (useRbp : Bool) (src : Label) : List Label → Prop
  | [] => True
  | dst :: rest =>
    program.blocks src = LiftedCopy.block (address src) dst (LiftedCopy.dstReg useRbp) ∧
    Linked useRbp dst rest

set_option maxHeartbeats 800000 in
private theorem linked (streak : SquareStreak) :
    Linked streak.useRbp streak.firstReturn (streak.returnLabels.drop 1) := by
  cases streak <;> repeat' first | exact True.intro | rfl | constructor

private theorem returnLabel_bounds (streak : SquareStreak) :
    ∀ l ∈ streak.returnLabels, 0x100000 ≤ (address l).toNat ∧ (address l).toNat + 60 ≤ 0x12aa00 := by
  have h : streak.returnLabels.all
      (fun l => decide (0x100000 ≤ (address l).toNat ∧ (address l).toNat + 60 ≤ 0x12aa00)) =
      true := by cases streak <;> decide +kernel
  exact fun l hl => of_decide_eq_true (List.all_eq_true.mp h l hl)

private theorem returnLabels_head_tail (streak : SquareStreak) :
    streak.firstReturn :: streak.returnLabels.drop 1 = streak.returnLabels := by
  cases streak <;> rfl

private theorem returnLabels_tail_length (streak : SquareStreak) :
    (streak.returnLabels.drop 1).length = streak.count - 1 := by
  cases streak <;> rfl

private theorem reachesLabels (code : CodeMap) (stack : List LIR.lifted.StackFrame)
    (useRbp : Bool) (base : Word) (hroom : 112 ≤ base.toNat) (halign : base.toNat % 16 = 0)
    (hap : base.toNat + 80 ≤ 0x100000 ∨ 0x12aa00 ≤ base.toNat - 112)
    {l : LIR.lifted.Location} {w : Limbs} (tail : List Label)
    (hlink : Linked useRbp l.label tail)
    (hb : ∀ lab ∈ l.label :: tail,
      0x100000 ≤ (address lab).toNat ∧ (address lab).toNat + 60 ≤ 0x12aa00)
    (h : LiftedCopy.Ready code useRbp base w l) :
    ∃ t, (program.sem (Lift.dialect code)).Reaches ⟨l, stack⟩ ⟨t, stack⟩ ∧
      t.label = tail.getLastD l.label ∧
      LiftedCopy.Ready code useRbp base (SqrtChain.iter squareWords tail.length w) t ∧
      RamWriteFrame l.store t.store [roundStack base] ∧
      (∀ i : Fin Reg.count, i.val ∈ LiftedSquare.preserved →
        t.arguments[i.val] = l.arguments[i.val]) := by
  cases tail with
  | nil => exact ⟨l, .refl _, rfl, h, RamWriteFrame.refl _ _, fun _ _ => rfl⟩
  | cons dst rest =>
    have hpc := hb l.label List.mem_cons_self
    have hapSquare : base.toNat + 80 ≤ 0x1145f0 ∨ 0x1148c4 ≤ base.toNat - 112 := by omega
    have ha : base.toNat + 80 ≤ (address l.label).toNat ∨
        (address l.label).toNat + 60 ≤ base.toNat - 112 := by omega
    have hr : (address l.label + 60#64).toNat < 2^32 := by
      rw [BitVec.toNat_add]
      change ((address l.label).toNat + 60) % 2^64 < _
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    obtain ⟨u, hu, hlabel, hReady, hFrame, hRegs⟩ :=
      LiftedCopy.resume stack hlink.1 hroom halign (by omega) hr ha hapSquare h
    obtain ⟨t, ht, htlabel, htReady, htFrame, htRegs⟩ :=
      reachesLabels code stack useRbp base hroom halign hap (l := u) rest (by rw [hlabel]; exact hlink.2)
        (by
          rw [hlabel]
          intro x hx
          exact hb x (List.mem_cons_of_mem _ hx)) hReady
    rw [hlabel] at htlabel
    have he : (dst :: rest).getLastD (l.label : Label) = rest.getLastD dst := List.getLastD_cons
    exact ⟨t, hu.trans ht, htlabel.trans he.symm, htReady,
      hFrame.trans htFrame (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩),
      fun i hi => (htRegs i hi).trans (hRegs i hi)⟩
termination_by tail.length

theorem executeLifted (streak : SquareStreak) (code : CodeMap)
    (stack : List LIR.lifted.StackFrame) {start : LIR.lifted.Location} {base : Word}
    {words : Limbs} (hl : start.label = streak.firstReturn)
    (hroom : 112 ≤ base.toNat) (halign : base.toNat % 16 = 0)
    (hap : base.toNat + 80 ≤ 0x100000 ∨ 0x12aa00 ≤ base.toNat - 112)
    (h : LiftedCopy.Ready code streak.useRbp base words start) :
    ∃ t, (program.sem (Lift.dialect code)).Reaches ⟨start, stack⟩ ⟨t, stack⟩ ∧
      t.label = streak.lastReturn ∧
      LiftedCopy.Ready code streak.useRbp base (SqrtChain.iter squareWords (streak.count - 1) words) t ∧
      RamWriteFrame start.store t.store [roundStack base] ∧
      (∀ i : Fin Reg.count, i.val ∈ LiftedSquare.preserved →
        t.arguments[i.val] = start.arguments[i.val]) := by
  have hlinks : Linked streak.useRbp start.label (streak.returnLabels.drop 1) :=
    hl.symm ▸ streak.linked
  have hb : ∀ l ∈ start.label :: streak.returnLabels.drop 1,
      0x100000 ≤ (address l).toNat ∧ (address l).toNat + 60 ≤ 0x12aa00 := by
    intro lab hmem
    have hmem' : lab ∈ streak.firstReturn :: (streak.returnLabels.drop 1) := hl ▸ hmem
    exact streak.returnLabel_bounds lab (streak.returnLabels_head_tail ▸ hmem')
  obtain ⟨t, ht, hlabel, hReady, hFrame, hRegs⟩ :=
    reachesLabels code stack streak.useRbp base hroom halign hap _ hlinks hb h
  rw [hl] at hlabel
  rw [streak.returnLabels_tail_length] at hReady
  exact ⟨t, ht, hlabel, hReady, hFrame, hRegs⟩

end K256.Proofs.Sec1.Sqrt.SquareStreak
