import K256.Proofs.Sec1.Serialize.Coordinates.Round
import K256.Proofs.Sec1.Tactic.Lemma.Refine

namespace K256.Proofs.Sec1.Serialize.Coordinates

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR
open K256.Proofs.Common.Field

structure Cut (args b : Values Value Reg.count) (m m' : Ram) (base point dest : Word)
    (x y : Limbs) : Prop where
  rsp : b[4] = ⟨64, base⟩
  rbx : b[3] = ⟨64, dest⟩
  rbp : b[5] = ⟨64, 0⟩
  r14 : b[14] = ⟨64, point⟩
  kept : ∀ i : Fin Reg.count, i.val ∈ [12,13,22,39,50,51] → b[i] = args[i]
  frame : RamWriteFrame m m' [⟨(base - 121).toNat, 433⟩]
  saved : SerializerSaved args m' base
  slot : memLoad m' (base + 312) 64 = memLoad m (base + 312) 64
  finite : memLoad m' (point + 80) 8 = memLoad m (point + 80) 8
  packedX : WordsAt m' (base + 151) 64 (packWords (Normalize.normalize x))
  packedY : WordsAt m' (base + 183) 64 (packWords (Normalize.normalize y))

private def bodyWrites (k : Axis) (base : Word) : List MemoryRegion :=
  [⟨(base - 121).toNat, 241⟩, ⟨(base + k.offset).toNat, 32⟩]

private theorem bodyFrame {base : Word} {m m' : Ram} (k : Axis)
    (lo : (base - 121).toNat + 433 ≤ 2^32)
    (h : RamWriteFrame m m' (normalizeWrites base ++ packWrites base k)) :
    RamWriteFrame m m' (bodyWrites k base) := by
  obtain ⟨hbase,hsp,hoff⟩ := stackOffsets lo
  apply (RamWriteFrame.refl _ _).trans h
  intro r hr
  simp [normalizeWrites, packWrites] at hr
  rcases hr with rfl|rfl|rfl|rfl
  all_goals simp [bodyWrites]
  all_goals have h80 : (base + 80).toNat = base.toNat + 80 := hoff 80 (by decide)
  all_goals omega

private theorem whole {base : Word} {m m' : Ram}
    (lo : (base - 121).toNat + 433 ≤ 2^32)
    (h : RamWriteFrame m m' (setupWrites .x base ++ bodyWrites .x base)) :
    RamWriteFrame m m' [⟨(base - 121).toNat, 433⟩] := by
  obtain ⟨hbase,hsp,hoff⟩ := stackOffsets lo
  apply (RamWriteFrame.refl _ _).trans h
  intro r hr
  simp [setupWrites, bodyWrites, Axis.offset] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  all_goals simp
  all_goals have h8 : (base + 8).toNat = base.toNat + 8 := hoff 8 (by decide)
  all_goals have h151 : (base + 151).toNat = base.toNat + 151 := hoff 151 (by decide)
  all_goals have h280 : (base + 280).toNat = base.toNat + 280 := hoff 280 (by decide)
  all_goals omega

private theorem secondFrame {base : Word} {m m' : Ram}
    (lo : (base - 121).toNat + 433 ≤ 2^32)
    (h : RamWriteFrame m m' (setupWrites .y base ++ bodyWrites .y base)) :
    RamWriteFrame m m' (bodyWrites .y base) := by
  obtain ⟨hbase,hsp,hoff⟩ := stackOffsets lo
  apply (RamWriteFrame.refl _ _).trans h
  intro r hr
  simp [setupWrites, bodyWrites] at hr
  rcases hr with rfl|rfl|rfl|rfl
  all_goals simp [bodyWrites]
  all_goals have h8 : (base + 8).toNat = base.toNat + 8 := hoff 8 (by decide)
  all_goals omega

theorem schedule {code : CodeMap} (cover : ∀ x ∈ fnCode, x ∈ code)
    {args : Values Value Reg.count} {m : Ram} {base point dest : Word} {x y : Limbs}
    (rsp : args[4].get 64 = base + 312) (src : args[6].get 64 = point)
    (dst : args[7].get 64 = dest) (flag : args[2].get 64 = 0) (df : args[22] = ⟨1, 0⟩)
    (w12 : args[12].width = 64) (w13 : args[13].width = 64)
    (win : Writable code m (base - 121) 433) (readPoint : Readable m point 88)
    (aligned : base.toNat % 16 = 0)
    (textApart : base.toNat + 312 ≤ 0x100000 ∨ 0x12a9bf ≤ (base - 121).toNat)
    (sep : base.toNat + 312 ≤ point.toNat)
    (wx : WordsAt m point 64 x) (wy : WordsAt m (point + 40) 64 y) :
    ∃ (b : Values Value Reg.count) (m' : Ram), (program.sem (dialect code)).Reaches
      ⟨⟨.l1215e0, args, m⟩, []⟩ ⟨⟨.l121692, b, m'⟩, []⟩ ∧ Cut args b m m' base point dest x y := by
  have lo := win.readable.low
  have pointLow := readPoint.low
  obtain ⟨hbase,_,off⟩ := stackOffsets lo
  have h40 : (point + 40).toNat = point.toNat + 40 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change point.toNat + 40 < 2 ^ 64; omega)]
    rfl
  have h80 : (point + 80).toNat = point.toNat + 80 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change point.toNat + 80 < 2 ^ 64; omega)]
    rfl
  have h151 : (base + 151).toNat = base.toNat + 151 := off 151 (by decide)
  have h183 : (base + 183).toNat = base.toNat + 183 := off 183 (by decide)
  have h312 : (base + 312).toNat = base.toNat + 312 := off 312 (by decide)
  obtain ⟨cx, sx, setupX, saved⟩ := normalizeSetupX cover rsp src dst flag win readPoint (Or.inr sep) wx
  obtain ⟨bx, mx, reachX, rspX, destX, flagX, pointX, keptX, frameX, packedX⟩ :=
    round .x cover setupX win aligned textApart df w12 w13
  have fx := bodyFrame .x lo frameX
  have first := whole lo (appendFrames setupX.frame fx)
  have wy' : WordsAt mx (point + 40) 64 y := wy.of_frame first (by decide) (by
    simp [Outside]
    omega)
  obtain ⟨cy, sy, setupY⟩ := normalizeSetupY cover (congrArg (Value.get 64) rspX)
    pointX destX flagX (win.of_frame first) (readPoint.of_frame first) (Or.inr sep) wy'
  obtain ⟨b, m', reachY, rspY, destY, flagY, pointY, keptY, frameY, packedY⟩ :=
    round .y cover setupY (win.of_frame first) aligned textApart
      ((keptX 22 (by decide)).trans df)
      ((congrArg Value.width (keptX 12 (by decide))).trans w12)
      ((congrArg Value.width (keptX 13 (by decide))).trans w13)
  have fy := secondFrame lo (appendFrames setupY.frame (bodyFrame .y lo frameY))
  have full := first.trans fy (by
    intro r hr
    simp [bodyWrites, Axis.offset] at hr
    rcases hr with rfl|rfl <;> simp <;> omega)
  have savedRead (i : Nat) (hi : 280 ≤ i ∧ i ≤ 304) :
      memLoad m' (base + BitVec.ofNat 64 i) 64 = memLoad sx (base + BitVec.ofNat 64 i) 64 := by
    have ha := off i (by omega)
    apply (appendFrames fx fy).memLoad_eq
    simp [Outside, bodyWrites, Axis.offset]
    omega
  refine ⟨b, m', reachX.trans reachY, rspY, destY, flagY, pointY,
    fun i hi => (keptY i hi).trans (keptX i hi), full, ?_, ?_, ?_, ?_, packedY⟩
  · exact ⟨(savedRead 280 (by decide)).trans saved.rbx, (savedRead 288 (by decide)).trans saved.r14,
      (savedRead 296 (by decide)).trans saved.r15, (savedRead 304 (by decide)).trans saved.rbp⟩
  · apply full.memLoad_eq
    simp [Outside]
    omega
  · apply full.memLoad_eq
    simp [Outside]
    omega
  · apply packedX.of_frame fy (by decide)
    simp [Outside, bodyWrites, Axis.offset]
    omega

end K256.Proofs.Sec1.Serialize.Coordinates
