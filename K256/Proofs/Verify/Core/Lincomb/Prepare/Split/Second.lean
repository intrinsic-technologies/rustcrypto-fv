import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.First
import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.NegateStaged

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Multiply.Prepare.Bases.Negate (storeFour)
open Generate.Curve

private theorem finishSecond {a b c : Registers} {m n o : Ram} {sp src tables digits : BitVec 64}
    {k : Nat} (entry : RoutineEntry a m sp 0x558)
    (s : FirstMagnitude a m sp src tables digits k b n)
    (rsp : c[4] = ⟨64,frameSp sp⟩) (keep : KeptForMagnitude b c)
    (foot : RamWriteFrame n o (negateWrites (frameSp sp) 176))
    (words : WordsAt o (frameSp sp + 0xb0) 64 (scalarWords (second k).natAbs)) :
    SplitState a m sp src tables digits k c o := by
  have room := entry.room
  have limit := entry.returnSlot.low
  have base : (frameSp sp).toNat = sp.toNat - 696 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 696 ≤ sp.toNat; omega))
  have outside (q : BitVec 64) (l : Nat)
      (lo : (frameSp sp).toNat ≤ q.toNat) (hi : q.toNat + l ≤ sp.toNat)
      (staged : q.toNat + l ≤ (frameSp sp).toNat + 56 ∨ (frameSp sp).toNat + 88 ≤ q.toNat)
      (dst : q.toNat + l ≤ (frameSp sp).toNat + 176 ∨ (frameSp sp).toNat + 208 ≤ q.toNat) :
      Outside (negateWrites (frameSp sp) 176) q l := by
    refine ⟨by omega, ?_⟩
    intro r hr
    simp only [negateWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · right; change (frameSp sp).toNat - 56 + 56 ≤ q.toNat; omega
    · exact staged
    · exact dst
  have saved (off : BitVec 64) (nonzero : 8 ≤ off.toNat) (small : off.toNat ≤ 48) :
      memLoad o (sp - off) 64 = memLoad n (sp - off) 64 := by
    apply foot.memLoad_eq
    have pos := BitVec.toNat_sub_of_le (x := sp) (y := off) (BitVec.le_def.mpr (by omega))
    apply outside <;> try simp only [Nat.reduceDiv]
    all_goals first | omega | exact Or.inr (by omega)
  have keepSlot (off : BitVec 64) (width : Nat) (size : off.toNat + width/8 ≤ 696)
      (staged : off.toNat + width/8 ≤ 56 ∨ 88 ≤ off.toNat)
      (dst : off.toNat + width/8 ≤ 176 ∨ 208 ≤ off.toNat) :
      memLoad o (frameSp sp + off) width = memLoad n (frameSp sp + off) width := by
    have pos : (frameSp sp + off).toNat = (frameSp sp).toNat + off.toNat := by
      rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]
    apply foot.memLoad_eq
    apply outside <;> omega
  refine ⟨s.toSavedFrame.preserve rsp keep saved,
    s.frame.trans foot (negateWritesWithin room (by decide)),(keepSlot _ _ (by decide) (by decide) (by decide)).trans s.pointPtr,
    (keepSlot _ _ (by decide) (by decide) (by decide)).trans s.digitPtr,
    (congrArg (Value.get 8) (keep 14 (by decide))).trans s.firstSign,
    (keepSlot _ _ (by decide) (by decide) (by decide)).trans s.secondSign,?first,words⟩
  case first =>
    intro i hi
    have h := s.firstWords i hi
    rcases (by omega : i=0 ∨ i=1 ∨ i=2 ∨ i=3) with rfl|rfl|rfl|rfl
    all_goals
      simp only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,
        BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] at h ⊢
      exact (keepSlot _ _ (by decide) (by decide) (by decide)).trans h

theorem storeSecondMagnitude {a b : Registers} {m n : Ram} {sp src tables digits : BitVec 64}
    {k : Nat} (entry : RoutineEntry a m sp 0x558)
    (s : FirstMagnitude a m sp src tables digits k b n) :
    ∃ c o, Reaches (secondLabel k) b n .l10f4af c o ∧ SplitState a m sp src tables digits k c o := by
  let base := frameSp sp
  let x := splitSecond k
  have room := entry.room
  have limit := entry.returnSlot.low
  have baseNat : base.toNat = sp.toNat - 696 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 696 ≤ sp.toNat; omega))
  have dstNat : (base+176).toNat = base.toNat + 176 := by
    rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by change base.toNat + 176 < 2^64; omega)]
    rfl
  have st : SecondRegisters b n base (scalarWords x) :=
    ⟨congrArg (Value.get 64) s.rsp,s.low,s.midLow,s.midHigh,s.high⟩
  have bound : x < domain.n := Nat.mod_lt _ (by decide)
  have hmag := Generate.Generator.Multiply.Prepare.Bases.selectMagnitude bound
  change (if signByte (second k) = 0 then scalarWords x else _) = scalarWords (second k).natAbs at hmag
  have stack : Writable Extracted.programImage n (sp-1368) 1368 := entry.stack.of_frame s.frame
  have bot : (sp - (1368 : BitVec 64)).toNat = sp.toNat - 1368 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr room)
  have win : Writable Extracted.programImage n base 0x100 := stack.sub (by omega) (by omega)
  by_cases neg : second k < 0
  · have pushed : (base - 8).toNat = base.toNat - 8 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 8 ≤ base.toNat; omega))
    have below : Writable Extracted.programImage n (base-8) 8 := stack.sub (by omega) (by omega)
    obtain ⟨c,call,rsp,di,si,dx,ws,keep⟩ := stageSecond st s.arguments win below
    obtain ⟨d,o,path,rs,fixed,_,foot,words⟩ :=
      negateStaged (off := 176) entry s.toSplitFrame (by decide) (by decide) (by decide : (0x10f44a : BitVec 64).toNat < 2^32)
        bound ws keep rsp di si dx call
    simp only [signByte,neg,ite_true,BitVec.reduceEq,ite_false] at hmag
    exact ⟨_,_,by simpa only [secondLabel,neg,ite_true] using path.trans (magnitudeJoin _ _),
      finishSecond entry s rs fixed foot (hmag ▸ words)⟩
  · obtain ⟨c,path,rsp,keep⟩ := copySecond st win
    have atDst : InRegions (negateWrites base 176) (base+176) 32 :=
      ⟨_,.tail _ (.tail _ (.head _)),by dsimp only; omega,by dsimp only; omega,by omega⟩
    have frame := Serializer.storeWords_frame (scalarWords x) (RamWriteFrame.refl n _) atDst
    have words := Serializer.storeWords_wordsAt n (base+176) (scalarWords x) (by omega)
    simp only [signByte,neg,ite_false,ite_true] at hmag
    exact ⟨_,_,by simpa only [secondLabel,neg,ite_false,storeFour] using path,
      finishSecond entry s (rsp.trans s.rsp) keep frame (hmag ▸ words)⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
