import K256.Proofs.Signing.Nonce.Initialize.Seed.Reduce.Arithmetic
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)

open Common.Invert.LinearCombination Common.Invert.ModularShift Generate.Generator.Multiply

def digestStage (m : Ram) (sp : BitVec 64) (x : Nat) : Ram :=
  let w := scalarWords x
  let p := scalarWords Secp256k1.domain.n
  let d := words (digestDifference x).1
  let b (i : Fin 4) := borrow w[i] p[i] d[i]
  let m := memStore m (sp - 184) w[3]
  let m := memStore m (sp - 208) w[0]
  let m := memStore m (sp - 176) w[0]
  let m := memStore m (sp - 168) w[1]
  let m := memStore m (sp - 160) w[2]
  let m := memStore m (sp - 152) w[3]
  let m := memStore m (sp - 120) d[0]
  let m := memStore m (sp - 272) (b 0)
  let m := memStore m (sp - 272) (b 1)
  let m := memStore m (sp - 272) (b 2)
  let m := memStore m (sp - 272) (b 3)
  let m := memStore m (sp - 272) d[0]
  let m := memStore m (sp - 264) d[1]
  let m := memStore m (sp - 256) d[2]
  let m := memStore m (sp - 248) d[3]
  let m := memStore m (sp - 208) (b 0)
  let m := memStore m (sp - 208) (b 1)
  let m := memStore m (sp - 208) (b 2)
  let m := memStore m (sp - 208) (b 3)
  memStore m (sp - 288) (0x10126c : BitVec 64)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 6000 in
theorem subtractDigest {fr : Activation} {a : Verify.Core.Registers} {m : Ram} {x : Nat}
    (depth : 2208 ≤ fr.rsp.toNat) (limit : fr.rsp.toNat + 784 < 2^32)
    (bound : x < 2^256) (ready : DigestLimbs fr a m x) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l1010ae,a,m⟩ =
        .call ⟨.l127ea0,b,digestStage m fr.rsp x⟩ (Verify.resumeAt .l10126c 0x10126c) ∧
      b[4] = ⟨64,fr.rsp - 288⟩ ∧ b[7] = ⟨64,fr.rsp - 272⟩ ∧
      b[2] = ⟨64,fr.rsp - 176⟩ ∧ b[6] = ⟨64,4⟩ ∧ b[1] = ⟨64,4⟩ ∧
      b[8] = ⟨64,if x < Secp256k1.domain.n then 1 else 0⟩ ∧
      b[5] = ⟨64,fr.rsp - 272⟩ ∧ b[13].width = 64 ∧
      b[14] = ⟨64,fr.rdi⟩ ∧ ParseSignature.ArgumentWidths b ∧
      ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i] := by
  have atoms := ready.atoms
  simp only [Fn100ea0.frameAt,Fn100ea0.frameAtG1,Atom.All,Atom.Holds] at atoms
  obtain ⟨rsp,_,_,_,_,_,_,_,_,savedDi,_,_,_,_,_,_,_,_,_,win,_⟩ := atoms
  have sp : a[4].get 64 = fr.rsp - 280 := congrArg (Value.get 64) rsp
  let w := scalarWords x
  let p := scalarWords Secp256k1.domain.n
  let d := words (digestDifference x).1
  let bit (i : Fin 4) := borrow w[i] p[i] d[i]
  have p0 : a[15].get 64 = p[0] := congrArg (Value.get 64) ready.w0
  have w0 : memLoad m (fr.rsp - 272) 64 = w[0] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.add_zero,Lift.reduceAddOffset] using ready.words 0 (by decide)
  have d0 : w[0] - p[0] = d[0] := by rfl
  have b0 : (((~~~w[0] ||| p[0]) &&& d[0]) ||| (p[0] &&& ~~~w[0])) >>> 63 = bit 0 := by rfl
  have p1 : a[14].get 64 = p[1] := congrArg (Value.get 64) ready.w1
  have w1 : memLoad m (fr.rsp - 264) 64 = w[1] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.add_zero,Lift.reduceAddOffset] using ready.words 1 (by decide)
  have d1 : ((0 : BitVec 64) - bit 0).sshiftRight 63 + (w[1] - p[1]) = d[1] := by rw [show (0 : BitVec 64) - bit 0 = -(bit 0) from BitVec.zero_sub _]; rfl
  have b1 : ((d[1] &&& (~~~w[1] ||| p[1])) ||| (p[1] &&& ~~~w[1])) >>> 63 = bit 1 := by rw [BitVec.and_comm d[1]]; rfl
  have p2 : a[13].get 64 = p[2] := congrArg (Value.get 64) ready.w2
  have w2 : memLoad m (fr.rsp - 256) 64 = w[2] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.add_zero,Lift.reduceAddOffset] using ready.words 2 (by decide)
  have d2 : ((0 : BitVec 64) - bit 1).sshiftRight 63 + (w[2] - p[2]) = d[2] := by rw [show (0 : BitVec 64) - bit 1 = -(bit 1) from BitVec.zero_sub _]; rfl
  have b2 : ((d[2] &&& (~~~w[2] ||| p[2])) ||| (p[2] &&& ~~~w[2])) >>> 63 = bit 2 := by rw [BitVec.and_comm d[2]]; rfl
  have p3 : a[3].get 64 = p[3] := congrArg (Value.get 64) ready.w3
  have w3 : memLoad m (fr.rsp - 248) 64 = w[3] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.add_zero,Lift.reduceAddOffset] using ready.words 3 (by decide)
  have d3 : ((0 : BitVec 64) - bit 2).sshiftRight 63 + (w[3] - p[3]) = d[3] := by rw [show (0 : BitVec 64) - bit 2 = -(bit 2) from BitVec.zero_sub _]; rfl
  have b3 : ((d[3] &&& (~~~w[3] ||| p[3])) ||| (p[3] &&& ~~~w[3])) >>> 63 = bit 3 := by rw [BitVec.and_comm d[3]]; rfl
  let m1 := memStore m (fr.rsp - 184) w[3]
  have put1 : memStore m (fr.rsp - 184) w[3] = m1 := rfl
  let m2 := memStore m1 (fr.rsp - 208) w[0]
  have put2 : memStore m1 (fr.rsp - 208) w[0] = m2 := rfl
  let m3 := memStore m2 (fr.rsp - 176) w[0]
  have put3 : memStore m2 (fr.rsp - 176) w[0] = m3 := rfl
  let m4 := memStore m3 (fr.rsp - 168) w[1]
  have put4 : memStore m3 (fr.rsp - 168) w[1] = m4 := rfl
  let m5 := memStore m4 (fr.rsp - 160) w[2]
  have put5 : memStore m4 (fr.rsp - 160) w[2] = m5 := rfl
  let m6 := memStore m5 (fr.rsp - 152) w[3]
  have put6 : memStore m5 (fr.rsp - 152) w[3] = m6 := rfl
  let m7 := memStore m6 (fr.rsp - 120) d[0]
  have put7 : memStore m6 (fr.rsp - 120) d[0] = m7 := rfl
  let m8 := memStore m7 (fr.rsp - 272) (bit 0)
  have put8 : memStore m7 (fr.rsp - 272) (bit 0) = m8 := rfl
  let m9 := memStore m8 (fr.rsp - 272) (bit 1)
  have put9 : memStore m8 (fr.rsp - 272) (bit 1) = m9 := rfl
  let m10 := memStore m9 (fr.rsp - 272) (bit 2)
  have put10 : memStore m9 (fr.rsp - 272) (bit 2) = m10 := rfl
  let m11 := memStore m10 (fr.rsp - 272) (bit 3)
  have put11 : memStore m10 (fr.rsp - 272) (bit 3) = m11 := rfl
  let m12 := memStore m11 (fr.rsp - 272) d[0]
  have put12 : memStore m11 (fr.rsp - 272) d[0] = m12 := rfl
  let m13 := memStore m12 (fr.rsp - 264) d[1]
  have put13 : memStore m12 (fr.rsp - 264) d[1] = m13 := rfl
  let m14 := memStore m13 (fr.rsp - 256) d[2]
  have put14 : memStore m13 (fr.rsp - 256) d[2] = m14 := rfl
  let m15 := memStore m14 (fr.rsp - 248) d[3]
  have put15 : memStore m14 (fr.rsp - 248) d[3] = m15 := rfl
  let m16 := memStore m15 (fr.rsp - 208) (bit 0)
  have put16 : memStore m15 (fr.rsp - 208) (bit 0) = m16 := rfl
  let m17 := memStore m16 (fr.rsp - 208) (bit 1)
  have put17 : memStore m16 (fr.rsp - 208) (bit 1) = m17 := rfl
  let m18 := memStore m17 (fr.rsp - 208) (bit 2)
  have put18 : memStore m17 (fr.rsp - 208) (bit 2) = m18 := rfl
  let m19 := memStore m18 (fr.rsp - 208) (bit 3)
  have put19 : memStore m18 (fr.rsp - 208) (bit 3) = m19 := rfl
  have get0 : memLoad m1 (fr.rsp - 272) 64 = w[0] := by
    dsimp only [m1]
    segment_words [w0,w1,w2,savedDi] <;> rfl
  have get1 : memLoad m1 (fr.rsp - 264) 64 = w[1] := by
    dsimp only [m1]
    segment_words [w0,w1,w2,savedDi] <;> rfl
  have get2 : memLoad m2 (fr.rsp - 256) 64 = w[2] := by
    dsimp only [m2, m1]
    segment_words [w0,w1,w2,savedDi] <;> rfl
  have get3 : memLoad m8 (fr.rsp - 272) 64 = bit 0 := by
    dsimp only [m8]
    segment_words [w0,w1,w2,savedDi] <;> rfl
  have get4 : memLoad m8 (fr.rsp - 168) 64 = w[1] := by
    dsimp only [m8, m7, m6, m5, m4]
    segment_words [w0,w1,w2,savedDi] <;> rfl
  have get5 : memLoad m9 (fr.rsp - 272) 64 = bit 1 := by
    dsimp only [m9]
    segment_words [w0,w1,w2,savedDi] <;> rfl
  have get6 : memLoad m9 (fr.rsp - 160) 64 = w[2] := by
    dsimp only [m9, m8, m7, m6, m5]
    segment_words [w0,w1,w2,savedDi] <;> rfl
  have get7 : memLoad m10 (fr.rsp - 152) 64 = w[3] := by
    dsimp only [m10, m9, m8, m7, m6]
    segment_words [w0,w1,w2,savedDi] <;> rfl
  have get8 : memLoad m10 (fr.rsp - 272) 64 = bit 2 := by
    dsimp only [m10]
    segment_words [w0,w1,w2,savedDi] <;> rfl
  have get9 : memLoad m10 (fr.rsp - 88) 64 = fr.rdi := by
    dsimp only [m10, m9, m8, m7, m6, m5, m4, m3, m2, m1]
    segment_words [w0,w1,w2,savedDi] <;> rfl
  have get10 : memLoad m11 (fr.rsp - 120) 64 = d[0] := by
    dsimp only [m11, m10, m9, m8, m7]
    segment_words [w0,w1,w2,savedDi] <;> rfl
  have get11 : memLoad m16 (fr.rsp - 208) 64 = bit 0 := by
    dsimp only [m16]
    segment_words [w0,w1,w2,savedDi] <;> rfl
  have get12 : memLoad m17 (fr.rsp - 208) 64 = bit 1 := by
    dsimp only [m17]
    segment_words [w0,w1,w2,savedDi] <;> rfl
  have get13 : memLoad m18 (fr.rsp - 208) 64 = bit 2 := by
    dsimp only [m18]
    segment_words [w0,w1,w2,savedDi] <;> rfl
  have byte : memLoad m19 (fr.rsp - 208) 8 = (bit 3).setWidth 8 := by
    have small := extractLsb'_memLoad m19 (fr.rsp - 208) (n := 64) 0 8 (by decide) (by decide) (by decide)
    have wb : memLoad m19 (fr.rsp - 208) 64 = bit 3 := memLoad_memStore_same _ _ _ (by decide) (by decide)
    rw [wb] at small
    rw [BitVec.setWidth_eq_extractLsb' (by decide)]
    simpa only [Nat.zero_div,BitVec.add_zero] using small.symm
  have win0 := win
  have win1 : Writable Extracted.programImage m1 (fr.rsp - 2208) 2208 := win0.memStore (fr.rsp - 184) w[3]
  have win2 : Writable Extracted.programImage m2 (fr.rsp - 2208) 2208 := win1.memStore (fr.rsp - 208) w[0]
  have win3 : Writable Extracted.programImage m3 (fr.rsp - 2208) 2208 := win2.memStore (fr.rsp - 176) w[0]
  have win4 : Writable Extracted.programImage m4 (fr.rsp - 2208) 2208 := win3.memStore (fr.rsp - 168) w[1]
  have win5 : Writable Extracted.programImage m5 (fr.rsp - 2208) 2208 := win4.memStore (fr.rsp - 160) w[2]
  have win6 : Writable Extracted.programImage m6 (fr.rsp - 2208) 2208 := win5.memStore (fr.rsp - 152) w[3]
  have win7 : Writable Extracted.programImage m7 (fr.rsp - 2208) 2208 := win6.memStore (fr.rsp - 120) d[0]
  have win8 : Writable Extracted.programImage m8 (fr.rsp - 2208) 2208 := win7.memStore (fr.rsp - 272) (bit 0)
  have win9 : Writable Extracted.programImage m9 (fr.rsp - 2208) 2208 := win8.memStore (fr.rsp - 272) (bit 1)
  have win10 : Writable Extracted.programImage m10 (fr.rsp - 2208) 2208 := win9.memStore (fr.rsp - 272) (bit 2)
  have win11 : Writable Extracted.programImage m11 (fr.rsp - 2208) 2208 := win10.memStore (fr.rsp - 272) (bit 3)
  have win12 : Writable Extracted.programImage m12 (fr.rsp - 2208) 2208 := win11.memStore (fr.rsp - 272) d[0]
  have win13 : Writable Extracted.programImage m13 (fr.rsp - 2208) 2208 := win12.memStore (fr.rsp - 264) d[1]
  have win14 : Writable Extracted.programImage m14 (fr.rsp - 2208) 2208 := win13.memStore (fr.rsp - 256) d[2]
  have win15 : Writable Extracted.programImage m15 (fr.rsp - 2208) 2208 := win14.memStore (fr.rsp - 248) d[3]
  have win16 : Writable Extracted.programImage m16 (fr.rsp - 2208) 2208 := win15.memStore (fr.rsp - 208) (bit 0)
  have win17 : Writable Extracted.programImage m17 (fr.rsp - 2208) 2208 := win16.memStore (fr.rsp - 208) (bit 1)
  have win18 : Writable Extracted.programImage m18 (fr.rsp - 2208) 2208 := win17.memStore (fr.rsp - 208) (bit 2)
  have win19 : Writable Extracted.programImage m19 (fr.rsp - 2208) 2208 := win18.memStore (fr.rsp - 208) (bit 3)
  have flagEq : bit 3 = (if x < Secp256k1.domain.n then 1 else 0) := (digestChoice bound).2
  have flagClean : (⟨64, ((mergeGPR 8 (((bit 3).setWidth 8) &&& 1)
      (((bit 3).setWidth 8).setWidth 64)).setWidth 8).setWidth 64⟩ : Value) =
      ⟨64,if x < Secp256k1.domain.n then 1 else 0⟩ := by
    rw [flagEq]; split <;> rfl
  refine ⟨?_,?call,?regs⟩
  case call =>
    cfg_eval [sp, Lift.reduceAddOffset, p0, w0, d0, b0, p1, w1, d1, b1, p2, w2, d2, b2, p3, w3, d3,
      b3, put1, put2, put3, put4, put5, put6, put7, put8, put9, put10, put11, put12, put13, put14,
      put15, put16, put17, put18, put19, get0, get1, get2, get3, get4, get5, get6, get7, get8, get9,
      get10, get11, get12, get13, byte, savedDi]
    simp -index only [b0]
    simp only [put8,get3,get4]
    simp -index only [d1,b1,put9,get5,get6,d2,b2,put10,get7,get8,get9,d3,b3,put11,
      get10,put12,put13,put14,put15,put16,get11,put17,get12,put18,get13,put19,byte]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1010ae)
    rfl
  case regs =>
    refine ⟨rfl,rfl,rfl,rfl,rfl,flagClean,rfl,rfl,rfl,?_,?_⟩
    · intro ⟨i, hi⟩ member
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · intro ⟨i,hi⟩ member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Signing.Nonce.Initialize
