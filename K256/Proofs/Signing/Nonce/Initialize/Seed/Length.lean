import K256.Proofs.Signing.Nonce.Initialize.Seed.Stages
import K256.Proofs.Verify.LIR.Fn100ea0
import K256.Proofs.Verify.Core.Affine.Call
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)

private theorem orderLimb0 : (scalarWords Secp256k1.domain.n)[0] = 0xbfd25e8cd0364141 := by decide +kernel

private theorem orderLimb1 : (scalarWords Secp256k1.domain.n)[1] = 0xbaaedce6af48a03b := by decide +kernel

private theorem orderLimb2 : (scalarWords Secp256k1.domain.n)[2] = 0xfffffffffffffffe := by decide +kernel

private theorem orderLimb3 : (scalarWords Secp256k1.domain.n)[3] = 0xffffffffffffffff := by decide +kernel

private theorem lengthJump {l l' : Label} {a b : Verify.Core.Registers} {m n : Ram}
    (run : program.runBlock (dialect Extracted.programImage) ⟨l, a, m⟩ = .jump ⟨l', b, n⟩) :
    Verify.Core.Reaches l a m l' b n := by
  apply Semantics.Reaches.single
  change (program.runBlock (dialect Extracted.programImage) _).next _ [] = _
  rw [run]
  rfl

private theorem lengthTrans {l l' l'' : Label} {a b c : Verify.Core.Registers} {m n o : Ram}
    (first : Verify.Core.Reaches l a m l' b n) (next : Verify.Core.Reaches l' b n l'' c o) :
    Verify.Core.Reaches l a m l'' c o :=
  first.trans next

set_option maxHeartbeats 650000 in
theorem digestLength {fr : Activation} {a : Verify.Core.Registers}
    (entry : Atom.All Extracted.programImage a fr.original (Fn100ea0.frameAt .l100ea0 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (depth : 2208 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 2208)
    (limit : fr.rsp.toNat + 784 < 2^32)
    (window : Writable Extracted.programImage fr.original fr.rsp 784)
    (dst : fr.rdi = fr.rsp + 712) (secretPtr : fr.rsi = fr.rsp + 32)
    (digestPtr : fr.rcx = fr.rsp + 376)
    (secretLen : fr.rdx = 32) (digestLen : fr.r8 = 32) (extraPtr : fr.r9 = 1)
    (extraLen : memLoad fr.original (fr.rsp + 8) 64 = 0)
    (orderPtr : memLoad fr.original (fr.rsp + 16) 64 = fr.rsp + 616)
    (orderWords : WordsAt fr.original (fr.rsp + 616) 64 (Vector.ofFn fun i : Fin 4 =>
      BitVec.ofNat 64 (Secp256k1.domain.n / 2^(64*i.val))))
    : ∃ b m, Verify.Core.Reaches .l100ea0 a fr.original .l101026 b m ∧ DigestLength fr b m := by
  have _ := image
  have _ := dst
  have _ := secretPtr
  have _ := digestPtr
  have _ := extraPtr
  have _ := extraLen
  generalize original_eq : fr.original = original at entry window orderPtr orderWords ⊢
  have atoms := entry
  simp only [Fn100ea0.frameAt, Fn100ea0.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp, df, cx, dx, bx, bp, si, di, r8, r9, r12, r13, r14, r15, mx, ft, fc,
    retRead, ret, retLow, stack, room, align, readC8, gotC8, readD0, gotD0, readE0, gotE0,
    read10, got10, read20, got20, apart, _⟩ := atoms
  have spBits : a[4].get 64 = fr.rsp := congrArg (Value.get 64) sp
  have cxBits : a[1].get 64 = fr.rcx := congrArg (Value.get 64) cx
  have dxBits : a[2].get 64 = 32 := (congrArg (Value.get 64) dx).trans secretLen
  have bxBits : a[3].get 64 = fr.rbx := congrArg (Value.get 64) bx
  have bpBits : a[5].get 64 = fr.rbp := congrArg (Value.get 64) bp
  have siBits : a[6].get 64 = fr.rsi := congrArg (Value.get 64) si
  have diBits : a[7].get 64 = fr.rdi := congrArg (Value.get 64) di
  have r8Bits : a[8].get 64 = 32 := (congrArg (Value.get 64) r8).trans digestLen
  have r9Bits : a[9].get 64 = fr.r9 := congrArg (Value.get 64) r9
  have r12Bits : a[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
  have r13Bits : a[13].get 64 = fr.r13 := congrArg (Value.get 64) r13
  have r14Bits : a[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have r15Bits : a[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
  have q0 : memLoad original (fr.rsp + 616) 64 = 0xbfd25e8cd0364141 := by
    calc
      _ = (scalarWords Secp256k1.domain.n)[0] := by
        simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using orderWords 0 (by decide)
      _ = _ := orderLimb0
  have q1 : memLoad original (fr.rsp + 624) 64 = 0xbaaedce6af48a03b := by
    calc
      _ = (scalarWords Secp256k1.domain.n)[1] := by
        simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using orderWords 1 (by decide)
      _ = _ := orderLimb1
  have q2 : memLoad original (fr.rsp + 632) 64 = 0xfffffffffffffffe := by
    calc
      _ = (scalarWords Secp256k1.domain.n)[2] := by
        simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using orderWords 2 (by decide)
      _ = _ := orderLimb2
  have q3 : memLoad original (fr.rsp + 640) 64 = 0xffffffffffffffff := by
    calc
      _ = (scalarWords Secp256k1.domain.n)[3] := by
        simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
          BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using orderWords 3 (by decide)
      _ = _ := orderLimb3
  have scan0 : BitVec.ofNat 64 (highestSetBit 0xbfd25e8cd0364141#64) = 63 := by decide +kernel
  have scan1 : BitVec.ofNat 64 (highestSetBit 0xbaaedce6af48a03b#64) = 63 := by decide +kernel
  have scan2 : BitVec.ofNat 64 (highestSetBit 0xfffffffffffffffe#64) = 63 := by decide +kernel
  have scan3 : BitVec.ofNat 64 (highestSetBit 0xffffffffffffffff#64) = 63 := by decide +kernel
  have zeroWord3 : (testFlags (0xffffffffffffffff : BitVec 64)).ZF.getD false = false := by decide +kernel
  have zeroWord2 : (testFlags (0xfffffffffffffffe : BitVec 64)).ZF.getD false = false := by decide +kernel
  have zeroWord1 : (testFlags (0xbaaedce6af48a03b : BitVec 64)).ZF.getD false = false := by decide +kernel
  have readByte (m : Ram) (p : BitVec 64) (x : BitVec 8) :
      memLoad (memStore m p x) p 8 = x :=
    memLoad_memStore_same m p x (by decide) (by decide)
  have extraByte (m : Ram) : memLoad (memStore (memStore m (fr.rsp - 272) (0#8))
      (fr.rsp - 112) fr.r9) (fr.rsp - 272) 8 = 0 := by
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _
      (RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))]
    exact readByte _ _ _
  refine ⟨?_, ?_, ?steps, ?post⟩
  case steps =>
    refine lengthTrans (l' := .l100f18) (b := ?_) (n := ?_) (lengthJump ?start) ?afterStart
    case start =>
      cfg_eval [spBits, cxBits, dxBits, bxBits, bpBits, siBits, diBits, r8Bits, r9Bits,
        r12Bits, r13Bits, r14Bits, r15Bits, cmpSpec, subSpec]
      segment_words [orderPtr, q0, q1, q2, q3]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using (fun x hx => Verify.Core.Affine.coreText x (code_l100ea0 x hx)))
      rfl
    case' afterStart =>
      refine lengthTrans (l' := .l100f75) (b := ?_) (n := ?_) (lengthJump ?test) ?afterTest
    case test =>
      cfg_eval [r8Bits, siBits, readByte, zeroWord3, zeroWord2, zeroWord1]
      simp only [readByte, Bool.not_false, ↓reduceIte, BitVec.reduceSetWidth]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using (fun x hx => Verify.Core.Affine.coreText x (code_l100f18 x hx)))
      rfl
    case' afterTest =>
      refine lengthTrans (l' := .l100f82) (b := ?_) (n := ?_) (lengthJump ?check) ?afterCheck
    case check =>
      cfg_eval [r8Bits, cmpSpec, subSpec]
      rfl
    case' afterCheck =>
      refine lengthTrans (l' := .l101023) (b := ?_) (n := ?_) (lengthJump ?bits) ?afterBits
    case bits =>
      cfg_eval [r8Bits, r9Bits, extraByte, scan0, scan1, scan2, scan3]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using (fun x hx => Verify.Core.Affine.coreText x (code_l100f82 x hx)))
      simp only [extraByte, BitVec.reduceSetWidth]
      rfl
    case afterBits =>
      apply lengthJump
      cfg_eval [r8Bits]
      rfl
  case post =>
    refine ⟨⟨?atoms, ?written⟩, ?order, rfl, rfl, rfl, ?widths⟩
    case atoms =>
      simp only [Fn100ea0.frameAt, Fn100ea0.frameAtG1, Atom.All, Atom.Holds]
      refine ⟨rfl, df, rfl, r8, congrArg (Value.mk 64) secretLen.symm, r12, mx, ft, fc,
        ?_, ?savedLen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, retLow, ?_, room, align,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, apart, trivial⟩
      case savedLen =>
        refine Eq.trans ?_ secretLen.symm
        segment_words []
      all_goals first
        | slot_state region
        | (segment_words [ret, gotC8, gotD0, gotE0, got10, got20]; try rfl)
    case written =>
      rw [original_eq]
      have addr (k : BitVec 64) (hk : k.toNat ≤ 2208) :
          (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
        BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
      have inStack (k : BitVec 64) (bytes : Nat) (hk : k.toNat ≤ 2208) (fit : bytes ≤ k.toNat) :
          InRegions [fr.region] (fr.rsp - k) bytes := by
        refine ⟨fr.region, List.mem_singleton_self _, ?_⟩
        simp only [InRegion, Activation.region, low, addr 2208 (by decide), addr k hk,
          BitVec.reduceToNat]
        omega
      repeat' apply RamWriteFrame.memStore _ _ (inStack _ _ (by decide) (by decide))
      exact RamWriteFrame.refl _ _
    case order =>
      exact ⟨congrArg (Value.mk 64) orderLimb0.symm, congrArg (Value.mk 64) orderLimb1.symm,
        congrArg (Value.mk 64) orderLimb2.symm, congrArg (Value.mk 64) orderLimb3.symm⟩
    case widths =>
      rintro ⟨i, hi⟩ member
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact congrArg Value.width r8

end K256.Proofs.Signing.Nonce.Initialize
