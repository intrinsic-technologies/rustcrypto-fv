import K256.Proofs.Ecdh.Decode.Input
import K256.Proofs.Ecdh.Decode.Packing.Verify

namespace K256.Proofs.Ecdh.Decode.Packing

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Ecdh.LIR
open Standards.SECG.ECC

abbrev Reaches (code : CodeMap) :=
  (program.sem (dialect code)).Reaches

private theorem jump {code : CodeMap} {l l' : Label} {a b : Values Value Reg.count}
    {m n : Ram} (stack : List (StackFrame Value Label signature Reg.count))
    (h : program.runBlock (dialect code) ⟨l, a, m⟩ = .jump ⟨l', b, n⟩) :
    Reaches code ⟨⟨l, a, m⟩, stack⟩ ⟨⟨l', b, n⟩, stack⟩ := by
  apply Semantics.Reaches.single
  change (program.runBlock _ _).next _ _ = _
  rw [h]
  rfl

private theorem saved_initial (sp : BitVec 64) (regs : Values Value Reg.count) (m : Ram) :
    memLoad (pushedMemory sp regs m) (sp + 240) 64 = regs[3].get 64 ∧
    memLoad (pushedMemory sp regs m) (sp + 248) 64 = regs[14].get 64 ∧
    memLoad (pushedMemory sp regs m) (sp + 256) 64 = regs[15].get 64 := by
  unfold pushedMemory
  have keep {p : Ram} {u v : BitVec 64} (w : BitVec 64)
      (apart : 8 ≤ (v - u).toNat ∧ 8 ≤ (u - v).toNat) :
      memLoad (memStore p (sp + u) w) (sp + v) 64 = memLoad p (sp + v) 64 :=
    memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl apart)
  refine ⟨memLoad_memStore_same _ _ _ (by decide) (by decide), ?_, ?_⟩
  · rw [keep _ (by decide), memLoad_memStore_same _ _ _ (by decide) (by decide)]
  · rw [keep _ (by decide), keep _ (by decide), memLoad_memStore_same _ _ _ (by decide) (by decide)]

def AffineCallReady (code : CodeMap) (sp : BitVec 64) (regs : Values Value Reg.count)
    (m : Ram) (bytes : ByteArray) (stack : List (StackFrame Value Label signature Reg.count)) :
    Prop :=
  ∃ args final,
    Reaches code ⟨⟨.l120f30, regs, m⟩, stack⟩
      ⟨⟨.l121480, args, final⟩, affineResume :: stack⟩ ∧
    args[3] = ⟨64, regs[7].get 64⟩ ∧ args[4] = ⟨64, sp - 8⟩ ∧
    args[6] = ⟨64, sp + 72⟩ ∧ args[7] = ⟨64, sp + 144⟩ ∧
    args[14] = ⟨64, sp + 144⟩ ∧ args[15].get 8 = 1 ∧
    args[15] = ⟨64, args[15].get 64⟩ ∧ args[8].width = 64 ∧ args[9].width = 64 ∧
    registersKept regs args ∧
    (∀ i < 65, memByte final (sp + 72 + BitVec.ofNat 64 i) = bytes.data[i]?.getD 0) ∧
    memLoad final (sp - 8) 64 = 0x121177 ∧
    memLoad final (sp + 240) 64 = regs[3].get 64 ∧
    memLoad final (sp + 248) 64 = regs[14].get 64 ∧
    memLoad final (sp + 256) 64 = regs[15].get 64 ∧
    RamWriteFrame m final [window sp]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem packToAffine {code : CodeMap} {sp src : BitVec 64}
    {regs : Values Value Reg.count} {m : Ram} {bytes : ByteArray} {q : Curve.Point}
    (stack : List (StackFrame Value Label signature Reg.count))
    (hsp : regs[4].get 64 = sp + 264) (hsrc : regs[6].get 64 = src)
    (r8Width : regs[8].width = 64) (r9Width : regs[9].width = 64)
    (win : Writable code m (sp - 8) 272) (read : Readable m src 33)
    (apart : Outside [window sp] src 33)
    (input : ∀ i < 33, memByte m (src + BitVec.ofNat 64 i) = bytes.data[i]?.getD 0)
    (point : K256.Spec.Secp256k1.groupPoint bytes = some q)
    (hc : ∀ x ∈ fnCode, x ∈ code) :
    AffineCallReady code sp regs m bytes stack := by
  have cases := groupPoint_cases point
  obtain ⟨tag, tag_head, valid, identity⟩ :
      ∃ tag : UInt8, bytes.data[0]? = some tag ∧
        (tag = 0 ∨ tag = 2 ∨ tag = 3 ∨ tag = 5) ∧
        (tag = 0 → bytes = ⟨Array.replicate 33 0⟩) := by
    rcases cases with ⟨h, _⟩ | ⟨_, tag, hd, valid, _⟩
    · exact ⟨0, by rw [h]; rfl, .inl rfl, fun _ => h⟩
    · refine ⟨tag, hd, .inr valid, fun e => ?_⟩
      rcases valid with rfl | rfl | rfl <;> contradiction
  have size : bytes.size = 33 := by
    rcases cases with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; rfl
    · exact h
  have tagValid : tag.toBitVec = 0 ∨ tag.toBitVec = 2 ∨ tag.toBitVec = 3 ∨ tag.toBitVec = 5 := by
    rcases valid with rfl | rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr rfl))
  have head : memLoad m src 8 = tag.toBitVec := by
    apply memLoad_eq_of_memByte (by decide)
    intro i hi
    have eq : i = 0 := by omega
    subst i
    rw [input 0 (by decide), tag_head]
    simp [storedByte]
  let pushed := pushedMemory sp regs m
  have pushFrame := pushedMemory_frame regs win
  have pushWin := win.of_frame pushFrame
  have pushRead := read.of_frame pushFrame
  have pushedInput (i : Nat) (hi : i < 33) :
      memByte pushed (src + BitVec.ofNat 64 i) = bytes.data[i]?.getD 0 :=
    (input_byte_of_frame pushFrame apart hi).trans (input i hi)
  have natSp : sp.toNat = (sp - 8).toNat + 8 :=
    toNat_of_offsets (n := 232) (c := 0) (addr_self sp) (addr_sub sp 8) win.readable.low (by decide)
  have lowWin := win.readable.low
  have lowSp : sp.toNat + 232 < 2^64 := by omega
  have apartSp : Outside [⟨sp.toNat, 232⟩] src 33 := by
    refine ⟨apart.1, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    have h := apart.2 (window sp) (List.mem_singleton_self _)
    simp only [window] at h
    change src.toNat + 33 ≤ sp.toNat ∨ sp.toNat + 232 ≤ src.toNat
    omega
  have accRead :
      memLoad (compressedZeros.memory sp src pushed 0) (src + 7) 32 = memLoad pushed (src + 7) 32 := by
    apply (compressedZeros.frame sp src pushed 0 (by decide +kernel) lowSp).memLoad_eq
    have rLow := read.low
    have eq : (src + (7 : BitVec 64)).toNat = src.toNat + 7 := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change src.toNat + 7 < _; omega)]
      rfl
    refine ⟨by rw [eq]; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    have h := apartSp.2 _ (List.mem_singleton_self _)
    change src.toNat + 33 ≤ sp.toNat ∨ sp.toNat + 232 ≤ src.toNat at h
    change (src + (7 : BitVec 64)).toNat + 4 ≤ sp.toNat ∨ sp.toNat + 232 ≤ (src + (7 : BitVec 64)).toNat
    rw [eq]
    omega
  obtain ⟨entry, eRun, rt, rbx, rsp, rsi, eKeep⟩ :=
    entryBlock hsp hsrc read win apart head tagValid hc
  obtain ⟨body, dRun, dKeep⟩ := dispatchBlock (code := code) (m := pushed) rt tagValid
  have bodySp : body[4].get 64 = sp :=
    (congrArg (Value.get 64) (dKeep 4 (by decide) (by decide))).trans rsp
  have bodySrc : body[6].get 64 = src :=
    (congrArg (Value.get 64) ((dKeep 6 (by decide) (by decide)).trans rsi)).trans hsrc
  have bodyBx : body[3] = ⟨64, regs[7].get 64⟩ :=
    (dKeep 3 (by decide) (by decide)).trans rbx
  have body8 : body[8].width = 64 :=
    (congrArg Value.width ((dKeep 8 (by decide) (by decide)).trans
      (eKeep 8 (by decide) (by decide)))).trans r8Width
  have bodyKeep : registersKept regs body := by
    intro r hr h
    exact (dKeep r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega) h).trans
      (eKeep r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega) h)
  obtain ⟨img, args, acc, run, accEq, bx, s, choice, r15Width, r8BodyWidth, keep, bound, packedBound, independent, byte⟩ :
      ∃ (img : StackImage) (args : Values Value Reg.count) (acc : BitVec 32),
        Reaches code ⟨⟨.l120f30, regs, m⟩, stack⟩
          ⟨⟨.l121105, args, img.memory sp src pushed 0⟩, stack⟩ ∧
        args[0].get 32 = acc ∧ args[3] = ⟨64, regs[7].get 64⟩ ∧
        args[4].get 64 = sp ∧ args[15].get 8 = 1 ∧ args[15] = ⟨64, args[15].get 64⟩ ∧
        args[8].width = 64 ∧ registersKept regs args ∧
        img.endOffset ≤ 232 ∧
        (packedImage img).endOffset ≤ 232 ∧
        (∀ a, img.memory sp src pushed a = img.memory sp src pushed 0) ∧
        (∀ i < 65, memByte ((packedImage img).memory sp src pushed acc)
          (sp + BitVec.ofNat 64 (72 + i)) = bytes.data[i]?.getD 0) := by
    by_cases isZero : tag.toBitVec = 0
    · have allZero := identity (UInt8.toBitVec_inj.mp isZero)
      have zero (i : Nat) (hi : i < 33) : memByte pushed (src + BitVec.ofNat 64 i) = 0 := by
        rw [pushedInput i hi, allZero]
        simp [hi]
      rw [ite_eq_left isZero] at dRun
      obtain ⟨args, run, acc, bx, spEq, c, w15, w8, keep⟩ := identityBlock body pushed sp src
        bodySp bodySrc pushWin pushRead zero hc
      refine ⟨identityImage, args, 0, (jump stack eRun).trans ((jump stack dRun).trans (jump stack run)),
        acc, bx.trans bodyBx, spEq, c, w15, w8,
        bodyKeep.trans keep, by decide +kernel, by decide +kernel, fun _ => rfl, ?_⟩
      intro i hi
      rw [identity_bytes _ _ _ lowSp apartSp _ hi, allZero]
      by_cases h : i < 33 <;> simp [h]
    · rw [ite_eq_right isZero] at dRun
      obtain ⟨args, run, acc, bx, spEq, c, w15, w8, keep⟩ := compressedBlock body pushed sp src
        bodySp bodySrc body8 pushWin pushRead hc
      refine ⟨compressedImage, args, memLoad pushed (src + 7) 32, (jump stack eRun).trans ((jump stack dRun).trans (jump stack run)),
        acc.trans accRead, bx.trans bodyBx, spEq, c, w15, w8,
        bodyKeep.trans keep, by decide +kernel, by decide +kernel, fun _ => rfl, ?_⟩
      intro i hi
      rw [compressed_bytes _ _ _ lowSp apartSp _ hi]
      by_cases inside : i < 33
      · rw [ite_eq_left inside, pushedInput i inside]
      · rw [ite_eq_right inside, Array.getElem?_eq_none (by change bytes.size ≤ i; omega)]
        rfl
  obtain ⟨finalArgs, called, cbx, csp, csrc, cdst, cr14, cr15, cr8, ckeep⟩ :=
    affineCallBlock args (img.memory sp src pushed 0) sp s
      (pushWin.of_frame (image_frame pushWin img 0 bound)) hc
  let packed := (packedImage img).memory sp src pushed acc
  let final := memStore packed (sp - 8) (0x121177 : BitVec 64)
  rw [accEq, packed_suffix_memory img sp src pushed acc independent] at called
  have callStep : Reaches code ⟨⟨.l121105, args, img.memory sp src pushed 0⟩, stack⟩
      ⟨⟨.l121480, finalArgs, final⟩, affineResume :: stack⟩ := by
    apply Semantics.Reaches.single
    change (program.runBlock _ _).next _ _ = _
    rw [called]
    rfl
  obtain ⟨savedBx, saved14, saved15⟩ := saved_initial sp regs m
  refine ⟨finalArgs, final, run.trans callStep, cbx.trans bx,
    csp, csrc, cdst, cr14, (congrArg _ cr15).trans choice, ?_,
    (congrArg Value.width cr8).trans r8BodyWidth,
    (congrArg Value.width ((keep.trans ckeep) 9 (by decide) (by decide))).trans r9Width,
    keep.trans ckeep,
    fun i hi => (packedCall_byte hi).trans (byte i hi),
    memLoad_memStore_same _ _ _ (by decide) (by decide), ?_, ?_, ?_, ?_⟩
  · rw [cr15]
    exact r15Width
  · exact (saved_after_packing pushWin.readable.low packedBound acc (off := 240) (by decide)).trans savedBx
  · exact (saved_after_packing pushWin.readable.low packedBound acc (off := 248) (by decide)).trans saved14
  · exact (saved_after_packing pushWin.readable.low packedBound acc (off := 256) (by decide)).trans saved15
  · exact pushFrame.trans (packedCall_frame pushWin _ acc packedBound) fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩

end K256.Proofs.Ecdh.Decode.Packing
