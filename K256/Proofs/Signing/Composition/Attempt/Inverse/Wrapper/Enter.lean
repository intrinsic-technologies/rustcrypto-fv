import K256.Proofs.Signing.Composition.Attempt.Inverse.Wrapper.State
import K256.Proofs.Signing.Composition.Attempt.Memory
import K256.Proofs.Signing.LIR.Fn105420
import K256.Proofs.Signing.LIR.Functions1
import K256.Proofs.Verify.LIR.Fn108e30.Frame
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult)

private def pushed (m : Ram) (p : BitVec 64) : Ram :=
  memStore m (p-8) (0x105b0f : BitVec 64)

private def staged (a : Registers) (m : Ram) (p : BitVec 64) : Ram :=
  let n := memStore (pushed m p) (p-16) (p+456)
  let n := memStore n (p-24) (a[14].get 64)
  let n := memStore n (p-32) (p+656)
  let n := memStore n (p-40) (p+8)
  let n := memStore n (p-48) (p+624)
  memStore n (p-104) (0x109db2 : BitVec 64)

private theorem signingText : ∀ x ∈ LIR.fnCode, x ∈ Extracted.programImage := by
  intro x hx
  apply List.mem_flatMap.mpr
  refine ⟨LIR.textSection, by simp [Extracted.programSections, LIR.textSection], ?_⟩
  simpa only [LIR.fnCode, LIR.sections, ImageSections.toCodeMap, List.flatMap_cons,
    List.flatMap_nil, List.append_nil] using hx

private theorem callWrapper {a : Registers} {m : Ram} {p : BitVec 64}
    (rsp : a[4].get 64 = p) (out : a[12].get 64 = p+8)
    (window : Writable Extracted.programImage m (p-104) 104) :
    ∃ b : Registers,
      LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105afc,a,m⟩ =
        .call ⟨.l109d80,b,pushed m p⟩ (resume .l105b0f 0x105b0f) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[3] = ⟨64,p+624⟩ ∧
      b[6] = ⟨64,p+624⟩ ∧ b[7] = ⟨64,p+8⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [5,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  refine ⟨?_, ?run, ?regs⟩
  case run =>
    cfg_eval [rsp, out]
    refine Eq.trans (ite_eq_left ?_) ?_
    · slot_guard using (fun x hx => signingText x (LIR.code_l105afc x hx))
    · rfl
  case regs =>
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 1600 in
private theorem callCore {a b : Registers} {m : Ram} {p : BitVec 64}
    (rsp : b[4].get 64 = p-8) (bx : b[3].get 64 = p+624)
    (src : b[6] = ⟨64,p+624⟩) (dest : b[7].get 64 = p+8)
    (r12 : b[12].get 64 = p+8) (r13 : b[13].get 64 = p+656)
    (r14 : b[14].get 64 = a[14].get 64) (r15 : b[15].get 64 = p+456)
    (window : Writable Extracted.programImage (pushed m p) (p-104) 104) :
    ∃ c : Registers,
      LIR.program.runBlock (dialect Extracted.programImage) ⟨.l109d80,b,pushed m p⟩ =
        .call ⟨.l108e30,c,staged a m p⟩ (resume .l109db2 0x109db2) ∧
      c[4] = ⟨64,p-104⟩ ∧ c[7] = ⟨64,p-88⟩ ∧ c[6] = ⟨64,p+624⟩ ∧
      c[3] = ⟨64,p+8⟩ ∧ c[2] = ⟨64,0x2021a0⟩ ∧ c[1] = ⟨64,0xb4f20099aa774ec1⟩ ∧
      c[8] = ⟨64,0x202180⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [5,22,39,50,51] → c[i] = b[i] := by
  refine ⟨?_, ?run, ?regs⟩
  case run =>
    cfg_eval [rsp, bx, dest, r12, r13, r14, r15]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using (fun x hx => signingText x (LIR.code_l109d80 x hx)))
    rfl
  case regs =>
    refine ⟨rfl, rfl, src, rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxHeartbeats 550000 in
set_option maxRecDepth 2000 in
theorem enterCore {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg]) {a : Registers} {m : Ram} {st : State} {k : Nat}
    (reduced : DigestReduced s d msg st k a m) (pos : 0 < k) (bound : k < domain.n) :
    ∃ b n, Reach (core .l105afc a m)
        ⟨⟨.l108e30,b,n⟩,resume .l109db2 0x109db2 :: wrapperStack⟩ ∧
      Entry b n (coreSp s) k ∧ Preserved s b ∧ Saved s n ∧ RamWriteFrame m n (inverseRegion s) := by
  let p := sp s
  let n := staged a m p
  obtain ⟨room, high, stackBase⟩ := stackBounds call
  change p.toNat = (stackPtr s).toNat - 1288 at stackBase
  have sub (k : Nat) (hk : k ≤ 9904) : (p - BitVec.ofNat 64 k).toNat = p.toNat - k :=
    belowNat call hk
  have above (k : Nat) (hk : k ≤ 1296) : (p + BitVec.ofNat 64 k).toNat = p.toNat + k :=
    offsetNat call hk
  have lowNat : (p-840).toNat = p.toNat-840 := sub 840 (by decide)
  have coreNat : (coreSp s).toNat = p.toNat-104 := sub 104 (by decide)
  have dstAddr : coreSp s + 16 = p-88 := by dsimp only [coreSp,p]; bv_omega
  have srcAddr : coreSp s + 728 = p+624 := by dsimp only [coreSp,p]; bv_omega
  have stackAddr : coreSp s - BitVec.ofNat 64 736 = p-840 := by
    dsimp only [coreSp,p]; bv_omega
  have dstNat : (p-88).toNat = p.toNat-88 := sub 88 (by decide)
  have srcNat : (p+624).toNat = p.toNat+624 := above 624 (by decide)
  have writable : Writable Extracted.programImage m (p-840) 1104 := by
    rw [show p-840 = sp s + (-840) by rw [BitVec.add_neg_eq_sub]]
    exact stackWindow call reduced.toMemory (by decide)
  have window : Writable Extracted.programImage m (p-104) 104 := by
    rw [show p-104 = sp s + (-104) by rw [BitVec.add_neg_eq_sub]]
    exact stackWindow call reduced.toMemory (by decide)
  have writPushed : Writable Extracted.programImage (pushed m p) (p-104) 104 :=
    window.memStore (p-8) (0x105b0f : BitVec 64)
  have inStack (k : BitVec 64) (hk : k.toNat ≤ 104) :
      InRegions (inverseRegion s) (p-k) 8 := by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change (p-840).toNat ≤ (p-k).toNat ∧ (p-k).toNat + 8 ≤ (p-840).toNat + 1104 ∧
      (p-k).toNat + 8 ≤ 2^64
    have pk : (p-k).toNat = p.toNat-k.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    rw [lowNat, pk]
    omega
  have written : RamWriteFrame m n (inverseRegion s) := by
    dsimp only [n, staged, pushed]
    repeat' apply RamWriteFrame.memStore _ _ (inStack _ (by decide))
    exact .refl _ _
  have windowAfter := writable.of_frame written
  have image := Generate.Generator.Affine.Invert.Core.stackImage writable written (reduced.toMemory.image call)
  have ro : Verify.LIR.rodataSection ∈ Extracted.programSections := by
    simp [Verify.LIR.rodataSection, Extracted.programSections]
  have slots := Verify.LIR.Fn108e30.callSlots_loaded ro image
  obtain ⟨slotRead1, slot1⟩ := slots (0x203de0,0x129770) (by decide)
  obtain ⟨slotRead2, slot2⟩ := slots (0x203e20,0x100a20) (by decide)
  have avoid := (call.separation.2 _ (show Stack.region s signingKeyTrySign.minStackBytes ∈
    writtenRegions signingKeyTrySign s by simp [writtenRegions])).1
  have span := Verify.LIR.Fn108e30.callSlots_span ro
  have apart := apart_of_avoids (lo := 0x203de0) (hi := 0x203e28) avoid
    (fun addr hlo hhi => by
      obtain ⟨v, hv⟩ := span addr hlo hhi
      exact Or.inl ⟨v, Common.programSections_fetchByte_of_mem hv⟩)
    (by rw [stackRegion call]; exact (by decide : 0 < 11200)) (by decide) (by decide)
  rw [stackRegion call] at apart
  change (stackPtr s-11192).toNat + 11200 ≤ 0x203de0 ∨ 0x203e28 ≤ (stackPtr s-11192).toNat at apart
  have bottom : (stackPtr s-11192).toNat = (stackPtr s).toNat - 11192 :=
    Common.stackOffset (off := 11192) call.stackAvailable (by decide)
  rw [bottom] at apart
  have aligned := call.stackAvailable.2.2.2
  change (stackPtr s).toNat % 16 = 8 at aligned
  have bits (a : Value) (v : BitVec 64) (h : a = ⟨64,v⟩) : a.get 64 = v := by
    subst a
    exact BitVec.setWidth_eq _
  obtain ⟨b, first, b4, b3, b6, b7, keepB⟩ :=
    callWrapper (bits _ _ reduced.rsp) (bits _ _ reduced.r12) window
  obtain ⟨c, second, c4, c7, c6, c3, c2, c1, c8, keepC⟩ := callCore
    (bits _ _ b4) (bits _ _ b3) b6 (bits _ _ b7)
    (bits _ _ ((keepB 12 (by decide)).trans reduced.r12))
    (bits _ _ ((keepB 13 (by decide)).trans reduced.r13))
    (congrArg (Value.get 64) (keepB 14 (by decide)))
    (bits _ _ ((keepB 15 (by decide)).trans reduced.r15)) writPushed
  have keep (i : Fin Reg.count) (hi : i.val ∈ [5,22,39,50,51]) : c[i] = a[i] :=
    (keepC i hi).trans (keepB i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      rcases hi with eq | eq | eq | eq | eq <;> simp only [eq,true_or,or_true]))
  have df := (keep 22 (by decide)).trans reduced.df
  refine ⟨c, n, ?reach, ?entry, ?preserved, ?save, written⟩
  case reach =>
    refine .step (b := wrapped .l109d80 b (pushed m p)) ?_ (.step ?_ (.refl _))
    · exact congrArg (Transfer.next (dialect Extracted.programImage) [resume .l102795 0x102795]) first
    · exact congrArg (Transfer.next (dialect Extracted.programImage) wrapperStack) second
  case entry =>
    refine ⟨⟨c4, c7.trans (congrArg (Value.mk 64) dstAddr.symm), df, image, ?_, ?_, ?_, ?_, by decide, ?_, ?_, ?_⟩,
      c6.trans (congrArg (Value.mk 64) srcAddr.symm), c2, c1, c8, ?_, ?_, ?_, pos, bound, slotRead1, slot1, slotRead2, slot2, ?_⟩
    · rw [coreNat]; omega
    · rw [coreNat]; omega
    · exact windowAfter.readable.sub (by rw [lowNat,coreNat]; omega) (by rw [lowNat,coreNat]; omega)
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · rw [stackAddr]
      exact windowAfter.sub (Nat.le_refl _) (by omega)
    · rw [dstAddr]
      exact windowAfter.sub (by rw [lowNat,dstNat]; omega) (by rw [lowNat,dstNat]; omega)
    · rw [coreNat,dstAddr,dstNat]; omega
    · rw [srcAddr]
      have rd : Writable Extracted.programImage m (p+624) 32 := stackWindow call reduced.toMemory (by decide)
      exact rd.readable.of_frame written
    · rw [srcAddr]
      apply WordsAt.of_frame reduced.nonce written (by decide)
      refine ⟨by rw [srcNat]; omega, fun r hr => ?_⟩
      obtain rfl := List.mem_singleton.mp hr
      right
      change (p-840).toNat + 1104 ≤ (p+624).toNat
      rw [lowNat,srcNat]; omega
    · rw [coreNat]; omega
    · rw [coreNat]; omega
  case preserved =>
    exact ⟨c3,(keep 5 (by decide)).trans reduced.rbp,df,
      (congrArg Value.width (keep 39 (by decide))).trans reduced.fp.1,
      (congrArg Value.width (keep 50 (by decide))).trans reduced.fp.2.1,
      (congrArg Value.width (keep 51 (by decide))).trans reduced.fp.2.2⟩
  case save =>
    constructor <;> dsimp only [n, staged, pushed, p] <;> segment_words []

end K256.Proofs.Signing.Composition.Attempt.Inverse
