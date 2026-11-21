import K256.Proofs.Signing.Composition.Attempt.Inverse.Wrapper.State
import K256.Proofs.Verify.Core.Scalars.Digest.Reduce.Barrier
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Tactic
import K256.Proofs.Signing.Transfer.Verify
import K256.Proofs.Signing.Composition.Reach
import K256.Proofs.Signing.Composition.Attempt.Memory

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

open Verify.LIR in
private theorem loadChoice {s : RamState} {b : Registers} {m : Ram} {x : BitVec 64} {k : Nat}
    (stack : Writable Extracted.programImage m (x-9) 64)
    (room : 9 ≤ x.toNat) (rsp : b[4] = ⟨64,x⟩)
    (pos : x = sp s-96) (regs : Preserved s b) (width : b[9].width = 64)
    (words : WordsAt m (x+8) 64 (scalarWords (Curve.inverse domain.n k)))
    (flag : memLoad m (x+40) 8 = 1) :
    ∃ c n, Reach (wrapped .l109db2 b m) (wrapped .l109dcf c n) ∧ Unmasked s c k ∧
      RamWriteFrame m n [Verify.Core.Reduce.scratch x] := by
  let v := scalarWords (Curve.inverse domain.n k)
  have rspBits : b[4].get 64 = x := congrArg (Value.get 64) rsp
  have word0 : memLoad m (x+8) 64 = v[0] := by
    simpa only [wordAddr, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using words 0 (by decide)
  have word1 : memLoad m (x+16) 64 = v[1] := by
    have h := words 1 (by decide)
    dsimp only [wordAddr] at h
    rw [BitVec.add_assoc] at h
    exact h
  have word2 : memLoad m (x+24) 64 = v[2] := by
    have h := words 2 (by decide)
    dsimp only [wordAddr] at h
    rw [BitVec.add_assoc] at h
    exact h
  have word3 : memLoad m (x+32) 64 = v[3] := by
    have h := words 3 (by decide)
    dsimp only [wordAddr] at h
    rw [BitVec.add_assoc] at h
    exact h
  have lowByte : (memLoad m (x+40) 32).setWidth 8 = 1 := by
    rw [← flag]
    have h32 := storedByte_memLoad m (x+40) (n := 32) 0 (by decide)
    have h8 := storedByte_memLoad m (x+40) (n := 8) 0 (by decide)
    have eq := congrArg UInt8.toBitVec (h32.trans h8.symm)
    simpa only [storedByte, Nat.mul_zero, Nat.shiftRight_zero, UInt8.toBitVec_ofNat',
      BitVec.ofNat_toNat, BitVec.setWidth_eq] using eq
  have firstCode : ∀ p ∈ codeRange 0x109db2 bytes_l109db2, p ∈ Extracted.programImage :=
    fun p hp => Common.fnCode_subset_programImage p (code_l109db2 p hp)
  have call : ∃ a : Registers,
      program.runBlock (dialect Extracted.programImage) ⟨.l109db2,b,m⟩ =
        .call ⟨.l127d50,a,memStore m (x-8) (0x109dcf : BitVec 64)⟩ (Verify.Core.Reduce.resume .l109dcf 0x109dcf) ∧
      a[4].get 64 = x-8 ∧ (a[7].get 64).setWidth 8 = 1 ∧
      a[14] = ⟨64,v[0]⟩ ∧ a[15] = ⟨64,v[1]⟩ ∧ a[12] = ⟨64,v[2]⟩ ∧ a[13] = ⟨64,v[3]⟩ ∧
      a[9] = b[9] ∧ a[3] = b[3] ∧ a[5] = b[5] ∧ a[22] = b[22] ∧ a[39] = b[39] ∧
      a[50] = b[50] ∧ a[51] = b[51] := by
    refine ⟨?args, ?runCall, ?stackCall, ?flagCall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case runCall =>
      cfg_eval [rspBits, word0, word1, word2, word3]
      simp (disch := slot_guard using firstCode) only [ite_eq_left]
      rfl
    case stackCall => rfl
    case flagCall =>
      change ((memLoad m (x+40) 32).setWidth 64 |>.setWidth 8) = 1
      simpa only [BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide)] using lowByte
    all_goals rfl
  obtain ⟨a, call, pushSp, choice, a14, a15, a12, a13, a9, a3, a5, a22, a39, a50, a51⟩ := call
  have window : Writable Extracted.programImage m (x-9) 9 :=
    stack.sub (Nat.le_refl _) (by omega)
  obtain ⟨c,n,reach,sp,success,scratch,keep⟩ :=
    Verify.Core.Reduce.barrier call pushSp window room (by decide)
  have lifted := Signing.Transfer.verifyReachesAt (dst := .l109db2) (dst' := .l109dcf) rfl rfl reach
  refine ⟨c,n,appendStack lifted wrapperStack,⟨⟨?_,?_,?_,?_,?_,?_⟩,(by simpa only [pos] using sp),?_,?_,?_,?_,?_,?_⟩,scratch⟩
  · exact (keep 3 (by decide)).trans (a3.trans regs.rbx)
  · exact (keep 5 (by decide)).trans (a5.trans regs.rbp)
  · exact (keep 22 (by decide)).trans (a22.trans regs.df)
  · exact (congrArg Value.width ((keep 39 (by decide)).trans a39)).trans regs.fp.1
  · exact (congrArg Value.width ((keep 50 (by decide)).trans a50)).trans regs.fp.2.1
  · exact (congrArg Value.width ((keep 51 (by decide)).trans a51)).trans regs.fp.2.2
  · rw [success, choice]; rfl
  · exact (keep 14 (by decide)).trans a14
  · exact (keep 15 (by decide)).trans a15
  · exact (keep 12 (by decide)).trans a12
  · exact (keep 13 (by decide)).trans a13
  · exact (congrArg Value.width ((keep 9 (by decide)).trans a9)).trans width

private theorem savedBelow {s : RamState} {m n : Ram} {regions : List MemoryRegion}
    (depth : 840 ≤ (sp s).toNat) (high : (sp s).toNat < 2^32)
    (before : Saved s m) (writes : RamWriteFrame m n regions)
    (below : ∀ r ∈ regions, r.start + r.size ≤ (sp s).toNat - 48) : Saved s n := by
  have keep (k : BitVec 64) (hk : k.toNat ≤ 48) :
      memLoad n (sp s-k) 64 = memLoad m (sp s-k) 64 := by
    apply writes.memLoad_eq
    have addr : (sp s-k).toNat = (sp s).toNat-k.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    refine ⟨by rw [addr]; omega, fun r hr => Or.inr ?_⟩
    have := below r hr
    rw [addr]; omega
  exact ⟨(keep 8 (by decide)).trans before.ret,(keep 16 (by decide)).trans before.r15,
    (keep 32 (by decide)).trans before.r13,(keep 40 (by decide)).trans before.r12,
    (keep 48 (by decide)).trans before.rbx⟩

theorem passInverseChoice (execute : CoreExecution) {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg]) {a b : Registers} {m n : Ram} {st : State} {k : Nat}
    (reduced : DigestReduced s d msg st k a m) (entry : Entry b n (coreSp s) k)
    (regs : Preserved s b) (saved : Saved s n) (writes : RamWriteFrame m n (inverseRegion s)) :
    ∃ c t, Reach ⟨⟨.l108e30,b,n⟩,resume .l109db2 0x109db2 :: wrapperStack⟩ (wrapped .l109dcf c t) ∧
      Unmasked s c k ∧ Saved s t ∧ RamWriteFrame m t (inverseRegion s) := by
  obtain ⟨out,exec,result,inv,flag,r9⟩ := execute entry
  let p := coreSp s
  let x := p+8
  have uNat := (stackBounds call).2.2
  have deep := (stackBounds call).1
  have high := (stackBounds call).2.1
  have hp : p.toNat = (sp s).toNat-104 := belowNat call (depth := 104) (by decide)
  have hx : x = sp s-96 := by dsimp only [x,p,coreSp]; bv_omega
  have bx : x.toNat = (sp s).toNat-96 := hx ▸ belowNat call (depth := 96) (by decide)
  have base : (sp s-840).toNat = (sp s).toNat-840 := belowNat call (depth := 840) (by decide)
  have first : (p-BitVec.ofNat 64 736).toNat = (sp s).toNat-840 := by
    rw [show p-BitVec.ofNat 64 736 = sp s-840 by dsimp only [p,coreSp]; bv_omega,base]
  have second : (p+16).toNat = (sp s).toNat-88 := by
    rw [show p+16 = sp s-88 by dsimp only [p,coreSp]; bv_omega]
    exact belowNat call (depth := 88) (by decide)
  have bounds (r : MemoryRegion) (hr : r ∈ [⟨(p-BitVec.ofNat 64 736).toNat,736⟩,⟨(p+16).toNat,33⟩]) :
      (sp s).toNat-840 ≤ r.start ∧ r.start+r.size ≤ (sp s).toNat-48 := by
    rcases List.mem_cons.mp hr with eq | mem
    · subst r; change _ ≤ (p-BitVec.ofNat 64 736).toNat ∧ (p-BitVec.ofNat 64 736).toNat+736 ≤ _
      rw [first]; omega
    · obtain rfl := List.mem_singleton.mp mem
      change _ ≤ (p+16).toNat ∧ (p+16).toNat+33 ≤ _
      rw [second]; omega
  have before := writes.trans result.frame (by
    intro r hr
    have h := bounds r hr
    refine ⟨_,List.mem_singleton_self _,?_,?_⟩ <;> change _ ≤ _ <;> dsimp only [inverseRegion]
    · change (sp s-840).toNat ≤ _; rw [base]; omega
    · change _ ≤ (sp s-840).toNat+1104; rw [base]; omega)
  have kept := savedBelow (by omega) (by omega) saved result.frame (fun r hr => (bounds r hr).2)
  have preserved : Preserved s out.values := by
    refine ⟨(result.kept 3 (by decide) (congrArg Value.width regs.rbx)).trans regs.rbx,
      (result.kept 5 (by decide) (congrArg Value.width regs.rbp)).trans regs.rbp,
      (result.controls 22 (by decide)).trans regs.df,
      (congrArg Value.width (result.controls 39 (by decide))).trans regs.fp.1,
      (congrArg Value.width (result.controls 50 (by decide))).trans regs.fp.2.1,
      (congrArg Value.width (result.controls 51 (by decide))).trans regs.fp.2.2⟩
  have win : Writable Extracted.programImage out.store (x-9) 64 := by
    rw [hx,show sp s-96-9 = sp s+(0-105) by bv_omega]
    exact (stackWindow call reduced.toMemory (by decide)).of_frame before
  have wi : x+8 = p+16 := by dsimp only [x]; bv_omega
  have fi : x+40 = p+48 := by dsimp only [x]; bv_omega
  obtain ⟨c,t,choice,unmasked,scratch⟩ := loadChoice win (by omega) result.rsp hx preserved r9
    (wi ▸ inv) (fi ▸ flag)
  have small : (x-9).toNat = (sp s).toNat-105 := by
    rw [hx,show sp s-96-9 = sp s-105 by bv_omega]
    exact belowNat call (depth := 105) (by decide)
  have later (r : MemoryRegion) (hr : r ∈ [Verify.Core.Reduce.scratch x]) :
      (sp s).toNat-840 ≤ r.start ∧ r.start+r.size ≤ (sp s).toNat-48 := by
    obtain rfl := List.mem_singleton.mp hr
    change _ ≤ (x-9).toNat ∧ (x-9).toNat+9 ≤ _
    rw [small]; omega
  have resumePath : Reach ⟨⟨.l108e30,b,n⟩,resume .l109db2 0x109db2 :: wrapperStack⟩
      (wrapped .l109db2 out.values out.store) := by
    exact ParseSignature.exec_reaches_resume exec _ _ (by rw [result.returned]; rfl)
  refine ⟨c,t,resumePath.trans choice,unmasked,
    savedBelow (by omega) (by omega) kept scratch (fun r hr => (later r hr).2), before.trans scratch ?_⟩
  intro r hr
  have h := later r hr
  refine ⟨_,List.mem_singleton_self _,?_,?_⟩
  · change (sp s-840).toNat ≤ _; rw [base]; omega
  · change _ ≤ (sp s-840).toNat+1104; rw [base]; omega

end K256.Proofs.Signing.Composition.Attempt.Inverse
