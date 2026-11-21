import K256.Proofs.Signing.Composition.Wrapper.Frame
import K256.Proofs.Signing.Transfer.Generator
import K256.Proofs.Signing.Transfer.Verify
import K256.Proofs.Signing.Affine

namespace K256.Proofs.Signing.Composition.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

private def affineFrame (s : RamState) (a : Registers) (m : Ram) : Activation :=
  let q := localSp s
  { Activation.ofEntry s 1456 0x1026a6 with
    original := memStore m (q-8) (0x1026a6 : BitVec 64)
    rsp := q-8
    low := q-984
    rbx := s.regValue .rdi
    rsi := q+200
    rdi := q+352
    r12 := q+200
    r14 := s.regValue .rcx
    r15 := s.regValue .rdx
    mxcsr := a[39].get 32
    ftw := a[50].get 16
    fcw := a[51].get 16 }

private theorem affineBlock {s : RamState} {d : Nat} {a : Registers} {m : Ram}
    (entry : Multiplied s d a m)
    (ok : StoreOk Extracted.programImage m (localSp s-8) 8 0x1026a1 5) :
    let fr := affineFrame s a m
    ∃ c : Registers, LIR.program.runBlock (dialect Extracted.programImage) ⟨.l102696,a,m⟩ =
      .call ⟨.l10fe50,c,fr.original⟩ (resume .l1026a6 0x1026a6) ∧
      c[4] = ⟨64,fr.rsp⟩ ∧ c[6] = ⟨64,fr.rsi⟩ ∧ c[7] = ⟨64,fr.rdi⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → c[i] = a[i] := by
  have rsp := congrArg (Value.get 64) entry.rsp
  have ptr := congrArg (Value.get 64) entry.pointPtr
  simp only [Value.get_mk] at rsp ptr
  dsimp only
  refine ⟨?args,?run,?post⟩
  case run =>
    cfg_eval [rsp,ptr]
    rw [ite_eq_left ok]
    rfl
  case post =>
    refine ⟨rfl,rfl,rfl,?_⟩
    rintro ⟨i,_⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem valueOfWidth (v : Value) {w : Nat} (h : v.width = w) : v = ⟨w,v.get w⟩ := by
  cases v
  cases h
  rw [Value.get_mk]

private theorem decodedRange {secret : ByteArray} {d : Nat}
    (decoded : Keys.decodeSecret domain secret = some d) : 0 < d ∧ d < domain.n := by
  unfold Keys.decodeSecret at decoded
  dsimp only at decoded
  split at decoded
  · rename_i valid
    obtain rfl := Option.some.inj decoded
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at valid
    exact ⟨valid.1.2,valid.2⟩
  · contradiction

set_option maxHeartbeats 1200000 in
theorem affine {s : RamState} {secret msg : ByteArray} {d : Nat} {a : Registers} {m : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    (decoded : Keys.decodeSecret domain secret = some d)
    (entry : Multiplied s d a m) :
    ∃ b n, Reach (atBlock .l102696 a m) (atBlock .l1026a6 b n) ∧ Decoded s d b n := by
  let q := localSp s
  let fr := affineFrame s a m
  obtain ⟨room,high,_⟩ := stackBounds call
  have align : (stackPtr s).toNat % 16 = 8 := call.stackAvailable.2.2.2
  have addr (off depth : Nat) (fit : off + depth = 472) :
      q + BitVec.ofNat 64 off = stackPtr s - BitVec.ofNat 64 depth := by
    rw [show q = stackPtr s - 472 from localSp_eq s, show (472 : BitVec 64) = BitVec.ofNat 64 (off+depth) by rw [fit]; rfl,
      BitVec.ofNat_add]
    bv_omega
  have topAddr : fr.rsp = stackPtr s - 480 := by
    change localSp s - 8 = _
    rw [localSp_eq s]
    bv_omega
  have lowAddr : fr.low = stackPtr s - 1456 := by
    change localSp s - 984 = _
    rw [localSp_eq s]
    bv_omega
  have srcAddr : fr.rsi = stackPtr s - 272 := addr 200 272 rfl
  have dstAddr : fr.rdi = stackPtr s - 120 := addr 352 120 rfl
  have top : fr.rsp.toNat = (stackPtr s).toNat-480 := by
    rw [topAddr]
    exact Common.stackOffset (off := 480) call.stackAvailable (by decide)
  have low : fr.low.toNat = (stackPtr s).toNat-1456 := by
    rw [lowAddr]
    exact Common.stackOffset (off := 1456) call.stackAvailable (by decide)
  have src : fr.rsi.toNat = (stackPtr s).toNat-272 := by
    rw [srcAddr]
    exact Common.stackOffset (off := 272) call.stackAvailable (by decide)
  have dst : fr.rdi.toNat = (stackPtr s).toNat-120 := by
    rw [dstAddr]
    exact Common.stackOffset (off := 120) call.stackAvailable (by decide)
  have window (depth len : Nat) (fit : depth ≤ 11192) (within : len ≤ depth + 8) (pos : 0 < len) :
      Writable Extracted.programImage m (stackPtr s - BitVec.ofNat 64 depth) len :=
    (Common.stackWritable call fit within pos).of_frame entry.written
  have slot : Writable Extracted.programImage m fr.rsp 8 := by
    rw [topAddr]
    exact window 480 8 (by decide) (by decide) (by decide)
  have included := fun x h => Common.fnCode_subset_programImage x (LIR.code_l102696 x h)
  have store : StoreOk Extracted.programImage m fr.rsp 8 0x1026a1 5 :=
    ParseSignature.storeOk_of_codeRange (off := 11) slot included (by decide)
  obtain ⟨c,step,rsp,si,di,keep⟩ := affineBlock entry store
  have pushed : RamWriteFrame m fr.original [⟨fr.rsp.toNat,8⟩] := by
    apply (RamWriteFrame.refl m _).memStore
    exact ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _, by change fr.rsp.toNat + 8 ≤ 2^64; omega⟩
  have preMem := preserveSlots call entry.toMemory pushed (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change _ ≤ fr.rsp.toNat ∧ fr.rsp.toNat + 8 ≤ _
    omega)
  have image := preMem.image call
  have win : Writable Extracted.programImage fr.original (fr.rsp-976) 976 := by
    rw [show fr.rsp-976 = fr.low by change q-8-976 = q-984; bv_omega, lowAddr]
    exact (window 1456 976 (by decide) (by decide) (by decide)).of_frame pushed
  have read : Readable fr.original fr.rsp 8 := (slot.of_frame pushed).readable
  have source : Readable fr.original fr.rsi 120 := by
    rw [srcAddr]
    exact ((window 272 120 (by decide) (by decide) (by decide)).of_frame pushed).readable
  have dest : Writable Extracted.programImage fr.original fr.rdi 88 := by
    rw [dstAddr]
    exact (window 120 88 (by decide) (by decide) (by decide)).of_frame pushed
  have ro : Generate.LIR.rodataSection ∈ Extracted.programSections := by
    simp [Generate.LIR.rodataSection, Extracted.programSections]
  have got := Generate.LIR.Fn10fe50.callSlots_loaded ro image
  obtain ⟨got₁,val₁⟩ := got (0x203de0,0x129770) (by decide)
  obtain ⟨got₂,val₂⟩ := got (0x203e20,0x100a20) (by decide)
  let stk := Stack.region s signingKeyTrySign.minStackBytes
  have avoids := (call.separation.2 stk (by simp [stk,writtenRegions])).1
  have stkPos : 0 < stk.size := by
    change 0 < (stackPtr s).toNat+8-((stackPtr s).toNat-11192)
    omega
  have apart := apart_of_avoids avoids (lo := 0x203de0) (hi := 0x203e28)
    (fun a hlo hhi => by
      obtain ⟨byte,hbyte⟩ := Generate.LIR.Fn10fe50.callSlots_span ro a hlo hhi
      exact Or.inl ⟨byte, Common.programSections_fetchByte_of_mem hbyte⟩)
    stkPos (by decide) (by decide)
  change (stackPtr s).toNat-11192 + ((stackPtr s).toNat+8-((stackPtr s).toNat-11192)) ≤ _ ∨
    _ ≤ (stackPtr s).toNat-11192 at apart
  have atoms : Atom.All Extracted.programImage c fr.original (Verify.Core.Affine.atomsAt .l10fe50 fr) := by
    have h39 := (keep 39 (by decide)).trans (valueOfWidth _ entry.fp.1)
    have h50 := (keep 50 (by decide)).trans (valueOfWidth _ entry.fp.2.1)
    have h51 := (keep 51 (by decide)).trans (valueOfWidth _ entry.fp.2.2)
    have hret : memLoad fr.original fr.rsp 64 = fr.ret := memLoad_memStore_same _ _ _ (by decide) (by decide)
    refine ⟨rsp,(keep 22 (by decide)).trans entry.df,trivial,trivial,
      (keep 3 (by decide)).trans entry.output,(keep 5 (by decide)).trans entry.rbp,si,di,trivial,trivial,
      (keep 12 (by decide)).trans entry.pointPtr,(keep 13 (by decide)).trans entry.r13,
      (keep 14 (by decide)).trans entry.length,(keep 15 (by decide)).trans entry.message,
      h39,h50,h51,read,hret,?_,win,?_,?_,got₁,val₁,got₂,val₂,?_,trivial⟩
    · change (0x1026a6 : Nat) < 2^32
      decide
    · change fr.low.toNat + 976 ≤ fr.rsp.toNat
      omega
    · change fr.rsp.toNat % 16 = 8
      omega
    ·
      change 0x2041f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0
      omega
  have proj : Generate.Generator.Affine.ProjectiveAt fr.original fr.rsi (Generate.Curve.generatorWindow d) := by
    obtain ⟨x,y,z,xl,yl,zl,wx,wy,wz,rx,ry,rz,eq⟩ := entry.point
    have safe (offset : BitVec 64)
        (bounds : 8 ≤ (offset-(0-8)).toNat ∧ 40 ≤ ((0-8)-offset).toNat) :
        RangeApart (localSp s-8) 8 (localSp s+offset) 40 :=
      RangeApart.of_offsets (addr_sub (localSp s) 8) rfl bounds
    refine ⟨x,y,z,xl,yl,zl,wx.write_apart _ _ (safe 200 (by decide)),
      wy.write_apart _ _ ?_,wz.write_apart _ _ ?_,rx,ry,rz,eq⟩
    · change RangeApart (localSp s-8) 8 (localSp s+200+40) 40
      rw [BitVec.add_assoc]
      exact safe 240 (by decide)
    · change RangeApart (localSp s-8) 8 (localSp s+200+80) 40
      rw [BitVec.add_assoc]
      exact safe 280 (by decide)
  have state : Signing.Affine.CallState .l10fe50 fr c fr.original :=
    ⟨atoms,image,source,dest,by omega,by omega,.refl _ _⟩
  obtain ⟨out,exec,tag,done_,writes,_⟩ := Signing.Affine.execution state proj
    (Generate.Curve.generatorWindow_ne_infinity d (decodedRange decoded).1 (decodedRange decoded).2)
  have finalMem := preserveSlots call preMem writes (by
    intro r hr
    rcases List.mem_cons.mp hr with h | h
    · subst r
      change _ ≤ fr.low.toNat ∧ fr.low.toNat + (fr.rsp.toNat-fr.low.toNat) ≤ _
      omega
    · obtain rfl := List.mem_singleton.mp h
      change _ ≤ fr.rdi.toNat ∧ fr.rdi.toNat + 88 ≤ _
      omega)
  have key : WordsAt out.store (q+40) 64 (scalarWords d) := by
    intro i hi
    have loc : (wordAddr (q+40) 64 i).toNat = (stackPtr s).toNat - 432 + 8*i := by
      change ((q+40) + BitVec.ofNat 64 (8*i)).toNat = _
      rw [show q+40 = stackPtr s-432 from addr 40 432 rfl]
      have base := Common.stackOffset (off := 432) call.stackAvailable (by decide)
      change (stackPtr s - (432 : BitVec 64)).toNat = _ at base
      rw [BitVec.toNat_add, base, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8*i) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have outside : Outside (Generate.Generator.Affine.writes fr) (wordAddr (q+40) 64 i) 8 := by
      refine ⟨by rw [loc]; omega, fun r hr => ?_⟩
      rw [loc]
      rcases List.mem_cons.mp hr with h | h
      · subst r
        exact Or.inr (show fr.low.toNat + (fr.rsp.toNat-fr.low.toNat) ≤ _ by omega)
      · obtain rfl := List.mem_singleton.mp h
        exact Or.inl (show _ ≤ fr.rdi.toNat by omega)
    rw [writes.memLoad_eq outside]
    refine (memLoad_memStore_of_rangeApart _ _ _ _ _ ?_).trans (entry.key i hi)
    have slotTop : (localSp s-8).toNat = (stackPtr s).toNat-480 := top
    apply RangeApart.of_toNat
    · change (localSp s-8).toNat + 8 ≤ 2^64
      rw [slotTop]
      omega
    · change (wordAddr (q+40) 64 i).toNat + 8 ≤ 2^64
      rw [loc]
      omega
    · left
      change (localSp s-8).toNat + 8 ≤ (wordAddr (q+40) 64 i).toNat
      rw [slotTop,loc]
      omega
  have exe := Transfer.verifyExec (src := .l10fe50) (dst := .l10fe50)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (Transfer.generator (src := .l10fe50) (dst := .l10fe50)
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) exec)
  have signedTag : out.tag = some ⟨64,0x1026a6⟩ := tag
  rcases done_ with ⟨back,df,bx,bp,r12,r13,r14,r15,mx,ft,cw,_⟩
  have regs : Saved s out.values := by
    refine ⟨back.trans ?_, bx,bp,r13,r15,r14,congrArg Value.width r12,df,
      congrArg Value.width mx,congrArg Value.width ft,congrArg Value.width cw⟩
    apply congrArg (Value.mk 64)
    change q-8+8 = q
    bv_omega
  refine ⟨out.values,out.store,?_,⟨regs,finalMem,key⟩⟩
  refine .step (b := ⟨⟨.l10fe50,c,fr.original⟩,[resume .l1026a6 0x1026a6]⟩) ?_ ?_
  · exact congrArg (Transfer.next (dialect Extracted.programImage) []) step
  · exact ParseSignature.exec_reaches_resume exe (resume .l1026a6 0x1026a6) [] (by rw [signedTag]; rfl)

end K256.Proofs.Signing.Composition.Wrapper
