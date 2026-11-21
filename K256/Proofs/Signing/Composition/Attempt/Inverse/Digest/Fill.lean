import K256.Proofs.Signing.Composition.Attempt.Inverse.Digest.Setup

import K256.Proofs.Signing.Composition.Attempt.Inverse.Digest.Memory
import K256.Proofs.Signing.Composition.Attempt.Inverse.Digest.Branch
import K256.Proofs.Verify.Core.Scalars.Digest.Fill.Call

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Standards.NIST.SHA2

private def fillActivation (s : RamState) (a : Registers) (m : Ram) : Activation where
  original := m
  rsp := sp s-8
  ret := 0x105aaa
  low := sp s-216
  rbx := sp s+456
  rbp := sp s+192
  r12 := sp s+8
  r13 := sp s+256
  r14 := a[14].get 64
  r15 := sp s+160
  rdi := sp s+352
  rsi := 32
  rdx := sp s+256
  rcx := 4
  r8 := 256
  r9 := a[9].get 64
  mxcsr := a[39].get 32
  ftw := a[50].get 16
  fcw := a[51].get 16
  fs := s.FS

local macro "addr_bounds" : tactic => `(tactic|
  (simp only [BitVec.toNat_add,BitVec.toNat_sub,BitVec.reduceToNat,Nat.reducePow,Nat.reduceDiv] at *
   omega))

theorem fillDigest {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg]) {a : Registers} {m : Ram} {st : State} {k : Nat}
    (parsed : NonceParsed s d msg st k a m) :
    ∃ b n, Verify.Core.Reaches .l1059fb a m .l105aba b n ∧ DigestFilled s d msg st k b n := by
  let p := sp s
  obtain ⟨room,limit,base⟩ := stackBounds call
  change p.toNat = _ at base
  have align := call.stackAvailable.2.2.2
  change (stackPtr s).toNat % 16 = 8 at align
  have window : Writable Extracted.programImage m (p-8) 664 := by
    simpa only [p, BitVec.add_neg_eq_sub] using
      (stackWindow (offset := -8) (size := 664) call parsed.toMemory (by decide))
  obtain ⟨c,n,run,rsp,si,di,cx,dx,r8,keep,writes,ret,nonce⟩ :=
    setupDigestFill window (by omega) parsed.rsp parsed.r13 parsed.nonce
  let regions := digestRegions p
  have boundSetup : RegionsWithin (setupRegions p) regions := by
    intro r hr
    simp only [setupRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_,List.mem_cons_self,by addr_bounds⟩
    · exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),by addr_bounds⟩
  have initFrame := (RamWriteFrame.refl m regions).trans writes boundSetup
  have initMem := preserveDigestMemory call parsed.toLoopMemory initFrame
  let ch := fillActivation s a n
  have image := initMem.toMemory.image call
  have ro : Verify.LIR.rodataSection ∈ Extracted.programSections := by
    simp [Verify.LIR.rodataSection,Extracted.programSections]
  have slots := Verify.LIR.Fn127d70.callSlots_loaded ro image
  obtain ⟨r1,v1⟩ := slots (0x203dd0,0x12a820) (by decide)
  obtain ⟨r2,v2⟩ := slots (0x203de0,0x129770) (by decide)
  obtain ⟨r3,v3⟩ := slots (0x203e20,0x100a20) (by decide)
  have avoid := (call.separation.2 _ (show Stack.region s signingKeyTrySign.minStackBytes ∈
    writtenRegions signingKeyTrySign s by simp [writtenRegions])).1
  have span := Verify.LIR.Fn127d70.callSlots_span ro
  have apart := apart_of_avoids (lo := 0x203dd0) (hi := 0x203e28) avoid
    (fun addr hl hh => by obtain ⟨b,hb⟩ := span addr hl hh; exact Or.inl ⟨b,Common.programSections_fetchByte_of_mem hb⟩)
    (by rw [stackRegion call]; exact (by decide : 0 < 11200)) (by decide) (by decide)
  rw [stackRegion call] at apart
  change (stackPtr s-11192).toNat+11200 ≤ 0x203dd0 ∨ 0x203e28 ≤ (stackPtr s-11192).toNat at apart
  have bottom : (stackPtr s-11192).toNat = (stackPtr s).toNat-11192 := Common.stackOffset (off := 11192) call.stackAvailable (by decide)
  rw [bottom] at apart
  have retRead : Readable n (p-8) 8 := (window.of_frame writes).readable.sub (by omega) (by omega)
  have stack : Writable Extracted.programImage n (p-8-208) 208 := by
    rw [show p-8-208 = p+(-216) by bv_omega]
    exact stackWindow call initMem.toMemory (by decide)
  have word (v : Value) {w : Nat} (h : v.width = w) : v = ⟨w,v.get w⟩ := by
    cases v with | mk n x => change n = w at h; subst w; simp only [Value.get, BitVec.setWidth_eq]
  have entry : Atom.All Extracted.programImage c n (Verify.LIR.Fn127d70.frameAt .l127d70 ch) := by
    simp only [Verify.LIR.Fn127d70.frameAt,Verify.LIR.Fn127d70.frameAtG28,Atom.All,Atom.Holds,ch,fillActivation]
    refine ⟨rsp,(keep 22 (by decide)).trans parsed.df,cx,dx,(keep 3 (by decide)).trans parsed.rbx,
      (keep 5 (by decide)).trans parsed.rbp,si,di,r8,(keep 9 (by decide)).trans (word _ (parsed.widths _ (by decide))),
      (keep 12 (by decide)).trans parsed.r12,(keep 13 (by decide)).trans parsed.r13,
      (keep 14 (by decide)).trans (word _ parsed.r14),(keep 15 (by decide)).trans parsed.r15,
      (keep 39 (by decide)).trans (word _ parsed.fp.1),(keep 50 (by decide)).trans (word _ parsed.fp.2.1),
      (keep 51 (by decide)).trans (word _ parsed.fp.2.2),retRead,ret,by decide,stack,?_,?_,r1,v1,r2,v2,r3,v3,?_,trivial⟩
    · change (p-216).toNat+208 ≤ (p-8).toNat
      addr_bounds
    · change (p-8).toNat % 16 = 8
      addr_bounds
    · change 0x203ef8 ≤ (p-8).toNat ∨ (p-8).toNat ≤ 0x203dd0
      addr_bounds
  have src := (stackWindow (offset := 352) (size := 32) call initMem.toMemory (by decide)).readable
  have dst := stackWindow (offset := 256) (size := 32) call initMem.toMemory (by decide)
  have size : (SHA256.hashBytes msg).size = 32 := initMem.hash.1
  have num : ParseSignature.scalarValue n (p+352) = Encoding.octetsToNat (SHA256.hashBytes msg) := by
    have val := Common.octetsToNat_extract_eq_words (off := 0) initMem.hash (by omega)
    have whole : (SHA256.hashBytes msg).extract 0 32 = SHA256.hashBytes msg := by rw [← size,ByteArray.extract_zero_size]
    simpa only [ParseSignature.scalarValue, Nat.zero_add, whole, Nat.add_zero,
      BitVec.ofNat_toNat, BitVec.setWidth_eq] using val.symm
  obtain ⟨out,exec,tag,done_,wf,widths,status,words⟩ := Verify.Core.fillScalar (fr := ch)
    entry rfl rfl rfl src dst
    (by change Outside [⟨(p-216).toNat,(p-8).toNat+8-(p-216).toNat⟩] (p+352) 32; simp only [Outside,List.mem_singleton,forall_eq]; addr_bounds)
    (by change Outside [⟨(p-216).toNat,(p-8).toNat+8-(p-216).toNat⟩] (p+256) 32; simp only [Outside,List.mem_singleton,forall_eq]; addr_bounds)
    (by change Outside [⟨(p+256).toNat,32⟩] (p+352) 32; simp only [Outside,List.mem_singleton,forall_eq]; addr_bounds)
    (by change Outside [⟨(p+256).toNat,32⟩] 0x203dd0 8; simp only [Outside,List.mem_singleton,forall_eq]; addr_bounds)
  have firstRun : Verify.Core.Reaches .l1059fb a m .l105aaa out.values out.store :=
    Verify.reachesOfCall run exec tag
  simp only [Verify.LIR.Fn127d70.doneAt,Atom.All,Atom.Holds,ch,fillActivation,BitVec.sub_add_cancel] at done_
  obtain ⟨sp',df,bx,bp,r12,_,r14,r15,mx,ft,fc,_⟩ := done_
  obtain ⟨b,branch,r13,kept,wb⟩ := digestFillBranch (m := out.store) status (congrArg (Value.get 64) sp') widths
  change RamWriteFrame n out.store [⟨(p-216).toNat,(p-8).toNat-(p-216).toNat⟩,⟨(p+256).toNat,32⟩] at wf
  have total := initFrame.trans wf (by
    intro r hr
    refine ⟨_,List.mem_cons_self,?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> addr_bounds)
  change WordsAt out.store (p+256) 64 (scalarWords (ParseSignature.scalarValue n (p+352))) at words
  rw [num] at words
  refine ⟨b,out.store,firstRun.trans branch,preserveDigestMemory call parsed.toLoopMemory total,
    ⟨(kept 4 (by decide)).trans sp',(kept 22 (by decide)).trans df,(kept 3 (by decide)).trans bx,
      (kept 5 (by decide)).trans bp,(kept 12 (by decide)).trans r12,r13,
      congrArg Value.width ((kept 14 (by decide)).trans r14),(kept 15 (by decide)).trans r15,wb,
      congrArg Value.width ((kept 39 (by decide)).trans mx),congrArg Value.width ((kept 50 (by decide)).trans ft),
      congrArg Value.width ((kept 51 (by decide)).trans fc)⟩,?_,words⟩
  apply nonce.of_frame wf (by decide)
  simp only [Outside,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  addr_bounds

end K256.Proofs.Signing.Composition.Attempt.Inverse
