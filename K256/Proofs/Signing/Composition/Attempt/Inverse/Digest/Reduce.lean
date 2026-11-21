import K256.Proofs.Signing.Composition.Attempt.Inverse.Digest.Memory
import K256.Proofs.Signing.Composition.Attempt.Inverse.Digest.State
import K256.Proofs.Verify.Choice
import K256.Proofs.Verify.Core.Scalars.Digest.Reduce

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Standards.NIST.SHA2

private def stageDigest (m : Ram) (p : BitVec 64) : Ram :=
  let n := memStore m (p+32) (memLoad m (p+280) 64)
  let n := memStore n (p+24) (memLoad m (p+272) 64)
  let n := memStore n (p+16) (memLoad m (p+264) 64)
  let n := memStore n (p+8) (memLoad m (p+256) 64)
  memStore n (p-8) (0x105afc : BitVec 64)

private theorem stagedDigestWords {m : Ram} {p : BitVec 64} {w : Vector (BitVec 64) 4}
    (words : WordsAt m (p+256) 64 w) : WordsAt (stageDigest m p) (p+8) 64 w := by
  intro i hi
  rw [← words i hi]
  obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
  all_goals simp (disch := store_disch) only [stageDigest, wordAddr, Nat.reduceDiv, Nat.reduceMul,
    BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
    memLoad_memStore_same, memLoad_memStore_of_rangeApart]

open Verify.LIR in
set_option maxRecDepth 4096 in
private theorem prepareDigestReduction {a : Registers} {m : Ram} {p : BitVec 64}
    (rsp : a[4].get 64 = p) (rbx : a[3].get 64 = p+456)
    (r12 : a[12].get 64 = p+8) (r13 : a[13].get 64 = p+656)
    (area : Writable Extracted.programImage m (p-8) 296) :
    ∃ b : Registers,
      Verify.LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105aba,a,m⟩ =
        .call ⟨.l109f80,b,stageDigest m p⟩ (Verify.resumeAt .l105afc 0x105afc) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[6] = ⟨64,p+8⟩ ∧ b[7] = ⟨64,p+656⟩ ∧
      b[15] = ⟨64,p+456⟩ ∧ b[1].width = 64 ∧
      (∀ i : Fin Reg.count, i.val ∈ [2,3,5,8,9,12,13,14,22,39,50,51] → b[i] = a[i]) := by
  refine ⟨?b, ?step, ?regs⟩
  case step =>
    cfg_eval [rsp,rbx,r12,r13]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using Verify.LIR.code_l105aba)
    simp (disch := store_disch) only [stageDigest, memLoad_memStore_of_rangeApart] <;> rfl
  case regs =>
    refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
    intro ⟨i,_⟩ hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private def reductionActivation (s : RamState) (a b : Registers) (m : Ram) : Activation where
  original := stageDigest m (sp s)
  rsp := sp s-8
  ret := 0x105afc
  low := sp s-105
  rbx := sp s+456
  rbp := sp s+192
  r12 := sp s+8
  r13 := sp s+656
  r14 := a[14].get 64
  r15 := sp s+456
  rdi := sp s+656
  rsi := sp s+8
  rdx := b[2].get 64
  rcx := b[1].get 64
  r8 := b[8].get 64
  r9 := b[9].get 64
  mxcsr := a[39].get 32
  ftw := a[50].get 16
  fcw := a[51].get 16
  fs := s.FS

local macro "digest_bounds" : tactic => `(tactic|
  (simp only [BitVec.toNat_add,BitVec.toNat_sub,BitVec.reduceToNat,Nat.reducePow,Nat.reduceDiv] at *
   omega))

set_option maxRecDepth 4096 in
theorem reduceFilledDigest {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg]) {a : Registers} {m : Ram} {st : State} {k : Nat}
    (filled : DigestFilled s d msg st k a m) :
    ∃ b n, Verify.Core.Reaches .l105aba a m .l105afc b n ∧ DigestReduced s d msg st k b n := by
  let p := sp s
  obtain ⟨room,limit,base⟩ := stackBounds call
  change p.toNat = _ at base
  have area : Writable Extracted.programImage m (p-8) 296 := by
    simpa only [p, BitVec.add_neg_eq_sub] using
      (stackWindow (offset := -8) (size := 296) call filled.toMemory (by decide))
  have word (v : Value) {w : Nat} (h : v.width = w) : v = ⟨w,v.get w⟩ := by
    cases v with | mk n x => change n = w at h; subst w; simp only [Value.get_mk]
  obtain ⟨b,run,rsp,si,di,r15,cx,keep⟩ :=
    prepareDigestReduction
      (by rw [filled.rsp,Value.get_mk])
      (by rw [filled.rbx,Value.get_mk])
      (by rw [filled.r12,Value.get_mk])
      (by rw [filled.r13,Value.get_mk]) area
  let ch := reductionActivation s a b m
  have staged : RamWriteFrame m ch.original [⟨(p-8).toNat,48⟩] := by
    change RamWriteFrame m (stageDigest m p) [⟨(p-8).toNat,48⟩]
    have slot (off : BitVec 64) (ho : off.toNat ≤ 32) :
        InRegions [⟨(p-8).toNat,48⟩] (p+off) 8 := by
      refine ⟨_,List.mem_singleton_self _,?_⟩
      change (p-8).toNat ≤ (p+off).toNat ∧
        (p+off).toNat+8 ≤ (p-8).toNat+48 ∧ (p+off).toNat+8 ≤ 2^64
      digest_bounds
    have retSlot : InRegions [⟨(p-8).toNat,48⟩] (p-8) 8 := by
      refine ⟨_,List.mem_singleton_self _,?_⟩
      change (p-8).toNat ≤ (p-8).toNat ∧
        (p-8).toNat+8 ≤ (p-8).toNat+48 ∧ (p-8).toNat+8 ≤ 2^64
      digest_bounds
    unfold stageDigest
    apply RamWriteFrame.memStore _ _ retSlot
    repeat' apply RamWriteFrame.memStore _ _ (slot _ (by decide))
    exact .refl _ _
  have stack : Writable Extracted.programImage ch.original (ch.rsp-97) 97 := by
    change Writable Extracted.programImage ch.original (p-8-97) 97
    rw [show p-8-97 = p+(-105) by bv_omega]
    exact (stackWindow call filled.toMemory (by decide)).of_frame staged
  have align := call.stackAvailable.2.2.2
  change (stackPtr s).toNat % 16 = 8 at align
  have arg (i : Fin Reg.count) (hi : i.val ∈ [2,8,9]) : b[i] = ⟨64,b[i].get 64⟩ := by
    apply word
    rw [keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)]
    apply filled.widths
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega
  have ent : Atom.All Extracted.programImage b ch.original (Verify.LIR.Fn109f80.frameAt .l109f80 ch) := by
    simp only [Verify.LIR.Fn109f80.frameAt,Verify.LIR.Fn109f80.frameAtG11,Atom.All,Atom.Holds,ch,reductionActivation]
    refine ⟨rsp,(keep 22 (by decide)).trans filled.df,word _ cx,arg 2 (by decide),
      (keep 3 (by decide)).trans filled.rbx,(keep 5 (by decide)).trans filled.rbp,si,di,
      arg 8 (by decide),arg 9 (by decide),(keep 12 (by decide)).trans filled.r12,
      (keep 13 (by decide)).trans filled.r13,(keep 14 (by decide)).trans (word _ filled.r14),r15,
      (keep 39 (by decide)).trans (word _ filled.fp.1),
      (keep 50 (by decide)).trans (word _ filled.fp.2.1),
      (keep 51 (by decide)).trans (word _ filled.fp.2.2),?_,?_,by decide,stack,?_,?_,trivial⟩
    · change Readable ch.original (p-8) 8
      exact (area.of_frame staged).readable.sub (Nat.le_refl _) (by omega)
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · change (p-105).toNat+97 ≤ (p-8).toNat
      digest_bounds
    · change (p-8).toNat % 16 = 8
      digest_bounds
  have src : Readable ch.original ch.rsi 32 :=
    (stackWindow (offset := 8) (size := 32) call filled.toMemory (by decide)).readable.of_frame staged
  have dst : Writable Extracted.programImage ch.original ch.rdi 32 :=
    (stackWindow (offset := 656) (size := 32) call filled.toMemory (by decide)).of_frame staged
  have apart (off : BitVec 64) (ho : 8 ≤ off.toNat ∧ off.toNat ≤ 656) :
      Outside [ParseSignature.callStack ch] (p+off) 32 := by
    simp only [Outside,List.mem_singleton,forall_eq,ParseSignature.callStack,ch,reductionActivation]
    digest_bounds
  have size : (SHA256.hashBytes msg).size = 32 := filled.hash.1
  have bound : Encoding.octetsToNat (SHA256.hashBytes msg) < 2^256 := by
    have num := Common.octetsToNat_extract_eq_words (off := 0) filled.hash (by omega)
    have whole : (SHA256.hashBytes msg).extract 0 32 = SHA256.hashBytes msg := by
      rw [← size,ByteArray.extract_zero_size]
    simp only [Nat.zero_add,Nat.add_zero,whole] at num
    rw [num]
    have w (i : Nat) := (Common.scalarWord m (BitVec.ofNat 64 (p+352).toNat) i).isLt
    have h0 := w 0
    have h1 := w 1
    have h2 := w 2
    have h3 := w 3
    simp only [Nat.reducePow] at *
    omega
  obtain ⟨out,exec,tag,done_,writes,words,widths⟩ := Verify.Core.reduceScalar ent src dst
    (apart 8 (by decide)) (apart 656 (by decide)) (stagedDigestWords filled.digest) bound
  have stagedFrame : RamWriteFrame m ch.original (digestRegions p) :=
    (RamWriteFrame.refl m _).trans staged (by
      intro r hr
      rcases List.mem_singleton.mp hr with rfl
      refine ⟨_,List.mem_cons_self,?_⟩
      change (p-216).toNat ≤ (p-8).toNat ∧ (p-8).toNat+48 ≤ (p-216).toNat+504
      digest_bounds)
  have frame := stagedFrame.trans writes (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨_,List.mem_cons_self,?_⟩
      change (p-216).toNat ≤ (p-105).toNat ∧
        (p-105).toNat+((p-8).toNat-(p-105).toNat) ≤ (p-216).toNat+504
      digest_bounds
    · refine ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),?_⟩
      change (p+624).toNat ≤ (p+656).toNat ∧ (p+656).toNat+32 ≤ (p+624).toNat+64
      digest_bounds)
  have stagedNonce : WordsAt ch.original (p+624) 64 (scalarWords k) := by
    apply filled.nonce.of_frame staged (by decide)
    simp only [Outside,List.mem_singleton,forall_eq]
    digest_bounds
  have nonce : WordsAt out.store (p+624) 64 (scalarWords k) := by
    apply stagedNonce.of_frame writes (by decide)
    simp only [Outside,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
      Activation.region,ParseSignature.buffer,ch,reductionActivation]
    digest_bounds
  simp only [Verify.LIR.Fn109f80.doneAt,Atom.All,Atom.Holds,ch,reductionActivation,BitVec.sub_add_cancel] at done_
  obtain ⟨sp',df,bx,bp,r12,r13,r14,r15,mx,ft,fc,_⟩ := done_
  exact ⟨_,_,Verify.reachesOfCall run exec tag,preserveDigestMemory call filled.toLoopMemory frame,
    ⟨sp',df,bx,bp,r12,r13,congrArg Value.width r14,r15,widths,
      congrArg Value.width mx,congrArg Value.width ft,congrArg Value.width fc⟩,nonce,words⟩

end K256.Proofs.Signing.Composition.Attempt.Inverse
