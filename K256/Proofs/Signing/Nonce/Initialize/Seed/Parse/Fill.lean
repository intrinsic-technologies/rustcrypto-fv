import K256.Proofs.Signing.Nonce.Initialize.Seed.Parse.State
import K256.Proofs.Signing.Nonce.Initialize.Seed.Parse.Setup
import K256.Proofs.Verify.Core.Scalars.Digest.Fill.Call
import K256.Proofs.Verify.Choice

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)

private def parseChild (fr : Activation) (m : Ram) : Activation :=
  { fr with
    original := m, rsp := fr.rsp - 280 - 8, low := fr.rsp - 496, ret := 0x10106a,
    rbx := (scalarWords Secp256k1.domain.n)[3], rbp := 0,
    r13 := (scalarWords Secp256k1.domain.n)[2], r14 := (scalarWords Secp256k1.domain.n)[1],
    r15 := (scalarWords Secp256k1.domain.n)[0], rsi := 32, rdi := fr.rcx, rcx := 4,
    rdx := fr.rsp - 280 + 104, r8 := 256, r9 := 256 }

local macro "bounds" : tactic => `(tactic|
  (simp only [Activation.region, ParseSignature.callStack, ParseSignature.buffer, BitVec.toNat_sub,
    BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow, Nat.reduceDiv, Nat.reduceAdd] at *
   omega))

theorem fillSeedDigest {fr : Activation} {a : Verify.Core.Registers} {m : Ram} {digest : ByteArray}
    (depth : 2208 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 2208)
    (limit : fr.rsp.toNat + 784 < 2^32)
    (window : Writable Extracted.programImage fr.original fr.rsp 784)
    (digestPtr : fr.rcx = fr.rsp + 376) (_digestLen : fr.r8 = 32)
    (hash : (⟨fr.rcx.toNat, 32⟩ : MemoryRegion).HasBytes fr.original digest)
    (ready : DigestLength fr a m) :
    ∃ b n, Verify.Core.Reaches .l101026 a m .l101072 b n ∧
      FilledDigest fr b n (Encoding.octetsToNat digest) := by
  have bottom : fr.low.toNat = fr.rsp.toNat - 2208 := by
    rw [low]
    exact BitVec.toNat_sub_of_le (by change 2208 ≤ fr.rsp.toNat; omega)
  have atoms := ready.atoms
  simp only [Fn100ea0.frameAt, Fn100ea0.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp,df,src,_,_,r12,mx,ft,fc,s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,
    rr,rv,rl,stack,room,align,gr0,gv0,gr1,gv1,gr2,gv2,gr3,gv3,gr4,gv4,sep,_⟩ := atoms
  have space : Writable Extracted.programImage m (fr.rsp - 280 - 8) 168 :=
    stack.sub (by bounds) (by bounds)
  obtain ⟨c,n,call,csp,csi,cdi,ccx,cdx,cr8,keep,setup,ret⟩ :=
    DigestParse.setup a m (fr.rsp - 280) fr.rcx (congrArg (Value.get 64) sp)
      ready.len (congrArg (Value.get 64) src) (congrArg (Value.get 64) ready.bits) space
  let ch := parseChild fr n
  have stack' := stack.of_frame setup
  have got (addr : BitVec 64) (lo : 0x203dc8 ≤ addr.toNat) (hi : addr.toNat + 8 ≤ 0x203e28) :
      Outside (DigestParse.setupWrites (fr.rsp - 280)) addr 8 := by
    simp only [DigestParse.setupWrites, Outside, List.mem_singleton, forall_eq]
    bounds
  have entry : Atom.All Extracted.programImage c n (Fn127d70.frameAt .l127d70 ch) := by
    simp only [Fn127d70.frameAt, Fn127d70.frameAtG28, Atom.All, Atom.Holds, ch, parseChild]
    refine ⟨csp,(keep 22 (by decide)).trans df,ccx,cdx,(keep 3 (by decide)).trans ready.w3,
      (keep 5 (by decide)).trans ready.shift,csi,cdi,cr8,(keep 9 (by decide)).trans ready.bits,
      (keep 12 (by decide)).trans r12,(keep 13 (by decide)).trans ready.w2,
      (keep 14 (by decide)).trans ready.w1,(keep 15 (by decide)).trans ready.w0,
      (keep 39 (by decide)).trans mx,(keep 50 (by decide)).trans ft,(keep 51 (by decide)).trans fc,
      stack'.readable.sub (by bounds) (by bounds),ret,by decide,
      stack'.sub (by bounds) (by bounds),?_,?_,gr1.of_frame setup,?_,gr2.of_frame setup,?_,
      gr4.of_frame setup,?_,?_,trivial⟩
    · bounds
    · bounds
    · exact (setup.memLoad_eq (got _ (by decide) (by decide))).trans gv1
    · exact (setup.memLoad_eq (got _ (by decide) (by decide))).trans gv2
    · exact (setup.memLoad_eq (got _ (by decide) (by decide))).trans gv4
    · bounds
  have setupWithin : RegionsWithin (DigestParse.setupWrites (fr.rsp - 280)) [fr.region] := by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, by bounds⟩
  have joined := ready.writes.trans setup setupWithin
  have size : digest.size = 32 := hash.1
  have bytes : (⟨fr.rcx.toNat,32⟩ : MemoryRegion).HasBytes n digest := by
    refine ⟨hash.1, fun i => (joined.outside _ ?_).trans (hash.2 i)⟩
    have hi := i.isLt
    simp only [Outside, List.mem_singleton, forall_eq]
    rw [digestPtr]
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow]
    bounds
  have num : ParseSignature.scalarValue n fr.rcx = Encoding.octetsToNat digest := by
    have val := Common.octetsToNat_extract_eq_words (off := 0) bytes (by omega)
    have whole : digest.extract 0 32 = digest := by rw [← size, ByteArray.extract_zero_size]
    simpa only [ParseSignature.scalarValue, Nat.zero_add, whole, Nat.add_zero,
      BitVec.ofNat_toNat, BitVec.setWidth_eq] using val.symm
  have srcRead : Readable n fr.rcx 32 := by
    rw [digestPtr]
    exact ((window.of_frame joined).sub (by bounds) (by bounds)).readable
  have dst : Writable Extracted.programImage n ch.rdx 32 :=
    stack'.sub (by dsimp [ch,parseChild]; bounds) (by dsimp [ch,parseChild]; bounds)
  obtain ⟨out,run,tag,done_,writes,widths,status,words⟩ :=
    Verify.Core.fillScalar (fr := ch) entry rfl rfl rfl srcRead dst
      (by simp only [Outside, List.mem_singleton, forall_eq, ch,parseChild, digestPtr]; bounds)
      (by simp only [Outside, List.mem_singleton, forall_eq, ch,parseChild]; bounds)
      (by simp only [Outside, List.mem_singleton, forall_eq, ch,parseChild, digestPtr]; bounds)
      (by simp only [Outside, List.mem_singleton, forall_eq, ch,parseChild]; bounds)
  have called : Verify.Core.Reaches .l101026 a m .l10106a out.values out.store :=
    Verify.reachesOfCall call run tag
  obtain ⟨b, branch, kept, wb⟩ := DigestParse.branch (mem := out.store) status widths
  have db : Atom.All Extracted.programImage b out.store (Fn127d70.doneAt ch) := by
    simp only [Fn127d70.doneAt, Atom.All, Atom.Holds] at done_ ⊢
    simpa only [kept 4 (by decide), kept 22 (by decide), kept 3 (by decide), kept 5 (by decide),
      kept 12 (by decide), kept 13 (by decide), kept 14 (by decide), kept 15 (by decide),
      kept 39 (by decide), kept 50 (by decide), kept 51 (by decide)] using done_
  simp only [Fn127d70.doneAt, Atom.All, Atom.Holds,ch,parseChild] at db
  obtain ⟨rsp,df',bx,bp,r12',r13,r14,r15,mx',ft',fc',_⟩ := db
  rw [BitVec.sub_add_cancel] at rsp
  let area : MemoryRegion := ⟨(fr.rsp - 496).toNat, 376⟩
  have delta : RamWriteFrame m out.store [area] := by
    refine ((RamWriteFrame.refl m [area]).trans setup ?_).trans writes ?_
    · intro reg hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_singleton_self _, by dsimp [area]; bounds⟩
    · intro reg hr
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only [area,ch, parseChild] <;> bounds
  have frame := ready.writes.trans delta (by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _,by dsimp [area]; bounds⟩)
  have preserved {p : BitVec 64} (upper : p.toNat + 8 ≤ 2^64)
      (apart : p.toNat + 8 ≤ fr.rsp.toNat - 496 ∨ fr.rsp.toNat - 120 ≤ p.toNat) :
      memLoad out.store p 64 = memLoad m p 64 := by
    apply delta.memLoad_eq
    simp only [Outside, List.mem_singleton, forall_eq,area]
    bounds
  change WordsAt out.store (fr.rsp - 280 + 104) 64 (scalarWords (ParseSignature.scalarValue n fr.rcx)) at words
  rw [num,show fr.rsp - 280 + 104 = fr.rsp - 176 by bv_omega] at words
  refine ⟨b,out.store,called.trans branch,⟨⟨?_,frame⟩,⟨r15,r14,r13,bx⟩,bp,words,wb⟩⟩
  simp only [Fn100ea0.frameAt, Fn100ea0.frameAtG1, Atom.All, Atom.Holds]
  refine ⟨rsp,df',r12',mx',ft',fc',?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,rr.of_frame delta,?_,
    rl,stack.of_frame delta,room,align,gr0.of_frame delta,?_,gr1.of_frame delta,?_,
    gr2.of_frame delta,?_,gr3.of_frame delta,?_,gr4.of_frame delta,?_,sep,trivial⟩ <;>
    (apply (preserved (by bounds) (by bounds)).trans; assumption)

end K256.Proofs.Signing.Nonce.Initialize
