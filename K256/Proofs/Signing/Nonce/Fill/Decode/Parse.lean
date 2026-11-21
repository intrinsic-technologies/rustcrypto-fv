import K256.Proofs.Signing.Nonce.Fill.Decode.Order
import K256.Proofs.Signing.Nonce.Fill.Decode.ParseBlocks
import K256.Proofs.Signing.Nonce.Fill.Memory

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Verify.Core (Registers Reaches)
open Initialize (State StateAt)

def decodeWrites (base : BitVec 64) : List MemoryRegion :=
  [⟨(base-216).toNat,216⟩, ⟨(base+8).toNat,32⟩, ⟨(base+60).toNat,4⟩,
    ⟨(base+104).toNat,32⟩, ⟨(base+152).toNat,32⟩]

local macro "decode_addr" : tactic => `(tactic|
  (try simp only [sp, BitVec.toNat_sub, BitVec.toNat_add, BitVec.reduceToNat,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, MemoryRegion.start, MemoryRegion.size]
   omega))

theorem decodeOutside {fr : Activation} (env : Environment fr)
    (p : BitVec 64) (len : Nat) (bound : p.toNat + len ≤ 2^64)
    (apart : p.toNat + len ≤ fr.rsp.toNat - 448 ∨
      fr.rsp.toNat ≤ p.toNat) :
    Outside (decodeWrites (sp fr)) p len := by
  have depth := env.depth
  have limit := env.limit
  refine ⟨bound, fun r hr => ?_⟩
  simp only [decodeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl <;> decode_addr

structure Parsed (fr : Activation) (a : Registers) (m : Ram) (x : Nat) : Prop where
  spEq : a[4] = ⟨64,sp fr⟩
  dst : a[12] = ⟨64,sp fr + 8⟩
  len : a[13] = ⟨64,32⟩
  shift : a[14] = ⟨64,0⟩
  order : a[15] = ⟨64,fr.rsp + 600⟩
  words : WordsAt m (sp fr + 104) 64 (scalarWords x)

private theorem parseChildEntry {fr : Activation} (env : Environment fr) {a : Registers}
    {m n : Ram} (start : Frame fr a m) {b : Registers}
    (setup : RamWriteFrame m n (decodeWrites (sp fr)))
    (ret : memLoad n (sp fr - 8) 64 = 0x100c38)
    (regs : b[4] = ⟨64,sp fr-8⟩ ∧ b[1] = ⟨64,4⟩ ∧ b[2] = ⟨64,sp fr+104⟩ ∧
      b[6] = ⟨64,32⟩ ∧ b[7] = ⟨64,fr.rsi⟩ ∧ b[8] = ⟨64,256⟩ ∧ b[9] = ⟨64,0⟩ ∧
      b[12] = ⟨64,sp fr+8⟩ ∧ b[13] = ⟨64,32⟩ ∧ b[14] = ⟨64,0⟩ ∧
      b[15] = ⟨64,fr.rsp+600⟩)
    (saved : b[3] = a[3] ∧ b[5] = a[5] ∧ b[22] = a[22] ∧ b[39] = a[39] ∧
      b[50] = a[50] ∧ b[51] = a[51]) :
    Atom.All Extracted.programImage b n (Fn127d70.frameAt .l127d70
      { fr with
        original := n, rsp := sp fr - 8, low := sp fr - 216, ret := 0x100c38
        rcx := 4, rdx := sp fr + 104, rsi := 32, rdi := fr.rsi, r8 := 256, r9 := 0
        rbx := a[3].get 64, rbp := a[5].get 64, r12 := sp fr + 8
        r13 := 32, r14 := 0, r15 := fr.rsp + 600 }) := by
  obtain ⟨sp',cx,dx,si,di,r8,r9,r12,r13,r14,r15⟩ := regs
  obtain ⟨bx,bp,df,mx,ft,fc⟩ := saved
  have atoms := start.atoms
  simp only [Fn100a40.frameAt, Fn100a40.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨_,df',mx',ft',fc',_,_,_,_,_,_,_,_,_,_,_,_,win,_,align,
    g0,v0,g1,v1,_,_,g3,v3,apart,_⟩ := atoms
  have depth := env.depth
  have limit := env.limit
  have stack := win.of_frame setup
  have word (i : Fin Reg.count) (h : i.val ∈ Activation.entryNumbers) :
      a[i] = ⟨64,a[i].get 64⟩ := by
    have width := start.widths i h
    generalize a[i] = v at width ⊢
    cases v with
    | mk width' bits =>
      cases width
      rfl
  have outside (p : BitVec 64) (lo : 0x203dd0 ≤ p.toNat) (hi : p.toNat + 8 ≤ 0x203e28) :
      Outside (decodeWrites (sp fr)) p 8 := by
    apply decodeOutside env p 8 (by omega)
    rcases apart with h | h <;> omega
  simp only [Fn127d70.frameAt, Fn127d70.frameAtG28, Atom.All, Atom.Holds]
  refine ⟨sp',df.trans df',cx,dx,bx.trans (word 3 (by decide)),bp.trans (word 5 (by decide)),
    si,di,r8,r9,r12,r13,r14,r15,mx.trans mx',ft.trans ft',fc.trans fc',
    stack.readable.sub (by decode_addr) (by decode_addr),ret,by decide,
    stack.sub (by decode_addr) (by decode_addr),by decode_addr,by decode_addr,
    g0.of_frame setup,(setup.memLoad_eq (outside _ (by decide) (by decide))).trans v0,
    g1.of_frame setup,(setup.memLoad_eq (outside _ (by decide) (by decide))).trans v1,
    g3.of_frame setup,(setup.memLoad_eq (outside _ (by decide) (by decide))).trans v3,
    by rcases apart with h|h <;> decode_addr,trivial⟩

set_option maxHeartbeats 1000000 in
theorem parseCandidate {fr : Activation} {state : State} {a : Registers} (env : Environment fr)
    {m : Ram} (updated : Updated fr state a m) :
    ∃ b n, Reaches .l100afb a m .l100c40 b n ∧ RamWriteFrame m n (decodeWrites (sp fr)) ∧
      Parsed fr b n (candidate state).1 ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i]) := by
  have frame := updated.toFrame
  have atoms := frame.atoms
  simp only [Fn100a40.frameAt, Fn100a40.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨spEq,_,_,_,_,dstSlot,lenSlot,genSlot,_,_,_,_,_,_,_,_,_,win,_,_,_⟩ := atoms
  have dstEq : sp fr + 40 = fr.rsp - 192 := by unfold sp; bv_omega
  have lenEq : sp fr + 48 = fr.rsp - 184 := by unfold sp; bv_omega
  have genEq : sp fr + 144 = fr.rsp - 88 := by unfold sp; bv_omega
  have depth := env.depth
  have limit := env.limit
  have upper := env.window.of_frame frame.writes
  have genRead : Readable m fr.rdi 8 := by
    rw [env.gen]
    exact upper.readable.sub (by decode_addr) (by decode_addr)
  have orderRead : Readable m (fr.rsp+600) 32 :=
    upper.readable.sub (by decode_addr) (by decode_addr)
  have words := frame.orderWords env
  have q0 : memLoad m (fr.rsp+600) 64 = 0xbfd25e8cd0364141 := by
    have e := words 0 (by decide)
    rw [show wordAddr (fr.rsp+600) 64 0 = fr.rsp+600 by simp only [wordAddr]; bv_omega] at e
    exact e.trans (by decide +kernel)
  have q1 : memLoad m (fr.rsp+600+8) 64 = 0xbaaedce6af48a03b :=
    (words 1 (by decide)).trans (by decide +kernel)
  have q2 : memLoad m (fr.rsp+600+16) 64 = 0xfffffffffffffffe :=
    (words 2 (by decide)).trans (by decide +kernel)
  have q3 : memLoad m (fr.rsp+600+24) 64 = 0xffffffffffffffff :=
    (words 3 (by decide)).trans (by decide +kernel)
  have spBits : a[4].get 64 = sp fr := congrArg (Value.get 64) spEq
  have scanArea : Writable Extracted.programImage m (sp fr) 152 := by
    have h := frame.slot env 0 152 (by decide)
    rw [show sp fr + 0 = sp fr by bv_omega] at h
    exact h
  obtain ⟨c,o,scan,writeScan,csp,c12,c14,c15,c8,c9,c3,c5,c22,c39,c50,c51⟩ :=
    orderScanBlock spBits scanArea
      genRead orderRead (genEq.symm ▸ genSlot) (frame.orderPtr env) frame.bits q0 q1 q2 q3 (by
        simp only [Outside, List.mem_singleton, forall_eq]
        constructor <;> decode_addr)
  have scanPath : Reaches .l100afb a m .l100bf0 c o := by
    apply Semantics.Reaches.single
    change (program.runBlock _ _).next _ [] = _
    rw [scan]
    rfl
  have readScan (i : BitVec 64) (lo : 40 ≤ i.toNat) (hi : i.toNat ≤ 48) :
      memLoad o (sp fr+i) 64 = memLoad m (sp fr+i) 64 := by
    apply writeScan.memLoad_eq
    have h := env.slotNat i (by omega)
    have hs := env.slotNat 8 (by decide)
    simp only [Outside, List.mem_singleton, forall_eq, h, hs, Nat.reduceDiv, BitVec.reduceToNat]
    omega
  have cspBits : c[4].get 64 = sp fr := (congrArg (Value.get 64) csp).trans spBits
  obtain ⟨d,lenPath,d6,d13,keepD⟩ :=
    orderScanLength cspBits
      ((frame.slot env 48 8 (by decide)).readable.of_frame writeScan)
      ((readScan 48 (by decide) (by decide)).trans (lenEq.symm ▸ lenSlot.trans env.size))
  have area : Writable Extracted.programImage o (sp fr-8) 144 :=
    (win.of_frame writeScan).sub (by decode_addr) (by decode_addr)
  obtain ⟨e,p,call,writeSetup,ret,esp,e1,e2,e7,keepE⟩ :=
    enterParser ((congrArg (Value.get 64) (keepD 4 (by decide))).trans cspBits)
      (by decode_addr) ((keepD 8 (by decide)).trans c8) area
      ((readScan 40 (by decide) (by decide)).trans (dstEq.symm ▸ dstSlot))
  have writes : RamWriteFrame m p (decodeWrites (sp fr)) := by
    refine ((RamWriteFrame.refl m _).trans writeScan ?_).trans writeSetup ?_
    · intro r hr
      rcases List.mem_singleton.mp hr with rfl
      exact ⟨⟨(sp fr + 8).toNat,32⟩,by simp only [decodeWrites, List.mem_cons, true_or, or_true],
        Nat.le_refl _,Nat.add_le_add_left (by decide : 1 ≤ 32) _⟩
    · intro r hr
      simp only [parserSetupWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl|rfl|rfl
      · refine ⟨⟨(sp fr-216).toNat,216⟩, by simp only [decodeWrites, List.mem_cons, true_or], ?_, ?_⟩ <;>
          decode_addr
      · exact ⟨⟨(sp fr + 60).toNat,4⟩,by simp only [decodeWrites, List.mem_cons, or_true, true_or],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨⟨(sp fr + 104).toNat,32⟩,by simp only [decodeWrites, List.mem_cons, or_true, true_or],Nat.le_refl _,Nat.le_refl _⟩
  let ch : Activation :=
    { fr with
      original := p, rsp := sp fr - 8, low := sp fr - 216, ret := 0x100c38
      rcx := 4, rdx := sp fr + 104, rsi := 32, rdi := fr.rsi, r8 := 256, r9 := 0
      rbx := a[3].get 64, rbp := a[5].get 64, r12 := sp fr + 8, r13 := 32, r14 := 0, r15 := fr.rsp + 600 }
  have regs (i : Fin Reg.count) (h : i.val ∈ [3,5,12,14,15,22,39,50,51]) :
      e[i] = c[i] := (keepE i (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)).trans
        (keepD i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega))
  have e22 := (regs 22 (by decide)).trans c22
  have e39 := (regs 39 (by decide)).trans c39
  have e50 := (regs 50 (by decide)).trans c50
  have e51 := (regs 51 (by decide)).trans c51
  have entry : Atom.All Extracted.programImage e p (Fn127d70.frameAt .l127d70 ch) :=
    parseChildEntry env frame writes ret
      ⟨esp,e1,e2,(keepE 6 (by decide)).trans d6,e7,(keepE 8 (by decide)).trans ((keepD 8 (by decide)).trans c8),
       (keepE 9 (by decide)).trans ((keepD 9 (by decide)).trans c9),
       (regs 12 (by decide)).trans c12,(keepE 13 (by decide)).trans d13,
       (regs 14 (by decide)).trans c14,(regs 15 (by decide)).trans c15⟩
      ⟨(regs 3 (by decide)).trans c3,(regs 5 (by decide)).trans c5,e22,e39,e50,e51⟩
  have dstRead : Readable p fr.rsi 32 := by
    rw [env.dst]
    exact (upper.of_frame writes).readable.sub (by decode_addr) (by decode_addr)
  have localDst := (frame.slot env 104 32 (by decide)).of_frame writes
  obtain ⟨out,ran,tag,done_,callWrites,_,status,parsed⟩ :=
    Verify.Core.fillScalar (fr := ch) entry rfl rfl rfl dstRead localDst
      (by simp only [Outside, List.mem_singleton, forall_eq, ch, ParseSignature.callStack, env.dst]; constructor <;> decode_addr)
      (by simp only [Outside, List.mem_singleton, forall_eq, ch, ParseSignature.callStack]; constructor <;> decode_addr)
      (by simp only [Outside, List.mem_singleton, forall_eq, ch, ParseSignature.buffer, env.dst]; constructor <;> decode_addr)
      (by
        have globals := frame.atoms
        simp only [Fn100a40.frameAt, Fn100a40.frameAtG1, Atom.All, Atom.Holds] at globals
        obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,apart,_⟩ := globals
        simp only [Outside, List.mem_singleton, forall_eq, ch, ParseSignature.buffer]
        constructor <;> (rcases apart with h|h <;> decode_addr))
  have callPath := Verify.reachesOfCall call ran tag
  obtain ⟨b,branch,kept⟩ := parseStatus (m := out.store) status
  have bytes := UpdateV.Finalize.bytesAfter writes
    (decodeOutside env fr.rsi 32 (by rw [env.dst]; decode_addr) (Or.inr (by rw [env.dst]; decode_addr))) updated.bytes
  have numeric : ParseSignature.scalarValue p fr.rsi = (candidate state).1 := by
    rw [Drbg.candidate_eq]
    have size : (Drbg.updateValue state).value.size = 32 := bytes.1
    have whole : (Drbg.updateValue state).value.extract 0 32 = (Drbg.updateValue state).value := by
      rw [← size, ByteArray.extract_zero_size]
    have val := Common.octetsToNat_extract_eq_words (off := 0) bytes (by omega)
    simpa only [ParseSignature.scalarValue, Nat.zero_add, whole, Nat.add_zero,
      BitVec.ofNat_toNat, BitVec.setWidth_eq] using val.symm
  change WordsAt out.store (sp fr+104) 64 (scalarWords (ParseSignature.scalarValue p fr.rsi)) at parsed
  rw [numeric] at parsed
  have total : RamWriteFrame m out.store (decodeWrites (sp fr)) := by
    apply writes.trans callWrites
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl|rfl
    · refine ⟨⟨(sp fr-216).toNat,216⟩,by simp only [decodeWrites, List.mem_cons, true_or],?_,?_⟩
      · exact Nat.le_refl _
      · dsimp only [Activation.region, ch]
        decode_addr
    · exact ⟨⟨(sp fr+104).toNat,32⟩,by simp only [decodeWrites, List.mem_cons, or_true, true_or],Nat.le_refl _,Nat.le_refl _⟩
  simp only [Fn127d70.doneAt, Atom.All, Atom.Holds, ch] at done_
  obtain ⟨rsp,df,_,_,r12,r13,r14,r15,mx,ft,fc,_⟩ := done_
  refine ⟨b,out.store,(scanPath.trans lenPath).trans (callPath.trans branch),total,
    ⟨(kept 4 (by decide)).trans ?_, (kept 12 (by decide)).trans r12, (kept 13 (by decide)).trans r13,
     (kept 14 (by decide)).trans r14, (kept 15 (by decide)).trans r15, parsed⟩,?_⟩
  · simpa only [BitVec.sub_add_cancel] using rsp
  · have pre := frame.atoms
    simp only [Fn100a40.frameAt, Fn100a40.frameAtG1, Atom.All, Atom.Holds] at pre
    obtain ⟨_,df',mx',ft',fc',_⟩ := pre
    rintro ⟨i, _⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    · exact (kept 22 (by decide)).trans (df.trans df'.symm)
    · exact (kept 39 (by decide)).trans (mx.trans mx'.symm)
    · exact (kept 50 (by decide)).trans (ft.trans ft'.symm)
    · exact (kept 51 (by decide)).trans (fc.trans fc'.symm)

end K256.Proofs.Signing.Nonce.Fill
