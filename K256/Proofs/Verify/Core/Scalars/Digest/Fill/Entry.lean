import K256.Proofs.Verify.Core.Scalars.Digest.Fill.Setup
import K256.Proofs.Verify.Core.Memory
import K256.Proofs.Verify.LIR.Fn127d70.Frame
import K256.Proofs.ParseSignature.Contract
import K256.Proofs.Verify.Transfer.SignatureWords

namespace K256.Proofs.Verify.Core.DigestFill

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
open CFG Lift Refine Verify.LIR ParseSignature Standards.SECG.ECC

def child (fr : Activation) (n : Ram) (r9 : BitVec 64) : Activation :=
  {fr with
    original := n, rsp := localSp fr - 8, low := localSp fr - 216, ret := 0x10513d,
    rbx := fr.rdi, r12 := fr.rdx, r13 := fr.rcx, r14 := fr.rsi, r15 := fr.r8,
    rdi := fr.rdx, rsi := 32, rdx := localSp fr + 136, rcx := 4, r8 := 256, r9 := r9}

theorem childEntry {fr : Activation} {a b c : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s : Nat} {m n : Ram} (e : Entry fr a p digest r s) (h : Parsed fr b m r s)
    (sp : c[4] = ⟨64,localSp fr - 8⟩) (si : c[6] = ⟨64,32⟩) (di : c[7] = ⟨64,fr.rdx⟩)
    (cx : c[1] = ⟨64,4⟩) (dx : c[2] = ⟨64,localSp fr + 136⟩) (r8 : c[8] = ⟨64,256⟩)
    (kept : ∀ i : Fin Reg.count, i.val ∈ [3,5,9,12,13,14,15,22,39,50,51] → c[i] = b[i])
    (written : RamWriteFrame m n (setupWrites (localSp fr)))
    (ret : memLoad n (localSp fr - 8) 64 = 0x10513d) :
    let ch := child fr n (b[9].get 64)
    Atom.All Extracted.programImage c n (Fn127d70.frameAt .l127d70 ch) ∧
      Readable n ch.rdi 32 ∧ Writable Extracted.programImage n ch.rdx 32 ∧
      Outside [callStack ch] ch.rdi 32 ∧ Outside [callStack ch] ch.rdx 32 ∧
      Outside [buffer ch.rdx 32] ch.rdi 32 ∧ Outside [buffer ch.rdx 32] 0x203dd0 8 ∧
      scalarValue n ch.rdi = Encoding.octetsToNat digest := by
  intro ch
  have hlow := e.low
  have hroom := e.stackRoom
  have bottom := e.low_toNat
  have stackPointer : ch.rsp.toNat = fr.rsp.toNat - 496 := by
    change (fr.rsp - 488 - 8).toNat = _
    rw [BitVec.sub_sub]
    exact BitVec.toNat_sub_of_le (by change 496 ≤ fr.rsp.toNat; omega)
  have stackLowEq : ch.rsp - 208 = ch.low := by
    change localSp fr - 8 - 208 = localSp fr - 216
    rw [BitVec.sub_sub]
    rfl
  have stackLow : ch.low.toNat = fr.rsp.toNat - 704 := by
    change (fr.rsp - 488 - 216).toNat = _
    rw [BitVec.sub_sub]
    exact BitVec.toNat_sub_of_le (by change 704 ≤ fr.rsp.toNat; omega)
  have localPointer : (localSp fr).toNat = fr.rsp.toNat - 488 :=
    BitVec.toNat_sub_of_le (by change 488 ≤ fr.rsp.toNat; omega)
  have addLocal {offset : Nat} (fit : offset ≤ 320) :
      (localSp fr + BitVec.ofNat 64 offset).toNat = fr.rsp.toNat - 488 + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, localPointer,
      Nat.mod_eq_of_lt (a := offset) (by omega), Nat.mod_eq_of_lt (by omega)]
  have dst : ch.rdx.toNat = fr.rsp.toNat - 488 + 136 := addLocal (offset := 136) (by decide)
  have statusSlot : (localSp fr + 320).toNat = fr.rsp.toNat - 488 + 320 :=
    addLocal (offset := 320) (by decide)
  have src : ch.rdi.toNat = fr.rsp.toNat + 136 := by
    change fr.rdx.toNat = _
    rw [e.hash, BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by change fr.rsp.toNat + 136 < 2 ^ 64; omega)
  have setupWithin : RegionsWithin (setupWrites (localSp fr)) [fr.region] := by
    intro reg hr
    refine ⟨fr.region, List.mem_singleton_self _, ?_⟩
    simp only [setupWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    change (localSp fr - 8).toNat = _ at stackPointer
    rcases hr with rfl | rfl <;>
      simp only [Activation.region, bottom, stackPointer, statusSlot] <;> omega
  have frame := h.frame.trans written setupWithin
  have stack := e.stack.of_frame frame
  have stackWrite : Writable Extracted.programImage n (ch.rsp - 208) 208 := by
    rw [stackLowEq]
    exact stack.sub (by omega) (by omega)
  have retRead : Readable n ch.rsp 8 := stack.readable.sub (by omega) (by omega)
  have dstWrite : Writable Extracted.programImage n ch.rdx 32 :=
    stack.sub (by omega) (by omega)
  have size : digest.size = 32 := e.digestAt.1
  have digestAt : (⟨ch.rdi.toNat, 32⟩ : MemoryRegion).HasBytes n digest := by
    refine ⟨size, fun i => ?_⟩
    have hi := i.isLt
    have apart := e.above (off := 136 + i.val) (len := 1) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at apart
    change Outside [fr.region] (fr.rsp + 136 + BitVec.ofNat 64 i.val) 1 at apart
    rw [← e.hash, ← ofNat_toNat_add] at apart
    exact (frame.outside _ apart).trans (e.digestAt.2 i)
  have srcRead : Readable n ch.rdi 32 := by
    refine ⟨by omega, fun i hi => ?_⟩
    rw [← ofNat_toNat_add, digestAt.2 ⟨i, by omega⟩]
    rfl
  have digestValue : scalarValue n ch.rdi = Encoding.octetsToNat digest := by
    have val := Common.octetsToNat_extract_eq_words (off := 0) digestAt (by omega)
    have whole : digest.extract 0 32 = digest := by rw [← size, ByteArray.extract_zero_size]
    simpa only [scalarValue, Nat.zero_add, whole, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      using val.symm
  have parentAtoms := h.atoms
  simp only [Fn104f20.frameAt, Fn104f20.frameAtG6, Atom.All, Atom.Holds] at parentAtoms
  obtain ⟨_, _, _, _, r12, r13, r14, r15, _, _, _, _, _, _, _, _, _, _, _, _, _,
    align, got1Read, got1Val, got2Read, got2Val, got3Read, got3Val, gotSep, _⟩ := parentAtoms
  have slotApart {addr : BitVec 64} (lo : 0x203dd0 ≤ addr.toNat) (hi : addr.toNat + 8 ≤ 0x203e28) :
      Outside (setupWrites (localSp fr)) addr 8 := by
    change (localSp fr - 8).toNat = _ at stackPointer
    refine ⟨by omega, fun reg hr => ?_⟩
    simp only [setupWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      simp only [stackPointer, statusSlot] <;> omega
  have got1 := (written.memLoad_eq (k := 64)
    (slotApart (addr := 0x203dd0) (by decide) (by decide))).trans got1Val
  have got2 := (written.memLoad_eq (k := 64)
    (slotApart (addr := 0x203de0) (by decide) (by decide))).trans got2Val
  have got3 := (written.memLoad_eq (k := 64)
    (slotApart (addr := 0x203e20) (by decide) (by decide))).trans got3Val
  have r9 : c[9] = ⟨64, ch.r9⟩ := by
    change c[9] = ⟨64, b[9].get 64⟩
    refine (kept 9 (by decide)).trans ?_
    have pack (v : Value) (width : v.width = 64) : v = ⟨64, v.get 64⟩ := by
      obtain ⟨w, bits⟩ := v
      change w = 64 at width
      subst w
      rfl
    exact pack _ h.r9Width
  refine ⟨?_, srcRead, dstWrite, ?_, ?_, ?_, ?_, digestValue⟩
  · simp only [Fn127d70.frameAt, Fn127d70.frameAtG28, Atom.All, Atom.Holds]
    refine ⟨sp, (kept 22 (by decide)).trans h.df, cx, dx,
      (kept 3 (by decide)).trans h.dst, (kept 5 (by decide)).trans h.rbp, si, di, r8, r9,
      (kept 12 (by decide)).trans r12, (kept 13 (by decide)).trans r13,
      (kept 14 (by decide)).trans r14, (kept 15 (by decide)).trans r15,
      (kept 39 (by decide)).trans h.mxcsr, (kept 50 (by decide)).trans h.ftw,
      (kept 51 (by decide)).trans h.fcw, retRead, ret,
      by change (0x10513d : BitVec 64).toNat < 2 ^ 32; decide,
      stackWrite, by omega, by omega,
      got1Read.of_frame written, got1, got2Read.of_frame written, got2, got3Read.of_frame written, got3,
      ?_, trivial⟩
    change 0x203ef8 ≤ ch.rsp.toNat ∨ ch.rsp.toNat ≤ 0x203dd0
    omega
  · simp only [Outside, callStack, List.mem_singleton, forall_eq, stackLow, stackPointer, src]
    omega
  · simp only [Outside, callStack, List.mem_singleton, forall_eq, stackLow, stackPointer, dst]
    omega
  · simp only [Outside, buffer, List.mem_singleton, forall_eq, src, dst]
    omega
  · simp only [Outside, buffer, List.mem_singleton, forall_eq, dst, BitVec.reduceToNat, Nat.reducePow]
    omega

end K256.Proofs.Verify.Core.DigestFill
