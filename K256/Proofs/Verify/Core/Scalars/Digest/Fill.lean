import K256.Proofs.Verify.Core.Scalars.Digest.Fill.Frame
import K256.Proofs.Verify.Core.Scalars.Digest.Fill.Branch
import K256.Proofs.Verify.Core.Scalars.Digest.Fill.Call
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Generate.Generator.Multiply

structure DigestFilled (fr : Activation) (a : Registers) (m : Ram)
    (digest : ByteArray) (r s : Nat) : Prop extends Phase fr a m where
  atoms : Atom.All Extracted.programImage a m (Fn104f20.frameAt .l105145 fr)
  digestAt : WordsAt m (localSp fr + 136) 64 (scalarWords (Encoding.octetsToNat digest))
  rAt : WordsAt m (localSp fr + 256) 64 (scalarWords r)
  sAt : WordsAt m (localSp fr + 224) 64 (scalarWords s)
  widths : ParseSignature.ArgumentWidths a

local macro "fill_addr" : tactic => `(tactic|
  (simp only [localSp, BitVec.toNat_add, BitVec.toNat_sub, BitVec.reduceToNat, Nat.reducePow] at *
   omega))

private theorem outsideFillWrites {fr : Activation} {addr : BitVec 64} {n : Nat}
    (upper : addr.toNat + n ≤ 2^64)
    (stack : addr.toNat + n ≤ (localSp fr - 216).toNat ∨ (localSp fr - 216).toNat + 384 ≤ addr.toNat)
    (slot : addr.toNat + n ≤ (localSp fr + 320).toNat ∨ (localSp fr + 320).toNat + 4 ≤ addr.toNat) :
    Outside (DigestFill.writes fr) addr n := by
  refine ⟨upper, fun reg hr => ?_⟩
  simp only [DigestFill.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact stack
  · exact slot

local macro "fill_apart" : tactic => `(tactic| (apply outsideFillWrites <;> fill_addr))

theorem fillDigest {fr : Activation} {a b : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s : Nat} {m : Ram} (e : Entry fr a p digest r s) (h : Parsed fr b m r s) :
    ∃ c n, Reaches .l1050c1 b m .l105145 c n ∧ DigestFilled fr c n digest r s := by
  have atoms := h.atoms
  simp only [Fn104f20.frameAt, Fn104f20.frameAtG6, Atom.All, Atom.Holds] at atoms
  obtain ⟨_,_,_,_,hashReg,sizeReg,_,_,_,_,_,_,_,_,_,_,retRead,retMem,retLow,
    stack,roomOld,align,_,_,gotRead₁,gotVal₁,gotRead₂,gotVal₂,gotSep,_⟩ := atoms
  have low := e.low
  have room := e.stackRoom
  have lowNat := e.low_toNat
  have window : Writable Extracted.programImage m (localSp fr - 8) 332 :=
    (e.stack.of_frame h.frame).sub (by fill_addr) (by fill_addr)
  obtain ⟨c,n,call,sp,si,di,cx,dx,r8,kept,staged,ret⟩ :=
    DigestFill.setup b m (localSp fr) fr.rdx (congrArg (Value.get 64) h.sp)
      ((congrArg (Value.get 64) sizeReg).trans e.size) (congrArg (Value.get 64) hashReg) window
  let ch := DigestFill.child fr n (b[9].get 64)
  obtain ⟨ent,src,dst,srcApart,dstApart,disjoint,slot,num⟩ :=
    DigestFill.childEntry e h sp si di cx dx r8 kept staged ret
  obtain ⟨out,exec,tag,done_,wf,widths,status,words⟩ :=
    fillScalar (fr := ch) ent rfl rfl rfl src dst srcApart dstApart disjoint slot
  have called : Reaches .l1050c1 b m .l10513d out.values out.store := by
    refine .step (b := ⟨⟨.l127d70,c,n⟩,[DigestFill.resume]⟩) ?_ ?_
    · change program.step _ _ = _
      simp only [Program.step, call, Transfer.next]
    · exact ParseSignature.exec_reaches_resume exec DigestFill.resume [] (by simp only [tag]; rfl)
  obtain ⟨z,branched,regs,wz⟩ := DigestFill.branch (mem := out.store) status widths
  have delta := DigestFill.totalWrites e staged wf
  have frame := h.frame.trans delta (DigestFill.writesWithin e)
  have dz : Atom.All Extracted.programImage z out.store (Fn127d70.doneAt ch) := by
    simp only [Fn127d70.doneAt, Atom.All, Atom.Holds] at done_ ⊢
    simpa only [regs 4 (by decide),regs 22 (by decide),regs 3 (by decide),regs 5 (by decide),
      regs 12 (by decide),regs 13 (by decide),regs 14 (by decide),regs 15 (by decide),
      regs 39 (by decide),regs 50 (by decide),regs 51 (by decide)] using done_
  simp only [Fn127d70.doneAt, Atom.All, Atom.Holds, ch, DigestFill.child] at dz
  obtain ⟨rsp,df,rbx,rbp,r12,r13,r14,r15,mxcsr,ftw,fcw,_⟩ := dz
  rw [show localSp fr - 8 + 8 = localSp fr by bv_omega] at rsp
  have keepSlot (d : BitVec 64) (hd : d.toNat ≤ 40) :
      memLoad out.store (fr.rsp - d) 64 = memLoad m (fr.rsp - d) 64 := by
    apply delta.memLoad_eq
    fill_apart
  have saved : Saved fr z out.store :=
    ⟨rsp,rbx,rbp,df,mxcsr,ftw,fcw,(keepSlot _ (by decide)).trans h.rbx,
     (keepSlot _ (by decide)).trans h.r12,(keepSlot _ (by decide)).trans h.r13,
     (keepSlot _ (by decide)).trans h.r14,(keepSlot _ (by decide)).trans h.r15⟩
  change ParseSignature.scalarValue ch.original ch.rdi = _ at num
  rw [num] at words
  refine ⟨_,_,called.trans branched,⟨⟨saved,frame⟩,?_,words,?_,?_,wz⟩⟩
  · simp only [Fn104f20.frameAt, Fn104f20.frameAtG6, Atom.All, Atom.Holds]
    refine ⟨rsp,df,rbx,rbp,r12,r13,r14,r15,mxcsr,ftw,fcw,saved.rbx,saved.r12,saved.r13,
      saved.r14,saved.r15,retRead.of_frame delta,?_,retLow,stack.of_frame delta,roomOld,
      align,gotRead₁.of_frame delta,?_,gotRead₂.of_frame delta,?_,by omega,trivial⟩
    · exact (show memLoad out.store fr.rsp 64 = memLoad m fr.rsp 64 by simpa using keepSlot 0 (by decide)).trans retMem
    · exact (delta.memLoad_eq (by fill_apart)).trans gotVal₁
    · exact (delta.memLoad_eq (by fill_apart)).trans gotVal₂
  · apply h.rAt.of_frame delta (by decide)
    fill_apart
  · apply h.sAt.of_frame delta (by decide)
    fill_apart

end K256.Proofs.Verify.Core
