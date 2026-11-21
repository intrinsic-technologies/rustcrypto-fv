import K256.Proofs.Verify.Core.Scalars.Digest.Fill
import K256.Proofs.Verify.Core.Scalars.Digest.Frame
import K256.Proofs.Verify.Core.Scalars.Digest.Reduce
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1 ParseSignature

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}

private theorem octetsToNat_lt (input : ByteArray) : Encoding.octetsToNat input < 256 ^ input.size := by
  rcases input with ⟨data⟩
  rcases data with ⟨items⟩
  generalize hr : items.reverse = rev
  have he : items = rev.reverse := by rw [← hr, List.reverse_reverse]
  subst items
  clear hr
  induction rev with
  | nil => decide +kernel
  | cons byte rev ih =>
    let data := rev.reverse.toArray
    simp only [List.reverse_cons]
    have hpush : (⟨rev.reverse ++ [byte]⟩ : Array UInt8) = data.push byte := by
      apply Array.toList_inj.mp
      simp [data]
    rw [hpush]
    change Encoding.octetsToNat ⟨data⟩ < 256 ^ (ByteArray.size ⟨data⟩) at ih
    have hb := byte.toNat_lt
    simp only [ByteArray.size, Array.size_push]
    change (data.push byte).foldl (fun v b => 256*v+b.toNat) 0 < 256^(data.size+1)
    rw [Array.foldl_push, Nat.pow_succ]
    change 256 * Encoding.octetsToNat ⟨data⟩ + byte.toNat < 256 ^ (ByteArray.size ⟨data⟩) * 256
    omega

private theorem width64 {v : Value} (h : v.width = 64) : v = ⟨64, v.get 64⟩ := by
  obtain ⟨w,z⟩ := v
  change w = 64 at h
  subst w
  rfl

local macro "addr_bounds" : tactic => `(tactic|
  (simp only [localSp, BitVec.toNat_add, BitVec.toNat_sub, BitVec.reduceToNat, Nat.reducePow] at *
   omega))

theorem reduceDigest (e : Entry fr a p digest r s) {b m} (h : Parsed fr b m r s) :
    ∃ c n, Reaches .l1050c1 b m .l10518b c n ∧ Reduced fr c n digest r s := by
  obtain ⟨c,n,filled,f⟩ := fillDigest e h
  have area := e.stack.of_frame f.frame
  have low := e.low
  have room := e.stackRoom
  have lowNat := e.low_toNat
  have stack : Writable Extracted.programImage n (localSp fr - 8) 176 :=
    area.sub (by addr_bounds) (by addr_bounds)
  obtain ⟨args,call,sp,src,dst,cx,keep⟩ := Digest.prepare c n (localSp fr)
    (congrArg (Value.get 64) f.sp) stack
  let ch := Digest.activation fr args n
  have staged := Digest.stageFrame e n
  have stageArea := area.of_frame staged
  have ai := f.atoms
  simp only [Fn104f20.frameAt, Fn104f20.frameAtG6, Atom.All, Atom.Holds] at ai
  obtain ⟨_,_,_,_,key12,key13,key14,key15,_,_,_,_,_,_,_,_,retRead,retMem,retLow,
    stk,roomOld,align,gotRead₁,gotVal₁,gotRead₂,gotVal₂,gotApart,_⟩ := ai
  have arg (i : Fin Reg.count) (hi : i.val ∈ [2,8,9]) : args[i] = ⟨64, args[i].get 64⟩ := by
    apply width64
    rw [keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)]
    apply f.widths
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega
  have ent : Atom.All Extracted.programImage args ch.original (Fn109f80.frameAt .l109f80 ch) := by
    simp only [Fn109f80.frameAt, Fn109f80.frameAtG11, Atom.All, Atom.Holds]
    refine ⟨sp,(keep 22 (by decide)).trans f.df,width64 cx,arg 2 (by decide),
      (keep 3 (by decide)).trans f.dst,(keep 5 (by decide)).trans f.rbp,src,dst,
      arg 8 (by decide),arg 9 (by decide),(keep 12 (by decide)).trans key12,
      (keep 13 (by decide)).trans key13,(keep 14 (by decide)).trans key14,
      (keep 15 (by decide)).trans key15,(keep 39 (by decide)).trans f.mxcsr,
      (keep 50 (by decide)).trans f.ftw,(keep 51 (by decide)).trans f.fcw,?_,?_,by change (0x10518b : Nat) < 2^32; decide,?_,?_,?_,trivial⟩
    · exact stageArea.readable.sub (by change fr.low.toNat ≤ (localSp fr - 8).toNat; addr_bounds)
        (by change (localSp fr - 8).toNat + 8 ≤ _; addr_bounds)
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · apply stageArea.sub <;> dsimp only [ch, Digest.activation] <;> addr_bounds
    · dsimp only [ch, Digest.activation]; addr_bounds
    · dsimp only [ch, Digest.activation]; addr_bounds
  have atSrc : Readable ch.original ch.rsi 32 := by
    apply stageArea.readable.sub <;> dsimp only [ch,Digest.activation] <;> addr_bounds
  have atDst : Writable Extracted.programImage ch.original ch.rdi 32 := by
    apply stageArea.sub <;> dsimp only [ch,Digest.activation] <;> addr_bounds
  have apart (off : BitVec 64) (ho : off.toNat ≤ 352) : Outside [callStack ch] (localSp fr + off) 32 := by
    refine ⟨by addr_bounds, fun reg hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    dsimp only [callStack, ch, Digest.activation]
    addr_bounds
  obtain ⟨out,exec,tag,done_,post,words,_⟩ := reduceScalar ent atSrc atDst
    (apart 8 (by decide)) (apart 352 (by decide)) (Digest.stagedWords f.digestAt)
    (by simpa only [show digest.size = 32 from e.digestAt.1, show 256^32 = 2^256 by decide +kernel] using octetsToNat_lt digest)
  have delta := staged.trans post (Digest.calleeWithin e args n)
  have wf := f.frame.trans delta (Digest.writesWithin e)
  have finish : Reaches .l105145 c n .l10518b out.values out.store := by
    refine .step (b := ⟨⟨.l109f80,args,ch.original⟩,[Digest.resume]⟩) ?_ ?_
    · change program.step _ _ = _
      simp only [Program.step, call, Transfer.next, ch, Digest.activation]
    · exact exec_reaches_resume exec Digest.resume [] (by simp only [tag]; rfl)
  simp only [Fn109f80.doneAt, Atom.All, Atom.Holds, ch, Digest.activation] at done_
  obtain ⟨rsp,df,rbx,rbp,r12,r13,r14,r15,mxcsr,ftw,fcw,_⟩ := done_
  rw [show localSp fr - 8 + 8 = localSp fr by bv_omega] at rsp
  have keepSlot (d : BitVec 64) (hd : d.toNat ≤ 40) :
      memLoad out.store (fr.rsp - d) 64 = memLoad n (fr.rsp - d) 64 := by
    apply delta.memLoad_eq
    apply Digest.apartWrites <;> addr_bounds
  have saved : Saved fr out.values out.store :=
    ⟨rsp,rbx,rbp,df,mxcsr,ftw,fcw,(keepSlot _ (by decide)).trans f.rbx,
     (keepSlot _ (by decide)).trans f.r12,(keepSlot _ (by decide)).trans f.r13,
     (keepSlot _ (by decide)).trans f.r14,(keepSlot _ (by decide)).trans f.r15⟩
  refine ⟨_,_,filled.trans finish,⟨⟨saved,wf⟩,?_,words,?_,?_⟩⟩
  · simp only [Fn104f20.frameAt, Fn104f20.frameAtG6, Atom.All, Atom.Holds]
    refine ⟨rsp,df,rbx,rbp,r12,r13,r14,r15,mxcsr,ftw,fcw,saved.rbx,saved.r12,saved.r13,
      saved.r14,saved.r15,retRead.of_frame delta,?_,retLow,stk.of_frame delta,roomOld,
      align,gotRead₁.of_frame delta,?_,gotRead₂.of_frame delta,?_,gotApart,trivial⟩
    · exact (show memLoad out.store fr.rsp 64 = memLoad n fr.rsp 64 by simpa using keepSlot 0 (by decide)).trans retMem
    · exact (delta.memLoad_eq (Digest.apartWrites (by decide) (by addr_bounds) (by addr_bounds))).trans gotVal₁
    · exact (delta.memLoad_eq (Digest.apartWrites (by decide) (by addr_bounds) (by addr_bounds))).trans gotVal₂
  · apply f.rAt.of_frame delta (by decide)
    apply Digest.apartWrites <;> addr_bounds
  · apply f.sAt.of_frame delta (by decide)
    apply Digest.apartWrites <;> addr_bounds

end K256.Proofs.Verify.Core
