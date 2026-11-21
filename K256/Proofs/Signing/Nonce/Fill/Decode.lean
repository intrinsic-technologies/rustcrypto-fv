import K256.Proofs.Signing.Nonce.Fill.State
import K256.Proofs.Verify.LIR.Fn100a40
import K256.Proofs.Verify.Core.Affine.Call
import K256.Proofs.Verify.Choice
import K256.Proofs.Sec1.Serialize.Assemble.Memory
import K256.Proofs.Common.Tactic
import K256.Proofs.Signing.Nonce.Fill.Decode.Parse
import K256.Proofs.Signing.Nonce.Initialize.Seed.Parse.Shift

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
open Verify.Core (Registers Reaches)

private def shiftSetupWrites (base : BitVec 64) : List MemoryRegion :=
  [⟨(base+72).toNat,8⟩,⟨(base+232).toNat,32⟩]

set_option maxHeartbeats 450000 in
private theorem enterShift {base : BitVec 64} {a : Registers} {m : Ram} {w : Vector (BitVec 64) 4}
    (area : Writable Extracted.programImage m base 264)
    (rsp : a[4].get 64 = base+80) (dest : a[12] = ⟨64,base+88⟩) (shift : a[14] = ⟨64,0⟩)
    (words : WordsAt m (base+184) 64 w) :
    ∃ (b : Registers) (n : Ram),
      program.runBlock (dialect Extracted.programImage) ⟨.l100c40,a,m⟩ =
        .call ⟨.l1065b0,b,n⟩ (Verify.resumeAt .l100c8a 0x100c8a) ∧
      RamWriteFrame m n (shiftSetupWrites base) ∧ memLoad n (base+72) 64 = 0x100c8a ∧
      WordsAt n (base+232) 64 w ∧ b[4] = ⟨64,base+72⟩ ∧
      b[6] = ⟨64,base+232⟩ ∧ b[7] = ⟨64,base+88⟩ ∧ b[2] = ⟨64,0⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) := by
  have loc := area.readable.low
  have z : a[14].get 64 = 0 := congrArg (Value.get 64) shift
  have dst : a[12].get 64 = base+88 := congrArg (Value.get 64) dest
  have w0 : memLoad m (base+184) 64 = w[0] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.mul_zero, BitVec.add_zero] using words 0 (by decide)
  have w1 : memLoad m (base+192) 64 = w[1] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, Lift.reduceAddOffset] using words 1 (by decide)
  have w2 : memLoad m (base+200) 64 = w[2] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, Lift.reduceAddOffset] using words 2 (by decide)
  have w3 : memLoad m (base+208) 64 = w[3] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, Lift.reduceAddOffset] using words 3 (by decide)
  refine ⟨?_,?_,?step,?post⟩
  case step =>
    cfg_eval [rsp,z,dst,BitVec.add_assoc,BitVec.reduceAdd,Lift.reduceAddOffset]
    segment_words [w0,w1,w2,w3]
    have code : ∀ x ∈ codeRange 0x100c40 bytes_l100c40, x ∈ Extracted.programImage :=
      fun x hx => Verify.Core.Affine.coreText x (code_l100c40 x hx)
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code)
    rfl
  case post =>
    refine ⟨?_,?_,?_,rfl,rfl,rfl,rfl,?_⟩
    · unfold shiftSetupWrites
      slot_state region
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · apply Sec1.Serialize.Assemble.fourWordsAt <;>
        segment_words [w0,w1,w2,w3,BitVec.add_assoc, BitVec.reduceAdd]
    · rintro ⟨i,_⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Signing.Nonce.Fill

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Verify.Core (Registers Reaches)
open Initialize (State StateAt)
open Initialize.DigestShift

local macro "decode_addr" : tactic => `(tactic|
  (try simp only [sp, BitVec.toNat_sub, BitVec.toNat_add, BitVec.reduceToNat,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, MemoryRegion.start, MemoryRegion.size]
   omega))

set_option maxHeartbeats 1000000 in
theorem decode {fr : Activation} {state : State} {a : Registers} (env : Environment fr)
    {m : Ram} (updated : Updated fr state a m) :
    ∃ b n, Reaches .l100afb a m .l100c8a b n ∧ Decoded fr state b n := by
  have depth := env.depth
  have limit := env.limit
  let base := fr.rsp - 312
  obtain ⟨b,n,parse,parsedWrites,parsed,parsedFlags⟩ := parseCandidate env updated
  have stack := updated.toFrame.stack.of_frame parsedWrites
  have area : Writable Extracted.programImage n base 264 :=
    stack.sub (by dsimp only [base]; decode_addr) (by dsimp only [base]; decode_addr)
  have rspEq : base + 80 = sp fr := by dsimp only [base,sp]; bv_omega
  have sourceEq : base + 184 = sp fr + 104 := by dsimp only [base,sp]; bv_omega
  have destEq : base + 88 = sp fr + 8 := by dsimp only [base,sp]; bv_omega
  obtain ⟨c,p,call,copy,ret,word,csp,csrc,cdst,cshift,keepC⟩ :=
    enterShift area (rspEq.symm ▸ congrArg (Value.get 64) parsed.spEq)
      (destEq.symm ▸ parsed.dst) parsed.shift (sourceEq.symm ▸ parsed.words)
  have area' : Writable Extracted.programImage p base 216 :=
    (area.of_frame copy).sub (Nat.le_refl _) (by omega)
  obtain ⟨d,q,entry,save,slots,dsp,keepD⟩ := saveRegisters area' csp cshift
  have enter : Reaches .l1065b0 c p .l1065ca d q := by
    apply Semantics.Reaches.single
    change (program.runBlock _ _).next _ [] = _
    rw [entry]
    rfl
  have area'' := area'.of_frame save
  have lim := area''.readable.low
  have sourceRead : Readable q (base+232) 32 :=
    ((area.of_frame copy).of_frame save).readable.sub (by dsimp only [base]; decode_addr)
      (by dsimp only [base]; decode_addr)
  have off (k : BitVec 64) (hk : k.toNat ≤ 264) :
      (base+k).toNat = base.toNat+k.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have preserveSource : Outside [⟨(base+24).toNat,48⟩] (base+232) 32 := by
    simp only [Outside,List.mem_singleton,forall_eq,off 24 (by decide),off 232 (by decide),BitVec.reduceToNat]
    omega
  have limbs := word.of_frame save (by decide) preserveSource
  obtain ⟨e,r,maskPath,masks,esp,edst,keepE,maskWrites⟩ :=
    computeMasksFrom (area''.sub (Nat.le_refl _) (by omega)) sourceRead
      (RangeApart.of_offsets (x := base) rfl rfl (by decide)) limbs dsp
      ((keepD 6 (by decide)).trans csrc) ((keepD 7 (by decide)).trans cdst)
      ((keepD 2 (by decide)).trans cshift)
  have saved : Saved base b q 0x100c8a := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · exact (slots 0).trans (congrArg (Value.get 64) (keepC 3 (by decide)))
    · exact (slots 1).trans (congrArg (Value.get 64) (keepC 12 (by decide)))
    · exact (slots 2).trans (congrArg (Value.get 64) (keepC 13 (by decide)))
    · exact (slots 3).trans (congrArg (Value.get 64) (keepC 14 (by decide)))
    · exact (slots 4).trans (congrArg (Value.get 64) (keepC 15 (by decide)))
    · exact (slots 5).trans (congrArg (Value.get 64) (keepC 5 (by decide)))
    · apply (save.memLoad_eq ?_).trans ret
      simp only [Outside,List.mem_singleton,forall_eq,off 24 (by decide),off 72 (by decide),
        BitVec.reduceToNat,Nat.reduceDiv]
      omega
  obtain ⟨out,run,tag,shiftWrites,result,rsp,regs,keepOut,widths⟩ :=
    finishFrom (area''.of_frame maskWrites) esp masks edst (saved.of_scratch lim maskWrites)
  have shifted := Verify.reachesOfCall call (Program.Exec.of_sem ((enter.trans maskPath).exec run.sem)) tag
  have allWrites : RamWriteFrame m out.store (decodeWrites (sp fr)) := by
    refine (((parsedWrites.trans copy ?_).trans save ?_).trans maskWrites ?_).trans shiftWrites ?_
    · intro rgn h
      simp only [shiftSetupWrites,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl
      · refine ⟨⟨(sp fr-216).toNat,216⟩, by simp only [decodeWrites,List.mem_cons,true_or],?_,?_⟩ <;>
          dsimp only [base] <;> decode_addr
      · have eq : base+232 = sp fr+152 := by dsimp only [base,sp]; bv_omega
        rw [eq]
        exact ⟨⟨(sp fr+152).toNat,32⟩, by simp only [decodeWrites,List.mem_cons,or_true,true_or],Nat.le_refl _,Nat.le_refl _⟩
    · intro rgn h
      rcases List.mem_singleton.mp h with rfl
      refine ⟨⟨(sp fr-216).toNat,216⟩, by simp only [decodeWrites,List.mem_cons,true_or],?_,?_⟩ <;>
        dsimp only [base] <;> decode_addr
    · intro rgn h
      rcases List.mem_singleton.mp h with rfl
      refine ⟨⟨(sp fr-216).toNat,216⟩, by simp only [decodeWrites,List.mem_cons,true_or],?_,?_⟩ <;>
        dsimp only [base] <;> decode_addr
    · intro rgn h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl
      · refine ⟨⟨(sp fr-216).toNat,216⟩,by simp only [decodeWrites,List.mem_cons,true_or],?_,?_⟩ <;>
          dsimp only [base] <;> decode_addr
      · simp only [destEq]
        exact ⟨⟨(sp fr+8).toNat,32⟩,by simp only [decodeWrites,List.mem_cons,or_true,true_or],Nat.le_refl _,Nat.le_refl _⟩
  have regEq (i : Fin Reg.count) (h : i.val ∈ [22,39,50,51]) : out.values[i] = a[i] :=
    (keepOut i h).trans ((keepE i h).trans ((keepD i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega)).trans
      ((keepC i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega)).trans (parsedFlags i h))))
  have outWidths (i : Fin Reg.count) (h : i.val ∈ Activation.entryNumbers) : out.values[i].width = 64 := by
    have cases : i.val = 4 ∨ i.val ∈ Activation.argumentNumbers ∨ i.val ∈ [3,5,12,13,14,15] := by
      simp only [Activation.entryNumbers,Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      omega
    rcases cases with same|arg|saved
    · rw [show i = 4 from Fin.ext same]
      exact congrArg Value.width rsp
    · exact widths i arg
    · exact congrArg Value.width (regs i saved)
  have fr' := updated.toFrame.afterCall env allWrites (by
      intro r hr
      refine ⟨fr.region,by simp only [regions,List.mem_cons,true_or],?_,?_⟩ <;>
        simp only [decodeWrites,List.mem_cons,List.not_mem_nil,or_false] at hr <;>
        rcases hr with rfl|rfl|rfl|rfl|rfl <;> simp only [Activation.region,env.low] <;> decode_addr)
    (by
      intro k w slot
      apply allWrites.memLoad_eq
      have outside {k : BitVec 64} {n : Nat} (hk : k.toNat ≤ 192)
          (slots : (n = 8 ∧ k.toNat ∈ [0,8,16,24,32,40,48,88,96,168,184,192]) ∨
            (n = 4 ∧ k.toNat = 176)) : Outside (decodeWrites (sp fr)) (fr.rsp-k) n := by
        have nat := env.subNat k (by omega)
        refine ⟨by rw [nat]; rcases slots with ⟨rfl,_⟩|⟨rfl,_⟩ <;> omega,fun r hr => ?_⟩
        rw [nat]
        simp only [decodeWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at slots
        rcases hr with rfl|rfl|rfl|rfl|rfl <;> decode_addr
      rcases slot with ⟨rfl,h⟩|⟨rfl,rfl⟩
      · have bound : ∀ i ∈ ([0,8,16,24,32,40,48,88,96,168,184,192] : List Nat), i ≤ 192 := by decide
        exact outside (bound _ h) (Or.inl ⟨rfl,h⟩)
      · exact outside (by decide) (Or.inr ⟨rfl,rfl⟩))
    (rspEq ▸ rsp) regEq outWidths
  have after := stateAfter allWrites (decodeOutside env (fr.rdi+8) 64
    (by rw [env.gen]; decode_addr) (Or.inr (by rw [env.gen]; decode_addr))) updated.stateAt
  have restored (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15])
      (v : BitVec 64) (h : b[i] = ⟨64,v⟩) : out.values[i] = ⟨64,v⟩ := by
    apply (regs i hi).trans
    apply congrArg (Value.mk 64)
    simpa only [Value.get_mk_setWidth, BitVec.setWidth_eq] using congrArg (Value.get 64) h
  exact ⟨_,_,parse.trans shifted,⟨fr',after,destEq ▸ result,
    restored 12 (by decide) _ parsed.dst, restored 13 (by decide) _ parsed.len,
    restored 15 (by decide) _ parsed.order⟩⟩

end K256.Proofs.Signing.Nonce.Fill