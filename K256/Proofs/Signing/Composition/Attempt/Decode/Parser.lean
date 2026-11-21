import K256.Proofs.Signing.Composition.Attempt.Call
import K256.Proofs.Signing.Composition.Attempt.Decode.Entry
import K256.Proofs.Signing.Composition.Attempt.Decode.Transfer
import K256.Proofs.Signing.Transfer.Verify
import K256.Proofs.Verify.Core.Affine.Fill
import K256.Proofs.Generate.Generator.Multiply.Split.Addition.Arithmetic

namespace K256.Proofs.Signing.Composition.Attempt.Decode

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate Generate.Generator
open Generate.Generator.Multiply (scalarWords)
open Generate.LIR

structure Decoded (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (k : Nat)
    (a : Registers) (m : Ram) : Prop
    extends LoopMemory s d msg st m, RegistersAt s a (sp s+456) (sp s+192) (sp s+256) (sp s+160) where
  limbs : WordsAt m (sp s+8) 64 (scalarWords k)
  accepted : memLoad m (sp s+40) 8 = 1

private theorem decoderWrites {s : RamState} {secret msg : ByteArray} {m : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) :
    RamWriteFrame m (decoderMemory m (sp s)) (workRegions s) := by
  obtain ⟨room,high,base⟩ := stackBounds call
  have atOffset (i : Nat) (h : i ≤ 1296) := offsetNat call h
  have a424 : (sp s+424).toNat = (sp s).toNat+424 := atOffset 424 (by decide)
  have lower : (sp s-9904).toNat = (sp s).toNat-9904 := belowNat call (by decide)
  have slot : (sp s-8).toNat = (sp s).toNat-8 := belowNat call (by decide)
  have localWrite {i : Nat} (lo : 456 ≤ i) (hi : i+8 ≤ 488) :
      InRegions (workRegions s) (sp s+BitVec.ofNat 64 i) 8 := by
    refine ⟨⟨(sp s+424).toNat,168⟩,by simp only [workRegions,List.mem_cons,true_or,or_true],?_⟩
    change (sp s+424).toNat ≤ (sp s+BitVec.ofNat 64 i).toNat ∧
      (sp s+BitVec.ofNat 64 i).toNat+8 ≤ (sp s+424).toNat+168 ∧ _
    rw [a424,atOffset i (by omega)]
    omega
  have push : InRegions (workRegions s) (sp s-8) 8 := by
    refine ⟨⟨(sp s-9904).toNat,10248⟩,List.mem_cons_self,?_⟩
    change (sp s-9904).toNat ≤ (sp s-8).toNat ∧
      (sp s-8).toNat+8 ≤ (sp s-9904).toNat+10248 ∧ (sp s-8).toNat+8 ≤ 2^64
    rw [lower,slot]
    omega
  exact (((((RamWriteFrame.refl m _).memStore _ (localWrite (i:=480) (by decide) (by decide))).memStore _
    (localWrite (i:=472) (by decide) (by decide))).memStore _ (localWrite (i:=464) (by decide) (by decide))).memStore _
    (localWrite (i:=456) (by decide) (by decide))).memStore _ push

private theorem wordsOfValue (w : Nat → BitVec 64) :
    (Vector.ofFn fun i : Fin 4 => w i.val) =
      scalarWords (Sampling.limbsValue (w 0) (w 1) (w 2) (w 3)) := by
  let q : Common.Invert.LinearCombination.Limbs := ⟨w 0,w 1,w 2,w 3⟩
  calc
    _ = Common.Invert.ModularShift.words q := by
      apply Vector.ext
      intro i hi
      obtain rfl|rfl|rfl|rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      all_goals rfl
    _ = scalarWords q.toNat := Generate.Generator.Multiply.Split.Addition.limbWords_eq q
    _ = _ := by
      apply congrArg scalarWords
      simp only [q,Common.Invert.LinearCombination.Limbs.toNat,Sampling.limbsValue]
      omega

set_option maxHeartbeats 1300000 in
set_option maxRecDepth 4096 in
theorem parse {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {k : Nat}
    (outer : Outer s d msg st a m) (bound : k < domain.n)
    (nonce : (⟨(sp s+384).toNat,32⟩ : MemoryRegion).HasBytes m (Encoding.natToOctets 32 k)) :
    ∃ b n, Reach (core .l1058d0 a m) (core .l10591b b n) ∧ Decoded s d msg st k b n := by
  let args := decoderArgs a m (sp s)
  let mem := decoderMemory m (sp s)
  let child := activation s mem args 65 0x10591b
  have win : Writable Extracted.programImage m (sp s-8) 496 := by
    rw [addr_sub]
    exact stackWindow call outer.toMemory (by decide)
  have rsp : a[4].get 64 = sp s := congrArg (Value.get 64) outer.rsp
  have rbx : a[3].get 64 = sp s+456 := congrArg (Value.get 64) outer.rbx
  have r12 : a[12].get 64 = sp s+8 := congrArg (Value.get 64) outer.r12
  have path := decoderBlock rsp rbx r12 win
  have same (i : Fin Reg.count) (h : i.val ∉ [0,1,4,6,7]) :
      args[i] = a[i] := by
    obtain ⟨i,hi⟩ := i
    change args[i] = a[i]
    change i ∉ [0,1,4,6,7] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    simp (disch := omega) only [args,decoderArgs,Vector.getElem_set,ite_eq_right]
  have keep (i : Fin Reg.count) (h : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :
      args[i] = a[i] := by
    apply same
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    omega
  have widths : ParseSignature.ArgumentWidths args := by
    intro ⟨i,hi⟩ h
    change args[i].width = 64
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp (config := {decide := true}) only [args,decoderArgs,Vector.getElem_set,↓reduceIte]
    all_goals first
      | rfl
      | exact outer.widths 2 (by decide)
      | exact outer.widths 8 (by decide)
      | exact outer.widths 9 (by decide)
  have gp (i : Fin Reg.count) (h : i.val ∈ Activation.calleeSavedNumbers) : args[i].width = 64 := by
    rw [keep i (by simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega)]
    obtain ⟨i,hi⟩ := i
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact congrArg Value.width outer.rbx
      | exact congrArg Value.width outer.rbp
      | exact congrArg Value.width outer.r12
      | exact congrArg Value.width outer.r13
      | exact outer.r14
      | exact congrArg Value.width outer.r15
  have fpre := decoderWrites (m := m) call
  have stable := (loopMemory_of_outer outer).preserve_work call fpre
  have slot : memLoad mem (sp s-8) 64 = (0x10591b : BitVec 64) :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have fp : args[39].width = 32 ∧ args[50].width = 16 ∧ args[51].width = 16 := by
    exact ⟨(congrArg Value.width (keep 39 (by decide))).trans outer.fp.1,
      (congrArg Value.width (keep 50 (by decide))).trans outer.fp.2.1,
      (congrArg Value.width (keep 51 (by decide))).trans outer.fp.2.2⟩
  have rspArgs : args[4] = ⟨64,sp s-8⟩ := by
    simp (config := {decide := true}) only [args,decoderArgs,Vector.getElem_set,↓reduceIte]
  have si : child.rsi = sp s+456 := by
    simp (config := {decide := true}) only [child,activation,args,decoderArgs,Vector.getElem_set,↓reduceIte,Value.get_mk]
  have di : child.rdi = sp s+8 := by
    simp (config := {decide := true}) only [child,activation,args,decoderArgs,Vector.getElem_set,↓reduceIte,Value.get_mk]
  have entry := childAtoms call stable.toMemory Fn109e60.frameInfo rfl (by decide) (by decide)
    rspArgs ((keep 22 (by decide)).trans outer.df) gp fp widths slot (by decide)
  have src : Readable mem child.rsi 32 := by
    rw [si]
    exact (stackWindow call stable.toMemory (offset:=456) (size:=32) (by decide)).readable
  have dst : Writable Extracted.programImage mem child.rdi 33 := by
    rw [di]
    exact stackWindow call stable.toMemory (offset:=8) (by decide)
  obtain ⟨room,high,base⟩ := stackBounds call
  have sourceOutside {off n : Nat} (hin : off+n ≤ 1296) :
      Outside [ParseSignature.callStack child] (sp s+BitVec.ofNat 64 off) n := by
    have l : (sp s-8-65).toNat = (sp s).toNat-73 := by
      rw [show sp s-8-65 = sp s-73 by bv_omega]
      exact belowNat call (by decide)
    have u : (sp s-8).toNat = (sp s).toNat-8 := belowNat call (by decide)
    have p := offsetNat call (offset := off) (by omega)
    refine ⟨by rw [p]; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    change (sp s-8-65).toNat + ((sp s-8).toNat+8 - (sp s-8-65).toNat) ≤ _
    rw [l,u,p]
    omega
  obtain ⟨out,exec,tag,done_,writes,afterWidths,limbs,accepted⟩ :=
    Sample.decodeScalar child src dst (si.symm ▸ sourceOutside (off:=456) (n:=32) (by decide))
      (di.symm ▸ sourceOutside (off:=8) (n:=33) (by decide)) args entry
  have signed : Signing.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l109e60,args,mem⟩,[]⟩ out :=
    Transfer.verifyExecAt rfl (decodeScalarToVerify exec)
  have reached := callReaches path signed tag
  have after : LoopMemory s d msg st out.store := by
    apply stable.preserve_work call
    apply (RamWriteFrame.refl mem (workRegions s)).trans writes
    intro r hr
    refine ⟨⟨(sp s-9904).toNat,10248⟩,List.mem_cons_self,?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    have lower : (sp s-9904).toNat = (sp s).toNat-9904 := belowNat call (by decide)
    have u : (sp s-8).toNat = (sp s).toNat-8 := belowNat call (by decide)
    rcases hr with rfl | rfl
    · have lo : child.low.toNat = (sp s).toNat-73 := by
        change (sp s-8-65).toNat = _
        rw [show sp s-8-65 = sp s-73 by bv_omega]
        exact belowNat call (by decide)
      change (sp s-9904).toNat ≤ child.low.toNat ∧ child.low.toNat +
        ((sp s-8).toNat-child.low.toNat) ≤ (sp s-9904).toNat+10248
      rw [lower,lo,u]
      omega
    · have diNat : child.rdi.toNat = (sp s).toNat+8 := di.symm ▸ offsetNat call (offset:=8) (by decide)
      change (sp s-9904).toNat ≤ child.rdi.toNat ∧ child.rdi.toNat+33 ≤ (sp s-9904).toNat+10248
      rw [lower,diNat]
      omega
  let w := Common.scalarWord m (sp s+384)
  have width : k < 2^256 := Nat.lt_trans bound (by decide +kernel)
  have value : Sampling.limbsValue (w 0) (w 1) (w 2) (w 3) = k :=
    Verify.Core.Affine.scalarValue_of_octets nonce width
  have acceptedFlag : Sampling.orderFlag (w 0) (w 1) (w 2) (w 3) = 1 := by
    rw [Sampling.orderFlag_eq,value,ite_eq_left bound]
  rw [di,si] at limbs
  change WordsAt out.store (sp s+8) 64 (Vector.ofFn fun i : Fin 4 =>
    Common.scalarWord (decoderMemory m (sp s)) (sp s+456) i.val) at limbs
  have inputWords : (Vector.ofFn fun i : Fin 4 =>
      Common.scalarWord (decoderMemory m (sp s)) (sp s+456) i.val) = scalarWords k := by
    rw [← value,← wordsOfValue]
    apply Vector.ext
    intro i hi
    simpa only [Vector.getElem_ofFn] using decoderWord m (sp s) i hi
  rw [inputWords] at limbs
  rw [di,si] at accepted
  change memLoad out.store (sp s+8+32) 8 = (Sampling.orderFlag
    (Common.scalarWord (decoderMemory m (sp s)) (sp s+456) 0)
    (Common.scalarWord (decoderMemory m (sp s)) (sp s+456) 1)
    (Common.scalarWord (decoderMemory m (sp s)) (sp s+456) 2)
    (Common.scalarWord (decoderMemory m (sp s)) (sp s+456) 3)).setWidth 8 at accepted
  rw [decoderWord _ _ 0 (by decide),decoderWord _ _ 1 (by decide),
    decoderWord _ _ 2 (by decide),decoderWord _ _ 3 (by decide),
    show sp s+8+32 = sp s+40 by bv_omega] at accepted
  change memLoad out.store (sp s+40) 8 = (Sampling.orderFlag (w 0) (w 1) (w 2) (w 3)).setWidth 8 at accepted
  rw [acceptedFlag] at accepted
  change Atom.All _ _ _ (Fn109e60.doneAt child) at done_
  simp only [Fn109e60.doneAt,Atom.All,Atom.Holds] at done_
  obtain ⟨rs,df,bx,bp,p12,p13,p14,p15,mx,fw,fc,_⟩ := done_
  refine ⟨out.values,out.store,reached,after,⟨?_,df,?_,?_,?_,?_,?_,?_,afterWidths,?_⟩,limbs,accepted⟩
  · exact rs.trans (congrArg (Value.mk 64) (show sp s-8+8 = sp s by bv_omega))
  · exact bx.trans (congrArg (fun v => Value.mk 64 (v.get 64)) ((keep 3 (by decide)).trans outer.rbx))
  · exact bp.trans (congrArg (fun v => Value.mk 64 (v.get 64)) ((keep 5 (by decide)).trans outer.rbp))
  · exact p12.trans (congrArg (fun v => Value.mk 64 (v.get 64)) ((keep 12 (by decide)).trans outer.r12))
  · exact p13.trans (congrArg (fun v => Value.mk 64 (v.get 64)) ((keep 13 (by decide)).trans outer.r13))
  · exact congrArg Value.width p14
  · exact p15.trans (congrArg (fun v => Value.mk 64 (v.get 64)) ((keep 15 (by decide)).trans outer.r15))
  · exact ⟨congrArg Value.width mx,congrArg Value.width fw,congrArg Value.width fc⟩

end K256.Proofs.Signing.Composition.Attempt.Decode
