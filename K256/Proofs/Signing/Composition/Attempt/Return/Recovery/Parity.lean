import K256.Proofs.Signing.Composition.Attempt.Call
import K256.Proofs.Signing.Composition.Attempt.Return.Recovery.State
import K256.Proofs.Signing.Composition.Attempt.Return.Recovery.Memory
import K256.Proofs.Signing.Transfer.Verify
import K256.Proofs.Generate.Generator.Affine.NormalizeCall
import K256.Proofs.Sec1.Serialize.Choice
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Signing.LIR.Generated.Values
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Composition.Attempt.Return.Recovery

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

private abbrev Word := BitVec 64

private def Preserved (a b : Registers) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]

private theorem outerBlock {a : Registers} {m : Ram} {p : Word}
    (rsp : a[4].get 64 = p) (rbx : a[3].get 64 = p+256)
    (push : StoreOk Extracted.programImage m (p-8) 8 0x105ded 5) :
    ∃ b, LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105dea,a,m⟩ =
      .call ⟨.l1203b0,b,memStore m (p-8) (0x105df2 : Word)⟩ (resume .l105df2 0x105df2) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[7] = ⟨64,p+256⟩ ∧ Preserved a b := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp,rbx,push]
    rfl
  refine ⟨rfl,rfl,?_⟩
  intro ⟨i,_⟩ h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

open Verify.LIR in
private theorem normalizeBlock {a : Registers} {m : Ram} {p : Word}
    (rsp : a[4].get 64 = p-8) (rdi : a[7].get 64 = p+256)
    (push : StoreOk Extracted.programImage m (p-56) 8 0x1203bb 5) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l1203b0,a,m⟩ =
      .call ⟨.l114930,b,memStore m (p-56) (0x1203c0 : Word)⟩ (Verify.resumeAt .l1203c0 0x1203c0) ∧
      b[4] = ⟨64,p-56⟩ ∧ b[6] = ⟨64,p+296⟩ ∧ b[7] = ⟨64,p-48⟩ ∧ Preserved a b := by
  have offset48 : p-8-40 = p-48 := by bv_omega
  have offset56 : p-48-8 = p-56 := by bv_omega
  have offset296 : p+256+40 = p+296 := by bv_omega
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp,rdi,offset48,offset56,offset296,push]
    rfl
  refine ⟨rfl,rfl,rfl,?_⟩
  intro ⟨i,_⟩ h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

open Verify.LIR in
private theorem parityChoiceBlock {a : Registers} {m : Ram} {p : Word}
    (rsp : a[4].get 64 = p-48)
    (read : LoadOk m (p-48) 1)
    (push : StoreOk Extracted.programImage m (p-56) 8 0x1203c9 5) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l1203c0,a,m⟩ =
      .call ⟨.l127d50,b,memStore m (p-56) (0x1203ce : Word)⟩ (Verify.resumeAt .l1203ce 0x1203ce) ∧
      b[4] = ⟨64,p-56⟩ ∧ b[7].width = 64 ∧ Preserved a b ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,6,8,9] → b[i] = a[i]) := by
  have offset56 : p-48-8 = p-56 := by bv_omega
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp,read,offset56,push]
    rfl
  refine ⟨rfl,rfl,?_,?_⟩
  · intro ⟨i,_⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · intro ⟨i,_⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl <;> rfl

open Verify.LIR in
private theorem parityReturnBlock {a : Registers} {m : Ram} {p : Word}
    (rsp : a[4].get 64 = p-48) (slot : LoadOk m (p-8) 8)
    (tag : memLoad m (p-8) 64 = 0x105df2) :
    ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l1203ce,a,m⟩ = .returned out ∧
      out.tag = some ⟨64,0x105df2⟩ ∧ out.values[4] = ⟨64,p⟩ ∧ out.store = m ∧
      Preserved a out.values ∧
      (∀ i : Fin Reg.count, i.val ∈ Activation.argumentNumbers → out.values[i] = a[i]) := by
  have offset8 : p-48+40 = p-8 := by bv_omega
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp,offset8,slot,tag]
    rfl
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro ⟨i,_⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · intro ⟨i,_⟩ h
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private def normalizeTarget : Generate.LIR.Label → Option Verify.LIR.Label
  | .l114930 => some .l114930
  | .l127d50 => some .l127d50
  | .l114a10 => some .l114a10
  | _ => none

private theorem normalizeBlocks (src : Generate.LIR.Label) (dst : Verify.LIR.Label)
    (h : normalizeTarget src = some dst) :
    Generate.Serialize.Relabel.block normalizeTarget (Generate.LIR.program.blocks src) =
      Generate.Serialize.Relabel.block some (Verify.LIR.program.blocks dst) := by
  unfold normalizeTarget at h
  split at h <;> cases h <;> with_unfolding_all rfl

open Verify.LIR in
private def NormalizingCall : CFG.Transfer Value Ram Label signature Reg.count → Prop
  | .call location frame => location.label = .l127d50 ∧ frame.target = .l114a10
  | .stuck => True
  | _ => False

open Verify.LIR in
private def ReturnedWidths : CFG.Transfer Value Ram Label signature Reg.count → Prop
  | .returned out => ParseSignature.ArgumentWidths out.values
  | .stuck => True
  | _ => False

open Verify.LIR in
private def ReturnsOrStuck : CFG.Transfer Value Ram Label signature Reg.count → Prop
  | .returned _ | .stuck => True
  | _ => False

private theorem whenGuarded {T : Type} {stuck value : T} {test : Prop} [Decidable test]
    {P : T → Prop} (onStuck : P stuck) (onValue : P value) :
    P (if test then value else stuck) := by
  split <;> assumption

open Verify.LIR in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem normalizeCallsChoice {code : CodeMap} (a : Registers) (m : Ram) :
    NormalizingCall (program.runBlock (dialect code) ⟨.l114930,a,m⟩) := by
  cfg_eval [b_l114930_1,b_l114930_2]
  repeat' apply whenGuarded (show NormalizingCall .stuck from trivial)
  exact ⟨rfl,rfl⟩

open Verify.LIR in
private theorem choiceReturns {code : CodeMap} (a : Registers) (m : Ram) :
    ReturnsOrStuck (program.runBlock (dialect code) ⟨.l127d50,a,m⟩) := by
  cfg_eval
  repeat' apply whenGuarded (show ReturnsOrStuck .stuck from trivial)
  trivial

open Verify.LIR in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem normalizeReturnWidths {code : CodeMap} (a : Registers) (m : Ram) :
    ReturnedWidths (program.runBlock (dialect code) ⟨.l114a10,a,m⟩) := by
  cfg_eval [b_l114a10_1,b_l114a10_2]
  repeat' apply whenGuarded (show ReturnedWidths .stuck from trivial)
  intro ⟨i,_⟩ h
  simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

open Verify.LIR in
private theorem normalizeWidths {code : CodeMap} {a : Registers} {m : Ram}
    {out : Output Value Ram Reg.count}
    (run : program.Exec (dialect code) ⟨⟨.l114930,a,m⟩,[]⟩ out) :
    ParseSignature.ArgumentWidths out.values := by
  have isCall := normalizeCallsChoice (code := code) a m
  generalize hr : program.runBlock (dialect code) ⟨.l114930,a,m⟩ = transfer at isCall
  cases transfer with
  | call child frame =>
      obtain ⟨childLabel,retLabel⟩ := isCall
      rcases child with ⟨label,args,store⟩
      cases childLabel
      cases run with
      | done h => simp only [Program.step,hr,CFG.Transfer.next,reduceCtorEq] at h
      | next h tail =>
          simp only [Program.step,hr,CFG.Transfer.next,Outcome.next.injEq] at h
          subst h
          have isReturn := choiceReturns (code := code) args store
          generalize hc : program.runBlock (dialect code) ⟨.l127d50,args,store⟩ = choice at isReturn
          cases choice with
          | returned middle =>
              cases tail with
              | done h =>
                  simp only [Program.step,hc,CFG.Transfer.next] at h
                  split at h <;> cases h
              | next h finish =>
                  simp only [Program.step,hc,CFG.Transfer.next] at h
                  split at h
                  · injection h with eq
                    subst eq
                    have shape := normalizeReturnWidths (code := code)
                      (frame.resume middle).arguments middle.store
                    have loc : frame.resume middle =
                        ⟨.l114a10,(frame.resume middle).arguments,middle.store⟩ := by
                      cases frame
                      cases retLabel
                      rfl
                    rw [loc] at finish
                    generalize hf : program.runBlock (dialect code)
                       ⟨.l114a10,(frame.resume middle).arguments,middle.store⟩ = last at shape
                    cases finish with
                    | done h =>
                        cases last <;> simp only [Program.step,hf,CFG.Transfer.next,
                          Outcome.done.injEq,reduceCtorEq] at h
                        subst h
                        exact shape
                    | next h _ =>
                        cases last <;> first | exact False.elim shape |
                          simp only [Program.step,hf,CFG.Transfer.next,reduceCtorEq] at h
                  · cases h
          | stuck =>
              cases tail <;> simp only [Program.step,hc,CFG.Transfer.next,reduceCtorEq] at *
          | call | jump => exact False.elim isReturn
  | returned | jump => exact False.elim isCall
  | stuck =>
      cases run <;> simp only [Program.step,hr,CFG.Transfer.next,reduceCtorEq] at *

private def parityScratch (p : Word) (bytes : Nat) : List MemoryRegion := [⟨(p-169).toNat,bytes⟩]

private theorem scratchWithin {p : Word} {bytes : Nat} {regions : List MemoryRegion}
    (bounds : ∀ t ∈ regions, (p-169).toNat ≤ t.start ∧ t.start+t.size ≤ (p-169).toNat+bytes) :
    RegionsWithin regions (parityScratch p bytes) :=
  fun t ht => ⟨_,List.mem_singleton_self _,bounds t ht⟩

theorem parity {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {r sigS : Nat}
    (input : Staged s d r sigS a m) (rbx : a[3] = ⟨64,sp s+256⟩) :
    ∃ b n, Reach (core .l105dea a m) (core .l105df2 b n) ∧ Staged s d r sigS b n := by
  let p := sp s
  obtain ⟨room,high,base⟩ := stackBounds call
  have natAt (i : Nat) (hi : i ≤ 169) :
      (p-BitVec.ofNat 64 i).toNat = p.toNat-i := belowNat call (by omega)
  have n8 : (p-8).toNat = p.toNat-8 := natAt 8 (by decide)
  have n48 : (p-48).toNat = p.toNat-48 := natAt 48 (by decide)
  have n56 : (p-56).toNat = p.toNat-56 := natAt 56 (by decide)
  have n57 : (p-56-1).toNat = p.toNat-57 := by rw [BitVec.sub_sub]; exact natAt 57 (by decide)
  have n169 : (p-169).toNat = p.toNat-169 := natAt 169 (by decide)
  have srcNat : (p+296).toNat = p.toNat+296 := offsetNat call (by decide)
  have aligned : (stackPtr s).toNat % 16 = 8 := call.stackAvailable.2.2.2
  change p.toNat = (stackPtr s).toNat - 1288 at base
  have pAlign : p.toNat % 16 = 0 := by omega
  have depth : 169 ≤ p.toNat := by omega
  have low : p.toNat + 336 < 2^32 := by omega
  have win (q : Word) (n : Nat) (inside : (q+9904).toNat+n ≤ 11200) :
      Writable Extracted.programImage m (p+q) n := stackWindow call input.toMemory inside
  have entrySlot : Writable Extracted.programImage m (p-8) 8 := by
    rw [addr_sub]; exact win _ _ (by decide)
  have innerSlot : Writable Extracted.programImage m (p-56) 8 := by
    rw [addr_sub]; exact win _ _ (by decide)
  have store₁ : StoreOk Extracted.programImage m (p-8) 8 0x105ded 5 :=
    ParseSignature.storeOk_of_codeRange (off := 3) entrySlot
      (fun x hx => Common.fnCode_subset_programImage x (LIR.code_l105dea x hx)) (by decide)
  obtain ⟨b,outer,bsp,bdi,bkeep⟩ := outerBlock (p := p)
    (congrArg (Value.get 64) input.rsp) (congrArg (Value.get 64) rbx) store₁
  let m₁ := memStore m (p-8) (0x105df2 : Word)
  have store₂ : StoreOk Extracted.programImage m₁ (p-56) 8 0x1203bb 5 :=
    ParseSignature.storeOk_of_codeRange (off := 11) (innerSlot.memStore _ _)
      (fun x hx => Common.fnCode_subset_programImage x (Verify.LIR.code_l1203b0 x hx)) (by decide)
  obtain ⟨c,setup,csp,csi,cdi,ckeep⟩ := normalizeBlock (p := p)
    (congrArg (Value.get 64) bsp) (congrArg (Value.get 64) bdi) store₂
  let m₂ := memStore m₁ (p-56) (0x1203c0 : Word)
  have outerFrame : RamWriteFrame m m₁ (parityScratch p 169) := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_,List.mem_singleton_self _,?_⟩
    change (p-169).toNat ≤ (p-8).toNat ∧ (p-8).toNat+8 ≤ (p-169).toNat+169 ∧ _
    rw [n8,n169]
    omega
  have innerIn : InRegions (parityScratch p 161) (p-56) 8 := by
    refine ⟨_,List.mem_singleton_self _,?_⟩
    change (p-169).toNat ≤ (p-56).toNat ∧ (p-56).toNat+8 ≤ (p-169).toNat+161 ∧ _
    rw [n56,n169]
    omega
  have pushes : RamWriteFrame m₁ m₂ (parityScratch p 161) :=
    (RamWriteFrame.refl m₁ _).memStore (0x1203c0 : Word) innerIn
  have innerWithin : RegionsWithin (parityScratch p 161) (parityScratch p 169) := by
    apply scratchWithin
    intro t ht
    obtain rfl := List.mem_singleton.mp ht
    exact ⟨Nat.le_refl _,by change (p-169).toNat+161 ≤ (p-169).toNat+169; omega⟩
  have afterPushes := outerFrame.trans pushes innerWithin
  have cSaved (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) :
      c[i] = ⟨64,c[i].get 64⟩ := by
    have h : i.val ∈ [3,5,12,13,14,15,22,39,50,51] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega
    apply value_eq
    rw [ckeep i h,bkeep i h]
    exact input.saved i hi
  have childWin : Writable Extracted.programImage m₂ (p-56-113) 121 := by
    rw [BitVec.sub_sub,show p-(56+113) = p+(0-169) by bv_omega]
    exact (win _ _ (by decide)).of_frame afterPushes
  have childDest : Writable Extracted.programImage m₂ (p-48) 40 := by
    rw [addr_sub]; exact (win _ _ (by decide)).of_frame afterPushes
  have childSource : Readable m₂ (p+296) 40 := ((win _ _ (by decide)).of_frame afterPushes).readable
  let limbs : Common.Field.Limbs := Vector.ofFn fun i : Fin 5 => memLoad m₂ (wordAddr (p+296) 64 i.val) 64
  have limbWords : WordsAt m₂ (p+296) 64 limbs := by
    intro i hi
    simp only [limbs,Vector.getElem_ofFn]
  have cRet : memLoad m₂ (p-56) 64 = 0x1203c0 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  obtain ⟨norm,genRun,nTag,nsp,nkeep,nwrites,_⟩ := Generate.Generator.Affine.normalizeCall (sp := p-56) (src := p+296) (dst := p-48)
    csp csi cdi ((ckeep 22 (by decide)).trans ((bkeep 22 (by decide)).trans input.df))
    cSaved childWin childSource childDest (by rw [n56,srcNat]; omega) (by rw [n56,n48]; omega)
    (Or.inl (by rw [n48,srcNat]; omega)) (by rw [n48]; omega)
    (by rw [n56]; omega) (by rw [n56]; omega) cRet (by decide) limbWords
  have normRun : Verify.LIR.program.Exec (dialect Extracted.programImage)
      ⟨⟨.l114930,c,m₂⟩,[]⟩ norm :=
    Generate.Serialize.Relabel.exec normalizeBlocks genRun rfl
  have normWidths := normalizeWidths normRun
  have normFrame := pushes.trans nwrites (scratchWithin (p := p) (by
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    · change _ ≤ (p-56-113).toNat ∧ (p-56-113).toNat+113 ≤ _
      rw [show p-56-113 = p-169 by bv_omega]
      omega
    · change _ ≤ (p-48).toNat ∧ (p-48).toNat+40 ≤ _
      rw [n48,n169]
      omega))
  have nsp' : norm.values[4].get 64 = p-48 := by
    rw [nsp]; change p-56+8 = p-48; bv_omega
  have dstRead : LoadOk norm.store (p-48) 1 := by
    have w := childDest.of_frame nwrites
    exact LoadOk.of_region w.readable (Nat.le_refl _) (by omega)
  have choiceSlot := (innerSlot.memStore (p-8) (0x105df2 : Word)).of_frame normFrame
  have choiceGuard : StoreOk Extracted.programImage norm.store (p-56) 8 0x1203c9 5 :=
    ParseSignature.storeOk_of_codeRange (off := 9) choiceSlot
      (fun x hx => Common.fnCode_subset_programImage x (Verify.LIR.code_l1203c0 x hx)) (by decide)
  obtain ⟨e,choiceCall,esp,edi,ekeep,eArgs⟩ := parityChoiceBlock nsp' dstRead choiceGuard
  let m₃ := memStore norm.store (p-56) (0x1203ce : Word)
  have choiceFrame := normFrame.memStore (0x1203ce : Word) innerIn
  have choiceWork : Writable Extracted.programImage m₃ (p-56-1) 1 := by
    rw [BitVec.sub_sub,show p-(56+1) = p+(0-57) by bv_omega]
    exact ((win _ _ (by decide)).memStore (p-8) (0x105df2 : Word)).of_frame choiceFrame
  have eRet : memLoad m₃ (p-56) 64 = 0x1203ce :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  obtain ⟨choice,choiceBlock,cTag,qsp,_,qwrites,qkeep⟩ := Sec1.Serialize.choiceBlock (sp := p-56)
    (fun x hx => Common.fnCode_subset_programImage x (Sec1.LIR.code_l127d50 x hx))
    (congrArg (Value.get 64) esp) choiceWork ((innerSlot.memStore (p-8) (0x105df2 : Word)).of_frame choiceFrame).readable (eRet ▸ (by decide))
  have secRun : Sec1.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l127d50,e,m₃⟩,[]⟩ choice :=
    .done (by simp only [Program.step,choiceBlock,CFG.Transfer.next])
  have genChoice : Generate.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l127d50,e,m₃⟩,[]⟩ choice :=
    Generate.Serialize.Relabel.exec Generate.Serialize.matches_blocks secRun rfl
  have choiceRun : Verify.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l127d50,e,m₃⟩,[]⟩ choice :=
    Generate.Serialize.Relabel.exec normalizeBlocks
      genChoice rfl
  have qFrame := choiceFrame.trans qwrites (scratchWithin (p := p) (by
    intro t ht
    obtain rfl := List.mem_singleton.mp ht
    change _ ≤ (p-56-1).toNat ∧ (p-56-1).toNat+1 ≤ _
    rw [n57,n169]
    omega))
  have retOutside : Outside (parityScratch p 161) (p-8) 8 := by
    refine ⟨by rw [n8]; omega,?_⟩
    intro t ht
    obtain rfl := List.mem_singleton.mp ht
    right
    change (p-169).toNat+161 ≤ (p-8).toNat
    rw [n169,n8]
    omega
  have retPreserved : memLoad choice.store (p-8) 64 = 0x105df2 :=
    (qFrame.memLoad_eq retOutside).trans (memLoad_memStore_same _ _ _ (by decide) (by decide))
  have frame := outerFrame.trans qFrame innerWithin
  have retRead := (entrySlot.of_frame frame).readable
  have qsp' : choice.values[4].get 64 = p-48 := by
    rw [qsp]; change p-56+8 = p-48; bv_omega
  obtain ⟨out,endBlock,outTag,osp,ostore,okeep,oArgs⟩ :=
    parityReturnBlock qsp' ⟨retRead.low,retRead.present⟩ retPreserved
  have verifyRun : Verify.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l1203b0,b,m₁⟩,[]⟩ out := by
    apply ParseSignature.exec_call setup normRun (by rw [nTag]; rfl)
    apply ParseSignature.exec_call choiceCall choiceRun (by rw [cTag,eRet]; rfl)
    apply Program.Exec.done
    change (Verify.LIR.program.runBlock (dialect Extracted.programImage)
      ⟨.l1203ce,choice.values,choice.store⟩).next (dialect Extracted.programImage) [] = .done out
    rw [endBlock]
    rfl
  have full := callReaches outer (Signing.Transfer.verifyExecAt rfl verifyRun) outTag
  have keep : Preserved a out.values := by
    intro i hi
    exact (okeep i hi).trans ((qkeep i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega)).trans ((ekeep i hi).trans ((nkeep i hi).trans ((ckeep i hi).trans (bkeep i hi)))))
  have args : ParseSignature.ArgumentWidths out.values := by
    intro i hi
    rw [oArgs i hi,qkeep i (by
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega)]
    by_cases isDi : i.val = 7
    · have e : i = 7 := Fin.ext isDi
      exact e ▸ edi
    · rw [eArgs i (by
        simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
        omega)]
      exact normWidths i hi
  have memory := preserveCore call input.toCoreMemory frame (by
    intro t ht
    obtain rfl := List.mem_singleton.mp ht
    change p.toNat-9904 ≤ (p-169).toNat ∧ (p-169).toNat+169 ≤ p.toNat+344
    rw [n169]
    omega)
  have outside (i : Nat) (hi : i ≤ 224) :
      Outside (parityScratch p 169) (p+BitVec.ofNat 64 i) 32 := by
    have offset : (p+BitVec.ofNat 64 i).toNat = p.toNat+i := offsetNat call (by omega)
    rw [Outside,offset]
    refine ⟨by omega,?_⟩
    intro t ht
    obtain rfl := List.mem_singleton.mp ht
    right
    change (p-169).toNat+169 ≤ _
    rw [n169]
    omega
  refine ⟨_,_,full,ostore ▸ memory,osp,(keep 22 (by decide)).trans input.df,?_,args,?_,?_,?_⟩
  · intro i hi
    rw [keep i (by
      simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega)]
    exact input.saved i hi
  · exact ⟨(congrArg Value.width (keep 39 (by decide))).trans input.fp.1,
      (congrArg Value.width (keep 50 (by decide))).trans input.fp.2.1,
      (congrArg Value.width (keep 51 (by decide))).trans input.fp.2.2⟩
  · rw [ostore]
    exact input.first.of_frame frame (by decide) (outside 192 (by decide))
  · rw [ostore]
    exact input.second.of_frame frame (by decide) (outside 224 (by decide))

end K256.Proofs.Signing.Composition.Attempt.Return.Recovery
