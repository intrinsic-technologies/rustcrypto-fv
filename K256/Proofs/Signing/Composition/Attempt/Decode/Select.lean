import K256.Proofs.Signing.Composition.Attempt.Decode.Parser
import K256.Proofs.Signing.Composition.Attempt.Decode.SelectBlocks
import K256.Proofs.Ecdh.LIR.Fn10a220.Frame
import K256.Proofs.Signing.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Composition.Attempt.Decode

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Signing.LIR
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

structure Selected (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (k : Nat)
    (a : Registers) (m : Ram) : Prop
    extends LoopMemory s d msg st m, RegistersAt s a (sp s+456) (sp s+192) (sp s+256) (sp s+160) where
  limbs : WordsAt m (sp s+192) 64 (scalarWords k)
  accepted : a[14].get 8 = 1

set_option maxHeartbeats 1100000 in
set_option maxRecDepth 4096 in
theorem select {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {k : Nat}
    (parsed : Decoded s d msg st k a m) :
    ∃ b n, Reach (core .l10591b a m) (core .l105961 b n) ∧ Selected s d msg st k b n := by
  let args := selectArgs a m (sp s)
  let mem := selectMemory m (sp s)
  let child := activation s mem args 1 0x105961
  let flag := (memLoad m (sp s+40) 32).setWidth 64
  have rsp : a[4].get 64 = sp s := congrArg (Value.get 64) parsed.rsp
  have rbp : a[5].get 64 = sp s+192 := congrArg (Value.get 64) parsed.rbp
  have r12 : a[12].get 64 = sp s+8 := congrArg (Value.get 64) parsed.r12
  have r15 : a[15].get 64 = sp s+160 := congrArg (Value.get 64) parsed.r15
  have win : Writable Extracted.programImage m (sp s-8) 232 := by
    rw [addr_sub]
    exact stackWindow call parsed.toMemory (by decide)
  have path := selectBlock rsp rbp r12 r15 win
  have keep (i : Fin Reg.count) (hi : i.val ∈ preservedRegisters) : args[i] = a[i] := by
    obtain ⟨i,bound⟩ := i
    simp only [preservedRegisters,List.mem_cons,List.not_mem_nil,or_false] at hi
    change args[i] = a[i]
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp (config := {decide := true}) only [args,selectArgs,Vector.getElem_set,↓reduceIte]
  obtain ⟨df,gp,fp⟩ := fixedRegisters parsed.toRegistersAt keep
  have flagBit : flag.setWidth 8 = 1 := by
    dsimp only [flag]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]
    have bit := extractLsb'_memLoad m (sp s+40) (n := 32) 0 8 (by decide) (by decide) (by decide)
    rw [show (sp s+40)+BitVec.ofNat 64 (0/8) = sp s+40 by simp only [Nat.zero_div,BitVec.ofNat_eq_ofNat,BitVec.add_zero]] at bit
    exact bit.trans parsed.accepted
  have widths : ParseSignature.ArgumentWidths args := by
    intro ⟨i,hi⟩ member
    change args[i].width = 64
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp (config := {decide := true}) only [args,selectArgs,Vector.getElem_set,↓reduceIte]
    all_goals first | rfl | exact parsed.widths 8 (by decide) | exact parsed.widths 9 (by decide)
  have prep := (zeroFourFrame (m := m) call (off := 160) (by decide)).memStore (0x105961 : BitVec 64) (returnSlot call)
  have stable := parsed.toLoopMemory.preserve_work call prep
  have slot : memLoad mem (sp s-8) 64 = (0x105961 : BitVec 64) :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have spArg : args[4] = ⟨64,sp s-8⟩ := by
    simp (config := {decide := true}) only [args,selectArgs,Vector.getElem_set,↓reduceIte]
  have diEq : child.rdi = sp s+192 := by
    simp only [child,activation,args,selectArgs,Vector.getElem_set,↓reduceIte,Value.get_mk]
  have siEq : child.rsi = sp s+160 := by
    simp (config := {decide := true}) only [child,activation,args,selectArgs,Vector.getElem_set,↓reduceIte,Value.get_mk]
  have dxEq : child.rdx = sp s+8 := by
    simp (config := {decide := true}) only [child,activation,args,selectArgs,Vector.getElem_set,↓reduceIte,Value.get_mk]
  have c1Eq : child.rcx = flag := by
    simp (config := {decide := true}) only [child,activation,args,selectArgs,flag,Vector.getElem_set,↓reduceIte,Value.get_mk]
  have r14Eq : args[14] = ⟨64,flag⟩ := by
    simp (config := {decide := true}) only [args,selectArgs,flag,Vector.getElem_set,↓reduceIte]
  have entry := childAtoms call stable.toMemory Ecdh.LIR.Fn10a220.frameInfo rfl (by decide) (by decide)
    spArg df (fun i hi => by
      by_cases h : i.val = 14
      · obtain ⟨j,jh⟩ := i
        change j = 14 at h
        subst j
        exact congrArg Value.width r14Eq
      · exact gp i hi h) fp widths slot (by decide)
  have aboveDest : Outside [ParseSignature.callStack child] child.rdi 32 :=
    diEq.symm ▸ occursAboveCall call (depth := 1) (off := 192) (size := 32) (by decide) (by decide)
  have apart : Outside [child.region] child.rdx 32 := by
    obtain ⟨room,high,base⟩ := stackBounds call
    have floor : (sp s-8-1).toNat = (sp s).toNat-9 := by
      rw [show sp s-8-1 = sp s-9 by bv_omega]
      exact belowNat call (by decide)
    have top : (sp s-8).toNat = (sp s).toNat-8 := belowNat call (by decide)
    have src : child.rdx.toNat = (sp s).toNat+8 := dxEq.symm ▸ offsetNat call (offset:=8) (by decide)
    refine ⟨by rw [src]; omega,?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    change (sp s-8-1).toNat + ((sp s-8).toNat-(sp s-8-1).toNat) ≤ _
    rw [floor,top,src]
    omega
  obtain ⟨out,run,tag,done_,written,outWidths,limbs⟩ :=
    Ecdh.Scalar.select_call Common.fnCode_subset_programImage child (c1Eq.symm ▸ flagBit)
      (siEq.symm ▸ (stackWindow call stable.toMemory (offset:=160) (size:=32) (by decide)).readable)
      (dxEq.symm ▸ (stackWindow call stable.toMemory (offset:=8) (size:=32) (by decide)).readable)
      (diEq.symm ▸ stackWindow call stable.toMemory (offset:=192) (size:=32) (by decide)) apart aboveDest args entry
  have code : Signing.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l10a220,args,mem⟩,[]⟩ out :=
    Transfer.verifyExecAt rfl (selectScalarToVerify run)
  have after := callReaches path code tag
  have bound := childWithin (a := args) (m := mem) (ret := 0x105961) (depth := 1) call (by decide)
    (regions := [ParseSignature.buffer child.rdi 32]) (by
      intro r member
      obtain rfl := List.mem_singleton.mp member
      obtain ⟨room,_,base⟩ := stackBounds call
      have low : (sp s-9904).toNat = (sp s).toNat-9904 := belowNat call (by decide)
      have dst : child.rdi.toNat = (sp s).toNat+192 := diEq.symm ▸ offsetNat call (offset:=192) (by decide)
      change (sp s-9904).toNat ≤ child.rdi.toNat ∧ child.rdi.toNat+32 ≤ (sp s).toNat+344
      rw [low,dst]
      omega)
  have stableAfter := stable.preserve_work call ((RamWriteFrame.refl mem _).trans written bound)
  have copied : WordsAt mem (sp s+8) 64 (scalarWords k) := by
    intro i hi
    obtain rfl|rfl|rfl|rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals
      simpa (disch := store_disch) only [mem,selectMemory,zeroFour,wordAddr,Nat.reduceDiv,Nat.reduceMul,
        BitVec.add_zero,reduceAddOffset,memLoad_memStore_of_rangeApart] using parsed.limbs _ hi
  rw [diEq,dxEq] at limbs
  have scalar : WordsAt out.store (sp s+192) 64 (scalarWords k) := by
    intro i hi
    have word : memLoad out.store (wordAddr (sp s+192) 64 i) 64 =
        memLoad mem (wordAddr (sp s+8) 64 i) 64 := by
      simpa only [child,activation,Vector.getElem_ofFn] using limbs i hi
    exact word.trans (copied i hi)
  have regs := afterCall parsed.toRegistersAt keep done_ outWidths
  change Atom.All _ _ _ (Generate.LIR.Fn127d50.doneAt child) at done_
  simp only [Generate.LIR.Fn127d50.doneAt,Atom.All,Atom.Holds] at done_
  obtain ⟨_,_,_,_,_,_,bit,_,_,_,_,_⟩ := done_
  refine ⟨out.values,out.store,after,stableAfter,regs,scalar,?_⟩
  have keptFlag : out.values[14] = ⟨64,flag⟩ :=
    bit.trans (congrArg (fun v => Value.mk 64 (v.get 64)) r14Eq)
  exact (congrArg (Value.get 8) keptFlag).trans flagBit


end K256.Proofs.Signing.Composition.Attempt.Decode
