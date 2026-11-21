import K256.Proofs.Signing.Composition.Attempt.Decode.CompareBlocks
import K256.Proofs.Signing.Composition.Attempt.Decode.Select
import K256.Proofs.Verify.Core.Signature.Nonzero

namespace K256.Proofs.Signing.Composition.Attempt.Decode

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Sample (blackBox_call)

private theorem compareOperands {s : RamState} {secret msg : ByteArray} {m : Ram} {a : Registers}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (ptr : BitVec 64)
    (addr : ptr = sp s+192 ∨ ptr = sp s+256) :
    Outside [(activation s m a 16 0x10599c).region] ptr 32 := by
  obtain ⟨room,high,base⟩ := stackBounds call
  have floor : (sp s-8-16).toNat = (sp s).toNat-24 := by
    rw [show sp s-8-16 = sp s-24 by bv_omega]
    exact belowNat call (by decide)
  have top : (sp s-8).toNat = (sp s).toNat-8 := belowNat call (by decide)
  have ptrNat : ptr.toNat = (sp s).toNat+192 ∨ ptr.toNat = (sp s).toNat+256 := by
    rcases addr with rfl | rfl
    · exact .inl (offsetNat call (by decide))
    · exact .inr (offsetNat call (by decide))
  refine ⟨by rcases ptrNat with h|h <;> omega,?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  right
  change (sp s-8-16).toNat + ((sp s-8).toNat-(sp s-8-16).toNat) ≤ _
  rw [floor,top]
  rcases ptrNat with h|h <;> omega

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
theorem compare {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {k : Nat}
    (selected : Selected s d msg st k a m) (pos : 0 < k) (bound : k < domain.n) :
    ∃ b n, Reach (core .l105961 a m) (core .l10599c b n) ∧ Selected s d msg st k b n ∧ b[0].get 8 = 0 := by
  let args := compareArgs a (sp s)
  let mem := compareMemory m (sp s)
  let child := activation s mem args 16 0x10599c
  have spEq : a[4].get 64 = sp s := congrArg (Value.get 64) selected.rsp
  have bpEq : a[5].get 64 = sp s+192 := congrArg (Value.get 64) selected.rbp
  have p13Eq : a[13].get 64 = sp s+256 := congrArg (Value.get 64) selected.r13
  have win : Writable Extracted.programImage m (sp s-8) 296 := by
    rw [addr_sub]
    exact stackWindow call selected.toMemory (by decide)
  have path := compareBlock spEq bpEq p13Eq win
  have keep (i : Fin Reg.count) (hi : i.val ∈ preservedRegisters) : args[i] = a[i] := by
    obtain ⟨i,iDom⟩ := i
    simp only [preservedRegisters,List.mem_cons,List.not_mem_nil,or_false] at hi
    change args[i] = a[i]
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp (config := {decide := true}) only [args,compareArgs,Vector.getElem_set,↓reduceIte]
  obtain ⟨df,gp,fp⟩ := fixedRegisters selected.toRegistersAt keep
  have widths : ParseSignature.ArgumentWidths args := by
    intro ⟨i,hi⟩ member
    change args[i].width = 64
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp (config := {decide := true}) only [args,compareArgs,Vector.getElem_set,↓reduceIte]
    all_goals first | rfl | exact selected.widths 1 (by decide) | exact selected.widths 2 (by decide)
                    | exact selected.widths 8 (by decide) | exact selected.widths 9 (by decide)
  have prep := (zeroFourFrame (m := m) call (off := 256) (by decide)).memStore (0x10599c : BitVec 64) (returnSlot call)
  have stable := selected.toLoopMemory.preserve_work call prep
  have slot : memLoad mem (sp s-8) 64 = (0x10599c : BitVec 64) :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have spArg : args[4] = ⟨64,sp s-8⟩ := by
    simp (config := {decide := true}) only [args,compareArgs,Vector.getElem_set,↓reduceIte]
  have di : child.rdi = sp s+192 := by
    simp only [child,activation,args,compareArgs,Vector.getElem_set,↓reduceIte,Value.get_mk]
  have si : child.rsi = sp s+256 := by
    simp (config := {decide := true}) only [child,activation,args,compareArgs,Vector.getElem_set,↓reduceIte,Value.get_mk]
  have r14Arg : args[14] = a[14] := by
    simp (config := {decide := true}) only [args,compareArgs,Vector.getElem_set,↓reduceIte]
  have entry := childAtoms call stable.toMemory Generate.LIR.Fn10a280.frameInfo rfl (by decide) (by decide)
    spArg df (fun i hi => by
      by_cases h : i.val = 14
      · obtain ⟨j,jh⟩ := i
        change j = 14 at h
        subst j
        exact (congrArg Value.width r14Arg).trans selected.r14
      · exact gp i hi h) fp widths slot (by decide)
  have src : WordsAt mem (sp s+192) 64 (scalarWords k) := by
    intro i hi
    obtain rfl|rfl|rfl|rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals
      simpa (disch := store_disch) only [mem,compareMemory,zeroFour,wordAddr,Nat.reduceDiv,Nat.reduceMul,
        BitVec.add_zero,reduceAddOffset,memLoad_memStore_of_rangeApart] using selected.limbs _ hi
  have zero : WordsAt mem (sp s+256) 64 (Vector.replicate 4 0) := by
    intro i hi
    obtain rfl|rfl|rfl|rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals
      simpa (disch := store_disch) only [mem,compareMemory,wordAddr,Nat.reduceDiv,Nat.reduceMul,
        BitVec.add_zero,reduceAddOffset,memLoad_memStore_of_rangeApart] using (zeroFourWords (m := m) (dest := sp s+256)) _ hi
  obtain ⟨out,run,tag,done_,written,outWidths,bit⟩ :=
    Verify.Core.compareNonzero (fr := child) entry
      (di.symm ▸ (stackWindow call stable.toMemory (offset:=192) (size:=32) (by decide)).readable)
      (si.symm ▸ (stackWindow call stable.toMemory (offset:=256) (size:=32) (by decide)).readable)
      (compareOperands call _ (.inl di)) (compareOperands call _ (.inr si)) (di.symm ▸ src) (si.symm ▸ zero) pos
      (Nat.lt_trans bound (by decide +kernel))
  have code : Signing.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l10a280,args,mem⟩,[]⟩ out :=
    Transfer.verifyExecAt rfl run
  have after := callReaches path code tag
  have within := childWithin (a := args) (m := mem) (ret := 0x10599c) (depth := 16) call (by decide)
    (regions := []) (by simp only [List.not_mem_nil,false_implies,implies_true])
  have stableAfter := stable.preserve_work call ((RamWriteFrame.refl mem _).trans written within)
  have scalar := WordsAt.of_frame src written (by decide) (compareOperands call _ (.inl rfl))
  have regs := afterCall selected.toRegistersAt keep done_ outWidths
  change Atom.All _ _ _ (Generate.LIR.Fn127d50.doneAt child) at done_
  simp only [Generate.LIR.Fn127d50.doneAt,Atom.All,Atom.Holds] at done_
  obtain ⟨_,_,_,_,_,_,r14,_,_,_,_,_⟩ := done_
  refine ⟨out.values,out.store,after,⟨stableAfter,regs,scalar,?_⟩,bit⟩
  have preserved := r14.trans ((value_eq ((congrArg Value.width r14Arg).trans selected.r14)).symm.trans r14Arg)
  exact (congrArg (Value.get 8) preserved).trans selected.accepted

end K256.Proofs.Signing.Composition.Attempt.Decode
