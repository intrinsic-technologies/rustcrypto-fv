import K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator.Initialize
import K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator.Calls

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

macro "acc_call_bounds" " using " e:term : tactic =>
  `(tactic| (dsimp only [callWrites,tableOffset,tableSource,↓reduceIte,Bool.false_eq_true]; acc_bounds using $e))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem copyTables {fr : Activation} {a initial : Registers} {m : Ram} {d : Nat}
    (entry : CoreEntry fr initial d) (s : DigitsReady fr a m d) :
    ∃ b n, Reaches .l11d620 a m .l11d6d3 b n ∧ State .l11d6d3 fr b n ∧
      TableAt n (sp fr + 0x850) (firstBase d) ∧ TableAt n (sp fr + 0x490) (secondBase d) ∧
      identity.Stored n (sp fr + 0x128) ∧ memLoad n (sp fr + 0x38) 64 = 66 ∧
      RamWriteFrame m n (writes fr) ∧ b[5].get 64 = 0 ∧ b[12].get 64 = sp fr + 0x1d0 ∧
      b[14].get 64 = sp fr + 0x850 ∧ b[15].get 64 = sp fr + 0x490 := by
  let q := sp fr
  let n := setupMemory m q
  obtain ⟨rsp,df,stack⟩ := currentStack s.toState rfl
  have image := entry.loaded_of_frame s.frame
  obtain ⟨b,path,args,saved,b5,b12,b13,b15,keep⟩ := initializeAccumulator (congrArg (Value.get 64) rsp)
    (congrArg (Value.get 1) df) (stack.sub (by acc_bounds using entry) (by acc_bounds using entry) :
      Writable Extracted.programImage m (sp fr) 3256) image s.widths s.savedWidths
    (s.locals (0x100,1) (by simp)) (s.locals (0x1a0,1) (by simp)) (s.locals (0x1c0,fr.rcx) (by simp)) s.digitCount
  have localFrame : RamWriteFrame m n (writes fr) := by
    dsimp only [n,q,setupMemory,memCopy]
    apply RamWriteFrame.memStore
    · apply RamWriteFrame.memStore
      · apply (RamWriteFrame.refl _ _).memStore
        exact ⟨⟨(sp fr + 296).toNat,120⟩,by simp [writes],by acc_bounds using entry⟩
      · exact ⟨⟨(sp fr + 8).toNat,8⟩,by simp [writes],by acc_bounds using entry⟩
    · exact ⟨⟨(sp fr + 56).toNat,8⟩,by simp [writes],by acc_bounds using entry⟩
  have st : State .l11d6a6 fr b n := transported (t := .l11d6a6) entry s.toState rfl rfl localFrame args saved keep
  have ident := identity_stored image (addr := 0x203258) (Or.inr rfl)
  have cp : identity.Stored (memCopy m (q+0x128) 0x203258 120) (q+0x128) := by
    have src : identity.Stored m ((0x203258 : BitVec 64) + BitVec.ofNat 64 0) := ident
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using
      (Projective.Stored.memCopy (off := 0) (dst := q+0x128) src (by decide : 120 ≤ 2^64) (by decide))
  have idStored : identity.Stored n (q+0x128) := by
    apply cp.of_frame (rs := [⟨(q+8).toNat,8⟩,⟨(q+56).toNat,8⟩])
    · dsimp only [n,setupMemory]
      apply RamWriteFrame.memStore
      · apply (RamWriteFrame.refl _ _).memStore
        exact ⟨_,.head _,by dsimp only [q]; acc_bounds using entry⟩
      · exact ⟨_,List.mem_cons_of_mem _ (.head _),by dsimp only [q]; acc_bounds using entry⟩
    · dsimp only [q]; acc_bounds using entry
  have lim : memLoad n (q + 56) 64 = 66 := memLoad_memStore_same _ _ _ rfl (by decide)
  obtain ⟨bsp,_,bwin⟩ := currentStack st rfl
  obtain ⟨c,c₁,target,tmp,di,si,dx,kc⟩ := firstCopyBlock (congrArg (Value.get 64) bsp)
    (bwin.sub (by acc_bounds using entry) (by acc_bounds using entry)) st.widths st.savedWidths
    (congrArg (Value.get 64) b13)
  obtain ⟨v,o,path₁,st₁,left,f₁,kv⟩ := copyCall (r := .l11d6c2) true entry st rfl rfl c₁ (by decide) di si dx
    (s.firstTable.of_frame localFrame (by acc_bounds using entry))
  obtain ⟨vsp,_,vwin⟩ := currentStack st₁ rfl
  obtain ⟨e,c₂,di₂,si₂,dx₂,ke⟩ := secondCopyBlock (congrArg (Value.get 64) vsp)
    (vwin.sub (by acc_bounds using entry) (by acc_bounds using entry)) st₁.widths st₁.savedWidths
    (congrArg (Value.get 64) ((kv 13 (by decide)).trans ((kc 13 (by decide)).trans b13)))
    (congrArg (Value.get 64) ((kv 15 (by decide)).trans ((kc 15 (by decide)).trans b15)))
    ((congrArg (Value.get 64) (kv 3 (by decide))).trans target)
  have f₁' := localFrame.trans f₁ (by acc_call_bounds using entry)
  obtain ⟨u,z,path₂,st₂,right,f₂,ku⟩ := copyCall (r := .l11d6d3) false entry st₁ rfl rfl c₂ (by decide) di₂ si₂ dx₂
    (s.secondTable.of_frame f₁' (by acc_bounds using entry))
  refine ⟨u,z,(path.trans path₁).trans path₂,st₂,left.of_frame f₂ (by acc_call_bounds using entry),
    right,(idStored.of_frame f₁ (by dsimp only [q]; acc_call_bounds using entry)).of_frame f₂ (by dsimp only [q]; acc_call_bounds using entry),
    (f₂.memLoad_eq (by acc_call_bounds using entry)).trans ((f₁.memLoad_eq (by acc_call_bounds using entry)).trans lim),
    f₁'.trans f₂ (by acc_call_bounds using entry),?_,?_,?_,?_⟩
  · exact congrArg (Value.get 64) ((ku 5 (by decide)).trans ((ke 5 (by decide)).trans ((kv 5 (by decide)).trans ((kc 5 (by decide)).trans b5))))
  · exact congrArg (Value.get 64) ((ku 12 (by decide)).trans ((ke 12 (by decide)).trans ((kv 12 (by decide)).trans ((kc 12 (by decide)).trans b12))))
  · exact (congrArg (Value.get 64) ((ku 14 (by decide)).trans ((ke 14 (by decide)).trans (kv 14 (by decide))))).trans tmp
  · exact congrArg (Value.get 64) ((ku 15 (by decide)).trans ((ke 15 (by decide)).trans ((kv 15 (by decide)).trans ((kc 15 (by decide)).trans b15))))

end K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator
