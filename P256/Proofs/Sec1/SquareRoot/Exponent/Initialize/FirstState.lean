import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.FirstCopy
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.TableSetup
import P256.Proofs.Common.Instructions.Neg64

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)
open P256.Proofs.Common.Instructions.Neg64 (neg_r64_effect_step negR64Effect)

theorem firstCopyMemory_limb (s : RamState) (memory : Ram) {j : Nat} (hj : j<4) :
    memLoad (firstCopyMemory s memory)
      (exponentFrameBase s+0xc0#64+BitVec.ofNat 64 (8*j)) 64=
    memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 (8*j)) 64 := by
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    simp only [firstCopyMemory,List.foldl_cons,List.foldl_nil,Nat.reduceMul,
      BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero]
    repeat first
      | rw [memLoad_memStore_rangeApart _ _ _ _ 64
          (RangeApart.offsets (exponentFrameBase s) (by decide) (by decide) (by decide))]
      | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem initialize_table_first [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) :
    ∃ u, Advances boundary 173 s u ∧ TableState s u x 2 ∧
      u.RIP=0x114f80 ∧ u.regValue .rax=exponentFrameBase s+0xc0 := by
  obtain ⟨t,run,frame,rip,ax,count,parameter,input,memory,value,exponent,ones⟩ := initialize_copies ctx
  have data : TableData s t x 1 := by
    refine ⟨?_,exponent,value,frame.outputPointer⟩
    intro i hi
    have eq : i=0 := by omega
    subst i
    simpa only [Nat.pow_zero,show 1%P256.Spec.Operations.domain.p=1 from by decide +kernel] using ones 0 (by decide) (by decide)
  obtain ⟨v,av,fv,ipv,inverse,g,mem⟩ := copy_first ctx frame.scalarFrame rip input parameter
  have dataV : TableData s v x 1 := data.of_agrees g (by
    intro off ho c hc hv
    simp only [firstCopyComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    · obtain ⟨j,hj,eq⟩ := hv
      have apart : RangeApart (exponentFrameBase s+BitVec.ofNat 64 216) 8
          (exponentFrameBase s+BitVec.ofNat 64 off) 1 :=
        RangeApart.offsets (exponentFrameBase s) (by decide)
          (by unfold TableDataOffset at ho; omega) (by unfold TableDataOffset at ho; omega)
      apply apart j hj 0 (by decide)
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using eq.symm
    · obtain ⟨j,hj,eq⟩ := hv
      have apart : RangeApart (exponentFrameBase s+BitVec.ofNat 64 208) 8
          (exponentFrameBase s+BitVec.ofNat 64 off) 1 :=
        RangeApart.offsets (exponentFrameBase s) (by decide)
          (by unfold TableDataOffset at ho; omega) (by unfold TableDataOffset at ho; omega)
      apply apart j hj 0 (by decide)
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using eq.symm
    · obtain ⟨j,hj,eq⟩ := hv
      have apart : RangeApart (exponentFrameBase s+BitVec.ofNat 64 200) 8
          (exponentFrameBase s+BitVec.ofNat 64 off) 1 :=
        RangeApart.offsets (exponentFrameBase s) (by decide)
          (by unfold TableDataOffset at ho; omega) (by unfold TableDataOffset at ho; omega)
      apply apart j hj 0 (by decide)
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using eq.symm
    · obtain ⟨j,hj,eq⟩ := hv
      have apart : RangeApart (exponentFrameBase s+BitVec.ofNat 64 192) 8
          (exponentFrameBase s+BitVec.ofNat 64 off) 1 :=
        RangeApart.offsets (exponentFrameBase s) (by decide)
          (by unfold TableDataOffset at ho; omega) (by unfold TableDataOffset at ho; omega)
      apply apart j hj 0 (by decide)
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using eq.symm)
  have first : Field.MontgomeryAt v (exponentFrameBase s+0xc0) x := by
    apply Field.montgomeryAt_of_memLoad_limbs ctx.residue.1.1
    · have read := ScalarFrame.stack_readable (frameOffset := 1416) ctx.toCalleePre fv
        (offset := 0xc0) (len := 32) (by decide) (by decide)
      have sp : stackPtr v=exponentFrameBase s := fv.rsp
      rw [sp] at read
      exact read.mem
    · intro j hj
      rw [mem]
      exact (firstCopyMemory_limb s _ hj).trans (ctx.residue.1.memLoad_limb j hj)
  have data2 : TableData s v x 2 := by
    refine ⟨?_,dataV.exponent,dataV.input,dataV.output⟩
    intro i hi
    by_cases eq : i=1
    · subst i
      simpa only [Nat.pow_one,Nat.mod_eq_of_lt ctx.residue.1.1,Nat.reduceMul,Nat.reduceAdd,BitVec.ofNat_eq_ofNat] using first
    · exact dataV.table i (by omega)
  have axV : v.regValue .rax=exponentFrameBase s+0xc0 :=
    (g.read (n := 64) (r := 0) (by simp [firstCopyComponents])).trans ax
  have countV : v.regValue .r14=254 :=
    (g.read (n := 64) (r := 14) (by simp [firstCopyComponents])).trans count
  have parameterV : v.regValue .r15=s.regValue .rsi+32 :=
    (g.read (n := 64) (r := 15) (by simp [firstCopyComponents])).trans parameter
  obtain ⟨a,a1,f1,ip1,v1,g1,m1⟩ := frame_move_r64 ctx.outerBoundary fv
    0x14f6d 0x4d 0xe5 (by simp [RexWPrefix]) rfl (by decide) ipv
    (by decide) (by decide +kernel)
  change AgreesExcept [.reg 13,.rip] v a at g1
  have negativeA : a.regValue .r13=0xffffffffffffffff := v1.trans inverse
  obtain ⟨b,a2,r2,e2⟩ := (P256.Proofs.Common.Instructions.Neg64.neg_r64_effect_step 0x114f70 0x49 0xdd
      (by simp [RexWPrefix]) rfl rfl).advances
    (readyToStep f1.machine f1.bindingsSupported)
    (programText_slice (programLoaded_codeIn f1.loaded) 0x14f70 _ (by decide) (by decide +kernel))
    ip1 (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x14f73 (by decide)))
  have g2 : AgreesExcept [.reg 13,.flags,.rip] a b := e2.agrees
  have f2 := f1.after_registers r2 g2 (by simp [Component.Covers]) (by simp)
  have negativeB : b.regValue .r13=1 := by
    have h : b.regValue .r13 = -a.regValue .r13 := e2.writes
    rw [negativeA] at h
    exact h
  obtain ⟨c,a3,f3,ip3,v3,g3,m3⟩ := frame_lea_r64 ctx.outerBoundary f2
    0x14f73 0x48 5 (.sib 4 none 0 (.d8 0x10))
    (by simp [RexWPrefix]) (by decide) rfl rfl (by decide) e2.rip
    (by decide) (by decide +kernel)
  change AgreesExcept [.reg 5,.rip] b c at g3
  have outputC : c.regValue .rbp=exponentFrameBase s+0x10 := by
    change c.regValue .rbp=stackPtr b+0x10 at v3
    exact v3.trans (congrArg (fun p ↦ p+0x10) f2.rsp)
  obtain ⟨u,a4,f4,ip4,v4,g4,m4⟩ := frame_lea_r64 ctx.outerBoundary f3
    0x14f78 0x48 3 (.sib 4 none 0 (.d32 0x2f8))
    (by simp [RexWPrefix]) (by decide) rfl rfl (by decide) ip3
    (by decide) (by decide +kernel)
  change AgreesExcept [.reg 3,.rip] c u at g4
  have inputU : u.regValue .rbx=exponentFrameBase s+0x2f8 := by
    change u.regValue .rbx=stackPtr c+0x2f8 at v4
    exact v4.trans (congrArg (fun p ↦ p+0x2f8) f3.rsp)
  have all := ((g1.trans g2).trans g3).trans g4
  refine ⟨u,((((run.trans av).trans a1).trans a2).trans a3).trans a4,
    ⟨f4,data2.of_agrees all (by simp [Component.Covers]),
      (all.read (n := 64) (r := 14) (by simp)).trans countV,
      (all.read (n := 64) (r := 15) (by simp)).trans parameterV,inputU,
      (all.read (n := 64) (r := 12) (by simp)).trans inverse,
      ((g3.trans g4).read (n := 64) (r := 13) (by simp)).trans negativeB,
      (g4.read (n := 64) (r := 5) (by simp)).trans outputC⟩,
    ip4,(all.read (n := 64) (r := 0) (by simp)).trans axV⟩

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
