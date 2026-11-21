import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.FirstState

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

def oneCopyMemory (s : RamState) (memory : Ram) : Ram :=
  [24,16,8,0].foldl (fun m j ↦ memStore m
    (exponentFrameBase s+BitVec.ofNat 64 (48+j))
    (memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 (64+j)) 64)) memory

def oneCopyComponents (s : RamState) : List Component :=
  [.reg 0,.reg 2,.rip,.mem (exponentFrameBase s+72) 8,.mem (exponentFrameBase s+64) 8,
    .mem (exponentFrameBase s+56) 8,.mem (exponentFrameBase s+48) 8]

theorem copy_one [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (frame : Frame s t) (rip : t.RIP=0x1153ee)
    (parameter : t.regValue .r15=s.regValue .rsi+32) :
    ∃ u, Advances boundary 8 t u ∧ Frame s u ∧ u.RIP=0x115412 ∧
      AgreesExcept (oneCopyComponents s) t u ∧ u.external=oneCopyMemory s t.external := by
  have ptr1 : t.regValue .r15=s.regValue .rsi+32 := parameter
  have addr1 (next : BitVec 64) : (AddrMode.base 15 (.d8 56)).addr t next=
      s.regValue .rsi+BitVec.ofNat 64 88 := by
    change t.regValue .r15+56#64=_
    rw [ptr1,BitVec.add_assoc]
    rfl
  obtain ⟨t1,a1,f1,ip1,v1,g1,m1⟩ := frame_load_r64 ctx.outerBoundary frame
    0x153ee 0x49 0 (.base 15 (.d8 56))
    (by simp [RexWPrefix]) (by decide) rfl rfl (by decide) rip
    (by decide) (by decide +kernel)
    (by rw [addr1]; exact input_readable ctx frame (offset := 88) (by decide))
  change AgreesExcept [.reg 0,.rip] t t1 at g1
  have value1 : (Operand.reg 0 : Operand 64).read t1=
      memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 88) 64 := by
    rw [addr1] at v1
    exact v1.trans (input_memLoad_of_frame ctx frame (offset := 88) (by decide))
  obtain ⟨t2,a2,f2,ip2,v2,g2,m2⟩ := frame_store_r64 ctx.toCalleePre f1
    0x153f2 72 (.d8 72) 0x48 0
    (by simp [RexWPrefix]) rfl rfl rfl (by decide) ip1 (by decide) (by decide +kernel)
  have memory2 : t2.external=memStore t1.external (exponentFrameBase s+72)
      (memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 88) 64) :=
    m2.trans (congrArg (memStore t1.external _) (value1))
  have ptr3 : t2.regValue .r15=s.regValue .rsi+32 := ((g1.trans g2).read (n := 64) (r := 15) (by simp)).trans parameter
  have addr3 (next : BitVec 64) : (AddrMode.base 15 (.d8 48)).addr t2 next=
      s.regValue .rsi+BitVec.ofNat 64 80 := by
    change t2.regValue .r15+48#64=_
    rw [ptr3,BitVec.add_assoc]
    rfl
  obtain ⟨t3,a3,f3,ip3,v3,g3,m3⟩ := frame_load_r64 ctx.outerBoundary f2
    0x153f7 0x49 0 (.base 15 (.d8 48))
    (by simp [RexWPrefix]) (by decide) rfl rfl (by decide) ip2
    (by decide) (by decide +kernel)
    (by rw [addr3]; exact input_readable ctx f2 (offset := 80) (by decide))
  change AgreesExcept [.reg 0,.rip] t2 t3 at g3
  have value3 : (Operand.reg 0 : Operand 64).read t3=
      memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 80) 64 := by
    rw [addr3] at v3
    exact v3.trans (input_memLoad_of_frame ctx f2 (offset := 80) (by decide))
  obtain ⟨t4,a4,f4,ip4,v4,g4,m4⟩ := frame_store_r64 ctx.toCalleePre f3
    0x153fb 64 (.d8 64) 0x48 0
    (by simp [RexWPrefix]) rfl rfl rfl (by decide) ip3 (by decide) (by decide +kernel)
  have memory4 : t4.external=memStore t3.external (exponentFrameBase s+64)
      (memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 80) 64) :=
    m4.trans (congrArg (memStore t3.external _) (value3))
  have ptr5 : t4.regValue .r15=s.regValue .rsi+32 := ((((g1.trans g2).trans g3).trans g4).read (n := 64) (r := 15) (by simp)).trans parameter
  have addr5 (next : BitVec 64) : (AddrMode.base 15 (.d8 32)).addr t4 next=
      s.regValue .rsi+BitVec.ofNat 64 64 := by
    change t4.regValue .r15+32#64=_
    rw [ptr5,BitVec.add_assoc]
    rfl
  obtain ⟨t5,a5,f5,ip5,v5,g5,m5⟩ := frame_load_r64 ctx.outerBoundary f4
    0x15400 0x49 0 (.base 15 (.d8 32))
    (by simp [RexWPrefix]) (by decide) rfl rfl (by decide) ip4
    (by decide) (by decide +kernel)
    (by rw [addr5]; exact input_readable ctx f4 (offset := 64) (by decide))
  change AgreesExcept [.reg 0,.rip] t4 t5 at g5
  have value5 : (Operand.reg 0 : Operand 64).read t5=
      memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 64) 64 := by
    rw [addr5] at v5
    exact v5.trans (input_memLoad_of_frame ctx f4 (offset := 64) (by decide))
  have ptr6 : t5.regValue .r15=s.regValue .rsi+32 := (((((g1.trans g2).trans g3).trans g4).trans g5).read (n := 64) (r := 15) (by simp)).trans parameter
  have addr6 (next : BitVec 64) : (AddrMode.base 15 (.d8 40)).addr t5 next=
      s.regValue .rsi+BitVec.ofNat 64 72 := by
    change t5.regValue .r15+40#64=_
    rw [ptr6,BitVec.add_assoc]
    rfl
  obtain ⟨t6,a6,f6,ip6,v6,g6,m6⟩ := frame_load_r64 ctx.outerBoundary f5
    0x15404 0x49 2 (.base 15 (.d8 40))
    (by simp [RexWPrefix]) (by decide) rfl rfl (by decide) ip5
    (by decide) (by decide +kernel)
    (by rw [addr6]; exact input_readable ctx f5 (offset := 72) (by decide))
  change AgreesExcept [.reg 2,.rip] t5 t6 at g6
  have value6 : (Operand.reg 2 : Operand 64).read t6=
      memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 72) 64 := by
    rw [addr6] at v6
    exact v6.trans (input_memLoad_of_frame ctx f5 (offset := 72) (by decide))
  obtain ⟨t7,a7,f7,ip7,v7,g7,m7⟩ := frame_store_r64 ctx.toCalleePre f6
    0x15408 56 (.d8 56) 0x48 2
    (by simp [RexWPrefix]) rfl rfl rfl (by decide) ip6 (by decide) (by decide +kernel)
  have memory7 : t7.external=memStore t6.external (exponentFrameBase s+56)
      (memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 72) 64) :=
    m7.trans (congrArg (memStore t6.external _) (value6))
  obtain ⟨t8,a8,f8,ip8,v8,g8,m8⟩ := frame_store_r64 ctx.toCalleePre f7
    0x1540d 48 (.d8 48) 0x48 0
    (by simp [RexWPrefix]) rfl rfl rfl (by decide) ip7 (by decide) (by decide +kernel)
  have memory8 : t8.external=memStore t7.external (exponentFrameBase s+48)
      (memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 64) 64) :=
    m8.trans (congrArg (memStore t7.external _) (((g6.trans g7).read (n := 64) (r := 0) (by simp)).trans value5))
  refine ⟨t8,(((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8),f8,ip8,?_,?_⟩
  · apply (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).mono
    simp only [oneCopyComponents,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    grind only
  · simp only [memory8,memory7,m6,m5,memory4,m3,memory2,m1,
      oneCopyMemory,List.foldl_cons,List.foldl_nil,Nat.add_zero,BitVec.ofNat_eq_ofNat]

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
