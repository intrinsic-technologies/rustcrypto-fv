import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Prepared

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def firstCopyMemory (s : RamState) (memory : Ram) : Ram :=
  [(24,0xd8),(16,0xd0),(8,0xc8),(0,0xc0)].foldl
    (fun m pair ↦ memStore m (exponentFrameBase s+BitVec.ofNat 64 pair.2)
      (memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 pair.1) 64)) memory

def firstCopyComponents (s : RamState) : List Component :=
  [.reg 1,.reg 12,.rip,.mem (exponentFrameBase s+0xd8) 8,
    .mem (exponentFrameBase s+0xd0) 8,.mem (exponentFrameBase s+0xc8) 8,
    .mem (exponentFrameBase s+0xc0) 8]

theorem copy_first [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : Frame s t) (rip : t.RIP=0x114f3a)
    (input : t.regValue .rsi=s.regValue .rsi)
    (parameter : t.regValue .r15=s.regValue .rsi+32) :
    ∃ u, Advances boundary 9 t u ∧ Frame s u ∧ u.RIP=0x114f6d ∧
      u.regValue .r12=0xffffffffffffffff ∧
      AgreesExcept (firstCopyComponents s) t u ∧ u.external=firstCopyMemory s t.external := by

  have base1 : t.regValue .rsi=s.regValue .rsi := input
  have addr1 (next : BitVec 64) : (AddrMode.base 6 (.d8 24)).addr t next=s.regValue .rsi+BitVec.ofNat 64 24 := by
    change t.regValue .rsi+24#64=_
    rw [base1]
  obtain ⟨t1,a1,f1,ip1,v1,g1,m1⟩ :=
    frame_load_r64 ctx.outerBoundary hf 0x14f3a 0x48 1
      (.base 6 (.d8 24)) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      rip (by decide) (by decide +kernel)
      (by rw [addr1]; exact input_readable ctx hf (offset := 24) (by decide))
  change AgreesExcept [.reg 1,.rip] t t1 at g1
  have value1 : t1.regValue .rcx=memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 24) 64 := by
    rw [addr1] at v1
    exact v1.trans (input_memLoad_of_frame ctx hf (offset := 24) (by decide))
  obtain ⟨t2,a2,f2,ip2,v2,g2,m2⟩ :=
    frame_store_r64 ctx.toCalleePre f1 0x14f3e 0xd8 (.d32 0xd8)
      0x48 1 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip1 (by decide) (by decide +kernel)
  change AgreesExcept [.mem (exponentFrameBase s+0xd8) 8,.rip] t1 t2 at g2
  have memory2 : t2.external=memStore t1.external (exponentFrameBase s+0xd8)
      (memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 24) 64) :=
    m2.trans (congrArg (memStore t1.external _) value1)
  have base3 : t2.regValue .rsi=s.regValue .rsi := ((g1.trans g2).read (n := 64) (r := 6) (by simp)).trans input
  have addr3 (next : BitVec 64) : (AddrMode.base 6 (.d8 16)).addr t2 next=s.regValue .rsi+BitVec.ofNat 64 16 := by
    change t2.regValue .rsi+16#64=_
    rw [base3]
  obtain ⟨t3,a3,f3,ip3,v3,g3,m3⟩ :=
    frame_load_r64 ctx.outerBoundary f2 0x14f46 0x48 1
      (.base 6 (.d8 16)) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      ip2 (by decide) (by decide +kernel)
      (by rw [addr3]; exact input_readable ctx f2 (offset := 16) (by decide))
  change AgreesExcept [.reg 1,.rip] t2 t3 at g3
  have value3 : t3.regValue .rcx=memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 16) 64 := by
    rw [addr3] at v3
    exact v3.trans (input_memLoad_of_frame ctx f2 (offset := 16) (by decide))
  obtain ⟨t4,a4,f4,ip4,v4,g4,m4⟩ :=
    frame_store_r64 ctx.toCalleePre f3 0x14f4a 0xd0 (.d32 0xd0)
      0x48 1 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip3 (by decide) (by decide +kernel)
  change AgreesExcept [.mem (exponentFrameBase s+0xd0) 8,.rip] t3 t4 at g4
  have memory4 : t4.external=memStore t3.external (exponentFrameBase s+0xd0)
      (memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 16) 64) :=
    m4.trans (congrArg (memStore t3.external _) value3)
  have base5 : t4.regValue .rsi=s.regValue .rsi := ((((g1.trans g2).trans g3).trans g4).read (n := 64) (r := 6) (by simp)).trans input
  have addr5 (next : BitVec 64) : (AddrMode.base 6 (.d8 8)).addr t4 next=s.regValue .rsi+BitVec.ofNat 64 8 := by
    change t4.regValue .rsi+8#64=_
    rw [base5]
  obtain ⟨t5,a5,f5,ip5,v5,g5,m5⟩ :=
    frame_load_r64 ctx.outerBoundary f4 0x14f52 0x48 1
      (.base 6 (.d8 8)) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      ip4 (by decide) (by decide +kernel)
      (by rw [addr5]; exact input_readable ctx f4 (offset := 8) (by decide))
  change AgreesExcept [.reg 1,.rip] t4 t5 at g5
  have value5 : t5.regValue .rcx=memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 8) 64 := by
    rw [addr5] at v5
    exact v5.trans (input_memLoad_of_frame ctx f4 (offset := 8) (by decide))
  obtain ⟨t6,a6,f6,ip6,v6,g6,m6⟩ :=
    frame_store_r64 ctx.toCalleePre f5 0x14f56 0xc8 (.d32 0xc8)
      0x48 1 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip5 (by decide) (by decide +kernel)
  change AgreesExcept [.mem (exponentFrameBase s+0xc8) 8,.rip] t5 t6 at g6
  have memory6 : t6.external=memStore t5.external (exponentFrameBase s+0xc8)
      (memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 8) 64) :=
    m6.trans (congrArg (memStore t5.external _) value5)
  have base7 : t6.regValue .r15=s.regValue .rsi+32 := ((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).read (n := 64) (r := 15) (by simp)).trans parameter
  have addr7 (next : BitVec 64) : (AddrMode.base 15 (.d8 96)).addr t6 next=s.regValue .rsi+BitVec.ofNat 64 128 := by
    change t6.regValue .r15+96#64=_
    rw [base7]
    rw [BitVec.add_assoc]; rfl
  obtain ⟨t7,a7,f7,ip7,v7,g7,m7⟩ :=
    frame_load_r64 ctx.outerBoundary f6 0x14f5e 0x4d 4
      (.base 15 (.d8 96)) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      ip6 (by decide) (by decide +kernel)
      (by rw [addr7]; exact input_readable ctx f6 (offset := 128) (by decide))
  change AgreesExcept [.reg 12,.rip] t6 t7 at g7
  have value7 : t7.regValue .r12=memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 128) 64 := by
    rw [addr7] at v7
    exact v7.trans (input_memLoad_of_frame ctx f6 (offset := 128) (by decide))
  have base8 : t7.regValue .rsi=s.regValue .rsi := (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).read (n := 64) (r := 6) (by simp)).trans input
  have addr8 (next : BitVec 64) : (AddrMode.base 6 .none).addr t7 next=s.regValue .rsi+BitVec.ofNat 64 0 := by
    change t7.regValue .rsi+0#64=_
    rw [base8]
  obtain ⟨t8,a8,f8,ip8,v8,g8,m8⟩ :=
    frame_load_r64 ctx.outerBoundary f7 0x14f62 0x48 1
      (.base 6 .none) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      ip7 (by decide) (by decide +kernel)
      (by rw [addr8]; exact input_readable ctx f7 (offset := 0) (by decide))
  change AgreesExcept [.reg 1,.rip] t7 t8 at g8
  have value8 : t8.regValue .rcx=memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 0) 64 := by
    rw [addr8] at v8
    exact v8.trans (input_memLoad_of_frame ctx f7 (offset := 0) (by decide))
  obtain ⟨t9,a9,f9,ip9,v9,g9,m9⟩ :=
    frame_store_r64 ctx.toCalleePre f8 0x14f65 0xc0 (.d32 0xc0)
      0x48 1 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip8 (by decide) (by decide +kernel)
  change AgreesExcept [.mem (exponentFrameBase s+0xc0) 8,.rip] t8 t9 at g9
  have memory9 : t9.external=memStore t8.external (exponentFrameBase s+0xc0)
      (memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 0) 64) :=
    m9.trans (congrArg (memStore t8.external _) value8)
  refine ⟨t9,((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9),f9,ip9,?_,?_,?_⟩
  · have h : t9.regValue .r12=memLoad s.external (s.regValue .rsi+128#64) 64 :=
      ((g8.trans g9).read (n := 64) (r := 12) (by simp)).trans value7
    have v : memLoad s.external (s.regValue .rsi+32+96) 64=(-1 : BitVec 64) :=
      (parameters_inverse_bytes ctx.residue.2).memLoad (by decide) (by decide)
    change memLoad s.external (s.regValue .rsi+32+96) 64=(-1 : BitVec 64) at v
    rw [BitVec.add_assoc] at v
    exact h.trans v
  · apply ((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).mono
    simp only [firstCopyComponents,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    grind only
  · simp only [memory9,m8,m7,memory6,m5,memory4,m3,memory2,m1,
      firstCopyMemory,List.foldl_cons,List.foldl_nil,BitVec.ofNat_eq_ofNat]

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
