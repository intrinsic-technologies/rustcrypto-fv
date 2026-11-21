import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.WindowHead

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def modulusMemory (s : RamState) (memory : Ram) : Ram :=
  memStore (memStore (memStore memory (exponentFrameBase s+128) (0xffffffff#64))
    (exponentFrameBase s+152) (0#64)) (exponentFrameBase s+144) (0xffffffff00000001#64)

theorem initialize_modulus [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (frame : Frame s t) (rip : t.RIP=0x115421)
    (parameter : t.regValue .r15=s.regValue .rsi+32) :
    ∃ u, Advances boundary 6 t u ∧ Frame s u ∧ u.RIP=0x115445 ∧
      AgreesExcept [.reg 0,.rip,.mem (exponentFrameBase s+128) 8,
        .mem (exponentFrameBase s+152) 8,.mem (exponentFrameBase s+144) 8] t u ∧
      u.external=modulusMemory s t.external := by
  have param1 : t.regValue .r15=s.regValue .rsi+32 := parameter
  have addr1 (next : BitVec 64) : (AddrMode.base 15 (.d8 8)).addr t next=
      s.regValue .rsi+BitVec.ofNat 64 40 := by
    change t.regValue .r15+8#64=_
    rw [param1,BitVec.add_assoc]
    rfl
  obtain ⟨t1,a1,f1,ip1,v1,g1,m1⟩ := frame_load_r64 ctx.outerBoundary frame
    0x15421 0x49 0 (.base 15 (.d8 8)) (by simp [RexWPrefix]) (by decide)
    rfl rfl (by decide) rip (by decide) (by decide +kernel)
    (by rw [addr1]; exact input_readable ctx frame (offset := 40) (by decide))
  change AgreesExcept [.reg 0,.rip] t t1 at g1
  have val1 : t1.regValue .rax=0xffffffff := by
    rw [addr1] at v1
    have h := (parameters_modulus ctx.residue.2).memLoad_limb 1 (by decide)
    change memLoad s.external ((s.regValue .rsi+32)+8#64) 64=0xffffffff#64 at h
    rw [BitVec.add_assoc] at h
    exact v1.trans ((input_memLoad_of_frame ctx frame (offset := 40) (by decide)).trans h)
  obtain ⟨t2,a2,f2,ip2,v2,g2,m2⟩ := frame_store_r64 ctx.toCalleePre f1
    0x15425 128 (.d32 128) 0x48 0 (by simp [RexWPrefix]) rfl rfl rfl
    (by decide) ip1 (by decide) (by decide +kernel)
  have memory2 : t2.external=memStore t1.external (exponentFrameBase s+128) (0xffffffff#64) :=
    m2.trans (congrArg (memStore t1.external _) val1)
  have param3 : t2.regValue .r15=s.regValue .rsi+32 := ((g1.trans g2).read (n := 64) (r := 15) (by simp)).trans parameter
  have addr3 (next : BitVec 64) : (AddrMode.base 15 (.d8 16)).addr t2 next=
      s.regValue .rsi+BitVec.ofNat 64 48 := by
    change t2.regValue .r15+16#64=_
    rw [param3,BitVec.add_assoc]
    rfl
  obtain ⟨t3,a3,f3,ip3,v3,g3,m3⟩ := frame_load_r64 ctx.outerBoundary f2
    0x1542d 0x49 0 (.base 15 (.d8 16)) (by simp [RexWPrefix]) (by decide)
    rfl rfl (by decide) ip2 (by decide) (by decide +kernel)
    (by rw [addr3]; exact input_readable ctx f2 (offset := 48) (by decide))
  change AgreesExcept [.reg 0,.rip] t2 t3 at g3
  have val3 : t3.regValue .rax=0x0 := by
    rw [addr3] at v3
    have h := (parameters_modulus ctx.residue.2).memLoad_limb 2 (by decide)
    change memLoad s.external ((s.regValue .rsi+32)+16#64) 64=0x0#64 at h
    rw [BitVec.add_assoc] at h
    exact v3.trans ((input_memLoad_of_frame ctx f2 (offset := 48) (by decide)).trans h)
  obtain ⟨t4,a4,f4,ip4,v4,g4,m4⟩ := frame_store_r64 ctx.toCalleePre f3
    0x15431 152 (.d32 152) 0x48 0 (by simp [RexWPrefix]) rfl rfl rfl
    (by decide) ip3 (by decide) (by decide +kernel)
  have memory4 : t4.external=memStore t3.external (exponentFrameBase s+152) (0x0#64) :=
    m4.trans (congrArg (memStore t3.external _) val3)
  have param5 : t4.regValue .r15=s.regValue .rsi+32 := ((((g1.trans g2).trans g3).trans g4).read (n := 64) (r := 15) (by simp)).trans parameter
  have addr5 (next : BitVec 64) : (AddrMode.base 15 (.d8 24)).addr t4 next=
      s.regValue .rsi+BitVec.ofNat 64 56 := by
    change t4.regValue .r15+24#64=_
    rw [param5,BitVec.add_assoc]
    rfl
  obtain ⟨t5,a5,f5,ip5,v5,g5,m5⟩ := frame_load_r64 ctx.outerBoundary f4
    0x15439 0x49 0 (.base 15 (.d8 24)) (by simp [RexWPrefix]) (by decide)
    rfl rfl (by decide) ip4 (by decide) (by decide +kernel)
    (by rw [addr5]; exact input_readable ctx f4 (offset := 56) (by decide))
  change AgreesExcept [.reg 0,.rip] t4 t5 at g5
  have val5 : t5.regValue .rax=0xffffffff00000001 := by
    rw [addr5] at v5
    have h := (parameters_modulus ctx.residue.2).memLoad_limb 3 (by decide)
    change memLoad s.external ((s.regValue .rsi+32)+24#64) 64=0xffffffff00000001#64 at h
    rw [BitVec.add_assoc] at h
    exact v5.trans ((input_memLoad_of_frame ctx f4 (offset := 56) (by decide)).trans h)
  obtain ⟨t6,a6,f6,ip6,v6,g6,m6⟩ := frame_store_r64 ctx.toCalleePre f5
    0x1543d 144 (.d32 144) 0x48 0 (by simp [RexWPrefix]) rfl rfl rfl
    (by decide) ip5 (by decide) (by decide +kernel)
  have memory6 : t6.external=memStore t5.external (exponentFrameBase s+144) (0xffffffff00000001#64) :=
    m6.trans (congrArg (memStore t5.external _) val5)
  refine ⟨t6,(((((a1.trans a2).trans a3).trans a4).trans a5).trans a6),f6,ip6,?_,?_⟩
  · exact (((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).mono (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]; grind only)
  · simp only [memory6,m5,memory4,m3,memory2,m1,modulusMemory]

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
