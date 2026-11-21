import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.StoreStep

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def constantsMemory (s : RamState) (memory : Ram) : Ram :=
  memStore (memStore (memStore (memStore (memStore (memStore (memory) (exponentFrameBase s+728) (3 : BitVec 64)) (exponentFrameBase s+136) (0xffffffffffffffff : BitVec 64)) (exponentFrameBase s+696) (s.regValue .rsi+32 : BitVec 64)) (exponentFrameBase s+736) (0xffffffffffffffff : BitVec 64)) (exponentFrameBase s+688) (3 : BitVec 64)) (exponentFrameBase s+680) (15 : BitVec 64)

theorem initialize_constants [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (frame : Frame s t) (rip : t.RIP=0x115454)
    (mask : t.regValue .rax=3)
    (modulus : t.regValue .r11=0xffffffffffffffff)
    (parameter : t.regValue .r15=s.regValue .rsi+32)
    (inverse : t.regValue .r12=0xffffffffffffffff)
    (word : t.regValue .rbx=3)
    (window : t.regValue .r13=15)
    : ∃ u, Advances boundary 6 t u ∧ Frame s u ∧ u.RIP=0x115484 ∧
      AgreesExcept [.rip,.mem (exponentFrameBase s+728) 8,.mem (exponentFrameBase s+136) 8,
        .mem (exponentFrameBase s+696) 8,.mem (exponentFrameBase s+736) 8,
        .mem (exponentFrameBase s+688) 8,.mem (exponentFrameBase s+680) 8] t u ∧
      u.external=constantsMemory s t.external := by
  have value1 : t.regValue .rax=3 := mask
  obtain ⟨t1,a1,f1,ip1,v1,g1,m1⟩ := frame_store_r64 ctx.toCalleePre frame
    0x15454 728 (.d32 728) 0x48 0
    (by simp [RexWPrefix]) rfl rfl rfl (by decide) rip (by decide) (by decide +kernel)
  have memory1 : t1.external=memStore t.external (exponentFrameBase s+728) (3 : BitVec 64) :=
    m1.trans (congrArg (memStore t.external _) value1)
  have value2 : t1.regValue .r11=0xffffffffffffffff := (g1.read (n := 64) (r := 11) (by simp)).trans modulus
  obtain ⟨t2,a2,f2,ip2,v2,g2,m2⟩ := frame_store_r64 ctx.toCalleePre f1
    0x1545c 136 (.d32 136) 0x4c 3
    (by simp [RexWPrefix]) rfl rfl rfl (by decide) ip1 (by decide) (by decide +kernel)
  have memory2 : t2.external=memStore t1.external (exponentFrameBase s+136) (0xffffffffffffffff : BitVec 64) :=
    m2.trans (congrArg (memStore t1.external _) value2)
  have value3 : t2.regValue .r15=s.regValue .rsi+32 := ((g1.trans g2).read (n := 64) (r := 15) (by simp)).trans parameter
  obtain ⟨t3,a3,f3,ip3,v3,g3,m3⟩ := frame_store_r64 ctx.toCalleePre f2
    0x15464 696 (.d32 696) 0x4c 7
    (by simp [RexWPrefix]) rfl rfl rfl (by decide) ip2 (by decide) (by decide +kernel)
  have memory3 : t3.external=memStore t2.external (exponentFrameBase s+696) (s.regValue .rsi+32 : BitVec 64) :=
    m3.trans (congrArg (memStore t2.external _) value3)
  have value4 : t3.regValue .r12=0xffffffffffffffff := (((g1.trans g2).trans g3).read (n := 64) (r := 12) (by simp)).trans inverse
  obtain ⟨t4,a4,f4,ip4,v4,g4,m4⟩ := frame_store_r64 ctx.toCalleePre f3
    0x1546c 736 (.d32 736) 0x4c 4
    (by simp [RexWPrefix]) rfl rfl rfl (by decide) ip3 (by decide) (by decide +kernel)
  have memory4 : t4.external=memStore t3.external (exponentFrameBase s+736) (0xffffffffffffffff : BitVec 64) :=
    m4.trans (congrArg (memStore t3.external _) value4)
  have value5 : t4.regValue .rbx=3 := ((((g1.trans g2).trans g3).trans g4).read (n := 64) (r := 3) (by simp)).trans word
  obtain ⟨t5,a5,f5,ip5,v5,g5,m5⟩ := frame_store_r64 ctx.toCalleePre f4
    0x15474 688 (.d32 688) 0x48 3
    (by simp [RexWPrefix]) rfl rfl rfl (by decide) ip4 (by decide) (by decide +kernel)
  have memory5 : t5.external=memStore t4.external (exponentFrameBase s+688) (3 : BitVec 64) :=
    m5.trans (congrArg (memStore t4.external _) value5)
  have value6 : t5.regValue .r13=15 := (((((g1.trans g2).trans g3).trans g4).trans g5).read (n := 64) (r := 13) (by simp)).trans window
  obtain ⟨t6,a6,f6,ip6,v6,g6,m6⟩ := frame_store_r64 ctx.toCalleePre f5
    0x1547c 680 (.d32 680) 0x4c 5
    (by simp [RexWPrefix]) rfl rfl rfl (by decide) ip5 (by decide) (by decide +kernel)
  have memory6 : t6.external=memStore t5.external (exponentFrameBase s+680) (15 : BitVec 64) :=
    m6.trans (congrArg (memStore t5.external _) value6)
  refine ⟨t6,(((((a1.trans a2).trans a3).trans a4).trans a5).trans a6),f6,ip6,?_,?_⟩
  · exact (((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).mono (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]; grind only)
  · simp only [memory6,memory5,memory4,memory3,memory2,memory1,constantsMemory]

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
