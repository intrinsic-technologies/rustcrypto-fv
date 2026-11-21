import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.LoadStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.StoreStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.ExponentData

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def exponentSaveCopyMemory (s : RamState) (memory : Ram) : Ram :=
  [ (3, 0x550), (2, 0x548), (1, 0x540), (0, 0x538) ].foldl
    (fun m pair => memStore m (exponentFrameBase s + BitVec.ofNat 64 pair.2)
      (BitVec.ofNat 64 (sqrtExponent / 2^(64*pair.1)))) memory

def exponentSaveCopyComponents (s : RamState) : List Component :=
  [.reg 1, .rip, .mem (exponentFrameBase s + 0x550) 8,
    .mem (exponentFrameBase s + 0x548) 8, .mem (exponentFrameBase s + 0x540) 8,
    .mem (exponentFrameBase s + 0x538) 8]

set_option maxRecDepth 2048 in
theorem copy_saved_exponent [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : Frame s t) (rip : t.RIP = 0x114c3b)
    (input : t.regValue .rdx = 0x202fb8) :
    ∃ u, Advances boundary 8 t u ∧ Frame s u ∧ u.RIP = 0x114c6a ∧
      AgreesExcept (exponentSaveCopyComponents s) t u ∧
      u.external = exponentSaveCopyMemory s t.external := by
  have input1 : t.regValue .rdx = 0x202fb8 := input
  have addr1 : (AddrMode.base 2 (.d8 24)).addr t
      (Extracted.textAddress + BitVec.ofNat 64 (85051 + 3 + (AddrMode.base 2 (.d8 24)).tail.length)) =
      0x202fb8 + 24 := by
    change t.regValue .rdx + 24 = _
    rw [input1]
  obtain ⟨t1, a1, f1, ip1, v1, g1, m1⟩ :=
    frame_load_r64 ctx.outerBoundary hf 0x14c3b 0x48 1
      (AddrMode.base 2 (.d8 24)) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      rip (by decide) (by decide +kernel) (by
        rw [addr1]
        exact exponent_readable hf.loaded (offset := 24) (by decide))
  change AgreesExcept [.reg 1, .rip] t t1 at g1
  have value1 : (Operand.reg 1 : Operand 64).read t1 =
      BitVec.ofNat 64 (sqrtExponent / 2^(64*3)) := by
    rw [addr1] at v1
    exact v1.trans (exponent_memLoad_word hf.loaded 3 (by decide))
  obtain ⟨t2, a2, f2, ip2, _, g2, m2⟩ :=
    frame_store_r64 ctx.toCalleePre f1 0x14c3f 0x550 (.d32 0x550)
      0x48 1 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip1 (by decide) (by decide +kernel)
  have memory2 : t2.external = memStore t1.external
      (exponentFrameBase s + 0x550) (BitVec.ofNat 64 (sqrtExponent / 2^(64*3))) := by
    exact m2.trans (congrArg (memStore t1.external _) value1)
  have input3 : t2.regValue .rdx = 0x202fb8 := (g2.read (n := 64) (r := 2) (by simp)).trans ((g1.read (n := 64) (r := 2) (by simp)).trans (input))
  have addr3 : (AddrMode.base 2 (.d8 16)).addr t2
      (Extracted.textAddress + BitVec.ofNat 64 (85063 + 3 + (AddrMode.base 2 (.d8 16)).tail.length)) =
      0x202fb8 + 16 := by
    change t2.regValue .rdx + 16 = _
    rw [input3]
  obtain ⟨t3, a3, f3, ip3, v3, g3, m3⟩ :=
    frame_load_r64 ctx.outerBoundary f2 0x14c47 0x48 1
      (AddrMode.base 2 (.d8 16)) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      ip2 (by decide) (by decide +kernel) (by
        rw [addr3]
        exact exponent_readable f2.loaded (offset := 16) (by decide))
  change AgreesExcept [.reg 1, .rip] t2 t3 at g3
  have value3 : (Operand.reg 1 : Operand 64).read t3 =
      BitVec.ofNat 64 (sqrtExponent / 2^(64*2)) := by
    rw [addr3] at v3
    exact v3.trans (exponent_memLoad_word f2.loaded 2 (by decide))
  obtain ⟨t4, a4, f4, ip4, _, g4, m4⟩ :=
    frame_store_r64 ctx.toCalleePre f3 0x14c4b 0x548 (.d32 0x548)
      0x48 1 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip3 (by decide) (by decide +kernel)
  have memory4 : t4.external = memStore t3.external
      (exponentFrameBase s + 0x548) (BitVec.ofNat 64 (sqrtExponent / 2^(64*2))) := by
    exact m4.trans (congrArg (memStore t3.external _) value3)
  have input5 : t4.regValue .rdx = 0x202fb8 := (g4.read (n := 64) (r := 2) (by simp)).trans ((g3.read (n := 64) (r := 2) (by simp)).trans ((g2.read (n := 64) (r := 2) (by simp)).trans ((g1.read (n := 64) (r := 2) (by simp)).trans (input))))
  have addr5 : (AddrMode.base 2 (.d8 8)).addr t4
      (Extracted.textAddress + BitVec.ofNat 64 (85075 + 3 + (AddrMode.base 2 (.d8 8)).tail.length)) =
      0x202fb8 + 8 := by
    change t4.regValue .rdx + 8 = _
    rw [input5]
  obtain ⟨t5, a5, f5, ip5, v5, g5, m5⟩ :=
    frame_load_r64 ctx.outerBoundary f4 0x14c53 0x48 1
      (AddrMode.base 2 (.d8 8)) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      ip4 (by decide) (by decide +kernel) (by
        rw [addr5]
        exact exponent_readable f4.loaded (offset := 8) (by decide))
  change AgreesExcept [.reg 1, .rip] t4 t5 at g5
  have value5 : (Operand.reg 1 : Operand 64).read t5 =
      BitVec.ofNat 64 (sqrtExponent / 2^(64*1)) := by
    rw [addr5] at v5
    exact v5.trans (exponent_memLoad_word f4.loaded 1 (by decide))
  obtain ⟨t6, a6, f6, ip6, _, g6, m6⟩ :=
    frame_store_r64 ctx.toCalleePre f5 0x14c57 0x540 (.d32 0x540)
      0x48 1 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip5 (by decide) (by decide +kernel)
  have memory6 : t6.external = memStore t5.external
      (exponentFrameBase s + 0x540) (BitVec.ofNat 64 (sqrtExponent / 2^(64*1))) := by
    exact m6.trans (congrArg (memStore t5.external _) value5)
  have input7 : t6.regValue .rdx = 0x202fb8 := (g6.read (n := 64) (r := 2) (by simp)).trans ((g5.read (n := 64) (r := 2) (by simp)).trans ((g4.read (n := 64) (r := 2) (by simp)).trans ((g3.read (n := 64) (r := 2) (by simp)).trans ((g2.read (n := 64) (r := 2) (by simp)).trans ((g1.read (n := 64) (r := 2) (by simp)).trans (input))))))
  have addr7 : (AddrMode.base 2 .none).addr t6
      (Extracted.textAddress + BitVec.ofNat 64 (85087 + 3 + (AddrMode.base 2 .none).tail.length)) =
      0x202fb8 + 0 := by
    change t6.regValue .rdx + 0 = _
    rw [input7]
  obtain ⟨t7, a7, f7, ip7, v7, g7, m7⟩ :=
    frame_load_r64 ctx.outerBoundary f6 0x14c5f 0x48 1
      (AddrMode.base 2 .none) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      ip6 (by decide) (by decide +kernel) (by
        rw [addr7]
        exact exponent_readable f6.loaded (offset := 0) (by decide))
  change AgreesExcept [.reg 1, .rip] t6 t7 at g7
  have value7 : (Operand.reg 1 : Operand 64).read t7 =
      BitVec.ofNat 64 (sqrtExponent / 2^(64*0)) := by
    rw [addr7] at v7
    exact v7.trans (exponent_memLoad_word f6.loaded 0 (by decide))
  obtain ⟨t8, a8, f8, ip8, _, g8, m8⟩ :=
    frame_store_r64 ctx.toCalleePre f7 0x14c62 0x538 (.d32 0x538)
      0x48 1 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip7 (by decide) (by decide +kernel)
  have memory8 : t8.external = memStore t7.external
      (exponentFrameBase s + 0x538) (BitVec.ofNat 64 (sqrtExponent / 2^(64*0))) := by
    exact m8.trans (congrArg (memStore t7.external _) value7)
  refine ⟨t8, (((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8), f8, ip8, ?_, ?_⟩
  · apply (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).mono
    intro c hc
    simp only [exponentSaveCopyComponents, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc ⊢
    grind only
  · simp only [memory8, m7, memory6, m5, memory4, m3, memory2, m1,
      exponentSaveCopyMemory, List.foldl_cons, List.foldl_nil, BitVec.ofNat_eq_ofNat]

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
