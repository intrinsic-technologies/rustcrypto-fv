import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.LoadStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.StoreStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.ExponentData

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def exponentCopyMemory (s : RamState) (memory : Ram) : Ram :=
  [ (0, 0x318), (1, 0x320), (2, 0x328), (3, 0x330) ].foldl
    (fun m pair => memStore m (exponentFrameBase s + BitVec.ofNat 64 pair.2)
      (BitVec.ofNat 64 (sqrtExponent / 2^(64*pair.1)))) memory

def exponentCopyComponents (s : RamState) : List Component :=
  [.reg 0, .reg 8, .rip, .mem (exponentFrameBase s + 0x318) 8,
    .mem (exponentFrameBase s + 0x320) 8, .mem (exponentFrameBase s + 0x328) 8,
    .mem (exponentFrameBase s + 0x330) 8]

set_option maxRecDepth 2048 in
theorem copy_exponent [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : Frame s t) (rip : t.RIP = 0x114be3)
    (input : t.regValue .rdx = 0x202fb8) :
    ∃ u, Advances boundary 8 t u ∧ Frame s u ∧ u.RIP = 0x114c12 ∧
      AgreesExcept (exponentCopyComponents s) t u ∧
      u.external = exponentCopyMemory s t.external := by
  have input1 : t.regValue .rdx = 0x202fb8 := input
  have addr1 : (AddrMode.base 2 .none).addr t (Extracted.textAddress + BitVec.ofNat 64 (84963+3+(AddrMode.base 2 .none).tail.length)) =
      0x202fb8 + 0 := by
    change t.regValue .rdx + 0 = _
    rw [input1]
  obtain ⟨t1, a1, f1, ip1, v1, g1, m1⟩ :=
    frame_load_r64 ctx.outerBoundary hf 0x14be3 0x48 0
      (.base 2 .none) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      rip (by decide) (by decide +kernel) (by
        rw [addr1]
        exact exponent_readable hf.loaded (offset := 0) (by decide))
  change AgreesExcept [.reg 0, .rip] t t1 at g1
  have value1 : (Operand.reg 0 : Operand 64).read t1 =
      BitVec.ofNat 64 (sqrtExponent / 2^(64*0)) := by
    rw [addr1] at v1
    exact v1.trans (exponent_memLoad_word hf.loaded 0 (by decide))
  have input2 : t1.regValue .rdx = 0x202fb8 := (g1.read (n := 64) (r := 2) (by simp)).trans (input)
  have addr2 : (AddrMode.base 2 (.d8 8)).addr t1 (Extracted.textAddress + BitVec.ofNat 64 (84966+3+(AddrMode.base 2 (.d8 8)).tail.length)) =
      0x202fb8 + 8 := by
    change t1.regValue .rdx + 8 = _
    rw [input2]
  obtain ⟨t2, a2, f2, ip2, v2, g2, m2⟩ :=
    frame_load_r64 ctx.outerBoundary f1 0x14be6 0x4c 0
      (.base 2 (.d8 8)) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      ip1 (by decide) (by decide +kernel) (by
        rw [addr2]
        exact exponent_readable f1.loaded (offset := 8) (by decide))
  change AgreesExcept [.reg 8, .rip] t1 t2 at g2
  have value2 : (Operand.reg 8 : Operand 64).read t2 =
      BitVec.ofNat 64 (sqrtExponent / 2^(64*1)) := by
    rw [addr2] at v2
    exact v2.trans (exponent_memLoad_word f1.loaded 1 (by decide))
  have source3 : (Operand.reg 0 : Operand 64).read t2 =
      BitVec.ofNat 64 (sqrtExponent / 2^(64*0)) := by
    rw [g2.read (by simp), value1]
  obtain ⟨t3, a3, f3, ip3, _, g3, m3⟩ :=
    frame_store_r64 ctx.toCalleePre f2 0x14bea 0x318 (.d32 0x318)
      0x48 0 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip2 (by decide) (by decide +kernel)
  have memory3 : t3.external = memStore t2.external
      (exponentFrameBase s + 0x318)
      (BitVec.ofNat 64 (sqrtExponent / 2^(64*0))) := by
    exact m3.trans (congrArg (memStore t2.external _) source3)
  have source4 : (Operand.reg 8 : Operand 64).read t3 =
      BitVec.ofNat 64 (sqrtExponent / 2^(64*1)) := by
    rw [g3.read (by simp), value2]
  obtain ⟨t4, a4, f4, ip4, _, g4, m4⟩ :=
    frame_store_r64 ctx.toCalleePre f3 0x14bf2 0x320 (.d32 0x320)
      0x4c 0 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip3 (by decide) (by decide +kernel)
  have memory4 : t4.external = memStore t3.external
      (exponentFrameBase s + 0x320)
      (BitVec.ofNat 64 (sqrtExponent / 2^(64*1))) := by
    exact m4.trans (congrArg (memStore t3.external _) source4)
  have input5 : t4.regValue .rdx = 0x202fb8 := (g4.read (n := 64) (r := 2) (by simp)).trans ((g3.read (n := 64) (r := 2) (by simp)).trans ((g2.read (n := 64) (r := 2) (by simp)).trans ((g1.read (n := 64) (r := 2) (by simp)).trans (input))))
  have addr5 : (AddrMode.base 2 (.d8 16)).addr t4 (Extracted.textAddress + BitVec.ofNat 64 (84986+3+(AddrMode.base 2 (.d8 16)).tail.length)) =
      0x202fb8 + 16 := by
    change t4.regValue .rdx + 16 = _
    rw [input5]
  obtain ⟨t5, a5, f5, ip5, v5, g5, m5⟩ :=
    frame_load_r64 ctx.outerBoundary f4 0x14bfa 0x48 0
      (.base 2 (.d8 16)) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      ip4 (by decide) (by decide +kernel) (by
        rw [addr5]
        exact exponent_readable f4.loaded (offset := 16) (by decide))
  change AgreesExcept [.reg 0, .rip] t4 t5 at g5
  have value5 : (Operand.reg 0 : Operand 64).read t5 =
      BitVec.ofNat 64 (sqrtExponent / 2^(64*2)) := by
    rw [addr5] at v5
    exact v5.trans (exponent_memLoad_word f4.loaded 2 (by decide))
  have source6 : (Operand.reg 0 : Operand 64).read t5 =
      BitVec.ofNat 64 (sqrtExponent / 2^(64*2)) := by
    exact value5
  obtain ⟨t6, a6, f6, ip6, _, g6, m6⟩ :=
    frame_store_r64 ctx.toCalleePre f5 0x14bfe 0x328 (.d32 0x328)
      0x48 0 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip5 (by decide) (by decide +kernel)
  have memory6 : t6.external = memStore t5.external
      (exponentFrameBase s + 0x328)
      (BitVec.ofNat 64 (sqrtExponent / 2^(64*2))) := by
    exact m6.trans (congrArg (memStore t5.external _) source6)
  have input7 : t6.regValue .rdx = 0x202fb8 := (g6.read (n := 64) (r := 2) (by simp)).trans ((g5.read (n := 64) (r := 2) (by simp)).trans ((g4.read (n := 64) (r := 2) (by simp)).trans ((g3.read (n := 64) (r := 2) (by simp)).trans ((g2.read (n := 64) (r := 2) (by simp)).trans ((g1.read (n := 64) (r := 2) (by simp)).trans (input))))))
  have addr7 : (AddrMode.base 2 (.d8 24)).addr t6 (Extracted.textAddress + BitVec.ofNat 64 (84998+3+(AddrMode.base 2 (.d8 24)).tail.length)) =
      0x202fb8 + 24 := by
    change t6.regValue .rdx + 24 = _
    rw [input7]
  obtain ⟨t7, a7, f7, ip7, v7, g7, m7⟩ :=
    frame_load_r64 ctx.outerBoundary f6 0x14c06 0x48 0
      (.base 2 (.d8 24)) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      ip6 (by decide) (by decide +kernel) (by
        rw [addr7]
        exact exponent_readable f6.loaded (offset := 24) (by decide))
  change AgreesExcept [.reg 0, .rip] t6 t7 at g7
  have value7 : (Operand.reg 0 : Operand 64).read t7 =
      BitVec.ofNat 64 (sqrtExponent / 2^(64*3)) := by
    rw [addr7] at v7
    exact v7.trans (exponent_memLoad_word f6.loaded 3 (by decide))
  have source8 : (Operand.reg 0 : Operand 64).read t7 =
      BitVec.ofNat 64 (sqrtExponent / 2^(64*3)) := by
    exact value7
  obtain ⟨t8, a8, f8, ip8, _, g8, m8⟩ :=
    frame_store_r64 ctx.toCalleePre f7 0x14c0a 0x330 (.d32 0x330)
      0x48 0 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip7 (by decide) (by decide +kernel)
  have memory8 : t8.external = memStore t7.external
      (exponentFrameBase s + 0x330)
      (BitVec.ofNat 64 (sqrtExponent / 2^(64*3))) := by
    exact m8.trans (congrArg (memStore t7.external _) source8)
  refine ⟨t8, (((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8), f8, ip8, ?_, ?_⟩
  · apply (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).mono
    intro c hc
    simp only [exponentCopyComponents, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with (((((((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)) |
      (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl)
    all_goals simp
  · simp only [memory8, m7, memory6, m5, memory4, memory3, m2, m1,
      exponentCopyMemory, List.foldl_cons, List.foldl_nil, BitVec.ofNat_eq_ofNat]

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
