import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Steps
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem round_start [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x k : Nat}
    (ctx : ExponentPre s boundary x) (frame : ExponentFrame s t)
    (hip : t.RIP = 0x115550) (hk : k < 4) (hindex : t.regValue .r13 = BitVec.ofNat 64 k) :
    ∃ u, Advances boundary 4 t u ∧ ExponentFrame s u ∧ u.RIP = 0x115565 ∧
      (Operand.reg 6 : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x10 + BitVec.ofNat 64 (8*k)) : Operand 64).read t ∧
      (Operand.reg 0 : Operand 64).read u = (Operand.reg 6 : Operand 64).read u ∧
      exponentWordAt u (exponentFrameBase s + 0x70) (t.regValue .r8) ∧
      exponentWordAt u (exponentFrameBase s + 0x2f0) (t.regValue .r9) ∧
      AgreesExcept [.mem (exponentFrameBase s + 0x70) 8,
        .mem (exponentFrameBase s + 0x2f0) 8, .reg 6, .reg 0, .rip] t u := by
  obtain ⟨t1, ha1, hf1, hi1, hv1, hs1⟩ := store_stack ctx frame
    0x15550 0x4c 0 (.sib 4 none 0 (.d8 0x70)) 0x70
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by unfold scratchOffset; omega)
      (by decide) (by decide +kernel) hip
  obtain ⟨t2, ha2, hf2, hi2, hv2, hs2⟩ := store_stack ctx hf1
    0x15555 0x4c 1 (.sib 4 none 0 (.d32 0x2f0)) 0x2f0
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by unfold scratchOffset; omega)
      (by decide) (by decide +kernel) hi1
  have hi15 : t2.regValue .r13 = BitVec.ofNat 64 k :=
    (hs2.read (n := 64) (r := 13) (by simp)).trans ((hs1.read (by simp)).trans hindex)
  have haddr : (AddrMode.sib 4 (some 13) 3 (.d8 0x10)).addr t2 0x115562 =
      exponentFrameBase s + 0x10 + BitVec.ofNat 64 (8*k) := by
    change t2.regValue .rsp + (t2.regValue .r13 <<< 3) + 0x10 = _
    rw [hf2.rsp, hi15]
    have hshift := (show ∀ k : Fin 4, BitVec.ofNat 64 k.val <<< 3 =
      BitVec.ofNat 64 (8*k.val) by decide +kernel) ⟨k, hk⟩
    rw [hshift, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (8*k)) 0x10,
      ← BitVec.add_assoc]
  have hread : MemReadable t2 ((AddrMode.sib 4 (some 13) 3 (.d8 0x10)).addr t2 0x115562) 8 := by
    rw [haddr]
    have hh := stack_readable ctx hf2 (offset := 0x10 + 8*k) (len := 8) (by omega) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hh
    exact hh
  obtain ⟨t3, ha3, hr3, he3⟩ :=
    (mov_r64_m64_effect_step 0x11555d 0x4a (by simp [RexWPrefix]) 6
      (.sib 4 (some 13) 3 (.d8 0x10)) (by constructor <;> decide) rfl rfl).advances
      (readyToStep hf2.machine hf2.bindingsSupported)
      (programText_slice (programLoaded_codeIn hf2.loaded) 0x1555d
        [0x4a,0x8b,0x74,0xec,0x10] (by decide) (by decide +kernel))
      ⟨hi2, hread⟩ (boundary_ne_program ctx.outerBoundary
        (inProgram_of_textOffset 0x15562 (by decide)))
  have hs3 : AgreesExcept [.reg 6, .rip] t2 t3 := he3.agrees
  have hf3 := hf2.of_registers hr3 hs3 (by simp) (by simp [Component.Covers])
  have hv3 : (Operand.reg 6 : Operand 64).read t3 =
      (Operand.mem (exponentFrameBase s + 0x10 + BitVec.ofNat 64 (8*k)) : Operand 64).read t2 := by
    have hh := he3.writes
    change (Operand.reg 6 : Operand 64).read t3 =
      (Operand.mem ((AddrMode.sib 4 (some 13) 3 (.d8 0x10)).addr t2 0x115562) : Operand 64).read t2 at hh
    rwa [haddr] at hh
  obtain ⟨u, ha4, hr4, he4⟩ :=
    (mov_r64_r64_effect_step 0x115562 0x48 0xf0 (by simp [RexWPrefix]) rfl).advances
      hr3 (programText_slice (programLoaded_codeIn hf3.loaded) 0x15562
        [0x48,0x89,0xf0] (by decide) (by decide +kernel)) he3.rip
      (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15565 (by decide)))
  have hs4 : AgreesExcept [.reg 0, .rip] t3 u := he4.agrees
  have hv4 : (Operand.reg 0 : Operand 64).read u = (Operand.reg 6 : Operand 64).read t3 := he4.writes
  refine ⟨u, ((ha1.trans ha2).trans ha3).trans ha4,
    hf3.of_registers hr4 hs4 (by simp) (by simp [Component.Covers]), he4.rip, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs4.read (by simp), hv3, BitVec.add_assoc]
    have h60 := (show ∀ k : Fin 4, OffsetsApart 0x2f0 8 (0x10 + BitVec.ofNat 64 (8*k.val)) 8 by
      unfold OffsetsApart
      decide +kernel) ⟨k, hk⟩
    have h2e0 := (show ∀ k : Fin 4, OffsetsApart 0x70 8 (0x10 + BitVec.ofNat 64 (8*k.val)) 8 by
      unfold OffsetsApart
      decide +kernel) ⟨k, hk⟩
    rw [word_of_store_apart hs2 h60, word_of_store_apart hs1 h2e0]
  · exact hv4.trans (hs4.read (n := 64) (r := 6) (by simp)).symm
  · change (Operand.mem (exponentFrameBase s + 0x70) : Operand 64).read u = _
    rw [word_of_registers hs4, word_of_registers hs3,
      word_of_store_apart hs2 (by unfold OffsetsApart; decide +kernel)]
    exact hv1
  · change (Operand.mem (exponentFrameBase s + 0x2f0) : Operand 64).read u = _
    rw [word_of_registers hs4, word_of_registers hs3]
    exact hv2.trans (hs1.read (n := 64) (r := 9) (by simp))
  · exact (((hs1.trans hs2).trans hs3).trans hs4).mono (by
      intro c hm
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      grind only)

end P256.Proofs.Sec1.SquareRoot.SquareFour
