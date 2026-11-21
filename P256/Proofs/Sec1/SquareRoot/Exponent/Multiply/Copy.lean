import P256.Proofs.Sec1.SquareRoot.Exponent.Multiply.Copy.Steps
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Movs.RepTriple

set_option autoImplicit false

open P256.Proofs.Field (MontgomeryAt)
open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot.ExponentMultiply

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_result [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x n y : Nat}
    (ctx : ExponentPre s boundary x) (h : ExponentPosition s t x n)
    (rip : t.RIP = 0x1158d2) (value : Field.MontgomeryAt t (exponentFrameBase s + 0x10) y) :
    ∃ u, Advances boundary 9 t u ∧ ExponentPosition s u x n ∧ u.RIP = 0x1154c0 ∧
      Field.MontgomeryAt u (exponentFrameBase s + 0x30) y := by
  have hp0 := h
  obtain ⟨t1, ha1, hf1, hi1, hw1, hg1⟩ :=
    Copy.load_stack ctx hp0.frame 0x158d2 0x48 0 (.sib 4 none 0 (.d8 40)) 40
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) rip
  change AgreesExcept [.reg 0, .rip] t t1 at hg1
  have hp1 := position_of_registers hp0 (readyToStep hf1.machine hf1.bindingsSupported)
    (hg1.mono (by simp [volatileComponents]))
  have hv1 : (Operand.reg 0 : Operand 64).read t1 =
      (Operand.mem (exponentFrameBase s + 40) : Operand 64).read t := by
    change (Operand.reg 0 : Operand 64).read t1 =
      (Operand.mem (exponentFrameBase s + 40) : Operand 64).read t at hw1
    rw [hw1]
  obtain ⟨t2, ha2, hf2, hi2, hw2, hg2⟩ :=
    Copy.store_stack ctx hp1.frame 0x158d7 0x48 0 (.sib 4 none 0 (.d8 72)) 72
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide)
      (by decide) (by decide +kernel) hi1
  have hp2 := Copy.position_of_store ctx hp1 hf2 hg2
    (by decide)
  have hv2 : (Operand.mem (exponentFrameBase s + 72) : Operand 64).read t2 =
      (Operand.mem (exponentFrameBase s + 40) : Operand 64).read t := by
    change (Operand.mem (exponentFrameBase s + 72) : Operand 64).read t2 =
      (Operand.reg 0 : Operand 64).read t1 at hw2
    rw [hw2]
    exact hv1
  obtain ⟨t3, ha3, hf3, hi3, hw3, hg3⟩ :=
    Copy.load_stack ctx hp2.frame 0x158dc 0x48 0 (.sib 4 none 0 (.d8 32)) 32
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) hi2
  change AgreesExcept [.reg 0, .rip] t2 t3 at hg3
  have hp3 := position_of_registers hp2 (readyToStep hf3.machine hf3.bindingsSupported)
    (hg3.mono (by simp [volatileComponents]))
  have hv3 : (Operand.reg 0 : Operand 64).read t3 =
      (Operand.mem (exponentFrameBase s + 32) : Operand 64).read t := by
    change (Operand.reg 0 : Operand 64).read t3 =
      (Operand.mem (exponentFrameBase s + 32) : Operand 64).read t2 at hw3
    rw [hw3]
    rw [Copy.word_of_store_apart (base := exponentFrameBase s) (a := 72) (b := 32) hg2 (by unfold OffsetsApart; decide +kernel)]
    rw [Copy.word_of_registers hg1]
  obtain ⟨t4, ha4, hf4, hi4, hw4, hg4⟩ :=
    Copy.store_stack ctx hp3.frame 0x158e1 0x48 0 (.sib 4 none 0 (.d8 64)) 64
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide)
      (by decide) (by decide +kernel) hi3
  have hp4 := Copy.position_of_store ctx hp3 hf4 hg4
    (by decide)
  have hv4 : (Operand.mem (exponentFrameBase s + 64) : Operand 64).read t4 =
      (Operand.mem (exponentFrameBase s + 32) : Operand 64).read t := by
    change (Operand.mem (exponentFrameBase s + 64) : Operand 64).read t4 =
      (Operand.reg 0 : Operand 64).read t3 at hw4
    rw [hw4]
    exact hv3
  obtain ⟨t5, ha5, hf5, hi5, hw5, hg5⟩ :=
    Copy.load_stack ctx hp4.frame 0x158e6 0x48 0 (.sib 4 none 0 (.d8 16)) 16
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) hi4
  change AgreesExcept [.reg 0, .rip] t4 t5 at hg5
  have hp5 := position_of_registers hp4 (readyToStep hf5.machine hf5.bindingsSupported)
    (hg5.mono (by simp [volatileComponents]))
  have hv5 : (Operand.reg 0 : Operand 64).read t5 =
      (Operand.mem (exponentFrameBase s + 16) : Operand 64).read t := by
    change (Operand.reg 0 : Operand 64).read t5 =
      (Operand.mem (exponentFrameBase s + 16) : Operand 64).read t4 at hw5
    rw [hw5]
    rw [Copy.word_of_store_apart (base := exponentFrameBase s) (a := 64) (b := 16) hg4 (by unfold OffsetsApart; decide +kernel)]
    rw [Copy.word_of_registers hg3]
    rw [Copy.word_of_store_apart (base := exponentFrameBase s) (a := 72) (b := 16) hg2 (by unfold OffsetsApart; decide +kernel)]
    rw [Copy.word_of_registers hg1]
  obtain ⟨t6, ha6, hf6, hi6, hw6, hg6⟩ :=
    Copy.load_stack ctx hp5.frame 0x158eb 0x48 1 (.sib 4 none 0 (.d8 24)) 24
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) hi5
  change AgreesExcept [.reg 1, .rip] t5 t6 at hg6
  have hp6 := position_of_registers hp5 (readyToStep hf6.machine hf6.bindingsSupported)
    (hg6.mono (by simp [volatileComponents]))
  have hv6 : (Operand.reg 1 : Operand 64).read t6 =
      (Operand.mem (exponentFrameBase s + 24) : Operand 64).read t := by
    change (Operand.reg 1 : Operand 64).read t6 =
      (Operand.mem (exponentFrameBase s + 24) : Operand 64).read t5 at hw6
    rw [hw6]
    rw [Copy.word_of_registers hg5]
    rw [Copy.word_of_store_apart (base := exponentFrameBase s) (a := 64) (b := 24) hg4 (by unfold OffsetsApart; decide +kernel)]
    rw [Copy.word_of_registers hg3]
    rw [Copy.word_of_store_apart (base := exponentFrameBase s) (a := 72) (b := 24) hg2 (by unfold OffsetsApart; decide +kernel)]
    rw [Copy.word_of_registers hg1]
  obtain ⟨t7, ha7, hf7, hi7, hw7, hg7⟩ :=
    Copy.store_stack ctx hp6.frame 0x158f0 0x48 1 (.sib 4 none 0 (.d8 56)) 56
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide)
      (by decide) (by decide +kernel) hi6
  have hp7 := Copy.position_of_store ctx hp6 hf7 hg7
    (by decide)
  have hv7 : (Operand.mem (exponentFrameBase s + 56) : Operand 64).read t7 =
      (Operand.mem (exponentFrameBase s + 24) : Operand 64).read t := by
    change (Operand.mem (exponentFrameBase s + 56) : Operand 64).read t7 =
      (Operand.reg 1 : Operand 64).read t6 at hw7
    rw [hw7]
    exact hv6
  obtain ⟨t8, ha8, hf8, hi8, hw8, hg8⟩ :=
    Copy.store_stack ctx hp7.frame 0x158f5 0x48 0 (.sib 4 none 0 (.d8 48)) 48
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide)
      (by decide) (by decide +kernel) hi7
  have hp8 := Copy.position_of_store ctx hp7 hf8 hg8
    (by decide)
  have hv8 : (Operand.mem (exponentFrameBase s + 48) : Operand 64).read t8 =
      (Operand.mem (exponentFrameBase s + 16) : Operand 64).read t := by
    change (Operand.mem (exponentFrameBase s + 48) : Operand 64).read t8 =
      (Operand.reg 0 : Operand 64).read t7 at hw8
    rw [hw8]
    rw [hg7.read (by simp), hg6.read (by simp)]
    exact hv5
  obtain ⟨t9, ha9, hr9, he9⟩ :=
    (jmp_rel32_effect_step 0x1158fa 0xfffffbc1 (by decide)).advances
      (readyToStep hp8.frame.machine hp8.frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn hp8.frame.loaded) 0x158fa [0xe9, 0xc1, 0xfb, 0xff, 0xff]
        (by decide +kernel) rfl) hi8
      (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x154c0 (by decide)))
  have hg9 : AgreesExcept [.rip] t8 t9 := he9.agrees
  have hp9 := position_of_registers hp8 hr9 (hg9.mono (by simp [volatileComponents]))
  have hout48 : (Operand.mem (exponentFrameBase s + 48) : Operand 64).read t9 =
      (Operand.mem (exponentFrameBase s + 16) : Operand 64).read t := by
    rw [Copy.word_of_registers hg9]
    exact hv8
  have hout56 : (Operand.mem (exponentFrameBase s + 56) : Operand 64).read t9 =
      (Operand.mem (exponentFrameBase s + 24) : Operand 64).read t := by
    rw [Copy.word_of_registers hg9]
    rw [Copy.word_of_store_apart (base := exponentFrameBase s) (a := 48) (b := 56) hg8 (by unfold OffsetsApart; decide +kernel)]
    exact hv7
  have hout64 : (Operand.mem (exponentFrameBase s + 64) : Operand 64).read t9 =
      (Operand.mem (exponentFrameBase s + 32) : Operand 64).read t := by
    rw [Copy.word_of_registers hg9]
    rw [Copy.word_of_store_apart (base := exponentFrameBase s) (a := 48) (b := 64) hg8 (by unfold OffsetsApart; decide +kernel)]
    rw [Copy.word_of_store_apart (base := exponentFrameBase s) (a := 56) (b := 64) hg7 (by unfold OffsetsApart; decide +kernel)]
    rw [Copy.word_of_registers hg6]
    rw [Copy.word_of_registers hg5]
    exact hv4
  have hout72 : (Operand.mem (exponentFrameBase s + 72) : Operand 64).read t9 =
      (Operand.mem (exponentFrameBase s + 40) : Operand 64).read t := by
    rw [Copy.word_of_registers hg9]
    rw [Copy.word_of_store_apart (base := exponentFrameBase s) (a := 48) (b := 72) hg8 (by unfold OffsetsApart; decide +kernel)]
    rw [Copy.word_of_store_apart (base := exponentFrameBase s) (a := 56) (b := 72) hg7 (by unfold OffsetsApart; decide +kernel)]
    rw [Copy.word_of_registers hg6]
    rw [Copy.word_of_registers hg5]
    rw [Copy.word_of_store_apart (base := exponentFrameBase s) (a := 64) (b := 72) hg4 (by unfold OffsetsApart; decide +kernel)]
    rw [Copy.word_of_registers hg3]
    exact hv2
  refine ⟨t9, (((((((ha1.trans ha2).trans ha3).trans ha4).trans ha5).trans ha6).trans ha7).trans ha8).trans ha9,
    hp9, he9.rip, value.1, value.2.1, ?_⟩
  intro i hi
  have hw : memLoad t9.external (exponentFrameBase s + 48 + BitVec.ofNat 64 (i/8*8)) 64 =
      memLoad t.external (exponentFrameBase s + 16 + BitVec.ofNat 64 (i/8*8)) 64 := by
    have hd : i/8 = 0 ∨ i/8 = 1 ∨ i/8 = 2 ∨ i/8 = 3 := by omega
    rcases hd with hd | hd | hd | hd
    · simpa [hd, Operand.read, BitVec.add_assoc] using hout48
    · simpa [hd, Operand.read, BitVec.add_assoc] using hout56
    · simpa [hd, Operand.read, BitVec.add_assoc] using hout64
    · simpa [hd, Operand.read, BitVec.add_assoc] using hout72
  have hb := memByte_of_memLoad_eq hw (i%8) (by omega)
  have heq : i/8*8+i%8=i := by omega
  simp only [add_ofNat_add_ofNat, heq] at hb
  obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.mp
    ((hp9.frame.stack_readable ctx (offset := 48) (len := 32) (by decide)).mem i hi)
  change t9.external[exponentFrameBase s + 48 + BitVec.ofNat 64 i]? = some b at hb'
  have hs := value.2.2 i hi
  have he : b = UInt8.ofNat ((y * 2^256 % P256.Spec.Operations.domain.p) / 256^i % 256) := by
    simpa only [memByte, PhysicalMemory.read, hb', hs, Option.getD_some] using hb
  exact hb'.trans (congrArg some he)

end P256.Proofs.Sec1.SquareRoot.ExponentMultiply
