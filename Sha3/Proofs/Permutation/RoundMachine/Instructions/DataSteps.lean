import Sha3.Proofs.Permutation.RoundMachine.Instructions.Data
import Sha3.Proofs.Permutation.RoundMachine.Instructions.Registers
import Sha3.Proofs.Permutation.RoundMachine.Instructions.Memory
import Sha3.Proofs.Permutation.RoundMachine.Semantics
import Sha3.Proofs.Permutation.LoadStore.Store.Normalize

namespace Sha3.Proofs.Permutation.RoundMachine

open X86 X86.Machine X86.UserProcess X86Proofs RoundAlgebra Sha3.Spec.Program

theorem DataStep.of_effect [Bindings] {copy : Copy} {pc next : Nat} {op : Instruction}
    {bytes : List UInt8} {pre : RamState → Prop} {effect : RamState → Effect}
    (hstep : StepEffect pre (codeRange (BitVec.ofNat 64 pc) bytes) effect)
    (hpre : ∀ sp rc s, DataPre copy sp rc pc op s → pre s)
    (heffect : ∀ sp rc s, DataPre copy sp rc pc op s →
      effect s = instructionEffect sp (BitVec.ofNat 64 next) rc op (effect s).flags s) :
    DataStep copy pc next op bytes := by
  intro sp rc s hready hcode hp
  obtain ⟨t, hrun, ht, he⟩ := hstep s hready hcode (hpre sp rc s hp)
  exact ⟨t, (effect s).flags, hrun, ht, heffect sp rc s hp ▸ he⟩

theorem RoundMemory.tables_offset {sp : BitVec 64} {s : RamState}
    (h : RoundMemory sp s) (offset : BitVec 64) (ho : offset.toNat + 8 ≤ 216) :
    ∀ i, i < 8 → ¬ InPageTables (sp + offset + BitVec.ofNat 64 i) := by
  intro i hi
  have ht := h.tables (offset.toNat + i) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    ← BitVec.add_assoc] using ht

theorem DataPre.stackLoadPre {copy : Copy} {sp rc : BitVec 64} {pc : Nat} {op : Instruction}
    {s : RamState} (h : DataPre copy sp rc pc op s) (offset : BitVec 64)
    (ho : offset.toNat + 8 ≤ 216) :
    LoadPre (BitVec.ofNat 64 pc)
      (fun s ↦ (Operand.reg 4 : Operand 64).read s + offset) 8 s := by
  refine ⟨h.rip, ?_⟩
  rw [h.stack]
  exact Store.readable_offset h.memory.readable ho

theorem DataPre.stackStorePre {copy : Copy} {sp rc : BitVec 64} {pc : Nat} {op : Instruction}
    {s : RamState} (h : DataPre copy sp rc pc op s) (offset : BitVec 64)
    (ho : offset.toNat + 8 ≤ 216) :
    StorePreReadable (BitVec.ofNat 64 pc)
      (fun s ↦ (Operand.reg 4 : Operand 64).read s + offset) 8 s := by
  refine ⟨h.stackLoadPre offset ho, ?_⟩
  simpa only [h.stack] using h.memory.tables_offset offset ho

theorem dataStep_1000f0 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 8) (.reg 14))
      [0x4c, 0x89, 0x74, 0x24, 0x08] := by
  apply DataStep.of_effect (step_1000f0 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 8 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 8) (.reg 14))
      (movM64R64Effect (BitVec.ofNat 64 pc) 14 (.sib 4 none 0 (.d8 0x8)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1000f5 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 64) (.reg 13))
      [0x4c, 0x89, 0x6c, 0x24, 0x40] := by
  apply DataStep.of_effect (step_1000f5 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 64 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 64) (.reg 13))
      (movM64R64Effect (BitVec.ofNat 64 pc) 13 (.sib 4 none 0 (.d8 0x40)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1000fa [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.stack 208) (.reg 2))
      [0x48, 0x89, 0x94, 0x24, 0xd0, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_1000fa (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 208 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.stack 208) (.reg 2))
      (movM64R64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d32 0xd0)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100102 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 2) (.stack 80))
      [0x48, 0x8b, 0x54, 0x24, 0x50] := by
  apply DataStep.of_effect (step_100102 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 80 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 2) (.stack 80))
      (movR64M64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d8 0x50)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100107 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.xor (.reg 2) (.stack 32))
      [0x48, 0x33, 0x54, 0x24, 0x20] := by
  apply DataStep.of_effect (step_100107 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 32 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.xor (.reg 2) (.stack 32))
      (xorR64M64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d8 0x20)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10010c [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 8) (.reg 5))
      [0x49, 0x89, 0xe8] := by
  apply DataStep.of_effect (step_10010c (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10010f [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 8) (.reg 0))
      [0x49, 0x31, 0xc0] := by
  apply DataStep.of_effect (step_10010f (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100112 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 8) (.reg 2))
      [0x49, 0x31, 0xd0] := by
  apply DataStep.of_effect (step_100112 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100115 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.reg 2) (.stack 128))
      [0x48, 0x8b, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_100115 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 128 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.reg 2) (.stack 128))
      (movR64M64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d32 0x80)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10011d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 2) (.reg 9))
      [0x4c, 0x31, 0xca] := by
  apply DataStep.of_effect (step_10011d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100120 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 6) (.reg 15))
      [0x4c, 0x89, 0xfe] := by
  apply DataStep.of_effect (step_100120 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100123 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 72) (.reg 15))
      [0x4c, 0x89, 0x7c, 0x24, 0x48] := by
  apply DataStep.of_effect (step_100123 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 72 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 72) (.reg 15))
      (movM64R64Effect (BitVec.ofNat 64 pc) 15 (.sib 4 none 0 (.d8 0x48)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100128 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 15) (.stack 96))
      [0x4c, 0x8b, 0x7c, 0x24, 0x60] := by
  apply DataStep.of_effect (step_100128 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 96 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 15) (.stack 96))
      (movR64M64Effect (BitVec.ofNat 64 pc) 15 (.sib 4 none 0 (.d8 0x60)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10012d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 15) (.reg 1))
      [0x49, 0x31, 0xcf] := by
  apply DataStep.of_effect (step_10012d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100130 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 15) (.reg 2))
      [0x49, 0x31, 0xd7] := by
  apply DataStep.of_effect (step_100130 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100133 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 2) (.reg 6))
      [0x48, 0x89, 0xf2] := by
  apply DataStep.of_effect (step_100133 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100136 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.xor (.reg 2) (.stack 88))
      [0x48, 0x33, 0x54, 0x24, 0x58] := by
  apply DataStep.of_effect (step_100136 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 88 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.xor (.reg 2) (.stack 88))
      (xorR64M64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d8 0x58)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10013b [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 6) (.reg 12))
      [0x4c, 0x89, 0xe6] := by
  apply DataStep.of_effect (step_10013b (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10013e [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.xor (.reg 6) (.stack 48))
      [0x48, 0x33, 0x74, 0x24, 0x30] := by
  apply DataStep.of_effect (step_10013e (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 48 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.xor (.reg 6) (.stack 48))
      (xorR64M64Effect (BitVec.ofNat 64 pc) 6 (.sib 4 none 0 (.d8 0x30)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100143 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 6) (.reg 2))
      [0x48, 0x31, 0xd6] := by
  apply DataStep.of_effect (step_100143 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100146 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 7) (.reg 3))
      [0x48, 0x89, 0xdf] := by
  apply DataStep.of_effect (step_100146 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100149 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.stack 152) (.reg 3))
      [0x48, 0x89, 0x9c, 0x24, 0x98, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_100149 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 152 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.stack 152) (.reg 3))
      (movM64R64Effect (BitVec.ofNat 64 pc) 3 (.sib 4 none 0 (.d32 0x98)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100151 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 3) (.reg 14))
      [0x4c, 0x89, 0xf3] := by
  apply DataStep.of_effect (step_100151 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100154 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.xor (.reg 3) (.stack 104))
      [0x48, 0x33, 0x5c, 0x24, 0x68] := by
  apply DataStep.of_effect (step_100154 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 104 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.xor (.reg 3) (.stack 104))
      (xorR64M64Effect (BitVec.ofNat 64 pc) 3 (.sib 4 none 0 (.d8 0x68)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100159 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 2) (.stack 56))
      [0x48, 0x8b, 0x54, 0x24, 0x38] := by
  apply DataStep.of_effect (step_100159 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 56 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 2) (.stack 56))
      (movR64M64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d8 0x38)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10015e [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 13) (.reg 0))
      [0x49, 0x89, 0xc5] := by
  apply DataStep.of_effect (step_10015e (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100161 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 0) (.reg 2))
      [0x48, 0x89, 0xd0] := by
  apply DataStep.of_effect (step_100161 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100164 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.xor (.reg 0) (.stack 120))
      [0x48, 0x33, 0x44, 0x24, 0x78] := by
  apply DataStep.of_effect (step_100164 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 120 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.xor (.reg 0) (.stack 120))
      (xorR64M64Effect (BitVec.ofNat 64 pc) 0 (.sib 4 none 0 (.d8 0x78)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100169 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 0) (.reg 3))
      [0x48, 0x31, 0xd8] := by
  apply DataStep.of_effect (step_100169 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10016c [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 3) (.reg 7))
      [0x48, 0x89, 0xfb] := by
  apply DataStep.of_effect (step_10016c (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10016f [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.xor (.reg 3) (.stack 0))
      [0x48, 0x33, 0x1c, 0x24] := by
  apply DataStep.of_effect (step_10016f (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 0 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 4) rc (.xor (.reg 3) (.stack 0))
      (xorR64M64Effect (BitVec.ofNat 64 pc) 3 (.sib 4 none 0 .none) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100173 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 7) (.stack 64))
      [0x48, 0x8b, 0x7c, 0x24, 0x40] := by
  apply DataStep.of_effect (step_100173 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 64 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 7) (.stack 64))
      (movR64M64Effect (BitVec.ofNat 64 pc) 7 (.sib 4 none 0 (.d8 0x40)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100178 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.xor (.reg 7) (.stack 112))
      [0x48, 0x33, 0x7c, 0x24, 0x70] := by
  apply DataStep.of_effect (step_100178 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 112 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.xor (.reg 7) (.stack 112))
      (xorR64M64Effect (BitVec.ofNat 64 pc) 7 (.sib 4 none 0 (.d8 0x70)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10017d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 7) (.reg 3))
      [0x48, 0x31, 0xdf] := by
  apply DataStep.of_effect (step_10017d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100180 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 3) (.stack 24))
      [0x48, 0x8b, 0x5c, 0x24, 0x18] := by
  apply DataStep.of_effect (step_100180 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 24 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 3) (.stack 24))
      (movR64M64Effect (BitVec.ofNat 64 pc) 3 (.sib 4 none 0 (.d8 0x18)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100185 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 8) (.reg 3))
      [0x49, 0x31, 0xd8] := by
  apply DataStep.of_effect (step_100185 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100188 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 10) (.reg 1))
      [0x49, 0x89, 0xca] := by
  apply DataStep.of_effect (step_100188 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10018b [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 1) (.stack 40))
      [0x48, 0x8b, 0x4c, 0x24, 0x28] := by
  apply DataStep.of_effect (step_10018b (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 40 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 1) (.stack 40))
      (movR64M64Effect (BitVec.ofNat 64 pc) 1 (.sib 4 none 0 (.d8 0x28)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100190 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 15) (.reg 1))
      [0x49, 0x31, 0xcf] := by
  apply DataStep.of_effect (step_100190 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100193 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 0) (.reg 11))
      [0x4c, 0x31, 0xd8] := by
  apply DataStep.of_effect (step_100193 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100196 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 2) (.reg 0))
      [0x48, 0x89, 0xc2] := by
  apply DataStep.of_effect (step_100196 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100199 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.rol (.reg 2) 1)
      [0x48, 0xd1, 0xc2] := by
  apply DataStep.of_effect (step_100199 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10019c [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 2) (.reg 15))
      [0x4c, 0x31, 0xfa] := by
  apply DataStep.of_effect (step_10019c (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10019f [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.rol (.reg 15) 1)
      [0x49, 0xd1, 0xc7] := by
  apply DataStep.of_effect (step_10019f (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1001a2 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 14) (.stack 16))
      [0x4c, 0x8b, 0x74, 0x24, 0x10] := by
  apply DataStep.of_effect (step_1001a2 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 16 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 14) (.stack 16))
      (movR64M64Effect (BitVec.ofNat 64 pc) 14 (.sib 4 none 0 (.d8 0x10)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1001a7 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 7) (.reg 14))
      [0x4c, 0x31, 0xf7] := by
  apply DataStep.of_effect (step_1001a7 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1001aa [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 15) (.reg 7))
      [0x49, 0x31, 0xff] := by
  apply DataStep.of_effect (step_1001aa (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1001ad [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 3) (.reg 15))
      [0x4c, 0x31, 0xfb] := by
  apply DataStep.of_effect (step_1001ad (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1001b0 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.stack 144) (.reg 3))
      [0x48, 0x89, 0x9c, 0x24, 0x90, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_1001b0 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 144 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.stack 144) (.reg 3))
      (movM64R64Effect (BitVec.ofNat 64 pc) 3 (.sib 4 none 0 (.d32 0x90)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1001b8 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.xor (.stack 32) (.reg 15))
      [0x4c, 0x31, 0x7c, 0x24, 0x20] := by
  apply DataStep.of_effect (step_1001b8 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 32 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.xor (.stack 32) (.reg 15))
      (xorMREffect (BitVec.ofNat 64 pc) 5 64 15 (.sib 4 none 0 (.d8 0x20)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1001bd [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 13) (.reg 15))
      [0x4d, 0x31, 0xfd] := by
  apply DataStep.of_effect (step_1001bd (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1001c0 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.stack 192) (.reg 13))
      [0x4c, 0x89, 0xac, 0x24, 0xc0, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_1001c0 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 192 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.stack 192) (.reg 13))
      (movM64R64Effect (BitVec.ofNat 64 pc) 13 (.sib 4 none 0 (.d32 0xc0)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1001c8 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 5) (.reg 15))
      [0x4c, 0x31, 0xfd] := by
  apply DataStep.of_effect (step_1001c8 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1001cb [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.xor (.reg 15) (.stack 80))
      [0x4c, 0x33, 0x7c, 0x24, 0x50] := by
  apply DataStep.of_effect (step_1001cb (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 80 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.xor (.reg 15) (.stack 80))
      (xorR64M64Effect (BitVec.ofNat 64 pc) 15 (.sib 4 none 0 (.d8 0x50)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1001d0 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.stack 200) (.reg 15))
      [0x4c, 0x89, 0xbc, 0x24, 0xc8, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_1001d0 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 200 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.stack 200) (.reg 15))
      (movM64R64Effect (BitVec.ofNat 64 pc) 15 (.sib 4 none 0 (.d32 0xc8)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1001d8 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.reg 15) (.stack 136))
      [0x4c, 0x8b, 0xbc, 0x24, 0x88, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_1001d8 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 136 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.reg 15) (.stack 136))
      (movR64M64Effect (BitVec.ofNat 64 pc) 15 (.sib 4 none 0 (.d32 0x88)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1001e0 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 6) (.reg 15))
      [0x4c, 0x31, 0xfe] := by
  apply DataStep.of_effect (step_1001e0 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1001e3 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.rol (.reg 7) 1)
      [0x48, 0xd1, 0xc7] := by
  apply DataStep.of_effect (step_1001e3 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1001e6 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 7) (.reg 6))
      [0x48, 0x31, 0xf7] := by
  apply DataStep.of_effect (step_1001e6 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1001e9 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.rol (.reg 6) 1)
      [0x48, 0xd1, 0xc6] := by
  apply DataStep.of_effect (step_1001e9 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1001ec [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 6) (.reg 8))
      [0x4c, 0x31, 0xc6] := by
  apply DataStep.of_effect (step_1001ec (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1001ef [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.reg 3) (.stack 128))
      [0x48, 0x8b, 0x9c, 0x24, 0x80, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_1001ef (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 128 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.reg 3) (.stack 128))
      (movR64M64Effect (BitVec.ofNat 64 pc) 3 (.sib 4 none 0 (.d32 0x80)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1001f7 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 3) (.reg 6))
      [0x48, 0x31, 0xf3] := by
  apply DataStep.of_effect (step_1001f7 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1001fa [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 9) (.reg 6))
      [0x49, 0x31, 0xf1] := by
  apply DataStep.of_effect (step_1001fa (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1001fd [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 1) (.reg 6))
      [0x48, 0x31, 0xf1] := by
  apply DataStep.of_effect (step_1001fd (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100200 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 40) (.reg 1))
      [0x48, 0x89, 0x4c, 0x24, 0x28] := by
  apply DataStep.of_effect (step_100200 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 40 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 40) (.reg 1))
      (movM64R64Effect (BitVec.ofNat 64 pc) 1 (.sib 4 none 0 (.d8 0x28)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100205 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 10) (.reg 6))
      [0x49, 0x31, 0xf2] := by
  apply DataStep.of_effect (step_100205 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100208 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.stack 184) (.reg 10))
      [0x4c, 0x89, 0x94, 0x24, 0xb8, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_100208 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 184 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.stack 184) (.reg 10))
      (movM64R64Effect (BitVec.ofNat 64 pc) 10 (.sib 4 none 0 (.d32 0xb8)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100210 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.xor (.reg 6) (.stack 96))
      [0x48, 0x33, 0x74, 0x24, 0x60] := by
  apply DataStep.of_effect (step_100210 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 96 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.xor (.reg 6) (.stack 96))
      (xorR64M64Effect (BitVec.ofNat 64 pc) 6 (.sib 4 none 0 (.d8 0x60)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100215 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 15) (.reg 2))
      [0x49, 0x31, 0xd7] := by
  apply DataStep.of_effect (step_100215 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100218 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.xor (.stack 48) (.reg 2))
      [0x48, 0x31, 0x54, 0x24, 0x30] := by
  apply DataStep.of_effect (step_100218 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 48 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.xor (.stack 48) (.reg 2))
      (xorMREffect (BitVec.ofNat 64 pc) 5 64 2 (.sib 4 none 0 (.d8 0x30)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10021d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 12) (.reg 2))
      [0x49, 0x31, 0xd4] := by
  apply DataStep.of_effect (step_10021d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100220 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.xor (.stack 72) (.reg 2))
      [0x48, 0x31, 0x54, 0x24, 0x48] := by
  apply DataStep.of_effect (step_100220 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 72 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.xor (.stack 72) (.reg 2))
      (xorMREffect (BitVec.ofNat 64 pc) 5 64 2 (.sib 4 none 0 (.d8 0x48)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100225 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.xor (.reg 2) (.stack 88))
      [0x48, 0x33, 0x54, 0x24, 0x58] := by
  apply DataStep.of_effect (step_100225 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 88 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.xor (.reg 2) (.stack 88))
      (xorR64M64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d8 0x58)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10022a [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 13) (.reg 2))
      [0x49, 0x89, 0xd5] := by
  apply DataStep.of_effect (step_10022a (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10022d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 10) (.stack 120))
      [0x4c, 0x8b, 0x54, 0x24, 0x78] := by
  apply DataStep.of_effect (step_10022d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 120 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 10) (.stack 120))
      (movR64M64Effect (BitVec.ofNat 64 pc) 10 (.sib 4 none 0 (.d8 0x78)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100232 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 10) (.reg 7))
      [0x49, 0x31, 0xfa] := by
  apply DataStep.of_effect (step_100232 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100235 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 11) (.reg 7))
      [0x49, 0x31, 0xfb] := by
  apply DataStep.of_effect (step_100235 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100238 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.xor (.stack 56) (.reg 7))
      [0x48, 0x31, 0x7c, 0x24, 0x38] := by
  apply DataStep.of_effect (step_100238 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 56 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.xor (.stack 56) (.reg 7))
      (xorMREffect (BitVec.ofNat 64 pc) 5 64 7 (.sib 4 none 0 (.d8 0x38)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10023d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 2) (.stack 8))
      [0x48, 0x8b, 0x54, 0x24, 0x08] := by
  apply DataStep.of_effect (step_10023d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 8 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 2) (.stack 8))
      (movR64M64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d8 0x8)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100242 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 2) (.reg 7))
      [0x48, 0x31, 0xfa] := by
  apply DataStep.of_effect (step_100242 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100245 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.rol (.reg 8) 1)
      [0x49, 0xd1, 0xc0] := by
  apply DataStep.of_effect (step_100245 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100248 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.xor (.reg 7) (.stack 104))
      [0x48, 0x33, 0x7c, 0x24, 0x68] := by
  apply DataStep.of_effect (step_100248 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 104 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.xor (.reg 7) (.stack 104))
      (xorR64M64Effect (BitVec.ofNat 64 pc) 7 (.sib 4 none 0 (.d8 0x68)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10024d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 8) (.reg 7))
      [0x48, 0x89, 0x7c, 0x24, 0x08] := by
  apply DataStep.of_effect (step_10024d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 8 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 8) (.reg 7))
      (movM64R64Effect (BitVec.ofNat 64 pc) 7 (.sib 4 none 0 (.d8 0x8)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100252 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 8) (.reg 0))
      [0x49, 0x31, 0xc0] := by
  apply DataStep.of_effect (step_100252 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100255 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 0) (.stack 112))
      [0x48, 0x8b, 0x44, 0x24, 0x70] := by
  apply DataStep.of_effect (step_100255 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 112 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 0) (.stack 112))
      (movR64M64Effect (BitVec.ofNat 64 pc) 0 (.sib 4 none 0 (.d8 0x70)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10025a [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 0) (.reg 8))
      [0x4c, 0x31, 0xc0] := by
  apply DataStep.of_effect (step_10025a (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10025d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 14) (.reg 8))
      [0x4d, 0x31, 0xc6] := by
  apply DataStep.of_effect (step_10025d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100260 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 16) (.reg 14))
      [0x4c, 0x89, 0x74, 0x24, 0x10] := by
  apply DataStep.of_effect (step_100260 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 16 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 16) (.reg 14))
      (movM64R64Effect (BitVec.ofNat 64 pc) 14 (.sib 4 none 0 (.d8 0x10)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100265 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 7) (.stack 64))
      [0x48, 0x8b, 0x7c, 0x24, 0x40] := by
  apply DataStep.of_effect (step_100265 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 64 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 7) (.stack 64))
      (movR64M64Effect (BitVec.ofNat 64 pc) 7 (.sib 4 none 0 (.d8 0x40)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10026a [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 7) (.reg 8))
      [0x4c, 0x31, 0xc7] := by
  apply DataStep.of_effect (step_10026a (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10026d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.xor (.stack 152) (.reg 8))
      [0x4c, 0x31, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_10026d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 152 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.xor (.stack 152) (.reg 8))
      (xorMREffect (BitVec.ofNat 64 pc) 8 64 8 (.sib 4 none 0 (.d32 0x98)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100275 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 2) 21)
      [0x48, 0xc1, 0xc2, 0x15] := by
  apply DataStep.of_effect (step_100275 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100279 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.xor (.reg 8) (.stack 0))
      [0x4c, 0x33, 0x04, 0x24] := by
  apply DataStep.of_effect (step_100279 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 0 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 4) rc (.xor (.reg 8) (.stack 0))
      (xorR64M64Effect (BitVec.ofNat 64 pc) 8 (.sib 4 none 0 .none) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10027d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 11) 55)
      [0x49, 0xc1, 0xc3, 0x37] := by
  apply DataStep.of_effect (step_10027d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100281 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 6) 2)
      [0x48, 0xc1, 0xc6, 0x02] := by
  apply DataStep.of_effect (step_100281 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100285 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 8) 14)
      [0x49, 0xc1, 0xc0, 0x0e] := by
  apply DataStep.of_effect (step_100285 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100289 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 5) 41)
      [0x48, 0xc1, 0xc5, 0x29] := by
  apply DataStep.of_effect (step_100289 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10028d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 64) (.reg 3))
      [0x48, 0x89, 0x5c, 0x24, 0x40] := by
  apply DataStep.of_effect (step_10028d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 64 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 64) (.reg 3))
      (movM64R64Effect (BitVec.ofNat 64 pc) 3 (.sib 4 none 0 (.d8 0x40)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100292 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 12) 43)
      [0x49, 0xc1, 0xc4, 0x2b] := by
  apply DataStep.of_effect (step_100292 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100296 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 1) (.reg 15))
      [0x4c, 0x89, 0xf9] := by
  apply DataStep.of_effect (step_100296 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100299 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 1) 62)
      [0x48, 0xc1, 0xc1, 0x3e] := by
  apply DataStep.of_effect (step_100299 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10029d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 7) 39)
      [0x48, 0xc1, 0xc7, 0x27] := by
  apply DataStep.of_effect (step_10029d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002a1 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.stack 176) (.reg 0))
      [0x48, 0x89, 0x84, 0x24, 0xb0, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_1002a1 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 176 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.stack 176) (.reg 0))
      (movM64R64Effect (BitVec.ofNat 64 pc) 0 (.sib 4 none 0 (.d32 0xb0)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1002a9 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 9) 44)
      [0x49, 0xc1, 0xc1, 0x2c] := by
  apply DataStep.of_effect (step_1002a9 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002ad [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 0) (.reg 9))
      [0x4c, 0x89, 0xc8] := by
  apply DataStep.of_effect (step_1002ad (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002b0 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 0))
      [0x48, 0xf7, 0xd0] := by
  apply DataStep.of_effect (step_1002b0 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002b3 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 0) (.reg 12))
      [0x4c, 0x21, 0xe0] := by
  apply DataStep.of_effect (step_1002b3 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002b6 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 24) (.reg 0))
      [0x48, 0x89, 0x44, 0x24, 0x18] := by
  apply DataStep.of_effect (step_1002b6 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 24 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 24) (.reg 0))
      (movM64R64Effect (BitVec.ofNat 64 pc) 0 (.sib 4 none 0 (.d8 0x18)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1002bb [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 0) (.reg 2))
      [0x48, 0x89, 0xd0] := by
  apply DataStep.of_effect (step_1002bb (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002be [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 2))
      [0x48, 0xf7, 0xd2] := by
  apply DataStep.of_effect (step_1002be (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002c1 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 2) (.reg 8))
      [0x4c, 0x21, 0xc2] := by
  apply DataStep.of_effect (step_1002c1 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002c4 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 2) (.reg 12))
      [0x4c, 0x31, 0xe2] := by
  apply DataStep.of_effect (step_1002c4 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002c7 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.stack 136) (.reg 2))
      [0x48, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_1002c7 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 136 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.stack 136) (.reg 2))
      (movM64R64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d32 0x88)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1002cf [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 12))
      [0x49, 0xf7, 0xd4] := by
  apply DataStep.of_effect (step_1002cf (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002d2 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 12) (.reg 0))
      [0x49, 0x21, 0xc4] := by
  apply DataStep.of_effect (step_1002d2 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002d5 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 14) (.reg 0))
      [0x49, 0x89, 0xc6] := by
  apply DataStep.of_effect (step_1002d5 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002d8 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 12) (.reg 9))
      [0x4d, 0x31, 0xcc] := by
  apply DataStep.of_effect (step_1002d8 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002db [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.stack 128) (.reg 12))
      [0x4c, 0x89, 0xa4, 0x24, 0x80, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_1002db (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 128 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.stack 128) (.reg 12))
      (movM64R64Effect (BitVec.ofNat 64 pc) 12 (.sib 4 none 0 (.d32 0x80)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1002e3 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.reg 12) (.stack 144))
      [0x4c, 0x8b, 0xa4, 0x24, 0x90, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_1002e3 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 144 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.reg 12) (.stack 144))
      (movR64M64Effect (BitVec.ofNat 64 pc) 12 (.sib 4 none 0 (.d32 0x90)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1002eb [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 3) (.reg 12))
      [0x4c, 0x89, 0xe3] := by
  apply DataStep.of_effect (step_1002eb (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002ee [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 3))
      [0x48, 0xf7, 0xd3] := by
  apply DataStep.of_effect (step_1002ee (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002f1 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 3) (.reg 9))
      [0x4c, 0x21, 0xcb] := by
  apply DataStep.of_effect (step_1002f1 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002f4 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 2) (.reg 11))
      [0x4c, 0x89, 0xda] := by
  apply DataStep.of_effect (step_1002f4 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002f7 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 2))
      [0x48, 0xf7, 0xd2] := by
  apply DataStep.of_effect (step_1002f7 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002fa [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 2) (.reg 7))
      [0x48, 0x21, 0xfa] := by
  apply DataStep.of_effect (step_1002fa (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1002fd [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 2) (.reg 1))
      [0x48, 0x31, 0xca] := by
  apply DataStep.of_effect (step_1002fd (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100300 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 80) (.reg 2))
      [0x48, 0x89, 0x54, 0x24, 0x50] := by
  apply DataStep.of_effect (step_100300 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 80 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 80) (.reg 2))
      (movM64R64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d8 0x50)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100305 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 2) (.reg 5))
      [0x48, 0x89, 0xea] := by
  apply DataStep.of_effect (step_100305 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100308 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 2))
      [0x48, 0xf7, 0xd2] := by
  apply DataStep.of_effect (step_100308 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10030b [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.stack 168) (.reg 6))
      [0x48, 0x89, 0xb4, 0x24, 0xa8, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_10030b (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 168 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.stack 168) (.reg 6))
      (movM64R64Effect (BitVec.ofNat 64 pc) 6 (.sib 4 none 0 (.d32 0xa8)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100313 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 2) (.reg 6))
      [0x48, 0x21, 0xf2] := by
  apply DataStep.of_effect (step_100313 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100316 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 2) (.reg 7))
      [0x48, 0x31, 0xfa] := by
  apply DataStep.of_effect (step_100316 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100319 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 88) (.reg 2))
      [0x48, 0x89, 0x54, 0x24, 0x58] := by
  apply DataStep.of_effect (step_100319 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 88 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 88) (.reg 2))
      (movM64R64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d8 0x58)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10031e [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 15) (.reg 7))
      [0x49, 0x89, 0xff] := by
  apply DataStep.of_effect (step_10031e (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100321 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 15))
      [0x49, 0xf7, 0xd7] := by
  apply DataStep.of_effect (step_100321 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100324 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 15) (.reg 5))
      [0x49, 0x21, 0xef] := by
  apply DataStep.of_effect (step_100324 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100327 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 15) (.reg 11))
      [0x4d, 0x31, 0xdf] := by
  apply DataStep.of_effect (step_100327 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10032a [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 96) (.reg 15))
      [0x4c, 0x89, 0x7c, 0x24, 0x60] := by
  apply DataStep.of_effect (step_10032a (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 96 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 96) (.reg 15))
      (movM64R64Effect (BitVec.ofNat 64 pc) 15 (.sib 4 none 0 (.d8 0x60)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10032f [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 7) (.reg 6))
      [0x48, 0x89, 0xf7] := by
  apply DataStep.of_effect (step_10032f (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100332 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 7))
      [0x48, 0xf7, 0xd7] := by
  apply DataStep.of_effect (step_100332 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100335 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 7) (.reg 1))
      [0x48, 0x21, 0xcf] := by
  apply DataStep.of_effect (step_100335 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100338 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 1))
      [0x48, 0xf7, 0xd1] := by
  apply DataStep.of_effect (step_100338 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10033b [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 1) (.reg 11))
      [0x4c, 0x21, 0xd9] := by
  apply DataStep.of_effect (step_10033b (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10033e [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.mov (.stack 0) (.reg 1))
      [0x48, 0x89, 0x0c, 0x24] := by
  apply DataStep.of_effect (step_10033e (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 0 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 4) rc (.mov (.stack 0) (.reg 1))
      (movM64R64Effect (BitVec.ofNat 64 pc) 1 (.sib 4 none 0 .none) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100342 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.reg 0) (.stack 192))
      [0x48, 0x8b, 0x84, 0x24, 0xc0, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_100342 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 192 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.reg 0) (.stack 192))
      (movR64M64Effect (BitVec.ofNat 64 pc) 0 (.sib 4 none 0 (.d32 0xc0)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10034a [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 0) 3)
      [0x48, 0xc1, 0xc0, 0x03] := by
  apply DataStep.of_effect (step_10034a (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10034e [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 6) (.reg 10))
      [0x4c, 0x89, 0xd6] := by
  apply DataStep.of_effect (step_10034e (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100351 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 6) 28)
      [0x48, 0xc1, 0xc6, 0x1c] := by
  apply DataStep.of_effect (step_100351 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100355 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 1) (.stack 32))
      [0x48, 0x8b, 0x4c, 0x24, 0x20] := by
  apply DataStep.of_effect (step_100355 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 32 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 1) (.stack 32))
      (movR64M64Effect (BitVec.ofNat 64 pc) 1 (.sib 4 none 0 (.d8 0x20)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10035a [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.reg 10) (.stack 184))
      [0x4c, 0x8b, 0x94, 0x24, 0xb8, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_10035a (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 184 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.reg 10) (.stack 184))
      (movR64M64Effect (BitVec.ofNat 64 pc) 10 (.sib 4 none 0 (.d32 0xb8)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100362 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 10) 45)
      [0x49, 0xc1, 0xc2, 0x2d] := by
  apply DataStep.of_effect (step_100362 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100366 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 13) 61)
      [0x49, 0xc1, 0xc5, 0x3d] := by
  apply DataStep.of_effect (step_100366 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10036a [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 15) (.stack 16))
      [0x4c, 0x8b, 0x7c, 0x24, 0x10] := by
  apply DataStep.of_effect (step_10036a (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 16 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 15) (.stack 16))
      (movR64M64Effect (BitVec.ofNat 64 pc) 15 (.sib 4 none 0 (.d8 0x10)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10036f [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 15) 20)
      [0x49, 0xc1, 0xc7, 0x14] := by
  apply DataStep.of_effect (step_10036f (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100373 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 9) (.reg 15))
      [0x4d, 0x89, 0xf9] := by
  apply DataStep.of_effect (step_100373 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100376 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 9))
      [0x49, 0xf7, 0xd1] := by
  apply DataStep.of_effect (step_100376 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100379 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 9) (.reg 0))
      [0x49, 0x21, 0xc1] := by
  apply DataStep.of_effect (step_100379 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10037c [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 9) (.reg 6))
      [0x49, 0x31, 0xf1] := by
  apply DataStep.of_effect (step_10037c (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10037f [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 32) (.reg 9))
      [0x4c, 0x89, 0x4c, 0x24, 0x20] := by
  apply DataStep.of_effect (step_10037f (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 32 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 32) (.reg 9))
      (movM64R64Effect (BitVec.ofNat 64 pc) 9 (.sib 4 none 0 (.d8 0x20)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100384 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 9) (.reg 0))
      [0x49, 0x89, 0xc1] := by
  apply DataStep.of_effect (step_100384 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100387 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 9))
      [0x49, 0xf7, 0xd1] := by
  apply DataStep.of_effect (step_100387 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10038a [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 9) (.reg 10))
      [0x4d, 0x21, 0xd1] := by
  apply DataStep.of_effect (step_10038a (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10038d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 9) (.reg 15))
      [0x4d, 0x31, 0xf9] := by
  apply DataStep.of_effect (step_10038d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100390 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 11) (.reg 13))
      [0x4d, 0x89, 0xeb] := by
  apply DataStep.of_effect (step_100390 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100393 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 11))
      [0x49, 0xf7, 0xd3] := by
  apply DataStep.of_effect (step_100393 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100396 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 11) (.reg 6))
      [0x49, 0x21, 0xf3] := by
  apply DataStep.of_effect (step_100396 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100399 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 6))
      [0x48, 0xf7, 0xd6] := by
  apply DataStep.of_effect (step_100399 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10039c [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 15) (.reg 6))
      [0x49, 0x21, 0xf7] := by
  apply DataStep.of_effect (step_10039c (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10039f [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 6) (.reg 8))
      [0x4c, 0x89, 0xc6] := by
  apply DataStep.of_effect (step_10039f (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003a2 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 6))
      [0x48, 0xf7, 0xd6] := by
  apply DataStep.of_effect (step_1003a2 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003a5 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 6) (.reg 12))
      [0x4c, 0x21, 0xe6] := by
  apply DataStep.of_effect (step_1003a5 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003a8 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 6) (.reg 14))
      [0x4c, 0x31, 0xf6] := by
  apply DataStep.of_effect (step_1003a8 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003ab [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 120) (.reg 6))
      [0x48, 0x89, 0x74, 0x24, 0x78] := by
  apply DataStep.of_effect (step_1003ab (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 120 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 120) (.reg 6))
      (movM64R64Effect (BitVec.ofNat 64 pc) 6 (.sib 4 none 0 (.d8 0x78)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1003b0 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 3) (.reg 8))
      [0x4c, 0x31, 0xc3] := by
  apply DataStep.of_effect (step_1003b0 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003b3 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 112) (.reg 3))
      [0x48, 0x89, 0x5c, 0x24, 0x70] := by
  apply DataStep.of_effect (step_1003b3 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 112 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 112) (.reg 3))
      (movM64R64Effect (BitVec.ofNat 64 pc) 3 (.sib 4 none 0 (.d8 0x70)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1003b8 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 6) (.stack 48))
      [0x48, 0x8b, 0x74, 0x24, 0x30] := by
  apply DataStep.of_effect (step_1003b8 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 48 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 6) (.stack 48))
      (movR64M64Effect (BitVec.ofNat 64 pc) 6 (.sib 4 none 0 (.d8 0x30)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1003bd [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 3) (.reg 10))
      [0x4c, 0x89, 0xd3] := by
  apply DataStep.of_effect (step_1003bd (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003c0 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 3))
      [0x48, 0xf7, 0xd3] := by
  apply DataStep.of_effect (step_1003c0 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003c3 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 3) (.reg 13))
      [0x4c, 0x21, 0xeb] := by
  apply DataStep.of_effect (step_1003c3 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003c6 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 3) (.reg 0))
      [0x48, 0x31, 0xc3] := by
  apply DataStep.of_effect (step_1003c6 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003c9 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 48) (.reg 3))
      [0x48, 0x89, 0x5c, 0x24, 0x30] := by
  apply DataStep.of_effect (step_1003c9 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 48 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 48) (.reg 3))
      (movM64R64Effect (BitVec.ofNat 64 pc) 3 (.sib 4 none 0 (.d8 0x30)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1003ce [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 11) (.reg 10))
      [0x4d, 0x31, 0xd3] := by
  apply DataStep.of_effect (step_1003ce (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003d1 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 15) (.reg 13))
      [0x4d, 0x31, 0xef] := by
  apply DataStep.of_effect (step_1003d1 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003d4 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 16) (.reg 15))
      [0x4c, 0x89, 0x7c, 0x24, 0x10] := by
  apply DataStep.of_effect (step_1003d4 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 16 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 16) (.reg 15))
      (movM64R64Effect (BitVec.ofNat 64 pc) 15 (.sib 4 none 0 (.d8 0x10)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1003d9 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 7) (.reg 5))
      [0x48, 0x31, 0xef] := by
  apply DataStep.of_effect (step_1003d9 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003dc [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 104) (.reg 7))
      [0x48, 0x89, 0x7c, 0x24, 0x68] := by
  apply DataStep.of_effect (step_1003dc (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 104 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 104) (.reg 7))
      (movM64R64Effect (BitVec.ofNat 64 pc) 7 (.sib 4 none 0 (.d8 0x68)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1003e1 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 0) (.stack 40))
      [0x48, 0x8b, 0x44, 0x24, 0x28] := by
  apply DataStep.of_effect (step_1003e1 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 40 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 0) (.stack 40))
      (movR64M64Effect (BitVec.ofNat 64 pc) 0 (.sib 4 none 0 (.d8 0x28)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1003e6 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 0) 10)
      [0x48, 0xc1, 0xc0, 0x0a] := by
  apply DataStep.of_effect (step_1003e6 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003ea [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 3) (.stack 72))
      [0x48, 0x8b, 0x5c, 0x24, 0x48] := by
  apply DataStep.of_effect (step_1003ea (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 72 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 3) (.stack 72))
      (movR64M64Effect (BitVec.ofNat 64 pc) 3 (.sib 4 none 0 (.d8 0x48)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1003ef [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 3) 15)
      [0x48, 0xc1, 0xc3, 0x0f] := by
  apply DataStep.of_effect (step_1003ef (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003f3 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 5) (.reg 1))
      [0x48, 0x89, 0xcd] := by
  apply DataStep.of_effect (step_1003f3 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003f6 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 5) 36)
      [0x48, 0xc1, 0xc5, 0x24] := by
  apply DataStep.of_effect (step_1003f6 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1003fa [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 72) (.reg 5))
      [0x48, 0x89, 0x6c, 0x24, 0x48] := by
  apply DataStep.of_effect (step_1003fa (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 72 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 72) (.reg 5))
      (movM64R64Effect (BitVec.ofNat 64 pc) 5 (.sib 4 none 0 (.d8 0x48)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1003ff [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.reg 8) (.stack 176))
      [0x4c, 0x8b, 0x84, 0x24, 0xb0, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_1003ff (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 176 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.reg 8) (.stack 176))
      (movR64M64Effect (BitVec.ofNat 64 pc) 8 (.sib 4 none 0 (.d32 0xb0)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100407 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 8) 27)
      [0x49, 0xc1, 0xc0, 0x1b] := by
  apply DataStep.of_effect (step_100407 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10040b [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 2) (.stack 8))
      [0x48, 0x8b, 0x54, 0x24, 0x08] := by
  apply DataStep.of_effect (step_10040b (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 8 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 2) (.stack 8))
      (movR64M64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d8 0x8)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100410 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 2) 56)
      [0x48, 0xc1, 0xc2, 0x38] := by
  apply DataStep.of_effect (step_100410 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100414 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 8) (.reg 2))
      [0x48, 0x89, 0x54, 0x24, 0x08] := by
  apply DataStep.of_effect (step_100414 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 8 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 8) (.reg 2))
      (movM64R64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d8 0x8)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100419 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 5))
      [0x48, 0xf7, 0xd5] := by
  apply DataStep.of_effect (step_100419 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10041c [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 5) (.reg 0))
      [0x48, 0x21, 0xc5] := by
  apply DataStep.of_effect (step_10041c (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10041f [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 1) (.reg 0))
      [0x48, 0x89, 0xc1] := by
  apply DataStep.of_effect (step_10041f (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100422 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 1))
      [0x48, 0xf7, 0xd1] := by
  apply DataStep.of_effect (step_100422 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100425 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 1) (.reg 3))
      [0x48, 0x21, 0xd9] := by
  apply DataStep.of_effect (step_100425 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100428 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 14) (.reg 2))
      [0x49, 0x89, 0xd6] := by
  apply DataStep.of_effect (step_100428 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10042b [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 14))
      [0x49, 0xf7, 0xd6] := by
  apply DataStep.of_effect (step_10042b (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10042e [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 14) (.reg 8))
      [0x4d, 0x21, 0xc6] := by
  apply DataStep.of_effect (step_10042e (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100431 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 14) (.reg 3))
      [0x49, 0x31, 0xde] := by
  apply DataStep.of_effect (step_100431 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100434 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 15) (.reg 3))
      [0x49, 0x89, 0xdf] := by
  apply DataStep.of_effect (step_100434 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100437 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 15))
      [0x49, 0xf7, 0xd7] := by
  apply DataStep.of_effect (step_100437 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10043a [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 15) (.reg 2))
      [0x49, 0x21, 0xd7] := by
  apply DataStep.of_effect (step_10043a (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10043d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 15) (.reg 0))
      [0x49, 0x31, 0xc7] := by
  apply DataStep.of_effect (step_10043d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100440 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 2) (.stack 64))
      [0x48, 0x8b, 0x54, 0x24, 0x40] := by
  apply DataStep.of_effect (step_100440 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 64 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 2) (.stack 64))
      (movR64M64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d8 0x40)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100445 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.rol (.reg 2) 1)
      [0x48, 0xd1, 0xc2] := by
  apply DataStep.of_effect (step_100445 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100448 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 6) 6)
      [0x48, 0xc1, 0xc6, 0x06] := by
  apply DataStep.of_effect (step_100448 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10044c [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.reg 7) (.stack 152))
      [0x48, 0x8b, 0xbc, 0x24, 0x98, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_10044c (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 152 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.reg 7) (.stack 152))
      (movR64M64Effect (BitVec.ofNat 64 pc) 7 (.sib 4 none 0 (.d32 0x98)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100454 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 7) 8)
      [0x48, 0xc1, 0xc7, 0x08] := by
  apply DataStep.of_effect (step_100454 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100458 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 3) (.stack 56))
      [0x48, 0x8b, 0x5c, 0x24, 0x38] := by
  apply DataStep.of_effect (step_100458 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 56 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 3) (.stack 56))
      (movR64M64Effect (BitVec.ofNat 64 pc) 3 (.sib 4 none 0 (.d8 0x38)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_10045d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 3) 25)
      [0x48, 0xc1, 0xc3, 0x19] := by
  apply DataStep.of_effect (step_10045d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100461 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.reg 10) (.stack 200))
      [0x4c, 0x8b, 0x94, 0x24, 0xc8, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_100461 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 200 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.reg 10) (.stack 200))
      (movR64M64Effect (BitVec.ofNat 64 pc) 10 (.sib 4 none 0 (.d32 0xc8)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100469 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.rol (.reg 10) 18)
      [0x49, 0xc1, 0xc2, 0x12] := by
  apply DataStep.of_effect (step_100469 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10046d [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 0) (.reg 6))
      [0x48, 0x89, 0xf0] := by
  apply DataStep.of_effect (step_10046d (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100470 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 0))
      [0x48, 0xf7, 0xd0] := by
  apply DataStep.of_effect (step_100470 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100473 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 0) (.reg 3))
      [0x48, 0x21, 0xd8] := by
  apply DataStep.of_effect (step_100473 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100476 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 12) (.reg 7))
      [0x49, 0x89, 0xfc] := by
  apply DataStep.of_effect (step_100476 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100479 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 12))
      [0x49, 0xf7, 0xd4] := by
  apply DataStep.of_effect (step_100479 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10047c [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 12) (.reg 10))
      [0x4d, 0x21, 0xd4] := by
  apply DataStep.of_effect (step_10047c (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10047f [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 12) (.reg 3))
      [0x49, 0x31, 0xdc] := by
  apply DataStep.of_effect (step_10047f (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100482 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 3))
      [0x48, 0xf7, 0xd3] := by
  apply DataStep.of_effect (step_100482 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100485 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 3) (.reg 7))
      [0x48, 0x21, 0xfb] := by
  apply DataStep.of_effect (step_100485 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100488 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 13) (.reg 10))
      [0x4d, 0x89, 0xd5] := by
  apply DataStep.of_effect (step_100488 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10048b [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 13))
      [0x49, 0xf7, 0xd5] := by
  apply DataStep.of_effect (step_10048b (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10048e [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 13) (.reg 2))
      [0x49, 0x21, 0xd5] := by
  apply DataStep.of_effect (step_10048e (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100491 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 13) (.reg 7))
      [0x49, 0x31, 0xfd] := by
  apply DataStep.of_effect (step_100491 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_100494 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 56) (.reg 13))
      [0x4c, 0x89, 0x6c, 0x24, 0x38] := by
  apply DataStep.of_effect (step_100494 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 56 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 56) (.reg 13))
      (movM64R64Effect (BitVec.ofNat 64 pc) 13 (.sib 4 none 0 (.d8 0x38)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_100499 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 0) (.reg 2))
      [0x48, 0x31, 0xd0] := by
  apply DataStep.of_effect (step_100499 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10049c [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 3) (.reg 6))
      [0x48, 0x31, 0xf3] := by
  apply DataStep.of_effect (step_10049c (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_10049f [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 40) (.reg 3))
      [0x48, 0x89, 0x5c, 0x24, 0x28] := by
  apply DataStep.of_effect (step_10049f (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 40 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 40) (.reg 3))
      (movM64R64Effect (BitVec.ofNat 64 pc) 3 (.sib 4 none 0 (.d8 0x28)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1004a4 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 2))
      [0x48, 0xf7, 0xd2] := by
  apply DataStep.of_effect (step_1004a4 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1004a7 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 2) (.reg 6))
      [0x48, 0x21, 0xf2] := by
  apply DataStep.of_effect (step_1004a7 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1004aa [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 13) (.reg 2))
      [0x49, 0x89, 0xd5] := by
  apply DataStep.of_effect (step_1004aa (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1004ad [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 13) (.reg 10))
      [0x4d, 0x31, 0xd5] := by
  apply DataStep.of_effect (step_1004ad (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1004b0 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 5) (.reg 8))
      [0x4c, 0x31, 0xc5] := by
  apply DataStep.of_effect (step_1004b0 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1004b3 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 2) (.stack 72))
      [0x48, 0x8b, 0x54, 0x24, 0x48] := by
  apply DataStep.of_effect (step_1004b3 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 72 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 2) (.stack 72))
      (movR64M64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d8 0x48)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1004b8 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.xor (.reg 1) (.reg 2))
      [0x48, 0x31, 0xd1] := by
  apply DataStep.of_effect (step_1004b8 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1004bb [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.not (.reg 8))
      [0x49, 0xf7, 0xd0] := by
  apply DataStep.of_effect (step_1004bb (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1004be [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.and (.reg 8) (.reg 2))
      [0x49, 0x21, 0xd0] := by
  apply DataStep.of_effect (step_1004be (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1004c1 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.mov (.reg 2) (.stack 208))
      [0x48, 0x8b, 0x94, 0x24, 0xd0, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_1004c1 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 208 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.mov (.reg 2) (.stack 208))
      (movR64M64Effect (BitVec.ofNat 64 pc) 2 (.sib 4 none 0 (.d32 0xd0)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1004c9 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 3) (.mov (.reg 3) (.reg 8))
      [0x4c, 0x89, 0xc3] := by
  apply DataStep.of_effect (step_1004c9 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.rip
  · intros
    simp only [BitVec.ofNat_add]
    rfl

theorem dataStep_1004cc [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.xor (.reg 3) (.stack 8))
      [0x48, 0x33, 0x5c, 0x24, 0x08] := by
  apply DataStep.of_effect (step_1004cc (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 8 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.xor (.reg 3) (.stack 8))
      (xorR64M64Effect (BitVec.ofNat 64 pc) 3 (.sib 4 none 0 (.d8 0x8)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1004d1 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.reg 6) (.stack 24))
      [0x48, 0x8b, 0x74, 0x24, 0x18] := by
  apply DataStep.of_effect (step_1004d1 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 24 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.reg 6) (.stack 24))
      (movR64M64Effect (BitVec.ofNat 64 pc) 6 (.sib 4 none 0 (.d8 0x18)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1004d6 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 7) (.xorConstant (.reg 6))
      [0x48, 0x33, 0xb2, if copy = .absorb then 0x00 else 0xc0, 0x00, 0x20, 0x00] := by
  apply DataStep.of_effect (step_1004d6 copy (BitVec.ofNat 64 pc))
  · intro sp rc s hp
    cases copy <;> exact ⟨hp.rip, hp.constant.1⟩
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    have hc := hp.constant.2
    cases copy <;>
      change instructionEffect sp (BitVec.ofNat 64 pc + 7) _
        (.xorConstant (.reg 6)) _ s = _
    all_goals rw [← hc]; rfl

theorem dataStep_1004dd [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.mov (.reg 7) (.stack 0))
      [0x48, 0x8b, 0x3c, 0x24] := by
  apply DataStep.of_effect (step_1004dd (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 0 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 4) rc (.mov (.reg 7) (.stack 0))
      (movR64M64Effect (BitVec.ofNat 64 pc) 7 (.sib 4 none 0 .none) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1004e1 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.xor (.reg 7) (.stack 168))
      [0x48, 0x33, 0xbc, 0x24, 0xa8, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_1004e1 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 168 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.xor (.reg 7) (.stack 168))
      (xorR64M64Effect (BitVec.ofNat 64 pc) 7 (.sib 4 none 0 (.d32 0xa8)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1004e9 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 4) (.mov (.stack 0) (.reg 7))
      [0x48, 0x89, 0x3c, 0x24] := by
  apply DataStep.of_effect (step_1004e9 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 0 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 4) rc (.mov (.stack 0) (.reg 7))
      (movM64R64Effect (BitVec.ofNat 64 pc) 7 (.sib 4 none 0 .none) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1004ed [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 8) (.xor (.reg 6) (.stack 144))
      [0x48, 0x33, 0xb4, 0x24, 0x90, 0x00, 0x00, 0x00] := by
  apply DataStep.of_effect (step_1004ed (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackLoadPre 144 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 8) rc (.xor (.reg 6) (.stack 144))
      (xorR64M64Effect (BitVec.ofNat 64 pc) 6 (.sib 4 none 0 (.d32 0x90)) s).flags s = _
    rw [hp.stack]
    rfl

theorem dataStep_1004f5 [Bindings] (copy : Copy) (pc : Nat) :
    DataStep copy pc (pc + 5) (.mov (.stack 24) (.reg 6))
      [0x48, 0x89, 0x74, 0x24, 0x18] := by
  apply DataStep.of_effect (step_1004f5 (BitVec.ofNat 64 pc))
  · exact fun _ _ _ h ↦ h.stackStorePre 24 (by decide +kernel)
  · intro sp rc s hp
    simp only [BitVec.ofNat_add]
    change instructionEffect ((Operand.reg 4 : Operand 64).read s)
      (BitVec.ofNat 64 pc + 5) rc (.mov (.stack 24) (.reg 6))
      (movM64R64Effect (BitVec.ofNat 64 pc) 6 (.sib 4 none 0 (.d8 0x18)) s).flags s = _
    rw [hp.stack]
    rfl

set_option maxRecDepth 4096 in
private theorem dataSteps_0_64 [Bindings] (copy : Copy) (i : Fin 64) :
    let j := i.castAdd 193
    DataStep copy (dataPc copy j.castSucc) (dataPc copy j.succ) (dataOp j)
      (dataBytes copy j) := by
  cases copy <;> finite_cases i
  · exact dataStep_1000f0 .absorb _
  · exact dataStep_1000f5 .absorb _
  · exact dataStep_1000fa .absorb _
  · exact dataStep_100102 .absorb _
  · exact dataStep_100107 .absorb _
  · exact dataStep_10010c .absorb _
  · exact dataStep_10010f .absorb _
  · exact dataStep_100112 .absorb _
  · exact dataStep_100115 .absorb _
  · exact dataStep_10011d .absorb _
  · exact dataStep_100120 .absorb _
  · exact dataStep_100123 .absorb _
  · exact dataStep_100128 .absorb _
  · exact dataStep_10012d .absorb _
  · exact dataStep_100130 .absorb _
  · exact dataStep_100133 .absorb _
  · exact dataStep_100136 .absorb _
  · exact dataStep_10013b .absorb _
  · exact dataStep_10013e .absorb _
  · exact dataStep_100143 .absorb _
  · exact dataStep_100146 .absorb _
  · exact dataStep_100149 .absorb _
  · exact dataStep_100151 .absorb _
  · exact dataStep_100154 .absorb _
  · exact dataStep_100159 .absorb _
  · exact dataStep_10015e .absorb _
  · exact dataStep_100161 .absorb _
  · exact dataStep_100164 .absorb _
  · exact dataStep_100169 .absorb _
  · exact dataStep_10016c .absorb _
  · exact dataStep_10016f .absorb _
  · exact dataStep_100173 .absorb _
  · exact dataStep_100178 .absorb _
  · exact dataStep_10017d .absorb _
  · exact dataStep_100180 .absorb _
  · exact dataStep_100185 .absorb _
  · exact dataStep_100188 .absorb _
  · exact dataStep_10018b .absorb _
  · exact dataStep_100190 .absorb _
  · exact dataStep_100193 .absorb _
  · exact dataStep_100196 .absorb _
  · exact dataStep_100199 .absorb _
  · exact dataStep_10019c .absorb _
  · exact dataStep_10019f .absorb _
  · exact dataStep_1001a2 .absorb _
  · exact dataStep_1001a7 .absorb _
  · exact dataStep_1001aa .absorb _
  · exact dataStep_1001ad .absorb _
  · exact dataStep_1001b0 .absorb _
  · exact dataStep_1001b8 .absorb _
  · exact dataStep_1001bd .absorb _
  · exact dataStep_1001c0 .absorb _
  · exact dataStep_1001c8 .absorb _
  · exact dataStep_1001cb .absorb _
  · exact dataStep_1001d0 .absorb _
  · exact dataStep_1001d8 .absorb _
  · exact dataStep_1001e0 .absorb _
  · exact dataStep_1001e3 .absorb _
  · exact dataStep_1001e6 .absorb _
  · exact dataStep_1001e9 .absorb _
  · exact dataStep_1001ec .absorb _
  · exact dataStep_1001ef .absorb _
  · exact dataStep_1001f7 .absorb _
  · exact dataStep_1001fa .absorb _
  · exact dataStep_1000f0 .finalize _
  · exact dataStep_1000f5 .finalize _
  · exact dataStep_1000fa .finalize _
  · exact dataStep_100102 .finalize _
  · exact dataStep_100107 .finalize _
  · exact dataStep_10010c .finalize _
  · exact dataStep_10010f .finalize _
  · exact dataStep_100112 .finalize _
  · exact dataStep_100115 .finalize _
  · exact dataStep_10011d .finalize _
  · exact dataStep_100120 .finalize _
  · exact dataStep_100123 .finalize _
  · exact dataStep_100128 .finalize _
  · exact dataStep_10012d .finalize _
  · exact dataStep_100130 .finalize _
  · exact dataStep_100133 .finalize _
  · exact dataStep_100136 .finalize _
  · exact dataStep_10013b .finalize _
  · exact dataStep_10013e .finalize _
  · exact dataStep_100143 .finalize _
  · exact dataStep_100146 .finalize _
  · exact dataStep_100149 .finalize _
  · exact dataStep_100151 .finalize _
  · exact dataStep_100154 .finalize _
  · exact dataStep_100159 .finalize _
  · exact dataStep_10015e .finalize _
  · exact dataStep_100161 .finalize _
  · exact dataStep_100164 .finalize _
  · exact dataStep_100169 .finalize _
  · exact dataStep_10016c .finalize _
  · exact dataStep_10016f .finalize _
  · exact dataStep_100173 .finalize _
  · exact dataStep_100178 .finalize _
  · exact dataStep_10017d .finalize _
  · exact dataStep_100180 .finalize _
  · exact dataStep_100185 .finalize _
  · exact dataStep_100188 .finalize _
  · exact dataStep_10018b .finalize _
  · exact dataStep_100190 .finalize _
  · exact dataStep_100193 .finalize _
  · exact dataStep_100196 .finalize _
  · exact dataStep_100199 .finalize _
  · exact dataStep_10019c .finalize _
  · exact dataStep_10019f .finalize _
  · exact dataStep_1001a2 .finalize _
  · exact dataStep_1001a7 .finalize _
  · exact dataStep_1001aa .finalize _
  · exact dataStep_1001ad .finalize _
  · exact dataStep_1001b0 .finalize _
  · exact dataStep_1001b8 .finalize _
  · exact dataStep_1001bd .finalize _
  · exact dataStep_1001c0 .finalize _
  · exact dataStep_1001c8 .finalize _
  · exact dataStep_1001cb .finalize _
  · exact dataStep_1001d0 .finalize _
  · exact dataStep_1001d8 .finalize _
  · exact dataStep_1001e0 .finalize _
  · exact dataStep_1001e3 .finalize _
  · exact dataStep_1001e6 .finalize _
  · exact dataStep_1001e9 .finalize _
  · exact dataStep_1001ec .finalize _
  · exact dataStep_1001ef .finalize _
  · exact dataStep_1001f7 .finalize _
  · exact dataStep_1001fa .finalize _

set_option maxRecDepth 4096 in
private theorem dataSteps_64_128 [Bindings] (copy : Copy) (i : Fin 64) :
    let j := Fin.natAdd 64 (i.castAdd 129)
    DataStep copy (dataPc copy j.castSucc) (dataPc copy j.succ) (dataOp j)
      (dataBytes copy j) := by
  cases copy <;> finite_cases i
  · exact dataStep_1001fd .absorb _
  · exact dataStep_100200 .absorb _
  · exact dataStep_100205 .absorb _
  · exact dataStep_100208 .absorb _
  · exact dataStep_100210 .absorb _
  · exact dataStep_100215 .absorb _
  · exact dataStep_100218 .absorb _
  · exact dataStep_10021d .absorb _
  · exact dataStep_100220 .absorb _
  · exact dataStep_100225 .absorb _
  · exact dataStep_10022a .absorb _
  · exact dataStep_10022d .absorb _
  · exact dataStep_100232 .absorb _
  · exact dataStep_100235 .absorb _
  · exact dataStep_100238 .absorb _
  · exact dataStep_10023d .absorb _
  · exact dataStep_100242 .absorb _
  · exact dataStep_100245 .absorb _
  · exact dataStep_100248 .absorb _
  · exact dataStep_10024d .absorb _
  · exact dataStep_100252 .absorb _
  · exact dataStep_100255 .absorb _
  · exact dataStep_10025a .absorb _
  · exact dataStep_10025d .absorb _
  · exact dataStep_100260 .absorb _
  · exact dataStep_100265 .absorb _
  · exact dataStep_10026a .absorb _
  · exact dataStep_10026d .absorb _
  · exact dataStep_100275 .absorb _
  · exact dataStep_100279 .absorb _
  · exact dataStep_10027d .absorb _
  · exact dataStep_100281 .absorb _
  · exact dataStep_100285 .absorb _
  · exact dataStep_100289 .absorb _
  · exact dataStep_10028d .absorb _
  · exact dataStep_100292 .absorb _
  · exact dataStep_100296 .absorb _
  · exact dataStep_100299 .absorb _
  · exact dataStep_10029d .absorb _
  · exact dataStep_1002a1 .absorb _
  · exact dataStep_1002a9 .absorb _
  · exact dataStep_1002ad .absorb _
  · exact dataStep_1002b0 .absorb _
  · exact dataStep_1002b3 .absorb _
  · exact dataStep_1002b6 .absorb _
  · exact dataStep_1002bb .absorb _
  · exact dataStep_1002be .absorb _
  · exact dataStep_1002c1 .absorb _
  · exact dataStep_1002c4 .absorb _
  · exact dataStep_1002c7 .absorb _
  · exact dataStep_1002cf .absorb _
  · exact dataStep_1002d2 .absorb _
  · exact dataStep_1002d5 .absorb _
  · exact dataStep_1002d8 .absorb _
  · exact dataStep_1002db .absorb _
  · exact dataStep_1002e3 .absorb _
  · exact dataStep_1002eb .absorb _
  · exact dataStep_1002ee .absorb _
  · exact dataStep_1002f1 .absorb _
  · exact dataStep_1002f4 .absorb _
  · exact dataStep_1002f7 .absorb _
  · exact dataStep_1002fa .absorb _
  · exact dataStep_1002fd .absorb _
  · exact dataStep_100300 .absorb _
  · exact dataStep_1001fd .finalize _
  · exact dataStep_100200 .finalize _
  · exact dataStep_100205 .finalize _
  · exact dataStep_100208 .finalize _
  · exact dataStep_100210 .finalize _
  · exact dataStep_100215 .finalize _
  · exact dataStep_100218 .finalize _
  · exact dataStep_10021d .finalize _
  · exact dataStep_100220 .finalize _
  · exact dataStep_100225 .finalize _
  · exact dataStep_10022a .finalize _
  · exact dataStep_10022d .finalize _
  · exact dataStep_100232 .finalize _
  · exact dataStep_100235 .finalize _
  · exact dataStep_100238 .finalize _
  · exact dataStep_10023d .finalize _
  · exact dataStep_100242 .finalize _
  · exact dataStep_100245 .finalize _
  · exact dataStep_100248 .finalize _
  · exact dataStep_10024d .finalize _
  · exact dataStep_100252 .finalize _
  · exact dataStep_100255 .finalize _
  · exact dataStep_10025a .finalize _
  · exact dataStep_10025d .finalize _
  · exact dataStep_100260 .finalize _
  · exact dataStep_100265 .finalize _
  · exact dataStep_10026a .finalize _
  · exact dataStep_10026d .finalize _
  · exact dataStep_100275 .finalize _
  · exact dataStep_100279 .finalize _
  · exact dataStep_10027d .finalize _
  · exact dataStep_100281 .finalize _
  · exact dataStep_100285 .finalize _
  · exact dataStep_100289 .finalize _
  · exact dataStep_10028d .finalize _
  · exact dataStep_100292 .finalize _
  · exact dataStep_100296 .finalize _
  · exact dataStep_100299 .finalize _
  · exact dataStep_10029d .finalize _
  · exact dataStep_1002a1 .finalize _
  · exact dataStep_1002a9 .finalize _
  · exact dataStep_1002ad .finalize _
  · exact dataStep_1002b0 .finalize _
  · exact dataStep_1002b3 .finalize _
  · exact dataStep_1002b6 .finalize _
  · exact dataStep_1002bb .finalize _
  · exact dataStep_1002be .finalize _
  · exact dataStep_1002c1 .finalize _
  · exact dataStep_1002c4 .finalize _
  · exact dataStep_1002c7 .finalize _
  · exact dataStep_1002cf .finalize _
  · exact dataStep_1002d2 .finalize _
  · exact dataStep_1002d5 .finalize _
  · exact dataStep_1002d8 .finalize _
  · exact dataStep_1002db .finalize _
  · exact dataStep_1002e3 .finalize _
  · exact dataStep_1002eb .finalize _
  · exact dataStep_1002ee .finalize _
  · exact dataStep_1002f1 .finalize _
  · exact dataStep_1002f4 .finalize _
  · exact dataStep_1002f7 .finalize _
  · exact dataStep_1002fa .finalize _
  · exact dataStep_1002fd .finalize _
  · exact dataStep_100300 .finalize _

set_option maxRecDepth 4096 in
private theorem dataSteps_128_192 [Bindings] (copy : Copy) (i : Fin 64) :
    let j := Fin.natAdd 64 (Fin.natAdd 64 (i.castAdd 65))
    DataStep copy (dataPc copy j.castSucc) (dataPc copy j.succ) (dataOp j)
      (dataBytes copy j) := by
  cases copy <;> finite_cases i
  · exact dataStep_100305 .absorb _
  · exact dataStep_100308 .absorb _
  · exact dataStep_10030b .absorb _
  · exact dataStep_100313 .absorb _
  · exact dataStep_100316 .absorb _
  · exact dataStep_100319 .absorb _
  · exact dataStep_10031e .absorb _
  · exact dataStep_100321 .absorb _
  · exact dataStep_100324 .absorb _
  · exact dataStep_100327 .absorb _
  · exact dataStep_10032a .absorb _
  · exact dataStep_10032f .absorb _
  · exact dataStep_100332 .absorb _
  · exact dataStep_100335 .absorb _
  · exact dataStep_100338 .absorb _
  · exact dataStep_10033b .absorb _
  · exact dataStep_10033e .absorb _
  · exact dataStep_100342 .absorb _
  · exact dataStep_10034a .absorb _
  · exact dataStep_10034e .absorb _
  · exact dataStep_100351 .absorb _
  · exact dataStep_100355 .absorb _
  · exact dataStep_10035a .absorb _
  · exact dataStep_100362 .absorb _
  · exact dataStep_100366 .absorb _
  · exact dataStep_10036a .absorb _
  · exact dataStep_10036f .absorb _
  · exact dataStep_100373 .absorb _
  · exact dataStep_100376 .absorb _
  · exact dataStep_100379 .absorb _
  · exact dataStep_10037c .absorb _
  · exact dataStep_10037f .absorb _
  · exact dataStep_100384 .absorb _
  · exact dataStep_100387 .absorb _
  · exact dataStep_10038a .absorb _
  · exact dataStep_10038d .absorb _
  · exact dataStep_100390 .absorb _
  · exact dataStep_100393 .absorb _
  · exact dataStep_100396 .absorb _
  · exact dataStep_100399 .absorb _
  · exact dataStep_10039c .absorb _
  · exact dataStep_10039f .absorb _
  · exact dataStep_1003a2 .absorb _
  · exact dataStep_1003a5 .absorb _
  · exact dataStep_1003a8 .absorb _
  · exact dataStep_1003ab .absorb _
  · exact dataStep_1003b0 .absorb _
  · exact dataStep_1003b3 .absorb _
  · exact dataStep_1003b8 .absorb _
  · exact dataStep_1003bd .absorb _
  · exact dataStep_1003c0 .absorb _
  · exact dataStep_1003c3 .absorb _
  · exact dataStep_1003c6 .absorb _
  · exact dataStep_1003c9 .absorb _
  · exact dataStep_1003ce .absorb _
  · exact dataStep_1003d1 .absorb _
  · exact dataStep_1003d4 .absorb _
  · exact dataStep_1003d9 .absorb _
  · exact dataStep_1003dc .absorb _
  · exact dataStep_1003e1 .absorb _
  · exact dataStep_1003e6 .absorb _
  · exact dataStep_1003ea .absorb _
  · exact dataStep_1003ef .absorb _
  · exact dataStep_1003f3 .absorb _
  · exact dataStep_100305 .finalize _
  · exact dataStep_100308 .finalize _
  · exact dataStep_10030b .finalize _
  · exact dataStep_100313 .finalize _
  · exact dataStep_100316 .finalize _
  · exact dataStep_100319 .finalize _
  · exact dataStep_10031e .finalize _
  · exact dataStep_100321 .finalize _
  · exact dataStep_100324 .finalize _
  · exact dataStep_100327 .finalize _
  · exact dataStep_10032a .finalize _
  · exact dataStep_10032f .finalize _
  · exact dataStep_100332 .finalize _
  · exact dataStep_100335 .finalize _
  · exact dataStep_100338 .finalize _
  · exact dataStep_10033b .finalize _
  · exact dataStep_10033e .finalize _
  · exact dataStep_100342 .finalize _
  · exact dataStep_10034a .finalize _
  · exact dataStep_10034e .finalize _
  · exact dataStep_100351 .finalize _
  · exact dataStep_100355 .finalize _
  · exact dataStep_10035a .finalize _
  · exact dataStep_100362 .finalize _
  · exact dataStep_100366 .finalize _
  · exact dataStep_10036a .finalize _
  · exact dataStep_10036f .finalize _
  · exact dataStep_100373 .finalize _
  · exact dataStep_100376 .finalize _
  · exact dataStep_100379 .finalize _
  · exact dataStep_10037c .finalize _
  · exact dataStep_10037f .finalize _
  · exact dataStep_100384 .finalize _
  · exact dataStep_100387 .finalize _
  · exact dataStep_10038a .finalize _
  · exact dataStep_10038d .finalize _
  · exact dataStep_100390 .finalize _
  · exact dataStep_100393 .finalize _
  · exact dataStep_100396 .finalize _
  · exact dataStep_100399 .finalize _
  · exact dataStep_10039c .finalize _
  · exact dataStep_10039f .finalize _
  · exact dataStep_1003a2 .finalize _
  · exact dataStep_1003a5 .finalize _
  · exact dataStep_1003a8 .finalize _
  · exact dataStep_1003ab .finalize _
  · exact dataStep_1003b0 .finalize _
  · exact dataStep_1003b3 .finalize _
  · exact dataStep_1003b8 .finalize _
  · exact dataStep_1003bd .finalize _
  · exact dataStep_1003c0 .finalize _
  · exact dataStep_1003c3 .finalize _
  · exact dataStep_1003c6 .finalize _
  · exact dataStep_1003c9 .finalize _
  · exact dataStep_1003ce .finalize _
  · exact dataStep_1003d1 .finalize _
  · exact dataStep_1003d4 .finalize _
  · exact dataStep_1003d9 .finalize _
  · exact dataStep_1003dc .finalize _
  · exact dataStep_1003e1 .finalize _
  · exact dataStep_1003e6 .finalize _
  · exact dataStep_1003ea .finalize _
  · exact dataStep_1003ef .finalize _
  · exact dataStep_1003f3 .finalize _

set_option maxRecDepth 4096 in
private theorem dataSteps_192_257 [Bindings] (copy : Copy) (i : Fin 65) :
    let j := Fin.natAdd 64 (Fin.natAdd 64 (Fin.natAdd 64 (i)))
    DataStep copy (dataPc copy j.castSucc) (dataPc copy j.succ) (dataOp j)
      (dataBytes copy j) := by
  cases copy <;> finite_cases i
  · exact dataStep_1003f6 .absorb _
  · exact dataStep_1003fa .absorb _
  · exact dataStep_1003ff .absorb _
  · exact dataStep_100407 .absorb _
  · exact dataStep_10040b .absorb _
  · exact dataStep_100410 .absorb _
  · exact dataStep_100414 .absorb _
  · exact dataStep_100419 .absorb _
  · exact dataStep_10041c .absorb _
  · exact dataStep_10041f .absorb _
  · exact dataStep_100422 .absorb _
  · exact dataStep_100425 .absorb _
  · exact dataStep_100428 .absorb _
  · exact dataStep_10042b .absorb _
  · exact dataStep_10042e .absorb _
  · exact dataStep_100431 .absorb _
  · exact dataStep_100434 .absorb _
  · exact dataStep_100437 .absorb _
  · exact dataStep_10043a .absorb _
  · exact dataStep_10043d .absorb _
  · exact dataStep_100440 .absorb _
  · exact dataStep_100445 .absorb _
  · exact dataStep_100448 .absorb _
  · exact dataStep_10044c .absorb _
  · exact dataStep_100454 .absorb _
  · exact dataStep_100458 .absorb _
  · exact dataStep_10045d .absorb _
  · exact dataStep_100461 .absorb _
  · exact dataStep_100469 .absorb _
  · exact dataStep_10046d .absorb _
  · exact dataStep_100470 .absorb _
  · exact dataStep_100473 .absorb _
  · exact dataStep_100476 .absorb _
  · exact dataStep_100479 .absorb _
  · exact dataStep_10047c .absorb _
  · exact dataStep_10047f .absorb _
  · exact dataStep_100482 .absorb _
  · exact dataStep_100485 .absorb _
  · exact dataStep_100488 .absorb _
  · exact dataStep_10048b .absorb _
  · exact dataStep_10048e .absorb _
  · exact dataStep_100491 .absorb _
  · exact dataStep_100494 .absorb _
  · exact dataStep_100499 .absorb _
  · exact dataStep_10049c .absorb _
  · exact dataStep_10049f .absorb _
  · exact dataStep_1004a4 .absorb _
  · exact dataStep_1004a7 .absorb _
  · exact dataStep_1004aa .absorb _
  · exact dataStep_1004ad .absorb _
  · exact dataStep_1004b0 .absorb _
  · exact dataStep_1004b3 .absorb _
  · exact dataStep_1004b8 .absorb _
  · exact dataStep_1004bb .absorb _
  · exact dataStep_1004be .absorb _
  · exact dataStep_1004c1 .absorb _
  · exact dataStep_1004c9 .absorb _
  · exact dataStep_1004cc .absorb _
  · exact dataStep_1004d1 .absorb _
  · exact dataStep_1004d6 .absorb _
  · exact dataStep_1004dd .absorb _
  · exact dataStep_1004e1 .absorb _
  · exact dataStep_1004e9 .absorb _
  · exact dataStep_1004ed .absorb _
  · exact dataStep_1004f5 .absorb _
  · exact dataStep_1003f6 .finalize _
  · exact dataStep_1003fa .finalize _
  · exact dataStep_1003ff .finalize _
  · exact dataStep_100407 .finalize _
  · exact dataStep_10040b .finalize _
  · exact dataStep_100410 .finalize _
  · exact dataStep_100414 .finalize _
  · exact dataStep_100419 .finalize _
  · exact dataStep_10041c .finalize _
  · exact dataStep_10041f .finalize _
  · exact dataStep_100422 .finalize _
  · exact dataStep_100425 .finalize _
  · exact dataStep_100428 .finalize _
  · exact dataStep_10042b .finalize _
  · exact dataStep_10042e .finalize _
  · exact dataStep_100431 .finalize _
  · exact dataStep_100434 .finalize _
  · exact dataStep_100437 .finalize _
  · exact dataStep_10043a .finalize _
  · exact dataStep_10043d .finalize _
  · exact dataStep_100440 .finalize _
  · exact dataStep_100445 .finalize _
  · exact dataStep_100448 .finalize _
  · exact dataStep_10044c .finalize _
  · exact dataStep_100454 .finalize _
  · exact dataStep_100458 .finalize _
  · exact dataStep_10045d .finalize _
  · exact dataStep_100461 .finalize _
  · exact dataStep_100469 .finalize _
  · exact dataStep_10046d .finalize _
  · exact dataStep_100470 .finalize _
  · exact dataStep_100473 .finalize _
  · exact dataStep_100476 .finalize _
  · exact dataStep_100479 .finalize _
  · exact dataStep_10047c .finalize _
  · exact dataStep_10047f .finalize _
  · exact dataStep_100482 .finalize _
  · exact dataStep_100485 .finalize _
  · exact dataStep_100488 .finalize _
  · exact dataStep_10048b .finalize _
  · exact dataStep_10048e .finalize _
  · exact dataStep_100491 .finalize _
  · exact dataStep_100494 .finalize _
  · exact dataStep_100499 .finalize _
  · exact dataStep_10049c .finalize _
  · exact dataStep_10049f .finalize _
  · exact dataStep_1004a4 .finalize _
  · exact dataStep_1004a7 .finalize _
  · exact dataStep_1004aa .finalize _
  · exact dataStep_1004ad .finalize _
  · exact dataStep_1004b0 .finalize _
  · exact dataStep_1004b3 .finalize _
  · exact dataStep_1004b8 .finalize _
  · exact dataStep_1004bb .finalize _
  · exact dataStep_1004be .finalize _
  · exact dataStep_1004c1 .finalize _
  · exact dataStep_1004c9 .finalize _
  · exact dataStep_1004cc .finalize _
  · exact dataStep_1004d1 .finalize _
  · exact dataStep_1004d6 .finalize _
  · exact dataStep_1004dd .finalize _
  · exact dataStep_1004e1 .finalize _
  · exact dataStep_1004e9 .finalize _
  · exact dataStep_1004ed .finalize _
  · exact dataStep_1004f5 .finalize _

theorem dataSteps [Bindings] (copy : Copy) (i : Fin 257) :
    DataStep copy (dataPc copy i.castSucc) (dataPc copy i.succ) (dataOp i)
      (dataBytes copy i) := by
  let P : Fin 257 → Prop := fun j ↦
    DataStep copy (dataPc copy j.castSucc) (dataPc copy j.succ) (dataOp j)
      (dataBytes copy j)
  exact Fin.addCases (m := 64) (n := 193) (motive := P) (dataSteps_0_64 copy) (fun j ↦
    Fin.addCases (m := 64) (n := 129)
      (motive := fun k ↦ P (Fin.natAdd 64 k)) (dataSteps_64_128 copy) (fun k ↦
      Fin.addCases (m := 64) (n := 65)
        (motive := fun l ↦ P (Fin.natAdd 64 (Fin.natAdd 64 l)))
        (dataSteps_128_192 copy) (dataSteps_192_257 copy) k) j) i

end Sha3.Proofs.Permutation.RoundMachine
