import Md5.Proofs.Block.Rounds.Projection

namespace Md5.Proofs.Block.Rounds

open X86 X86.Machine X86.UserProcess X86Proofs

theorem read_reg64_low32 (s : RamState) (r : BitVec 5) :
    ((Operand.reg r : Operand 64).read s).setWidth 32 =
      (Operand.reg r : Operand 32).read s := by
  simp [Operand.read]

theorem read_mem64_low32 (s : RamState) (a : BitVec 64) :
    ((Operand.mem a : Operand 64).read s).setWidth 32 =
      (Operand.mem a : Operand 32).read s := memLoad_low32 s.external a

macro "md5_word_model" : tactic => `(tactic| with_unfolding_all
  simp (config := { decide := true }) only
    [WordInstruction.execute, WordSource.read, readMachineWord,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, read_reg64_low32, read_mem64_low32])

variable {stack input : BitVec 64} {s t : RamState} {model : WordState}
  {effect : Effect} {instruction : WordInstruction}

theorem MachineWords.of_reg_effect {dst : Nat} {value : BitVec 64}
    (hModel : MachineWords stack input s model) (hEffect : effect.Holds s t)
    (hWrite : effect.writes = [⟨.reg (BitVec.ofNat 5 dst), value⟩])
    (hDst : dst < 16) (hValid : instruction.valid)
    (hAction : instruction.execute (readMachineWord stack input s) =
      (readMachineWord stack input s).write (.reg dst) (value.setWidth 32)) :
    MachineWords stack input t (instruction.execute model) := by
  have h := (MachineWords.self stack input s).write_reg64 hEffect hWrite hDst
  rw [← hAction] at h
  exact h.congr (instruction.execute_congr hModel hValid)

theorem MachineWords.of_stack32_effect {dst : Nat} {value : BitVec 32}
    (hModel : MachineWords stack input s model) (hEffect : effect.Holds s t)
    (hWrite : effect.writes = [⟨.mem (stack + BitVec.ofNat 64 dst), value⟩])
    (hDst : dst ∈ scratchOffsets) (hApart : RangeApart stack 136 input 64)
    (hValid : instruction.valid)
    (hAction : instruction.execute (readMachineWord stack input s) =
      (readMachineWord stack input s).write (.stack dst) value) :
    MachineWords stack input t (instruction.execute model) := by
  have h := (MachineWords.self stack input s).write_stack32 hEffect hWrite hDst hApart
  rw [← hAction] at h
  exact h.congr (instruction.execute_congr hModel hValid)

theorem MachineWords.of_stack64_effect {dst : Nat} {value : BitVec 64}
    (hModel : MachineWords stack input s model) (hEffect : effect.Holds s t)
    (hWrite : effect.writes = [⟨.mem (stack + BitVec.ofNat 64 dst), value⟩])
    (hDst : dst ∈ scratchWideOffsets) (hApart : RangeApart stack 136 input 64)
    (hValid : instruction.valid)
    (hAction : instruction.execute (readMachineWord stack input s) =
      (readMachineWord stack input s).write (.stack dst) (value.setWidth 32)) :
    MachineWords stack input t (instruction.execute model) := by
  have h := (MachineWords.self stack input s).write_stack64 hEffect hWrite hDst hApart
  rw [← hAction] at h
  exact h.congr (instruction.execute_congr hModel hValid)

end Md5.Proofs.Block.Rounds
