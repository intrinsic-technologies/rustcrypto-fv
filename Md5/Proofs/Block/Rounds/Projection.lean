import Md5.Proofs.Block.Rounds.Word
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace Md5.Proofs.Block.Rounds

open X86 X86.Machine X86.UserProcess X86Proofs

def scratchOffsets : List Nat :=
  [4, 8, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 112, 120, 128]

def WordLocation.valid : WordLocation → Prop
  | .reg index => index < 16
  | .stack offset => offset ∈ scratchOffsets
  | .input index => index < 16

def readMachineWord (stack input : BitVec 64) (s : RamState) : WordState
  | .reg index => (Operand.reg (BitVec.ofNat 5 index) : Operand 32).read s
  | .stack offset => (Operand.mem (stack + BitVec.ofNat 64 offset) : Operand 32).read s
  | .input index => (Operand.mem (input + BitVec.ofNat 64 (4 * index)) : Operand 32).read s

def MachineWords (stack input : BitVec 64) (s : RamState) (words : WordState) : Prop :=
  ∀ loc, loc.valid → readMachineWord stack input s loc = words loc

theorem MachineWords.self (stack input : BitVec 64) (s : RamState) :
    MachineWords stack input s (readMachineWord stack input s) := fun _ _ ↦ rfl

theorem MachineWords.congr {stack input : BitVec 64} {s : RamState} {words words' : WordState}
    (h : MachineWords stack input s words)
    (he : ∀ loc, loc.valid → words loc = words' loc) :
    MachineWords stack input s words' := fun loc hv ↦ (h loc hv).trans (he loc hv)

theorem MachineWords.of_obs {stack input : BitVec 64} {s t : RamState} {words : WordState}
    (h : MachineWords stack input s words) (ho : Obs s t) :
    MachineWords stack input t words := by
  intro loc hv
  apply Eq.trans _ (h loc hv)
  cases loc <;> simp only [readMachineWord] <;> exact (ho.read _ (by simp)).symm

theorem MachineWords.write {stack input : BitVec 64} {s t : RamState} {words : WordState}
    (h : MachineWords stack input s words) (dst : WordLocation) (value : BitVec 32)
    (hvalue : dst.valid → readMachineWord stack input t dst = value)
    (hframe : ∀ loc, loc.valid → loc ≠ dst →
      readMachineWord stack input t loc = readMachineWord stack input s loc) :
    MachineWords stack input t (words.write dst value) := by
  intro loc hv
  by_cases he : loc = dst
  · subst loc
    exact (hvalue hv).trans (by simp [WordState.write])
  · exact (hframe loc hv he).trans ((h loc hv).trans (by simp [WordState.write, he]))

private theorem effect_single_write {e : Effect} {s t : RamState} {n : Nat}
    {dst : Operand n} {value : BitVec n} (h : e.Holds s t)
    (hw : e.writes = [⟨dst, value⟩]) (hf : dst.Full) : Obs (dst.write s value) t := by
  have ho := h.obs (Obs.refl s) (by
    rw [hw]
    intro w hm
    simp only [List.mem_singleton] at hm
    subst w
    exact hf)
  simpa only [hw, applyWrites_cons, applyWrites_nil, Write.apply_mk] using ho

theorem MachineWords.write_reg64 {stack input : BitVec 64} {s t : RamState}
    {words : WordState} {e : Effect} {dst : Nat} {value : BitVec 64}
    (h : MachineWords stack input s words) (he : e.Holds s t)
    (hw : e.writes = [⟨.reg (BitVec.ofNat 5 dst), value⟩]) (hdst : dst < 16) :
    MachineWords stack input t (words.write (.reg dst) (value.setWidth 32)) := by
  apply MachineWords.of_obs (s := (Operand.reg (BitVec.ofNat 5 dst)).write s value)
    _ (effect_single_write he hw (Operand.full_reg _))
  apply h.write (.reg dst) (value.setWidth 32)
  · intro _
    simp [readMachineWord]
  · intro loc hv hne
    cases loc with
    | reg index =>
      have hi : index < 16 := hv
      have hni : BitVec.ofNat 5 dst ≠ BitVec.ofNat 5 index := by
        intro heq
        apply hne
        congr 1
        have heq' := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat] at heq'
        omega
      simp only [readMachineWord, Operand.read_reg_write_reg]
      exact ite_eq_right_iff.mpr (fun heq ↦ (hni heq).elim)
    | stack offset => rfl
    | input index => rfl

theorem memLoad_low32 (m : Ram) (a : BitVec 64) :
    (memLoad m a 64).setWidth 32 = memLoad m a 32 := by
  simp [memLoad, List.range_succ, BitVec.setWidth_or]

def scratchWideOffsets : List Nat := [8, 64, 72, 80, 88, 112, 120, 128]

theorem scratchOffsets_apart32 :
    ∀ dst ∈ scratchOffsets, ∀ offset ∈ scratchOffsets, offset ≠ dst →
      OffsetsApart (BitVec.ofNat 64 dst) 4 (BitVec.ofNat 64 offset) 4 := by
  unfold OffsetsApart
  decide +kernel

theorem scratchOffsets_apart64 :
    ∀ dst ∈ scratchWideOffsets, ∀ offset ∈ scratchOffsets, offset ≠ dst →
      OffsetsApart (BitVec.ofNat 64 dst) 8 (BitVec.ofNat 64 offset) 4 := by
  unfold OffsetsApart
  decide +kernel

theorem scratchOffsets_bound : ∀ dst ∈ scratchOffsets, dst + 4 ≤ 136 := by
  decide +kernel

theorem scratchWideOffsets_bound : ∀ dst ∈ scratchWideOffsets, dst + 8 ≤ 136 := by
  decide +kernel

private theorem memLoad_low_store {n : Nat} (hn : n = 32 ∨ n = 64)
    (m : Ram) (a : BitVec 64) (v : BitVec n) :
    memLoad (memStore m a v) a 32 = v.setWidth 32 := by
  rcases hn with rfl | rfl
  · simpa only [BitVec.setWidth_eq] using memLoad_memStore m a (by decide) (by decide) v
  · rw [← memLoad_low32, memLoad_memStore m a (by decide) (by decide) v]

theorem MachineWords.write_stack {stack input : BitVec 64} {s t : RamState}
    {words : WordState} {e : Effect} {dst n : Nat} {value : BitVec n}
    (h : MachineWords stack input s words) (he : e.Holds s t)
    (hw : e.writes = [⟨.mem (stack + BitVec.ofNat 64 dst), value⟩])
    (hn : n = 32 ∨ n = 64) (hbound : dst + n / 8 ≤ 136)
    (hslots : ∀ offset ∈ scratchOffsets, offset ≠ dst →
      OffsetsApart (BitVec.ofNat 64 dst) (n / 8) (BitVec.ofNat 64 offset) 4)
    (hapart : RangeApart stack 136 input 64) :
    MachineWords stack input t (words.write (.stack dst) (value.setWidth 32)) := by
  apply MachineWords.of_obs (s := (Operand.mem (stack + BitVec.ofNat 64 dst)).write s value)
    _ (effect_single_write he hw (by
      rcases hn with rfl | rfl <;> rfl))
  apply h.write (.stack dst) (value.setWidth 32)
  · intro _
    exact memLoad_low_store hn _ _ _
  · intro loc hv hne
    cases loc with
    | reg index => rfl
    | stack offset =>
      apply memLoad_memStore_apart
      · exact hslots offset hv (fun heq ↦ hne (congrArg WordLocation.stack heq))
      · rcases hn with rfl | rfl <;> decide
      · decide
    | input index =>
      have hi : index < 16 := hv
      apply memLoad_congr
      intro j hj
      change ((memStore s.external (stack + BitVec.ofNat 64 dst) value)[
        input + BitVec.ofNat 64 (4 * index) + BitVec.ofNat 64 j]?).getD 0 = _
      rw [memStore_getElem?_of_ne]
      · rfl
      · intro i hi' heq
        apply hapart (dst + i) (by omega) (4 * index + j) (by omega)
        simpa only [BitVec.ofNat_add, BitVec.add_assoc] using heq

theorem MachineWords.write_stack32 {stack input : BitVec 64} {s t : RamState}
    {words : WordState} {e : Effect} {dst : Nat} {value : BitVec 32}
    (h : MachineWords stack input s words) (he : e.Holds s t)
    (hw : e.writes = [⟨.mem (stack + BitVec.ofNat 64 dst), value⟩])
    (hdst : dst ∈ scratchOffsets) (hapart : RangeApart stack 136 input 64) :
    MachineWords stack input t (words.write (.stack dst) value) := by
  exact h.write_stack he hw (Or.inl rfl) (scratchOffsets_bound dst hdst)
    (scratchOffsets_apart32 dst hdst) hapart

theorem MachineWords.write_stack64 {stack input : BitVec 64} {s t : RamState}
    {words : WordState} {e : Effect} {dst : Nat} {value : BitVec 64}
    (h : MachineWords stack input s words) (he : e.Holds s t)
    (hw : e.writes = [⟨.mem (stack + BitVec.ofNat 64 dst), value⟩])
    (hdst : dst ∈ scratchWideOffsets) (hapart : RangeApart stack 136 input 64) :
    MachineWords stack input t (words.write (.stack dst) (value.setWidth 32)) := by
  exact h.write_stack he hw (Or.inr rfl) (scratchWideOffsets_bound dst hdst)
    (scratchOffsets_apart64 dst hdst) hapart

instance WordLocation.decidableValid (loc : WordLocation) : Decidable loc.valid := by
  cases loc <;> unfold WordLocation.valid <;> infer_instance

def WordSource.valid : WordSource → Prop
  | .location loc => loc.valid
  | .immediate _ => True

instance WordSource.decidableValid (src : WordSource) : Decidable src.valid := by
  cases src <;> unfold WordSource.valid <;> infer_instance

def WordInstruction.valid : WordInstruction → Prop
  | .mov dst src | .add dst src | .and dst src | .or dst src | .xor dst src =>
    dst.valid ∧ src.valid
  | .not dst | .rol dst _ => dst.valid
  | .lea dst left right => dst.valid ∧ left.valid ∧ right.valid

instance WordInstruction.decidableValid (instruction : WordInstruction) :
    Decidable instruction.valid := by
  cases instruction <;> unfold WordInstruction.valid <;> infer_instance

theorem WordSource.read_congr {s t : WordState}
    (h : ∀ loc, loc.valid → s loc = t loc) {src : WordSource} (hv : src.valid) :
    src.read s = src.read t := by
  cases src with
  | location loc => exact h loc hv
  | immediate _ => rfl

theorem WordInstruction.execute_congr {s t : WordState}
    (h : ∀ loc, loc.valid → s loc = t loc)
    {instruction : WordInstruction} (hv : instruction.valid) :
    ∀ loc, loc.valid → instruction.execute s loc = instruction.execute t loc := by
  intro loc hl
  cases instruction with
  | mov dst src =>
    rw [execute_mov, execute_mov, WordSource.read_congr h hv.2, h loc hl]
  | add dst src =>
    rw [execute_add, execute_add, WordSource.read_congr h hv.2, h dst hv.1, h loc hl]
  | and dst src =>
    rw [execute_and, execute_and, WordSource.read_congr h hv.2, h dst hv.1, h loc hl]
  | or dst src =>
    rw [execute_or, execute_or, WordSource.read_congr h hv.2, h dst hv.1, h loc hl]
  | xor dst src =>
    rw [execute_xor, execute_xor, WordSource.read_congr h hv.2, h dst hv.1, h loc hl]
  | not dst => rw [execute_not, execute_not, h dst hv, h loc hl]
  | rol dst amount => rw [execute_rol, execute_rol, h dst hv, h loc hl]
  | lea dst left right =>
    rw [execute_lea, execute_lea, h left hv.2.1, h right hv.2.2, h loc hl]

theorem executeWords_congr {s t : WordState} (code : List WordInstruction)
    (h : ∀ loc, loc.valid → s loc = t loc)
    (hv : ∀ instruction ∈ code, instruction.valid) :
    ∀ loc, loc.valid → executeWords code s loc = executeWords code t loc := by
  induction code generalizing s t with
  | nil => simpa only [executeWords_nil] using h
  | cons instruction code ih =>
    rw [executeWords_cons, executeWords_cons]
    exact ih (WordInstruction.execute_congr h (hv instruction List.mem_cons_self))
      (fun i hi ↦ hv i (List.mem_cons_of_mem instruction hi))

end Md5.Proofs.Block.Rounds
