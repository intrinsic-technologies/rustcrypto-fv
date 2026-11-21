import Sha3.Proofs.Permutation.RoundMachine.Instructions.Data
import Sha3.Proofs.Permutation.RoundMachine.Preservation
import Sha3.Proofs.Permutation.RoundMachine.Control
import Sha3.Proofs.Permutation.Constants
import Sha3.Proofs.Permutation.Code

namespace Sha3.Proofs.Permutation.RoundMachine

open X86 X86.Machine X86.UserProcess X86Proofs RoundAlgebra Sha3.Spec.Program

theorem dataOp_valid (i : Fin 257) : ValidInstruction (dataOp i) := by
  have h : ∀ j : Fin 257, ValidInstruction (dataOp j) := by decide +kernel
  exact h i

theorem dataCode_subset_image (copy : Copy) (i : Fin 257) :
    ∀ x ∈ codeRange (BitVec.ofNat 64 (dataPc copy i.castSucc)) (dataBytes copy i),
      x ∈ Extracted.programImage := by
  have h : (BitVec.ofNat 64 (dataPc copy i.castSucc), dataBytes copy i) ∈ roundInstructionBytes copy := by
    unfold dataPc dataBytes
    rw [BitVec.ofNat_toNat]
    exact List.getElem_mem _
  exact fun x hx ↦ roundCode_subset_programImage copy x (instructionCode_subset_roundCode copy h x hx)

theorem dataPc_in_program (copy : Copy) (i : Fin 258) : InProgram (BitVec.ofNat 64 (dataPc copy i)) := by
  have h : ∀ j : Fin 258, 0x100000 ≤ (BitVec.ofNat 64 (dataPc copy j)).toNat ∧
      (BitVec.ofNat 64 (dataPc copy j)).toNat ≤ 0x106222 := by cases copy <;> decide +kernel
  exact inProgram_permutation_address (h i).1 (h i).2

theorem program_length : program.length = 257 := by decide +kernel

set_option maxRecDepth 4096 in
theorem runPrefix_succ (rc : BitVec 64) (a : RoundAlgebra.State) (i : Fin 257) :
    runPrefix rc a (i.val + 1) = execute rc (runPrefix rc a i.val) (dataOp i) := by
  unfold runPrefix
  rw [List.take_succ_eq_append_getElem (by rw [program_length]; exact i.isLt),
    List.foldl_append]
  rfl

theorem runPrefix_zero (rc : BitVec 64) (a : RoundAlgebra.State) : runPrefix rc a 0 = a := rfl

theorem runPrefix_full (rc : BitVec 64) (a : RoundAlgebra.State) : runPrefix rc a 257 = run rc a := by
  unfold runPrefix run
  rw [List.take_of_length_le (by rw [program_length]; exact Nat.le_refl _)]

theorem dataOp_constant_index (i : Fin 257) :
    match dataOp i with
    | .xorConstant _ => i.val = 251
    | _ => True := by
  have h : ∀ j : Fin 257, (match dataOp j with
      | .xorConstant _ => decide (j.val = 251)
      | _ => true) = true := by decide +kernel
  have hi := h i
  cases hop : dataOp i <;> simp_all

theorem prefix_constantPre (copy : Copy) {sp : BitVec 64} {s : RamState} {a : RoundAlgebra.State}
    {n : Nat} (hn : n < 24) (hc : a.regs 2 = BitVec.ofNat 64 (8 * n))
    (i : Fin 257) (hm : Models sp (runPrefix (Keccak.roundConstant (n : Int)) a i.val) s)
    (hcode : CodeIn Extracted.programImage s) :
    ConstantPre copy (Keccak.roundConstant (n : Int)) (dataOp i) s := by
  have hi := dataOp_constant_index i
  cases hop : dataOp i <;> try trivial
  rename_i dst
  rw [hop] at hi
  have hreg := hm (.reg 2) trivial
  change s.regValue .rdx = (runPrefix (Keccak.roundConstant (n : Int)) a i.val).regs 2 at hreg
  rw [hi, regs_counter_beforeConstant, hc] at hreg
  have hl : ProgramLoaded s := fun addr byte hb ↦ (hcode (addr, byte) hb).2
  have haddr : (Operand.reg 2 : Operand 64).read s + constantBase copy = constantAddress copy ⟨n, hn⟩ := by
    change s.regValue .rdx + constantBase copy = _
    rw [hreg]
    exact BitVec.add_comm _ _
  change MemReadable s _ 8 ∧ (constantOperand copy s).read s = _
  constructor
  · rw [haddr]
    exact constant_readable hl copy ⟨n, hn⟩
  · unfold constantOperand
    rw [haddr]
    exact constant_operand_read hl copy ⟨n, hn⟩

structure PrefixInvariant (copy : Copy) (initial : RamState) (n : Nat) (a : RoundAlgebra.State)
    (i : Fin 258) (s : RamState) : Prop where
  frame : CallFrame initial s
  memory : RoundMemory (frameBase initial) s
  rip : s.RIP = BitVec.ofNat 64 (dataPc copy i)
  model : Models (frameBase initial) (runPrefix (Keccak.roundConstant (n : Int)) a i.val) s

theorem dataStep_advance [Bindings] (copy : Copy) {boundary : ReturnBoundary} {initial : RamState}
    {n : Nat} {a : RoundAlgebra.State} (hn : n < 24)
    (hc : a.regs 2 = BitVec.ofNat 64 (8 * n)) (hb : ¬ InProgram boundary.rip)
    (i : Fin 257)
    (hs : DataStep copy (dataPc copy i.castSucc) (dataPc copy i.succ) (dataOp i) (dataBytes copy i)) :
    AdvanceTriple boundary 1 (PrefixInvariant copy initial n a i.castSucc)
      Extracted.programImage (fun _ t ↦ PrefixInvariant copy initial n a i.succ t) := by
  intro s hready hcode hp
  have hpre : DataPre copy (frameBase initial) (Keccak.roundConstant (n : Int))
      (dataPc copy i.castSucc) (dataOp i) s :=
    ⟨hp.rip, hp.frame.stack, hp.memory, prefix_constantPre copy hn hc i hp.model hcode⟩
  obtain ⟨t, flags, hstep, hready', he⟩ :=
    hs _ _ _ hready (hcode.mono (dataCode_subset_image copy i)) hpre
  have hne : t.RIP ≠ boundary.rip := by
    rw [he.rip]
    intro hip
    exact hb (hip ▸ dataPc_in_program copy i.succ)
  refine ⟨t, Advances.of_step hstep (.inl hne), hready',
    he.codeIn (instructionEffect_avoids (dataOp_valid i) hp.memory) hcode, ?_⟩
  refine ⟨instructionEffect_callFrame (dataOp_valid i) hp.memory hp.frame he,
    hp.memory.of_holds he, he.rip, ?_⟩
  change Models _ (runPrefix _ a (i.val + 1)) t
  rw [runPrefix_succ]
  exact models_execute hp.model (dataOp_valid i) he

theorem prefix_advance [Bindings] (copy : Copy) {boundary : ReturnBoundary} {initial : RamState}
    {n : Nat} {a : RoundAlgebra.State} (hn : n < 24)
    (hc : a.regs 2 = BitVec.ofNat 64 (8 * n)) (hb : ¬ InProgram boundary.rip)
    (steps : ∀ i : Fin 257,
      DataStep copy (dataPc copy i.castSucc) (dataPc copy i.succ) (dataOp i) (dataBytes copy i)) (k : Fin 258) :
    AdvanceTriple boundary k.val (PrefixInvariant copy initial n a 0) Extracted.programImage
      (fun _ t ↦ PrefixInvariant copy initial n a k t) := by
  induction k using Fin.induction with
  | zero =>
    intro s hready hcode hp
    exact ⟨s, (advances_zero boundary s s).mpr rfl, hready, hcode, hp⟩
  | succ i ih =>
    have hs := dataStep_advance copy (initial := initial) hn hc hb i (steps i)
    exact (ih.seq hs (fun _ _ _ hp ↦ hp)).conseq (fun _ hp ↦ hp)
      (fun _ _ _ ⟨_, _, hp⟩ ↦ hp)

end Sha3.Proofs.Permutation.RoundMachine
