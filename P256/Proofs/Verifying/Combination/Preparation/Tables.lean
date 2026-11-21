import P256.Proofs.Verifying.Combination.Preparation.SecondTable
import P256.Proofs.Verifying.Combination.Table.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare_tables [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {p q : Projective} {u v : Nat} (pre : Pre s boundary)
    (input : InputAt s (s.regValue .rsi) p q u v) :
    ∃ fuel t, Advances boundary fuel s t ∧ TablesOutput s t p q :=
  prepare_tables_of_correct Table.correct pre input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame TableSetup

def tablePackSite : CopyCallSite 1536 :=
  ⟨0x6636, by decide, by decide +kernel,
    ⟨6560, 1584, 3120, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩, rfl, by decide⟩

structure PackedTablesOutput [Bindings] (s t : RamState) (p q : Projective) : Prop
    extends FrameState s t 96 8808 6552, CopyRegisters s t 4656 where
  rip : t.RIP = 0x106639
  leftTable : Table.TableAt t (stackPtr s - 3120) (Table.oddTable p)
  rightTable : Table.TableAt t (stackPtr s - 2352) (Table.oddTable q)
  savedInput : memLoad t.external (stackPtr s - 6544) 64 = s.regValue .rsi
  savedOutput : memLoad t.external (stackPtr s - 6536) 64 = s.regValue .rdi

theorem pack_tables [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {p q : Projective} (pre : Pre s boundary) (input : TablesOutput s t p q) :
    ∃ fuel w, Advances boundary fuel t w ∧ PackedTablesOutput s w p q := by
  obtain ⟨fuel, w, run, result⟩ := copy_after_setup pre input.toFrameState
    tablePackSite 0x6626 tablePackBytes tablePackEffect
    (by decide) (by decide +kernel) (tablePack_correct boundary pre.outerBoundary) input.rip
    (by simp [tablePackEffect, Effect.components, Write.component, Operand.component, Component.Covers])
    (by simp [tablePackEffect, Effect.components, Write.component, Operand.component]) rfl (by
      intro a h
      exact ⟨(h.agrees.read (n := 64) (r := 14) (by simp [tablePackEffect, Effect.components, Write.component, Operand.component])).trans input.target,
        h.writes.1,
        h.writes.2.2.trans (scalar_stack_address (frameOffset := 6552) input.rsp
          (offset := 4968) (by decide) (by decide)), h.writes.2.1.trans input.third⟩)
  have regs : CopyRegisters s w 4656 := by
    constructor
    · exact result.registers .r15 (by simp) _ (fun _ h =>
        (h.agrees.read (n := 64) (r := 15) (by simp [tablePackEffect, Effect.components, Write.component, Operand.component])).trans input.input)
    · exact result.registers .r14 (by simp) _ (fun _ h =>
        (h.agrees.read (n := 64) (r := 14) (by simp [tablePackEffect, Effect.components, Write.component, Operand.component])).trans input.target)
    · exact result.registers .rbx (by simp) _ (fun _ h =>
        (h.agrees.read (n := 64) (r := 3) (by simp [tablePackEffect, Effect.components, Write.component, Operand.component])).trans input.first)
    · exact result.registers .r12 (by simp) _ (fun _ h =>
        (h.agrees.read (n := 64) (r := 12) (by simp [tablePackEffect, Effect.components, Write.component, Operand.component])).trans input.second)
    · exact result.registers .r13 (by simp) _ (fun _ h =>
        (h.agrees.read (n := 64) (r := 13) (by simp [tablePackEffect, Effect.components, Write.component, Operand.component])).trans input.third)
    · exact result.registers .rbp (by simp) _ (fun _ h =>
        (h.agrees.read (n := 64) (r := 5) (by simp [tablePackEffect, Effect.components, Write.component, Operand.component])).trans input.temporary)
  refine ⟨fuel, w, run, result.toFrameState, regs, result.rip, ?_, ?_, ?_, ?_⟩
  · exact input.leftTable.of_copy (fun i hi => result.bytes i (by omega))
  · apply input.rightTable.of_copy
    intro i hi
    have h := result.bytes (768+i) (by omega)
    change w.external[stackPtr s - 3120 + BitVec.ofNat 64 (768+i)]? =
      t.external[stackPtr s - 1584 + BitVec.ofNat 64 (768+i)]? at h
    have left : stackPtr s - 3120 + BitVec.ofNat 64 (768+i) =
        stackPtr s - 2352 + BitVec.ofNat 64 i := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      apply congrArg (fun x : BitVec 64 => x + BitVec.ofNat 64 i)
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    have right : stackPtr s - 1584 + BitVec.ofNat 64 (768+i) =
        stackPtr s - 816 + BitVec.ofNat 64 i := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      apply congrArg (fun x : BitVec 64 => x + BitVec.ofNat 64 i)
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rwa [left, right] at h

  · refine Eq.trans ?_ input.savedInput
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0)
      (result.kept 6544 8 (by decide) (by decide) (Or.inr (by decide)) i hi)
  · refine Eq.trans ?_ input.savedOutput
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0)
      (result.kept 6536 8 (by decide) (by decide) (Or.inr (by decide)) i hi)

end P256.Proofs.Verifying.Combination.Preparation
