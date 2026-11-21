import P256.Proofs.Verifying.Combination.Preparation.Naf.SecondRecode
import P256.Proofs.Verifying.Combination.Preparation.Naf.SecondCopy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame TableSetup
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure SecondCopiesOutput [Bindings] (s t : RamState) (p q : Projective) (u v : Nat) : Prop
    extends FrameState s t 96 8808 6552, NafCopyRegisters s t where
  rip : t.RIP = 0x10672b
  leftNaf : Combination.Naf.NafAt t (stackPtr s - 5200) u
  rightNaf : Combination.Naf.NafAt t (stackPtr s - 4928) v
  leftTable : Table.TableAt t (stackPtr s - 3120) (Table.oddTable p)
  rightTable : Table.TableAt t (stackPtr s - 2352) (Table.oddTable q)
  savedOutput : memLoad t.external (stackPtr s - 6536) 64 = s.regValue .rdi

theorem second_copy_result [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {p q : Projective} {u v : Nat} (pre : Pre s boundary)
    (input : SecondRecodeOutput s t p q u v) :
    ∃ fuel w, Advances boundary fuel t w ∧ SecondCopiesOutput s w p q u v := by
  obtain ⟨n, w, run, stateW, ripW, naf, regs, kept⟩ := second_copies pre input.toFrameState
    input.rip input.rightNaf input.toNafCopyRegisters
  refine ⟨n, w, run, stateW, regs, ripW, ?_, naf, ?_, ?_, ?_⟩
  · exact input.leftNaf.of_copy (kept 5200 272 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide))
  · exact input.leftTable.of_copy (kept 3120 768 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide))
  · exact input.rightTable.of_copy (kept 2352 768 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide))
  · refine Eq.trans ?_ input.savedOutput
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (kept 6536 8 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide) i hi)

def scalarPackSite : CopyCallSite 544 :=
  ⟨0x673b, by decide, by decide +kernel,
    ⟨6560, 5200, 4656, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩, rfl, by decide⟩

structure PackedNafOutput [Bindings] (s t : RamState) (p q : Projective) (u v : Nat) : Prop
    extends FrameState s t 96 8808 6552, NafCopyRegisters s t where
  rip : t.RIP = 0x10673e
  leftNaf : Combination.Naf.NafAt t (stackPtr s - 4656) u
  rightNaf : Combination.Naf.NafAt t (stackPtr s - 4384) v
  leftTable : Table.TableAt t (stackPtr s - 3120) (Table.oddTable p)
  rightTable : Table.TableAt t (stackPtr s - 2352) (Table.oddTable q)
  savedOutput : memLoad t.external (stackPtr s - 6536) 64 = s.regValue .rdi

theorem third_copy [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {p q : Projective} {u v : Nat} (pre : Pre s boundary)
    (input : SecondCopiesOutput s t p q u v) :
    ∃ fuel w, Advances boundary fuel t w ∧ PackedNafOutput s w p q u v := by
  obtain ⟨fuel, w, run, result⟩ := copy_after_setup pre input.toFrameState
    scalarPackSite 0x672b scalarPackBytes scalarPackEffect
    (by decide) (by decide +kernel) (scalarPack_correct boundary pre.outerBoundary) input.rip
    (by simp [scalarPackEffect, Effect.components, Write.component, Operand.component, Component.Covers])
    (by simp [scalarPackEffect, Effect.components, Write.component, Operand.component]) rfl (by
      intro a h
      exact ⟨(h.agrees.read (n := 64) (r := 14) (by simp [scalarPackEffect, Effect.components, Write.component, Operand.component])).trans input.target,
        h.writes.1,
        h.writes.2.2.trans (scalar_stack_address (frameOffset := 6552) input.rsp
          (offset := 1352) (by decide) (by decide)), h.writes.2.1.trans input.third⟩)
  have regs : NafCopyRegisters s w := by
    constructor
    · exact result.registers .rbp (by simp) _ (fun _ h =>
        (h.agrees.read (n := 64) (r := 5) (by simp [scalarPackEffect, Effect.components, Write.component, Operand.component])).trans input.input)
    · exact result.registers .r14 (by simp) _ (fun _ h =>
        (h.agrees.read (n := 64) (r := 14) (by simp [scalarPackEffect, Effect.components, Write.component, Operand.component])).trans input.target)
    · exact result.registers .r12 (by simp) _ (fun _ h =>
        (h.agrees.read (n := 64) (r := 12) (by simp [scalarPackEffect, Effect.components, Write.component, Operand.component])).trans input.first)
    · exact result.registers .r13 (by simp) _ (fun _ h =>
        (h.agrees.read (n := 64) (r := 13) (by simp [scalarPackEffect, Effect.components, Write.component, Operand.component])).trans input.second)
    · exact result.registers .r15 (by simp) _ (fun _ h =>
        (h.agrees.read (n := 64) (r := 15) (by simp [scalarPackEffect, Effect.components, Write.component, Operand.component])).trans input.third)
    · exact result.registers .rbx (by simp) _ (fun _ h =>
        (h.agrees.read (n := 64) (r := 3) (by simp [scalarPackEffect, Effect.components, Write.component, Operand.component])).trans input.temporary)
  refine ⟨fuel, w, run, result.toFrameState, regs, result.rip, ?_, ?_, ?_, ?_, ?_⟩
  · exact input.leftNaf.of_copy (fun i hi => result.bytes i (by omega))
  · apply input.rightNaf.of_copy
    intro i hi
    have h := result.bytes (272+i) (by omega)
    change w.external[stackPtr s - 4656 + BitVec.ofNat 64 (272+i)]? =
      t.external[stackPtr s - 5200 + BitVec.ofNat 64 (272+i)]? at h
    have left : stackPtr s - 4656 + BitVec.ofNat 64 (272+i) =
        stackPtr s - 4384 + BitVec.ofNat 64 i := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      apply congrArg (fun x : BitVec 64 => x + BitVec.ofNat 64 i)
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    have right : stackPtr s - 5200 + BitVec.ofNat 64 (272+i) =
        stackPtr s - 4928 + BitVec.ofNat 64 i := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      apply congrArg (fun x : BitVec 64 => x + BitVec.ofNat 64 i)
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rwa [left, right] at h
  · exact input.leftTable.of_copy (result.kept 3120 768 (by decide) (by decide) (Or.inl (by decide)))
  · exact input.rightTable.of_copy (result.kept 2352 768 (by decide) (by decide) (Or.inl (by decide)))
  · refine Eq.trans ?_ input.savedOutput
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0)
      (result.kept 6536 8 (by decide) (by decide) (Or.inr (by decide)) i hi)

end P256.Proofs.Verifying.Combination.Preparation.Naf
