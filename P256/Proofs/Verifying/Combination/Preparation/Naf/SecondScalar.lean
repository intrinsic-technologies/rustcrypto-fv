import P256.Proofs.Verifying.Combination.Preparation.Naf.FirstRecode
import P256.Proofs.Verifying.Combination.Preparation.Naf.FirstCopy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar

structure SecondScalarInput [Bindings] (s t : RamState) (p q : Projective) (u v : Nat) : Prop
    extends FrameState s t 96 8808 6552, NafCopyRegisters s t where
  rip : t.RIP = 0x1066de
  leftNaf : Combination.Naf.NafAt t (stackPtr s - 5200) u
  scalar : Nat256At t (stackPtr s - 6368 + 96) v
  leftTable : Table.TableAt t (stackPtr s - 3120) (Table.oddTable p)
  rightTable : Table.TableAt t (stackPtr s - 2352) (Table.oddTable q)
  savedOutput : memLoad t.external (stackPtr s - 6536) 64 = s.regValue .rdi
  cursorPointer : memLoad t.external (stackPtr s - 6528) 64 = stackPtr s - 6520
  pointPointer : memLoad t.external (stackPtr s - 6520) 64 = stackPtr s - 6368

theorem second_scalar_input [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {p q : Projective} {u v : Nat} (pre : Pre s boundary)
    (input : FirstRecodeOutput s t p q u v) :
    ∃ fuel a, Advances boundary fuel t a ∧ SecondScalarInput s a p q u v := by
  obtain ⟨n, a, run, stateA, ripA, naf, regs, kept⟩ := first_copies pre input.toFrameState
    input.rip input.naf input.iterator input.target input.buffer
  refine ⟨n, a, run, stateA, regs, ripA, naf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨input.second.1, ?_⟩
    intro i hi
    refine Eq.trans ?_ (input.second.2 i hi)
    have h := kept 6368 128 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide)
      (96+i) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using h
  · exact input.leftTable.of_copy (kept 3120 768 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide))
  · exact input.rightTable.of_copy (kept 2352 768 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide))
  · refine Eq.trans ?_ input.savedOutput
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (kept 6536 8 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide) i hi)
  · refine Eq.trans ?_ input.cursorPointer
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (kept 6528 8 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide) i hi)
  · refine Eq.trans ?_ input.pointPointer
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (kept 6520 8 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide) i hi)

end P256.Proofs.Verifying.Combination.Preparation.Naf
