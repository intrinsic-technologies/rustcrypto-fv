import P256.Proofs.Verifying.Combination.Preparation.Naf.SecondScalar

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def secondScalarSite : ScalarCallSite :=
  ⟨0x66e9, 0x4a82, by decide, by decide +kernel, by decide⟩

structure SecondRecodeOutput [Bindings] (s t : RamState) (p q : Projective) (u v : Nat) : Prop
    extends FrameState s t 96 8808 6552, NafCopyRegisters s t where
  rip : t.RIP = 0x1066ee
  leftNaf : Combination.Naf.NafAt t (stackPtr s - 5200) u
  rightNaf : Combination.Naf.NafAt t (stackPtr s - 6240) v
  leftTable : Table.TableAt t (stackPtr s - 3120) (Table.oddTable p)
  rightTable : Table.TableAt t (stackPtr s - 2352) (Table.oddTable q)
  savedOutput : memLoad t.external (stackPtr s - 6536) 64 = s.regValue .rdi

theorem second_recode (correct : Combination.Naf.Serialize.ScalarCorrect) [Bindings]
    {s t : RamState} {boundary : ReturnBoundary} {p q : Projective} {u v : Nat}
    (pre : Pre s boundary) (input : SecondScalarInput s t p q u v) :
    ∃ fuel w, Advances boundary fuel t w ∧ SecondRecodeOutput s w p q u v := by
  obtain ⟨n, a, runA, readyA, _, effectA⟩ := secondScalar_correct boundary pre.outerBoundary t
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0x66de secondScalarBytes
      (by decide) (by decide +kernel)) input.rip
  have agreesA : AgreesExcept [.reg 2, .reg 7, .reg 6, .rip] t a := effectA.agrees
  have stateA := input.toFrameState.after_registers readyA agreesA (by simp [Component.Covers]) (by simp)
  have memoryA := agreesA.external (by simp [Component.Covers])
  have scalarA : P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At a (stackPtr s - 6368 + 96) v := by
    refine ⟨input.scalar.1, ?_⟩
    intro i hi
    rw [memoryA]
    exact input.scalar.2 i hi
  have cursorA : memLoad a.external (stackPtr s - 6528) 64 = stackPtr s - 6520 := by
    rw [memoryA]; exact input.cursorPointer
  have pointA : memLoad a.external (stackPtr s - 6520) 64 = stackPtr s - 6368 := by
    rw [memoryA]; exact input.pointPointer
  obtain ⟨m, w, runW, stateW, ripW, naf, _, regs, kept⟩ := serialize_call_of_correct correct
    pre stateA secondScalarSite (by decide) (by decide) effectA.rip
    (effectA.writes.2.2.trans input.input) (effectA.writes.2.1.trans input.temporary)
    cursorA pointA scalarA
  have savedRegs : NafCopyRegisters s w := by
    constructor
    · exact (regs .rbp (by simp)).trans
        ((agreesA.read (n := 64) (r := 5) (by simp)).trans input.input)
    · exact (regs .r14 (by simp)).trans
        ((agreesA.read (n := 64) (r := 14) (by simp)).trans input.target)
    · exact (regs .r12 (by simp)).trans
        ((agreesA.read (n := 64) (r := 12) (by simp)).trans input.first)
    · exact (regs .r13 (by simp)).trans
        ((agreesA.read (n := 64) (r := 13) (by simp)).trans input.second)
    · exact (regs .r15 (by simp)).trans
        ((agreesA.read (n := 64) (r := 15) (by simp)).trans input.third)
    · exact (regs .rbx (by simp)).trans
        ((agreesA.read (n := 64) (r := 3) (by simp)).trans input.temporary)
  have memoryW (off len : Nat) (ho : off ≤ 6552) (hl : len ≤ off+8)
      (apart : off+272 ≤ 6240 ∨ 6240+len ≤ off)
      (apartCur : off+8 ≤ 6520 ∨ 6520+len ≤ off) :
      ∀ i < len, w.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
        t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? := by
    intro i hi
    exact (kept off len ho hl apart apartCur i hi).trans
      (congrArg (fun ram : Ram => ram[_]?) memoryA)
  refine ⟨n+m, w, runA.trans runW, stateW, savedRegs, ripW, ?_, naf, ?_, ?_, ?_⟩
  · exact input.leftNaf.of_copy (memoryW 5200 272 (by decide) (by decide)
      (Or.inl (by decide)) (Or.inl (by decide)))
  · exact input.leftTable.of_copy (memoryW 3120 768 (by decide) (by decide)
      (Or.inl (by decide)) (Or.inl (by decide)))
  · exact input.rightTable.of_copy (memoryW 2352 768 (by decide) (by decide)
      (Or.inl (by decide)) (Or.inl (by decide)))
  · refine Eq.trans ?_ input.savedOutput
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (memoryW 6536 8 (by decide) (by decide)
      (Or.inr (by decide)) (Or.inr (by decide)) i hi)

end P256.Proofs.Verifying.Combination.Preparation.Naf
