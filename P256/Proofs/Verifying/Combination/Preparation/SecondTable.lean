import P256.Proofs.Verifying.Combination.Preparation.FirstTable
import P256.Proofs.Verifying.Combination.TableSetup.Right

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame TableSetup
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def secondTableSite : TableCallSite :=
  ⟨0x65e4, 0x4a07, by decide, by decide +kernel, by decide⟩

structure TablesOutput [Bindings] (s t : RamState) (p q : Projective) : Prop
    extends FrameState s t 96 8808 6552, CopyRegisters s t 4656 where
  rip : t.RIP = 0x106626
  leftTable : Table.TableAt t (stackPtr s - 1584) (Table.oddTable p)
  rightTable : Table.TableAt t (stackPtr s - 816) (Table.oddTable q)
  savedInput : memLoad t.external (stackPtr s - 6544) 64 = s.regValue .rsi
  savedOutput : memLoad t.external (stackPtr s - 6536) 64 = s.regValue .rdi

theorem second_table_of_correct (correct : Table.Correct) [Bindings]
    {s t : RamState} {boundary : ReturnBoundary} {p q : Projective}
    (pre : Pre s boundary) (input : FirstTableOutput s t p q) :
    ∃ fuel w, Advances boundary fuel t w ∧ TablesOutput s w p q := by
  obtain ⟨n, a, runA, readyA, _, effectA⟩ := rightTable_correct boundary pre.outerBoundary t
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0x65d9 rightTableBytes
      (by decide) (by decide +kernel)) input.rip
  have agreesA : AgreesExcept [.reg 2, .reg 7, .reg 6, .rip] t a := effectA.agrees
  have stateA := input.toFrameState.after_registers readyA agreesA
    (by simp [Component.Covers]) (by simp)
  have memoryA := agreesA.external (by simp [Component.Covers])
  have argsA : a.regValue .rdx = 1 ∧ a.regValue .rdi = t.regValue .rbp ∧
      a.regValue .rsi = t.regValue .r15 := effectA.writes
  have cursorA : memLoad a.external (stackPtr s - 6520) 64 = stackPtr s - 6496 := by
    rw [memoryA]; exact input.cursor
  have pointA : memLoad a.external (stackPtr s - 6496) 64 = stackPtr s - 5344 := by
    rw [memoryA]; exact input.point
  have rightA := input.right.of_bytes_eq (fun _ _ => congrArg (fun ram : Ram => ram[_]?) memoryA)
  obtain ⟨m, b, runB, stateB, ripB, tableB, _, regsB, keptB⟩ :=
    table_call_of_correct correct pre stateA secondTableSite (by decide) (by decide)
      effectA.rip
      (argsA.2.2.trans input.input)
      (argsA.2.1.trans input.temporary) cursorA pointA rightA
  have savedRegs : CopyRegisters s b 4656 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (regsB .r15 (by simp)).trans
        ((agreesA.read (n := 64) (r := 15) (by simp)).trans input.input)
    · exact (regsB .r14 (by simp)).trans
        ((agreesA.read (n := 64) (r := 14) (by simp)).trans input.target)
    · exact (regsB .rbx (by simp)).trans
        ((agreesA.read (n := 64) (r := 3) (by simp)).trans input.first)
    · exact (regsB .r12 (by simp)).trans
        ((agreesA.read (n := 64) (r := 12) (by simp)).trans input.second)
    · exact (regsB .r13 (by simp)).trans
        ((agreesA.read (n := 64) (r := 13) (by simp)).trans input.third)
    · exact (regsB .rbp (by simp)).trans
        ((agreesA.read (n := 64) (r := 5) (by simp)).trans input.temporary)
  have leftB : Table.TableAt b (stackPtr s - 1584) (Table.oddTable p) := by
    apply input.table.of_copy
    intro i hi
    exact (keptB 1584 768 (by decide) (by decide) (Or.inl (by decide))
      (Or.inl (by decide)) i hi).trans (congrArg (fun ram : Ram => ram[_]?) memoryA)
  have originalB : memLoad b.external (stackPtr s - 6544) 64 = s.regValue .rsi := by
    refine Eq.trans ?_ input.savedInput
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 => x.getD 0)
    exact (keptB 6544 8 (by decide) (by decide) (Or.inr (by decide))
      (Or.inr (by decide)) i hi).trans (congrArg (fun ram : Ram => ram[_]?) memoryA)
  have outputB : memLoad b.external (stackPtr s - 6536) 64 = s.regValue .rdi := by
    refine Eq.trans ?_ input.savedOutput
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 => x.getD 0)
    exact (keptB 6536 8 (by decide) (by decide) (Or.inr (by decide))
      (Or.inr (by decide)) i hi).trans (congrArg (fun ram : Ram => ram[_]?) memoryA)
  obtain ⟨k, w, runW, stateW, ripW, tableW, regsW, keptW⟩ :=
    right_table_copies pre stateB ripB tableB savedRegs
  refine ⟨n+m+k, w, (runA.trans runB).trans runW, stateW, regsW, ripW, ?_, tableW, ?_, ?_⟩
  · exact leftB.of_copy (keptW 1584 768 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide))
  · refine Eq.trans ?_ originalB
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0)
      (keptW 6544 8 (by decide) (by decide)
        (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide) i hi)
  · refine Eq.trans ?_ outputB
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0)
      (keptW 6536 8 (by decide) (by decide)
        (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide) i hi)

theorem prepare_tables_of_correct (correct : Table.Correct) [Bindings]
    {s : RamState} {boundary : ReturnBoundary} {p q : Projective} {u v : Nat}
    (pre : Pre s boundary) (input : InputAt s (s.regValue .rsi) p q u v) :
    ∃ fuel t, Advances boundary fuel s t ∧ TablesOutput s t p q := by
  obtain ⟨n, a, runA, inputA⟩ := first_table_input pre input
  obtain ⟨m, b, runB, inputB⟩ := first_table_of_correct correct pre inputA
  obtain ⟨k, t, runT, output⟩ := second_table_of_correct correct pre inputB
  exact ⟨n+m+k, t, (runA.trans runB).trans runT, output⟩

end P256.Proofs.Verifying.Combination.Preparation
