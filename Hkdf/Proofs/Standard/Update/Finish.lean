import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Standard.Update
import Hkdf.Proofs.Standard.Update.State
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.MR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Update

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine

def finishPC (short : Bool) : BitVec 64 := if short then 0x10163b else 0x101706

def finishBranchCC (short : Bool) : BitVec 4 := if short then 4 else 5

def finishBranchDisplacement (short : Bool) : BitVec 32 :=
  if short then 0xdb else 0xffffff35

theorem finish_input [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} {index : Nat} {short : Bool}
    (ctx : Context initial salt inputs) (ready : ReadyToStep s)
    (state : InputDone initial s salt inputs index short) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      ((index + 1 = inputs.size ∧ Completed initial t salt inputs) ∨
        LoopState initial t salt inputs (index + 1)) := by
  have outside := (returnBoundary_valid ctx).2.2
  have incCode : CodeIn (codeRange (finishPC short) [0x49, 0xff, 0xc6]) s := by
    cases short
    · exact programText_slice (programLoaded_codeIn state.loaded) 0x1706 _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn state.loaded) 0x163b _
        (by decide) (by decide +kernel)
  have afterInc : InProgram (finishPC short + 3) := by
    cases short
    · exact inProgram_of_textOffset 0x1709 (by decide)
    · exact inProgram_of_textOffset 0x163e (by decide)
  obtain ⟨u, incRun, incReady, inc⟩ :=
    (inc_r64_effect_step (finishPC short) 0x49 0xc6
      (by simp [RexWPrefix]) rfl rfl).advances ready incCode state.rip
      (boundary_ne_program outside afterInc)
  have incFrame : AgreesExcept [.reg 14, .flags, .rip] s u := inc.agrees
  have current := buffered_of_noMem ctx state.toBuffered incRun incReady incFrame
    (by simp [Component.Covers]) (by simp) (by simp)
  have indexU : u.regValue .r14 = BitVec.ofNat 64 (index + 1) := by
    have word : u.regValue .r14 = s.regValue .r14 + 1 := inc.writes
    rw [word, state.indexRegister, BitVec.ofNat_add]
    rfl
  have readable : MemReadable u (stackPtr u + 8) 8 := by
    change MemReadable u (rspOf u + BitVec.ofNat 64 8) 8
    rw [stack_address current.rsp (offset := 8) (by decide)]
    exact stack_readable ctx current.toState (by decide) (by decide)
  have countU : memLoad u.external (stackPtr u + 8) 64 = initial.regValue .rsi := by
    change memLoad u.external (u.regValue .rsp + 8) 64 = _
    rw [current.rsp]
    exact current.inputCount
  have cmpCode : CodeIn (codeRange (finishPC short + 3) [0x4c, 0x39, 0x74, 0x24, 8]) u := by
    cases short
    · exact programText_slice (programLoaded_codeIn current.loaded) 0x1709 _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn current.loaded) 0x163e _
        (by decide) (by decide +kernel)
  have afterCmp : InProgram (finishPC short + 3 + 5) := by
    cases short
    · exact inProgram_of_textOffset 0x170e (by decide)
    · exact inProgram_of_textOffset 0x1643 (by decide)
  obtain ⟨v, cmpRun, cmpReady, cmp⟩ :=
    (cmp_m64_r64_effect_step (finishPC short + 3) 0x4c (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances incReady cmpCode
      ⟨inc.rip, by change MemReadable u (stackPtr u + 8) 8; exact readable⟩
      (boundary_ne_program outside afterCmp)
  have cmpFrame : AgreesExcept [.flags, .rip] u v := cmp.agrees
  have currentV := buffered_of_noMem ctx current cmpRun cmpReady cmpFrame
    (by simp [Component.Covers]) (by simp) (by simp)
  have countBound := input_count_bound ctx.call.pointerTableValid
  have indexBound : index + 1 < 2^64 := by have := state.remaining; omega
  have equalWords : (initial.regValue .rsi == BitVec.ofNat 64 (index + 1)) =
      decide (index + 1 = inputs.size) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro eq
      have natEq := congrArg BitVec.toNat eq
      rw [ctx.call.countArgumentMatchesInputs, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt indexBound] at natEq
      omega
    · intro eq
      apply BitVec.eq_of_toNat_eq
      rw [ctx.call.countArgumentMatchesInputs, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt indexBound, eq]
  have zero : (StatusFlags.ofRFLAGS v.RFLAGS).ZF = decide (index + 1 = inputs.size) := by
    have flags := cmp.flag .ZF
    change (StatusFlags.ofRFLAGS v.RFLAGS).ZF =
      (cmpSpec (memLoad u.external (stackPtr u + 8) 64) (u.regValue .r14)).ZF at flags
    rw [cmpSpec_ZF, countU, indexU] at flags
    exact flags.trans equalWords
  have branchCode : CodeIn (codeRange (finishPC short + 8)
      (0x0f :: jccOpcode32 (finishBranchCC short) :: immBytes 32 (finishBranchDisplacement short))) v := by
    cases short
    · exact programText_slice (programLoaded_codeIn currentV.loaded) 0x170e _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn currentV.loaded) 0x1643 _
        (by decide) (by decide +kernel)
  have targetBound : (branchTarget (finishPC short + 8) 6
      ((finishBranchDisplacement short).signExtend 64)).toNat < 2^32 := by
    cases short <;> decide +kernel
  obtain ⟨w, branchStep, branchReady, branch⟩ :=
    jcc_rel32_effect_step (finishPC short + 8) (finishBranchCC short)
      (finishBranchDisplacement short) v cmpReady branchCode
      ⟨by cases short <;> exact cmp.rip, fun _ ↦ targetBound⟩
  have target : w.RIP = if index + 1 = inputs.size then
      (if short then 0x101724 else 0x101714) else 0x101649 := by
    rw [branch.rip]
    cases short
    · change (if !(StatusFlags.ofRFLAGS v.RFLAGS).ZF then 0x101649 else 0x101714) = _
      rw [zero]
      by_cases last : index + 1 = inputs.size <;> simp [last]
    · change (if (StatusFlags.ofRFLAGS v.RFLAGS).ZF then 0x101724 else 0x101649) = _
      rw [zero]
      simp only [decide_eq_true_eq, ite_true]
  have branchRun : Advances (returnBoundary initial) 1 v w := by
    apply Advances.of_step branchStep
    left
    rw [target]
    split
    · cases short
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x1714 (by decide))
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x1724 (by decide))
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1649 (by decide))
  have branchFrame : AgreesExcept [.rip] v w := branch.agrees
  have currentW := buffered_of_noMem ctx currentV branchRun branchReady branchFrame
    (by simp [Component.Covers]) (by simp) (by simp)
  by_cases last : index + 1 = inputs.size
  · have final : Buffered initial w salt (concatenation inputs) := by
      simpa only [last, prefixConcatenation_size] using currentW
    cases short
    · have jumpRip : w.RIP = 0x101714 := by simpa [last] using target
      obtain ⟨t, run, readyT, jump⟩ :=
        (jmp_rel8_effect_step 0x101714 0x0e (by decide)).advances branchReady
          (programText_slice (programLoaded_codeIn final.loaded) 0x1714 [0xeb, 0x0e]
            (by decide) (by decide +kernel)) jumpRip
          (boundary_ne_program outside (inProgram_of_textOffset 0x1724 (by decide)))
      have frame : AgreesExcept [.rip] w t := jump.agrees
      have finalT := buffered_of_noMem ctx final run readyT frame
        (by simp [Component.Covers]) (by simp) (by simp)
      exact ⟨4, t, ((incRun.trans cmpRun).trans branchRun).trans run, readyT,
        .inl ⟨last, ⟨finalT, jump.rip⟩⟩⟩
    · exact ⟨3, w, (incRun.trans cmpRun).trans branchRun, branchReady,
        .inl ⟨last, ⟨final, by simpa [last] using target⟩⟩⟩
  · refine ⟨3, w, (incRun.trans cmpRun).trans branchRun, branchReady, .inr
      ⟨currentW, ?_, ?_, ?_, by have := state.remaining; omega⟩⟩
    · simpa [last] using target
    · exact (branchFrame.read (n := 64) (r := 14) (by simp)).trans
        ((cmpFrame.read (n := 64) (r := 14) (by simp)).trans indexU)
    · exact ((incFrame.trans cmpFrame).trans branchFrame).read
        (n := 64) (r := 12) (by simp) |>.trans state.copyRegister

end Hkdf.Proofs.Standard.Update
