import Hkdf.Proofs.NewExpand.Expand.LoopState
import Hkdf.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Test.Generated.AccImm8.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem previousBranch [Bindings] {s : RamState} {boundary : ReturnBoundary} {n : Nat}
    {key : ByteArray} (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (pc : s.RIP = 0x10f66c) (outside : ¬ InProgram boundary.rip)
    (flag : (s.regValue .rax).setWidth 8 = if n = 0 then 0 else 1)
    (hmac : HmacAt s (stackPtr s + 272) key ByteArray.empty)
    (readable : MemReadable s (stackPtr s + 335) 1) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      t.RIP = (if n = 0 then 0x10f6c3 else 0x10f682) ∧
      (n ≠ 0 → t.regValue .rbx = 0) ∧ AgreesExcept [.reg 3,.flags,.rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨a, runA, readyA, tested⟩ := (test_al_imm8_effect_step 0x10f66c 1).advances ready
    (programText_slice code 0xf66c _ (by decide) (by decide +kernel)) pc
    (boundary_ne_program outside (inProgram_of_textOffset 0xf66e (by decide)))
  have fA : AgreesExcept [.flags,.rip] s a := tested.agrees
  have zero := tested.flags.2.2.2.1
  change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = (((s.regValue .rax).setWidth 8 &&& 1) == 0) at zero
  rw [flag] at zero
  obtain ⟨b, stepB, readyB, jumped⟩ := jcc_rel8_effect_step 0x10f66e 4 0x53 a readyA
    (programText_slice (fA.codeIn (by simp [Component.Covers]) code) 0xf66e _
      (by decide) (by decide +kernel)) ⟨tested.rip, fun _ ↦ by decide⟩
  have pcB : b.RIP = (if n = 0 then 0x10f6c3 else 0x10f670) := by
    rw [jumped.rip]
    change (if (StatusFlags.ofRFLAGS a.RFLAGS).ZF then 0x10f6c3 else 0x10f670) = _
    rw [zero]
    split <;> rfl
  have runB := Advances.of_step (boundary := boundary) stepB (.inl (by
    rw [pcB]; split
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf6c3 (by decide))
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf670 (by decide))))
  have fB : AgreesExcept [.rip] a b := jumped.agrees
  have first : AgreesExcept [.flags,.rip] s b := (fA.trans fB).mono (by simp)
  by_cases h : n = 0
  · exact ⟨2, b, runA.trans runB, readyB, by simpa only [h, ↓reduceIte] using pcB,
      fun hn ↦ (hn h).elim, first.mono (by simp)⟩
  simp only [h, ↓reduceIte] at pcB ⊢
  have spB : stackPtr b = stackPtr s := first.read (n := 64) (r := 4) (by decide)
  have memB := first.external (by simp [Component.Covers])
  have codeB := first.codeIn (by simp [Component.Covers]) code
  obtain ⟨c, runC, readyC, load⟩ := (movzx_r32_m8_effect_step 0x10f670 3 (.sib 4 none 0 (.d32 335))
    (by decide) rfl rfl).advances readyB
    (programText_slice codeB 0xf670 _ (by decide) (by decide +kernel))
    ⟨pcB, by
      change MemReadable b (stackPtr b + 335) 1
      rw [spB]
      exact ⟨readable.low, fun i hi ↦ first.grow _ (readable.mem i hi)⟩⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0xf678 (by decide)))
  have fC : AgreesExcept [.reg 3,.rip] b c := load.agrees
  have rbxC : c.regValue .rbx = 0 := by
    have word : c.regValue .rbx = (memLoad b.external (stackPtr b + 335) 8).setWidth 64 := load.writes
    rw [word, spB, memB, memLoad_8]
    have emptyTail := hmac.inner.tailLength
    simp only [ByteArray.size_append, HMAC.xorPad_keyBlock_size, ByteArray.size_empty,
      Nat.add_zero, Nat.reduceMod, BitVec.add_assoc, BitVec.reduceAdd] at emptyTail
    change ((s.external[stackPtr s + 335]?).getD 0).toBitVec.setWidth 64 = 0
    change s.external[stackPtr s + 335]? = some 0 at emptyTail
    rw [emptyTail]
    rfl
  obtain ⟨d, runD, readyD, cmp⟩ := (cmp_r64_imm8_effect_step 0x10f678 0x48 0xfb 31
    (by simp [RexWPrefix]) rfl rfl).advances readyC
    (programText_slice (fC.codeIn (by simp [Component.Covers]) codeB) 0xf678 _
      (by decide) (by decide +kernel)) load.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xf67c (by decide)))
  have fD : AgreesExcept [.flags,.rip] c d := cmp.agrees
  have carry : (StatusFlags.ofRFLAGS d.RFLAGS).CF = decide ((c.regValue .rbx).toNat < 31) := cmp.flags.1
  rw [rbxC] at carry
  obtain ⟨t, stepT, readyT, jump⟩ := jcc_rel32_effect_step 0x10f67c 7 0x18e d readyD
    (programText_slice ((fC.trans fD).codeIn (by simp [Component.Covers]) codeB) 0xf67c _
      (by decide) (by decide +kernel)) ⟨cmp.rip, fun _ ↦ by decide⟩
  have pcT : t.RIP = 0x10f682 := by
    rw [jump.rip]
    change (if !((StatusFlags.ofRFLAGS d.RFLAGS).CF || (StatusFlags.ofRFLAGS d.RFLAGS).ZF)
      then 0x10f810 else 0x10f682) = _
    simp only [carry, BitVec.reduceToNat, Nat.reduceLT, decide_true, Bool.true_or,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have runT := Advances.of_step (boundary := boundary) stepT (.inl (by
    rw [pcT]
    exact boundary_ne_program outside (inProgram_of_textOffset 0xf682 (by decide))))
  have fT : AgreesExcept [.rip] d t := jump.agrees
  exact ⟨5, t, (((runA.trans runB).trans runC).trans runD).trans runT, readyT, pcT,
    fun _ ↦ ((fD.trans fT).read (n := 64) (r := 3) (by simp)).trans rbxC,
    (((first.trans fC).trans fD).trans fT).mono (by simp)⟩

end Hkdf.Proofs.NewExpand.Expand
