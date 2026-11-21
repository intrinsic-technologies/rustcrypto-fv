import P256.Proofs.Verifying.Combination.Loop.MultiMaximum
import P256.Proofs.Verifying.Combination.Loop.MultiSecondLength
import P256.Proofs.Verifying.Combination.Loop.MultiLengthFinish

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem entry_maximum [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q : Projective} {u v : Nat}
    (pre : MultiPre s boundary tables digits)
    (leftTable : Table.TableAt s tables (Table.oddTable p))
    (rightTable : Table.TableAt s (tables + 768) (Table.oddTable q))
    (leftDigits : Naf.NafAt s digits u) (rightDigits : Naf.NafAt s (digits + 272) v)
    (hu : u < 2^256) (hv : v < 2^256) :
    ∃ fuel t, Advances boundary fuel s t ∧ Memory s t tables digits p q u v ∧
      t.RIP = 0x10f11a ∧ t.regValue .rax = s.regValue .rsi ∧
      t.regValue .rdx = 0 ∧ t.regValue .r8 = digits ∧ t.regValue .r9 = 0 ∧
      t.regValue .rbx = BitVec.ofNat 64 (max (Naf.digits u).length (Naf.digits v).length) ∧
      memLoad t.external (stackPtr s - 400) 64 = 2 ∧
      memLoad t.external (stackPtr s - 392) 64 = s.regValue .rdi := by
  obtain ⟨fa, a, runA, memoryA, ripA, axA, dxA, siA, ptrA, indexA, nextA, lengthA, countA, outA⟩ :=
    entry_first_length pre leftTable rightTable leftDigits rightDigits
  obtain ⟨b, runB, stateB, ripB, siB, frameB⟩ :=
    remaining_count pre memoryA.toFrameState ripA siA nextA
  obtain ⟨fc, c, runC, stateC, ripC, _, nextC, cfC, frameC⟩ :=
    maximum_setup pre stateB ripB siB (by
      rw [frameB.external (by simp [Component.Covers])]
      exact countA)
  obtain ⟨d, runD, stateD, ripD, offsetD, frameD⟩ := short_maximum pre stateC ripC cfC
  have frameAD : AgreesExcept [.reg 6, .reg 10, .reg 1, .reg 7, .flags, .rip] a d :=
    ((frameB.trans frameC).trans frameD).mono (by simp)
  obtain ⟨fe, e, runE, stateE, ripE, ptrE, countE, offsetE, frameE⟩ :=
    second_length_setup pre stateD ripD
      ((frameAD.read (n := 64) (r := 8) (by simp)).trans ptrA)
      ((frameAD.read (n := 64) (r := 9) (by simp)).trans indexA)
      offsetD ((frameD.read (n := 64) (r := 1) (by simp)).trans nextC)
  have frameAE : AgreesExcept [.reg 6, .reg 10, .reg 1, .reg 7, .flags, .rip] a e :=
    (frameAD.trans frameE).mono (by simp)
  have memoryE := memory_of_frame pre stateE leftTable rightTable leftDigits rightDigits
  obtain ⟨f, runF, stateF, ripF, maximumF, frameF⟩ :=
    select_length pre stateE ripE ptrE offsetE
      ((frameAE.read (n := 64) (r := 3) (by simp)).trans lengthA)
      memoryE.rightDigits.length hu hv
  obtain ⟨t, runT, stateT, ripT, frameT⟩ := length_finish pre stateF ripF
    ((frameF.read (n := 64) (r := 7) (by simp)).trans offsetE)
    ((frameF.read (n := 64) (r := 1) (by simp)).trans countE)
  have frame : AgreesExcept [.reg 6, .reg 10, .reg 1, .reg 7, .reg 3, .flags, .rip] a t :=
    ((frameAE.trans frameF).trans frameT).mono (by simp)
  refine ⟨fa+2+fc+3+fe+4+3, t,
    (((((runA.trans runB).trans runC).trans runD).trans runE).trans runF).trans runT,
    memory_of_frame pre stateT leftTable rightTable leftDigits rightDigits, ripT,
    (frame.read (n := 64) (r := 0) (by simp)).trans axA,
    (frame.read (n := 64) (r := 2) (by simp)).trans dxA,
    (frame.read (n := 64) (r := 8) (by simp)).trans ptrA,
    (frame.read (n := 64) (r := 9) (by simp)).trans indexA,
    (frameT.read (n := 64) (r := 3) (by simp)).trans maximumF, ?_, ?_⟩
  · rw [frame.external (by simp [Component.Covers])]; exact countA
  · rw [frame.external (by simp [Component.Covers])]; exact outA

end P256.Proofs.Verifying.Combination.Loop.Multi
