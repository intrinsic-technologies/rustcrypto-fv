import P256.Proofs.Sec1.Decode.Header.Length

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def Header.accepts (tag : BitVec 8) (length : BitVec 64) : Bool :=
  Header.validTag tag && length == Header.expectedLength tag

theorem header [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x10e4f7)
    (readable : MemReadable s (s.regValue .rsi) 1) :
    ∃ t, Advances boundary
        (if Header.validTag (memLoad s.external (s.regValue .rsi) 8) then 10 else 8) s t ∧
      ReadyToStep t ∧
      t.RIP = (if Header.accepts (memLoad s.external (s.regValue .rsi) 8) (s.regValue .rdx)
        then 0x10e522 else 0x10e68e) ∧
      t.regValue .rcx = (memLoad s.external (s.regValue .rsi) 8).setWidth 64 ∧
      AgreesExcept [.reg 0, .reg 1, .reg 8, .flags, .rip] s t := by
  obtain ⟨u, au, ru, ripu, cxu, gu⟩ := Header.tag_branch ready loaded outside rip readable
  cases valid : Header.validTag (memLoad s.external (s.regValue .rsi) 8) with
  | false =>
    refine ⟨u, ?_, ru, ?_, cxu, gu⟩
    · simpa only [valid, Bool.false_eq_true, ↓reduceIte] using au
    · simpa only [Header.accepts, valid, Bool.false_and, Bool.false_eq_true, ↓reduceIte] using ripu
  | true =>
    have memu := gu.external (by simp [Component.Covers])
    have loadedU : ProgramLoaded u := by
      intro a b hb
      rw [memu]
      exact loaded a b hb
    have du : u.regValue .rdx = s.regValue .rdx := gu.read (n := 64) (r := 2) (by simp)
    obtain ⟨t, runT, rt, ript, gt⟩ := Header.length_branch ru loadedU outside
      (by simpa only [valid, ↓reduceIte] using ripu)
      (memLoad s.external (s.regValue .rsi) 8) valid cxu
    refine ⟨t, ?_, rt, ?_, ?_, (gu.trans gt).mono (by simp)⟩
    · simpa only [valid, ↓reduceIte] using au.trans runT
    · simpa only [Header.accepts, valid, Bool.true_and, beq_iff_eq, du] using ript
    · exact (gt.read (n := 64) (r := 1) (by simp)).trans cxu

end P256.Proofs.Sec1.Decode
