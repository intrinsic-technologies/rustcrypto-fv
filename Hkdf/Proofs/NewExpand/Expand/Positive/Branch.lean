import Hkdf.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine

theorem roundBranch [Bindings] {s : RamState} {boundary : ReturnBoundary} {length n : Nat}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pc : s.RIP = 0x10f57d) (remaining : s.regValue .rbp = BitVec.ofNat 64 (length - 32 * n))
    (bound : length < 2^64) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if 32 * n < length then 0x10f586 else 0x10f290) ∧
      AgreesExcept [.flags, .rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨u, testRun, readyU, tested⟩ :=
    (test_r64_r64_effect_step 0x10f57d 0x48 0xed (by constructor <;> rfl) rfl).advances
      ready (programText_slice code 0xf57d [0x48,0x85,0xed] (by decide) (by decide +kernel)) pc
      (boundary_ne_program outside (inProgram_of_textOffset 0xf580 (by decide)))
  have testFrame : AgreesExcept [.flags, .rip] s u := tested.agrees
  have zero := tested.flags.2.2.2.1
  change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = ((s.regValue .rbp &&& s.regValue .rbp) == 0) at zero
  rw [BitVec.and_self, remaining] at zero
  have zeroRemaining : BitVec.ofNat 64 (length - 32 * n) = 0 ↔ length ≤ 32 * n := by
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show length - 32 * n < 2^64 by omega),
        BitVec.reduceToNat] at hn
      omega
    · intro le
      rw [Nat.sub_eq_zero_of_le le]
      rfl
  obtain ⟨t, step, readyT, jumped⟩ := jcc_rel32_effect_step 0x10f580 4 0xfffffd0a u readyU
    (programText_slice (testFrame.codeIn (by simp [Component.Covers]) code)
      0xf580 [0x0f,0x84,0x0a,0xfd,0xff,0xff] (by decide) (by decide +kernel))
    ⟨tested.rip, fun _ => by decide⟩
  have next : t.RIP = (if 32 * n < length then 0x10f586 else 0x10f290) := by
    rw [jumped.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then (0x10f290 : BitVec 64) else 0x10f586) = _
    rw [zero]
    simp only [beq_iff_eq, zeroRemaining, ← Nat.not_lt, ite_not]
  have nextRun : Advances boundary 1 u t := Advances.of_step step (.inl (by
    rw [next]
    split
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf586 (by decide))
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf290 (by decide))))
  have nextFrame : AgreesExcept [.rip] u t := jumped.agrees
  exact ⟨t, testRun.trans nextRun, readyT, next, (testFrame.trans nextFrame).mono (by simp)⟩

end Hkdf.Proofs.NewExpand.Expand
