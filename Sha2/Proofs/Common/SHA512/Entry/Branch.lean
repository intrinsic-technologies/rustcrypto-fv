import Sha2.Proofs.Common.SHA512.State
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem entry_branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt64} {input : ByteArray} {count : Nat}
    (pre : CompressionPre s boundary hash input count) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if count = 0 then 0x11184c else 0x10dd99) ∧
      AgreesExcept [.flags, .rip] s t := by
  have hbound : count < 2^64 := by
    have hb := pre.inputBounded
    change (s.regValue .rsi).toNat + 128 * count < 2^32 at hb
    omega
  have hz : (s.regValue .rdx = 0) ↔ count = 0 := by
    rw [pre.countRegister]
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] at hn
      exact hn
    · rintro rfl
      rfl
  obtain ⟨u, hu, hru, heu⟩ :=
    (test_r64_r64_effect_step 0x10dd90 0x48 0xd2 (by constructor <;> rfl) rfl).advances
      (supportedMachine_readyToStep pre.machine)
      (programText_slice (programLoaded_codeIn pre.loaded) 0xdd90
        [0x48,0x85,0xd2] (by decide +kernel) (by decide +kernel)) pre.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xdd93 (by decide +kernel)))
  have hfu : AgreesExcept [.flags,.rip] s u := heu.agrees
  have zf : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .rdx == 0) := by
    have h := heu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = ((s.regValue .rdx &&& s.regValue .rdx) == 0) at h
    simpa only [BitVec.and_self] using h
  obtain ⟨t, step, hrt, het⟩ := jcc_rel32_effect_step 0x10dd93 4 0x3ab3 u hru
    (programText_slice (hfu.codeIn (by simp [Component.Covers]) (programLoaded_codeIn pre.loaded))
      0xdd93 [0x0f,0x84,0xb3,0x3a,0,0] (by decide +kernel) (by decide +kernel))
    ⟨heu.rip, fun _ => by decide +kernel⟩
  have ht : t.RIP = (if count = 0 then 0x11184c else 0x10dd99) := by
    rw [het.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then (0x11184c : BitVec 64) else 0x10dd99) = _
    rw [zf]
    simp only [beq_iff_eq, hz]
  have ha : Advances boundary 1 u t := Advances.of_step step (.inl (by
    rw [ht]
    split
    · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1184c (by decide +kernel))
    · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xdd99 (by decide +kernel))))
  have hft : AgreesExcept [.rip] u t := het.agrees
  exact ⟨t, hu.trans ha, hrt, ht, (hfu.trans hft).mono (by simp)⟩

end Sha2.Proofs.Common.SHA512
