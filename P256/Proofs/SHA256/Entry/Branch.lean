import P256.Proofs.SHA256.Interface
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.SHA256

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem entry_branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray} {count : Nat}
    (pre : CompressionPre s boundary hash input count) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if count = 0 then 0x1181a8 else 0x115999) ∧
      AgreesExcept [.flags, .rip] s t := by
  have hbound : count < 2^64 := by
    have hb := pre.inputBounded
    change (s.regValue .rsi).toNat + 64 * count < 2^32 at hb
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
    (test_r64_r64_effect_step 0x115990 0x48 0xd2 (by constructor <;> rfl) rfl).advances
      (readyToStep pre.machine pre.bindingsSupported)
      (programText_slice (programLoaded_codeIn pre.loaded) 0x15990
        [0x48,0x85,0xd2] (by decide +kernel) (by decide +kernel)) pre.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x15993 (by decide +kernel)))
  have hfu : AgreesExcept [.flags,.rip] s u := heu.agrees
  have zf : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .rdx == 0) := by
    have h := heu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = ((s.regValue .rdx &&& s.regValue .rdx) == 0) at h
    simpa only [BitVec.and_self] using h
  obtain ⟨t, step, hrt, het⟩ := jcc_rel32_effect_step 0x115993 4 0x280f u hru
    (programText_slice (hfu.codeIn (by simp [Component.Covers]) (programLoaded_codeIn pre.loaded))
      0x15993 [0x0f,0x84,0x0f,0x28,0,0] (by decide +kernel) (by decide +kernel))
    ⟨heu.rip, fun _ => by decide +kernel⟩
  have ht : t.RIP = (if count = 0 then 0x1181a8 else 0x115999) := by
    rw [het.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then (0x1181a8 : BitVec 64) else 0x115999) = _
    rw [zf]
    simp only [beq_iff_eq, hz]
  have ha : Advances boundary 1 u t := Advances.of_step step (.inl (by
    rw [ht]
    split
    · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x181a8 (by decide +kernel))
    · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x15999 (by decide +kernel))))
  have hft : AgreesExcept [.rip] u t := het.agrees
  exact ⟨t, hu.trans ha, hrt, ht, (hfu.trans hft).mono (by simp)⟩

end P256.Proofs.SHA256
