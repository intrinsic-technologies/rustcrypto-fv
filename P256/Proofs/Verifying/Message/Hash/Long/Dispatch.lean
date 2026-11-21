import P256.Proofs.Verifying.Message.Hash.Entry

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem dispatch [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (entered : Entered initial s t boundary message) (large : 64 ≤ message.size) :
    ∃ u, Advances boundary 3 t u ∧ Frame initial u ∧ u.RIP = 0x10d70f ∧
      AgreesExcept [.flags, .rip] t u := by
  have sizeBound : message.size < 2^32 := by
    have h := pre.messageBounded
    change (memLoad initial.external (initial.regValue .rdx) 64).toNat + message.size < 2^32 at h
    omega
  have carry : (StatusFlags.ofRFLAGS t.RFLAGS).CF = false := by
    rw [entered.carry]
    change decide ((BitVec.ofNat 64 message.size).toNat < (64 : BitVec 64).toNat) = false
    simp only [BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.mod_eq_of_lt (by omega : message.size < 2^64)]
    exact decide_eq_false (by omega)
  obtain ⟨a, stepA, readyA, effectA⟩ := jcc_rel8_effect_step 0x10d65d 2 0xb1 t
    (readyToStep entered.machine entered.bindingsSupported)
    (programText_slice (programLoaded_codeIn entered.loaded) 0xd65d _ (by decide) (by decide +kernel))
    ⟨entered.rip, by intro; decide⟩
  have ripA : a.RIP = 0x10d65f := by
    rw [effectA.rip]
    change (if (StatusFlags.ofRFLAGS t.RFLAGS).CF then (0x10d610 : BitVec 64) else 0x10d65f) = _
    rw [carry]
    rfl
  have runA : Advances boundary 1 t a := Advances.of_step stepA (.inl (by
    rw [ripA]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd65f (by decide))))
  have agreesA : AgreesExcept [.rip] t a := effectA.agrees
  have frameA := entered.toFrameState.after_registers readyA agreesA (by simp [Component.Covers]) (by simp)
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (test_r64_r64_effect_step 0x10d65f 0x48 0xdb (by simp [RexWPrefix]) rfl).advances
      readyA
      (programText_slice (programLoaded_codeIn frameA.loaded) 0xd65f _ (by decide) (by decide +kernel))
      ripA (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd662 (by decide)))
  have agreesB : AgreesExcept [.flags,.rip] a b := effectB.agrees
  have frameB := frameA.after_registers readyB agreesB (by simp [Component.Covers]) (by simp)
  have zero : (StatusFlags.ofRFLAGS b.RFLAGS).ZF = true := by
    have h := effectB.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS b.RFLAGS).ZF = ((a.regValue .rbx &&& a.regValue .rbx) == 0) at h
    have rb : a.regValue .rbx = 0 :=
      (agreesA.read (n := 64) (r := 3) (by simp)).trans entered.position
    rw [rb] at h
    exact h
  obtain ⟨u, stepU, readyU, effectU⟩ := jcc_rel32_effect_step 0x10d662 4 0xa7 b readyB
    (programText_slice (programLoaded_codeIn frameB.loaded) 0xd662 _ (by decide) (by decide +kernel))
    ⟨effectB.rip, by intro; decide⟩
  have ripU : u.RIP = 0x10d70f := by
    rw [effectU.rip]
    change (if (StatusFlags.ofRFLAGS b.RFLAGS).ZF then (0x10d70f : BitVec 64) else 0x10d668) = _
    rw [zero]
    rfl
  have runU : Advances boundary 1 b u := Advances.of_step stepU (.inl (by
    rw [ripU]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd70f (by decide))))
  have agreesU : AgreesExcept [.rip] b u := effectU.agrees
  exact ⟨u, (runA.trans runB).trans runU,
    frameB.after_registers readyU agreesU (by simp [Component.Covers]) (by simp), ripU,
    ((agreesA.trans agreesB).trans agreesU).mono (by simp)⟩

end P256.Proofs.Verifying.Message.Hash.Long
