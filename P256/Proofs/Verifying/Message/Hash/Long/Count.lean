import P256.Proofs.Verifying.Message.Hash.Entry
import P256.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Shr.Generated.R.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long.Count

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def bytes : List UInt8 := [0x4c,0x89,0xfd,0x48,0x89,0xea,0x48,0xc1,0xea,0x6]

def effect (s : RamState) : Effect :=
  { rip := 0x10d719
    writes := [⟨(.reg 5 : Operand 64), s.regValue .r15⟩,
      ⟨(.reg 2 : Operand 64), s.regValue .r15 >>> 6⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 (s.regValue .r15)) }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10d70f bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xd70f bytes (by decide) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10d70f)
      (codeRange 0x10d70f bytes) (Effect.post effect) := by
  advance_begin (mov_r64_r64_effect_step 0x10d70f 0x4c 0xfd (by simp [RexWPrefix]) rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xd712 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10d712 0x48 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d70f bytes 3 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd715 (by decide))⟩
  advance_then (shr_r64_imm8_effect_step 0x10d715 0x48 0xea 6 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d70f bytes 6 4
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd719 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effect]
  · x86_norm [effect]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [effect]
    all_goals rfl
  · x86_norm [effect]

theorem nonzero [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (frame : Frame initial s) (rip : s.RIP = 0x10d70f)
    (length : s.regValue .r15 = BitVec.ofNat 64 message.size) (large : 64 ≤ message.size) :
    ∃ fuel t, Advances boundary fuel s t ∧ Frame initial t ∧ t.RIP = 0x10d6b6 ∧
      t.regValue .rbp = BitVec.ofNat 64 message.size ∧
      t.regValue .rdx = BitVec.ofNat 64 (message.size / 64) ∧
      AgreesExcept [.reg 5, .reg 2, .flags, .rip] s t := by
  obtain ⟨fuel, a, runA, readyA, _, effectA⟩ := run boundary pre.outerBoundary s
    (readyToStep frame.machine frame.bindingsSupported) (code frame.loaded) rip
  have agreesA : AgreesExcept [.reg 5,.reg 2,.flags,.rip] s a := effectA.agrees
  have frameA := frame.after_registers readyA agreesA (by simp [Component.Covers]) (by simp)
  have sizeBound : message.size < 2^32 := by
    have h := pre.messageBounded
    change (memLoad initial.external (initial.regValue .rdx) 64).toNat + message.size < 2^32 at h
    omega
  have shifted : BitVec.ofNat 64 message.size >>> 6 = BitVec.ofNat 64 (message.size / 64) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega : message.size < 2^64),
      Nat.mod_eq_of_lt (by omega : message.size / 64 < 2^64)]
  have zero : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have h := effectA.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = (s.regValue .r15 >>> 6 == 0) at h
    rw [length, shifted] at h
    rw [h]
    apply beq_eq_false_iff_ne.mpr
    intro eq
    have en := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat, BitVec.reduceToNat,
      Nat.mod_eq_of_lt (by omega : message.size / 64 < 2^64)] at en
    omega
  obtain ⟨t, stepT, readyT, effectT⟩ := jcc_rel8_effect_step 0x10d719 5 0x9b a readyA
    (programText_slice (programLoaded_codeIn frameA.loaded) 0xd719 _ (by decide) (by decide +kernel))
    ⟨effectA.rip, by intro; decide⟩
  have ripT : t.RIP = 0x10d6b6 := by
    rw [effectT.rip]
    change (if !(StatusFlags.ofRFLAGS a.RFLAGS).ZF then (0x10d6b6 : BitVec 64) else 0x10d71b) = _
    rw [zero]
    rfl
  have runT : Advances boundary 1 a t := Advances.of_step stepT (.inl (by
    rw [ripT]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd6b6 (by decide))))
  have agreesT : AgreesExcept [.rip] a t := effectT.agrees
  have writes := effectA.writes
  change a.regValue .rbp = s.regValue .r15 ∧ a.regValue .rdx = s.regValue .r15 >>> 6 at writes
  rw [length, shifted] at writes
  exact ⟨fuel+1, t, runA.trans runT,
    frameA.after_registers readyT agreesT (by simp [Component.Covers]) (by simp), ripT,
    (agreesT.read (n := 64) (r := 5) (by simp)).trans writes.1,
    (agreesT.read (n := 64) (r := 2) (by simp)).trans writes.2,
    (agreesA.trans agreesT).mono (by simp)⟩

end P256.Proofs.Verifying.Message.Hash.Long.Count
