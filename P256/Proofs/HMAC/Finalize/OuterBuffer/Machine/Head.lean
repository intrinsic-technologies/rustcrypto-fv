import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.OuterBuffer.Machine.Head

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x101182
  readable : MemReadable s (rspOf s + 239) 1
  position : memLoad s.external (rspOf s + 239) 8 = 0

def bytes : List UInt8 :=
  [0x44,0x0f,0xb6,0xbc,0x24,0xef,0,0,0,0x49,0x83,0xff,0x1f,0x77,0x42]

def effect (_ : RamState) : Effect :=
  { rip := 0x101191
    writes := [⟨(.reg 15 : Operand 64), 0⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x101182 bytes) (Effect.post effect) := by
  intro s ready code hp
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (movzx_r_m8_rex_effect_step 0x101182 0x44 (by simp [RexPrefix]) 32 (.inr rfl)
      (fun _ => rfl) 7 (.sib 4 none 0 (.d32 239)) (by decide) rfl rfl).advances ready
      (code.mono (codeRange_slice_subset 0x101182 bytes 0 9))
      ⟨hp.rip, hp.readable⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x118b (by decide)))
  have agreesA : AgreesExcept [.reg 15,.rip] s a := effectA.agrees
  have zero : a.regValue .r15 = 0 := by
    have h : a.regValue .r15 = (memLoad s.external (rspOf s + 239) 8).setWidth 64 := effectA.writes
    rw [hp.position] at h
    exact h
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (cmp_r64_imm8_effect_step 0x10118b 0x49 0xff 31
      (by simp [RexWPrefix]) rfl rfl).advances readyA
      ((agreesA.codeIn (by simp [Component.Covers]) code).mono
        (codeRange_slice_subset 0x101182 bytes 9 4)) effectA.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x118f (by decide)))
  have agreesB : AgreesExcept [.flags,.rip] a b := effectB.agrees
  have codeB := (agreesA.trans agreesB).codeIn (by simp [Component.Covers]) code
  obtain ⟨t, step, readyT, branch⟩ := jcc_rel8_effect_step 0x10118f 7 0x42 b readyB
    (codeB.mono (codeRange_slice_subset 0x101182 bytes 13 2))
    ⟨effectB.rip, by intro; decide⟩
  have carry : (StatusFlags.ofRFLAGS b.RFLAGS).CF = true := by
    have h : (StatusFlags.ofRFLAGS b.RFLAGS).CF = (a.regValue .r15).ult 31 := effectB.flags.1
    rw [zero] at h
    exact h
  have rip : t.RIP = 0x101191 := by
    rw [branch.rip]
    change (if !((StatusFlags.ofRFLAGS b.RFLAGS).CF || (StatusFlags.ofRFLAGS b.RFLAGS).ZF)
      then 0x1011d3 else 0x101191) = _
    simp only [carry, Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have agreesT : AgreesExcept [.rip] b t := branch.agrees
  have agrees : AgreesExcept [.reg 15,.flags,.rip] s t :=
    (agreesA.trans agreesB |>.trans agreesT).mono (by simp)
  refine ⟨3, t, runA.trans (runB.trans (Advances.of_step step (.inl ?_))), readyT,
    agrees.codeIn (by simp [Component.Covers]) code, rip, ?_, ?_, ?_⟩
  · rw [rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x1191 (by decide))
  · exact ((agreesB.trans agreesT).read (n := 64) (r := 15) (by simp)).trans zero
  · exact ⟨trivial,trivial,trivial,trivial,trivial,trivial⟩
  · exact agrees

end P256.Proofs.HMAC.Finalize.OuterBuffer.Machine.Head
