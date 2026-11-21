import P256.Proofs.Program.Compare.Execution
import P256.Proofs.Program.Compare.Model
import X86Proofs.Instructions.Branch.Triple

namespace P256.Proofs.Program.Compare

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

theorem cmpSpec_zf {n : Nat} (x y : BitVec n) : (cmpSpec x y).ZF = (x == y) := by
  apply Bool.eq_iff_iff.mpr
  simp [cmpSpec, subSpec, BitVec.sub_eq_iff_eq_add]

def incrementBytes : List UInt8 := [0x49, 0x83, 0xc3, 0x10, 0x4d, 0x39, 0xd8]

def incrementEffect (s : RamState) : Effect :=
  { rip := 0x11c8ba
    writes := [⟨(Operand.reg 11 : Operand 64), (Operand.reg 11 : Operand 64).read s + 16⟩]
    flags := some (.ofStatusFlags
      (cmpSpec ((Operand.reg 8 : Operand 64).read s)
        ((Operand.reg 11 : Operand 64).read s + 16))) }

theorem increment_compare [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11c8b3) (codeRange 0x11c8b3 incrementBytes) incrementEffect := by
  unfold incrementBytes
  p256_memcmp_run_begin add_r64_imm8_effect_step 0x11c8b3 0x49 0xc3 16
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  p256_memcmp_run_then cmp_r64_r64_effect_step 0x11c8b7 0x4d 0xd8
    (by unfold RexWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11c8b3) (all := incrementBytes) 4 (by decide +kernel)
  apply RegisterBlock.block_end
  intro s t hp hH
  apply hH.weaken
  · x86_norm [incrementEffect]
  · x86_norm [incrementEffect] <;> rfl
  · intro i; cases i <;> x86_norm [incrementEffect] <;> rfl
  · x86_norm [incrementEffect]

def advanceEffect (s : RamState) : Effect :=
  { incrementEffect s with
    rip := if (Operand.reg 8 : Operand 64).read s ==
      (Operand.reg 11 : Operand 64).read s + 16 then 0x11c8bc else 0x11c890 }

theorem increment_code {s : RamState} (h : CodeIn Extracted.programSections.toCodeMap s) :
    CodeIn (codeRange 0x11c8b3 incrementBytes) s := by
  have hs := program_text_slice h 0x1c8b3 7 (by decide +kernel)
  have he : Extracted.textBytes.toListFrom 0x1c8b3 7 = incrementBytes := by decide +kernel
  simpa [he, Extracted.textAddress] using hs

theorem loop_advance [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11c8b3) Extracted.programSections.toCodeMap advanceEffect := by
  intro boundary s hr hc hp hb
  obtain ⟨n, u, ha, hu, _, he, hsp⟩ := increment_compare boundary s hr (increment_code hc) hp hb
  have hcu : CodeIn Extracted.programSections.toCodeMap u := he.codeIn
    (Effect.Avoids.of_noMem (by simp [incrementEffect, Effect.components, Component.Covers]) _) hc
  have hjcode : CodeIn (codeRange 0x11c8ba [0x75, 0xd4]) u :=
    program_text_slice hcu 0x1c8ba 2 (by decide +kernel)
  obtain ⟨t, hstep, ht, hj⟩ := jcc_rel8_effect_step 0x11c8ba 5 0xd4 u hu hjcode
    ⟨he.rip, fun _ ↦ by decide +kernel⟩
  have hag : AgreesExcept [.rip] u t := hj.agrees
  have hsp' : stackPtr t = stackPtr u := hag.read (n := 64) (by simp)
  have hip : InRoutine t.RIP := by
    rw [hj.rip]
    unfold jccEffect branchEffect
    split <;> constructor <;> decide +kernel
  have haj := (hb.of_stack_eq hsp).advances hstep hsp' hip
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      ((Operand.reg 8 : Operand 64).read s == (Operand.reg 11 : Operand 64).read s + 16) := by
    have hz := he.flags.2.2.2.1
    simpa only [incrementEffect, StatusFlagsOutcome.ofStatusFlags, FlagAllows, cmpSpec_zf] using hz
  have hrt : t.RIP = (advanceEffect s).rip := by
    rw [hj.rip]
    simp only [jccEffect, branchEffect, condHolds, hz, advanceEffect]
    cases ((Operand.reg 8 : Operand 64).read s ==
      (Operand.reg 11 : Operand 64).read s + 16) <;> rfl
  refine ⟨n + 1, t, ha.trans haj, ht, hag.codeIn (by simp [Component.Covers]) hcu,
    ?_, hsp'.trans hsp⟩
  exact holds_after_rip he hag hrt (by simp [incrementEffect, Write.Full, Operand.Full])

end P256.Proofs.Program.Compare
