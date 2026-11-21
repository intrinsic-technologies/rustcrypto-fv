import P256.Proofs.Projective.Multiply.Machine.Loop.Round.Stage
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.LookupArguments
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.LookupCall
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame ProjectiveLookup


theorem lookup_round [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective} {n : Nat} {point : Projective}
    (pre : Pre s boundary) (input : Lookup.TableAt s (s.regValue .rsi) table)
    (state : RoundState s t n 0x10338e 144 point) :
    ∃ fuel u, Advances boundary fuel t u ∧ RoundState s u n 0x1033a2 144 point ∧
      ProjectiveAt u (stackPtr s - 240) (signedLookup table (digits s (63-n))) := by
  have cursor : (Operand.mem (stackPtr t + 8) : Operand 64).read t =
      s.regValue .rcx + BitVec.ofNat 64 (63-n) := by
    exact (congrArg (fun a => (Operand.mem a : Operand 64).read t)
      (scalar_stack_address (frameOffset := 376) state.rsp (by decide) (show 8 ≤ 376 by decide))).trans state.cursor
  have address : (Operand.mem (stackPtr t + 8) : Operand 64).read t + t.regValue .rbx =
      s.regValue .rcx + BitVec.ofNat 64 (63-n) := by
    rw [state.rbx]
    exact (BitVec.add_zero _).trans cursor
  have readable := pre.digit_readable state.toFrameState (i := 63-n) (by omega)
  obtain ⟨fuel, v, run, ready, _, effect⟩ := lookup_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x338e lookupSetupBytes
      (by decide) (by decide +kernel))
    ⟨state.rip, stack_readable pre.toCalleePre state.toFrameState (offset := 8) (len := 8) (by decide) (by decide),
      address ▸ readable⟩
  have agrees : AgreesExcept [.reg 0, .reg 2, .reg 7, .reg 6, .rip] t v := effect.agrees
  have stateV := state.after_registers ready agrees effect.rip
    (by simp [Component.Covers]) (by simp) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hw := effect.writes
  change v.regValue .rax = (Operand.mem (stackPtr t + 8) : Operand 64).read t ∧
    v.regValue .rdx = ((Operand.mem
      ((Operand.mem (stackPtr t + 8) : Operand 64).read t + t.regValue .rbx) : Operand 8).read t).setWidth 64 ∧
    v.regValue .rdi = t.regValue .r12 ∧ v.regValue .rsi = t.regValue .r15 at hw
  have digit : (v.regValue .rdx).setWidth 8 = digits s (63-n) := by
    rw [hw.2.1, address, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    exact pre.digit_value state.toFrameState (i := 63-n) (by omega)
  obtain ⟨u, result⟩ := lookup_call pre stateV.toFrameState stateV.rip
    (hw.2.2.1.trans state.r12) (hw.2.2.2.trans state.r15) input digit
  have value : ProjectiveAt u (stackPtr s - BitVec.ofNat 64 144) point :=
    stateV.value.of_bytes_eq (fun i hi => result.bytes 144 96 (by decide) (by decide) (by decide) i hi)
  obtain ⟨fuel', run'⟩ := result.execution
  exact ⟨fuel+fuel', u, run.trans run', stateV.after_point_call result (by decide) value, result.value⟩

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
