import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode.Arguments
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.CallResult
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.SignatureFromDer.Fixed.Scalar (ScalarResultAt scalar_decode_correct)

theorem call_scalar [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Stage s t boundary)
    (second : Bool) (rip : t.RIP = if second then 0x10993b else 0x1098b2)
    (source : t.regValue (if second then .r14 else .r15) =
      stackPtr t + BitVec.ofNat 64 (if second then 160 else 128))
    (bytes : (MemoryRegion.mk (stackPtr t + BitVec.ofNat 64 (if second then 160 else 128)).toNat 32).HasBytes t.external input) :
    ∃ v, Stage s v boundary ∧ v.RIP = (if second then 0x10994b else 0x1098c2) ∧
      ScalarResultAt v (stackPtr v) input ∧ v.regValue .r14 = t.regValue .r14 ∧
      (∀ offset len i : Nat, 40 ≤ offset → offset + len ≤ 216 → i < len →
        v.external[stackPtr v + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) := by
  let off : Nat := if second then 160 else 128
  let ip : BitVec 64 := if second then 0x10993b else 0x1098b2
  have code : CodeIn (codeRange ip (argumentBytes second)) t := by
    cases second
    · exact programText_slice (programLoaded_codeIn state.loaded) 0x98b2 _ (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn state.loaded) 0x993b _ (by decide) (by decide +kernel)
  obtain ⟨fuel, a, run, ready, _, effect⟩ := arguments_run boundary pre.outerBoundary second t
    (readyToStep state.machine state.bindingsSupported) code rip
  have af : AgreesExcept [.reg 7, .reg 2, .reg 6, .rip] t a := effect.agrees
  have ast := state.after_registers run ready af (by simp [Component.Covers]) (by simp)
  have am := af.external (by simp [Component.Covers])
  have asp : stackPtr a = stackPtr t := af.read (n := 64) (r := 4) (by simp)
  have args : a.regValue .rdi = stackPtr t ∧ a.regValue .rdx = 32 ∧
      a.regValue .rsi = t.regValue (if second then .r14 else .r15) := effect.writes
  have dst : a.regValue .rdi = stackPtr a + 0#64 := by rw [asp, BitVec.add_zero]; exact args.1
  have src : a.regValue .rsi = stackPtr a + BitVec.ofNat 64 off := by rw [asp]; exact args.2.2.trans source
  let callOffset : Nat := if second then 0x9946 else 0x98bd
  let disp : BitVec 32 := if second then 0x60d5 else 0x615e
  let ret : BitVec 64 := if second then 0x10994b else 0x1098c2
  have arip : a.RIP = Extracted.textAddress + BitVec.ofNat 64 callOffset := by
    have h := effect.rip
    cases second <;> exact h
  have target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 callOffset) 5
      (disp.signExtend 64) = 0x10fa20 := by cases second <;> decide +kernel
  obtain ⟨u, runu, readyu, eu⟩ := Program.ScalarFrame.call_step pre (frameOffset := 216) (by decide) (by decide)
    (readyToStep ast.machine ast.bindingsSupported)
    ast.loaded ast.allocated ast.rsp callOffset disp
    (by cases second <;> decide) (by cases second <;> decide +kernel)
    (by rw [target]; decide) (by rw [target]; exact inProgram_of_textOffset 0xfa20 (by decide)) arip
  have call : (callEffect (fun _ => 0x10fa20) ret a).Holds a u := by
    rw [target] at eu
    cases second <;> exact eu
  have retp : InProgram ret := by
    cases second
    · exact inProgram_of_textOffset 0x98c2 (by decide)
    · exact inProgram_of_textOffset 0x994b (by decide)
  have cp : CalleePre u boundary 0x10fa20 32 40 288 :=
    local_pre pre ast.toFrame readyu call src dst retp
      (by cases second <;> decide) (by decide) (.inr (by cases second <;> decide)) (by decide)
  have size : u.regValue .rdx = 32 :=
    (call.agrees.read (n := 64) (r := 2) (by simp)).trans args.2.1
  have usrc : u.regValue .rsi = stackPtr t + BitVec.ofNat 64 off :=
    (call.agrees.read (n := 64) (r := 6) (by simp)).trans (args.2.2.trans source)
  have ub : (registerRegion u .rsi 32).HasBytes u.external input := by
    refine ⟨bytes.1, ?_⟩
    intro i
    change u.external[BitVec.ofNat 64 ((u.regValue .rsi).toNat + i.val)]? = _
    rw [usrc, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← asp]
    rw [Program.ScalarFrame.scalar_stack_address (frameOffset := 216) ast.rsp (by decide) (by cases second <;> decide),
      Program.ScalarFrame.call_byte (frameOffset := 216) (by decide) ast.rsp call (offset := 216-off) (len := 32)
        (by cases second <;> decide) (by cases second <;> decide)
        (by have := i.isLt; have : input.size = 32 := bytes.1; omega)]
    rw [← Program.ScalarFrame.scalar_stack_address (frameOffset := 216) ast.rsp (by decide) (by cases second <;> decide), asp, am]
    have h := bytes.2 i
    change t.external[BitVec.ofNat 64 ((stackPtr t + BitVec.ofNat 64 off).toNat + i.val)]? = _ at h
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    exact h
  obtain ⟨v, result, scalar⟩ := scalar_decode_correct cp size ub
  have vst := ast.after_call pre runu call dst (by decide) (by decide) result
  have vsp : stackPtr v = stackPtr t := vst.rsp.trans state.rsp.symm
  have udst : u.regValue .rdi = stackPtr t :=
    (call.agrees.read (n := 64) (r := 7) (by simp)).trans args.1
  refine ⟨v, vst, result.rip.trans (callEffect_stack call).1, ?_, ?_, ?_⟩
  · simpa only [udst, vsp] using scalar
  · exact (result.calleeSaved .r14 (by simp)).trans
      ((call.agrees.read (n := 64) (r := 14) (by simp)).trans
        (af.read (n := 64) (r := 14) (by simp)))
  · intro offset len i hlo hhi hi
    rw [vsp, ← asp, call_result_byte pre ast.toFrame call dst result (by decide) hhi
      (.inr (by omega)) hi, am, asp]

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode
