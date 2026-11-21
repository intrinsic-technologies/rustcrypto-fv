import P256.Proofs.SignatureFromDer.Fixed.Decode.Arguments
import P256.Proofs.SignatureFromDer.Fixed.Decode.Call
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Correct

set_option autoImplicit false

open P256.Proofs.Program (CalleePre CalleeResult readyToStep programLoaded_codeIn programText_slice inProgram_of_textOffset)

namespace P256.Proofs.SignatureFromDer.Fixed.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem call_scalar [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Stage s t boundary)
    (second : Bool) (rip : t.RIP = if second then 0x109b6b else 0x109afd)
    (bytes : (MemoryRegion.mk (stackPtr t + 72).toNat 32).HasBytes t.external input) :
    ∃ v, Stage s v boundary ∧ v.RIP = (if second then 0x109b7f else 0x109b11) ∧
      Scalar.ScalarResultAt v (stackPtr v + 8) input ∧ v.regValue .r14 = t.regValue .r14 ∧
      (∀ offset len i : Nat, 48 ≤ offset → offset + len ≤ 184 → i < len →
        v.external[stackPtr v + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) := by
  let offset : Nat := if second then 0x9b6b else 0x9afd
  let p := Extracted.textAddress + BitVec.ofNat 64 offset
  have bound : offset + 15 < 118431 := by cases second <;> decide
  have code : CodeIn (codeRange p argumentBytes) t :=
    programText_slice (programLoaded_codeIn state.loaded) offset argumentBytes
      (by cases second <;> decide) (by cases second <;> decide +kernel)
  obtain ⟨fuel, a, run, ready, _, effect⟩ := arguments_run boundary pre.outerBoundary offset bound t
    (readyToStep state.machine state.bindingsSupported) code (by cases second <;> exact rip)
  have af : AgreesExcept [.reg 7, .reg 6, .reg 2, .rip] t a := effect.agrees
  have ast := state.after_registers run ready af (by simp [Component.Covers]) (by simp)
  have am := af.external (by simp [Component.Covers])
  have asp : stackPtr a = stackPtr t := af.read (n := 64) (r := 4) (by simp)
  have args := effect.writes
  change a.regValue .rdi = stackPtr t + 8 ∧ a.regValue .rsi = stackPtr t + 72 ∧
    a.regValue .rdx = 32 at args
  have dst : a.regValue .rdi = stackPtr a + 8 := by rw [asp]; exact args.1
  have src : a.regValue .rsi = stackPtr a + 72 := by rw [asp]; exact args.2.1
  let callOffset : Nat := if second then 0x9b7a else 0x9b0c
  let disp : BitVec 32 := if second then 0x5ea1 else 0x5f0f
  let ret : BitVec 64 := if second then 0x109b7f else 0x109b11
  have arip : a.RIP = Extracted.textAddress + BitVec.ofNat 64 callOffset := by
    have h := effect.rip
    cases second <;> exact h
  have target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 callOffset) 5
      (disp.signExtend 64) = 0x10fa20 := by cases second <;> decide +kernel
  obtain ⟨u, runu, readyu, eu⟩ := Program.ScalarFrame.call_step pre (frameOffset := 184) (by decide) (by decide)
    (readyToStep ast.machine ast.bindingsSupported) ast.loaded ast.allocated ast.rsp callOffset disp
    (by cases second <;> decide) (by cases second <;> decide +kernel)
    (by rw [target]; decide) (by rw [target]; exact inProgram_of_textOffset 0xfa20 (by decide)) arip
  have call : (callEffect (fun _ => 0x10fa20) ret a).Holds a u := by
    rw [target] at eu
    cases second <;> exact eu
  have retp : InProgram ret := by
    cases second
    · exact inProgram_of_textOffset 0x9b11 (by decide)
    · exact inProgram_of_textOffset 0x9b7f (by decide)
  have cp := scalar_pre pre ast.toFrame readyu call src dst retp
  have size : u.regValue .rdx = 32 :=
    (call.agrees.read (n := 64) (r := 2) (by simp)).trans args.2.2
  have usrc : u.regValue .rsi = stackPtr t + 72 :=
    (call.agrees.read (n := 64) (r := 6) (by simp)).trans args.2.1
  have ub : (registerRegion u .rsi 32).HasBytes u.external input := by
    refine ⟨bytes.1, ?_⟩
    intro i
    change u.external[BitVec.ofNat 64 ((u.regValue .rsi).toNat + i.val)]? = _
    rw [usrc, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [← asp]
    change u.external[stackPtr a + 72#64 + BitVec.ofNat 64 i.val]? = _
    rw [Program.ScalarFrame.scalar_stack_address (frameOffset := 184) ast.rsp (by decide) (offset := 72) (by decide),
      Program.ScalarFrame.call_byte (frameOffset := 184) (by decide) ast.rsp call (offset := 112) (len := 32)
        (by decide) (by decide) (by have := i.isLt; have : input.size = 32 := bytes.1; omega)]
    rw [← Program.ScalarFrame.scalar_stack_address (frameOffset := 184) ast.rsp (by decide) (offset := 72) (by decide), asp, am]
    have h := bytes.2 i
    change t.external[BitVec.ofNat 64 ((stackPtr t + 72#64).toNat + i.val)]? = _ at h
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    exact h
  obtain ⟨v, result, scalar⟩ := Scalar.scalar_decode_correct cp size ub
  have frame := scalar_result_frame pre ast.toFrame call dst result
  have vsp : stackPtr v = stackPtr t := frame.rsp.trans state.rsp.symm
  have udst : u.regValue .rdi = stackPtr t + 8 :=
    (call.agrees.read (n := 64) (r := 7) (by simp)).trans args.1
  obtain ⟨n, hn⟩ := ast.execution
  obtain ⟨m, hm⟩ := result.execution
  refine ⟨v, ⟨frame, ⟨n + 1 + m, (hn.trans runu).trans hm⟩, ?_⟩,
    result.rip.trans (callEffect_stack call).1, ?_, ?_, ?_⟩
  · exact (result.calleeSaved .rbx (by simp)).trans
      ((call.agrees.read (n := 64) (r := 3) (by simp)).trans ast.output)
  · simpa only [udst, vsp] using scalar
  · exact (result.calleeSaved .r14 (by simp)).trans
      ((call.agrees.read (n := 64) (r := 14) (by simp)).trans
        (af.read (n := 64) (r := 14) (by simp)))
  · intro off len i hlo hhi hi
    rw [vsp, ← asp, scalar_result_byte pre ast.toFrame call dst result hlo hhi hi, am, asp]

end P256.Proofs.SignatureFromDer.Fixed.Decode
