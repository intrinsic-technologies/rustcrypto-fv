import P256.Proofs.Sec1.Decompress.State
import P256.Proofs.Field.Inverse.Tail.Support
import P256.Proofs.Sec1.Decompress.Select.Setup
import P256.Proofs.Sec1.Decompress.Cubic.Support
import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.PublicPoint.Normalize.Invert.SelectCall
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct
import P256.Proofs.Projective.Multiply.Machine.Lookup.Negate.Correct

set_option autoImplicit false
open P256.Proofs.Program P256.Proofs.Program.FieldCall P256.Proofs.Field
open P256.Proofs.Sec1.Decompress.Cubic (input_stack_address montgomeryAt_of_copy)

namespace P256.Proofs.Sec1.Decompress.Select

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def selectSite : BinaryCallSite 2592 408 0x114380 128 := {
  codeOffset := 0xff2c
  disp := 0x444f
  codeBound := by decide +kernel
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide +kernel
  entryProgram := inProgram_of_textOffset 0x14380 (by decide +kernel)
  layout := ⟨416,216,256,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 328
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide }

theorem select_result [Bindings] {s t : RamState} {boundary : ReturnBoundary} {y : Nat} {valid : Bool}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (rip : t.RIP = 0x10ff0e) (source : t.regValue .r13 = stackPtr s - 328)
    (zero : MontgomeryAt t (stackPtr s - 216) 0)
    (candidate : MontgomeryAt t (stackPtr s - 328) y)
    (validity : (Operand.mem (stackPtr s - 296) : Operand 8).read t = if valid then 1 else 0) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10ff31 ∧
      u.regValue .r12 = stackPtr s - 256 ∧
      (u.regValue .r15).setWidth 8 = (if valid then 1 else 0) ∧
      MontgomeryAt u (stackPtr s - 256) (if valid then y else 0) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r13, .r14], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 408 → len ≤ offset+8 →
        (offset+32 ≤ 256 ∨ 256+len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) := by
  have address : stackPtr t + 112 = stackPtr s - 296 := input_stack_address state.rsp (by decide)
  have setupPre : selectSetupPre t := by
    refine ⟨rip, ?_⟩
    change MemReadable t (stackPtr t + (112 : BitVec 8).signExtend 64) 4
    rw [show (112 : BitVec 8).signExtend 64 = (112 : BitVec 64) by decide +kernel, address]
    exact readable_of_grow (stack_sub_readable pre.stack
      (offset := 296) (by decide) (by decide)) state.allocated
  obtain ⟨n, a, advance, ready, _, effect⟩ := select_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xff0e selectSetupBytes
      (by decide +kernel) (by decide +kernel)) setupPre
  have frame : AgreesExcept [.reg 15, .reg 12, .reg 6, .reg 7, .reg 2, .reg 1, .rip] t a := effect.agrees
  have memory : a.external = t.external := frame.external (by simp [Component.Covers])
  have sa := state.after_registers ready frame (by simp [Component.Covers]) (by simp)
  have writes : (Operand.reg 15 : Operand 64).read a =
      ((Operand.mem (stackPtr t + 112) : Operand 32).read t).setWidth 64 ∧
      (Operand.reg 12 : Operand 64).read a = stackPtr t + 152 ∧
      (Operand.reg 6 : Operand 64).read a = stackPtr t + 192 ∧
      (Operand.reg 7 : Operand 64).read a = stackPtr t + 152 ∧
      (Operand.reg 2 : Operand 64).read a = (Operand.reg 13 : Operand 64).read t ∧
      (Operand.reg 1 : Operand 64).read a =
      ((Operand.mem (stackPtr t + 112) : Operand 32).read t).setWidth 64 := effect.writes
  have low : (((Operand.mem (stackPtr t + 112) : Operand 32).read t).setWidth 64).setWidth 8 =
      if valid then 1 else 0 := by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]
    change (memLoad t.external (stackPtr t + 112) 32).setWidth 8 = _
    rw [P256.Proofs.Field.Inverse.memLoad32_lowByte, ← memLoad_8, address]
    exact validity
  have choice : (a.regValue .rcx).setWidth 8 = if valid then 1 else 0 := by
    rw [show a.regValue .rcx = _ from writes.2.2.2.2.2]
    exact low
  have r15 : (a.regValue .r15).setWidth 8 = if valid then 1 else 0 := by
    rw [show a.regValue .r15 = _ from writes.1]
    exact low
  have src : a.regValue .rsi = stackPtr s - 216 := writes.2.2.1.trans (input_stack_address state.rsp (by decide))
  have right : a.regValue .rdx = stackPtr s - 328 := writes.2.2.2.2.1.trans source
  have dest : a.regValue .rdi = stackPtr s - 256 := writes.2.2.2.1.trans (input_stack_address state.rsp (by decide))
  have value0 : MontgomeryAt a (stackPtr s - 216) 0 := montgomeryAt_of_copy zero
    (fun i hi => congrArg (fun m : Ram => m[_]?) memory)
  have valueY : MontgomeryAt a (stackPtr s - 328) y := montgomeryAt_of_copy candidate
    (fun i hi => congrArg (fun m : Ram => m[_]?) memory)
  obtain ⟨m, u, called, su, ipu, value, abi, kept, _⟩ :=
    PublicPoint.Normalize.select_binary_call (op := fun x y => if valid then y else x) pre sa selectSite
      (fun v hp hc hx hy => by
        have choiceV : (v.regValue .rcx).setWidth 8 = if valid then 1 else 0 := by rw [hc]; exact choice
        obtain ⟨w, result, bytes⟩ := Projective.Multiply.Machine.Lookup.Select.field_select_bytes_correct hp choiceV
        refine ⟨w, result, ?_⟩
        cases valid
        · exact montgomeryAt_of_copy hx (fun i hi => bytes i hi)
        · exact montgomeryAt_of_copy hy (fun i hi => bytes i hi))
      effect.rip src right dest value0 valueY
  change u.RIP = 0x10ff31 at ipu
  refine ⟨n+m, u, advance.trans called, su, ipu,
    (abi .r12 (by simp)).trans (writes.2.1.trans (input_stack_address state.rsp (by decide))), ?_, value, ?_, ?_⟩
  · rw [abi .r15 (by simp)]
    exact r15
  · intro r hr
    apply (abi r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp)).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact frame.read (n := 64) (r := 3) (by simp)
    · exact frame.read (n := 64) (r := 5) (by simp)
    · exact frame.read (n := 64) (r := 13) (by simp)
    · exact frame.read (n := 64) (r := 14) (by simp)
  · intro off len ho hl ha i hi
    exact (kept off len ho hl ha i hi).trans (congrArg (fun m : Ram => m[_]?) memory)

end P256.Proofs.Sec1.Decompress.Select
