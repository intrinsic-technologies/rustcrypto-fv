import P256.Proofs.Sec1.Decompress.State
import P256.Proofs.Sec1.Decompress.Select.NegSetup
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

def negLayout : StackCallLayout 2592 32 32 24 :=
  ⟨416,408,112,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem neg_result [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (rip : t.RIP = 0x10ff64)
    (hx : MontgomeryAt t (stackPtr s - 408) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10ff77 ∧
      u.regValue .r13 = stackPtr s - 112 ∧ MontgomeryAt u (stackPtr s - 112) ((P256.Spec.Operations.domain.p - x) % P256.Spec.Operations.domain.p) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 408 → len ≤ offset + 8 →
        (offset + 32 ≤ 112 ∨ 112 + len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) := by
  obtain ⟨n, a, advance, ready, _, effect⟩ := neg_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xff64 negSetupBytes
      (by decide +kernel) negSetupBytes_extracted) rip
  have frame : AgreesExcept [.reg 13, .reg 6, .reg 7, .rip] t a := effect.agrees
  have memory : a.external = t.external := frame.external (by simp [Component.Covers])
  have sa := state.after_registers ready frame (by simp [Component.Covers]) (by simp)
  have writes : (Operand.reg 13 : Operand 64).read a = stackPtr t + 296 ∧
      (Operand.reg 6 : Operand 64).read a = stackPtr t ∧
      (Operand.reg 7 : Operand 64).read a = stackPtr t + 296 := effect.writes
  have address : stackPtr t + 296 = stackPtr s - 112 := input_stack_address state.rsp (by decide)
  have dest : a.regValue .rdi = stackPtr s - 112 := writes.2.2.trans address
  have src : a.regValue .rsi = stackPtr s - 408 := writes.2.1.trans state.rsp
  have value : MontgomeryAt a (stackPtr s - 408) x := by
    exact montgomeryAt_of_copy hx (fun i hi => congrArg (fun m : Ram => m[_]?) memory)
  obtain ⟨m, u, called, su, ipu, output, abi, kept, _⟩ :=
    unary_call (resultAt := fun u a => MontgomeryAt u a ((P256.Spec.Operations.domain.p - x) % P256.Spec.Operations.domain.p)) pre sa negLayout rfl (by decide) 0xff72 0x3859 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (inProgram_of_textOffset 0x137d0 (by decide +kernel))
      (fun v hp hv => Projective.Multiply.Machine.Lookup.Negate.negate_correct hp hv) effect.rip src dest value
  change u.RIP = 0x10ff77 at ipu
  refine ⟨n+m, u, advance.trans called, su, ipu,
    (abi .r13 (by simp)).trans (writes.1.trans address), output, ?_, ?_⟩
  · intro r hr
    apply (abi r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact frame.read (n := 64) (r := 3) (by simp)
    · exact frame.read (n := 64) (r := 5) (by simp)
    · exact frame.read (n := 64) (r := 12) (by simp)
    · exact frame.read (n := 64) (r := 14) (by simp)
    · exact frame.read (n := 64) (r := 15) (by simp)
  · intro off len ho hl ha i hi
    exact (kept off len ho hl ha i hi).trans (congrArg (fun m : Ram => m[_]?) memory)

end P256.Proofs.Sec1.Decompress.Select
