import P256.Proofs.Field.Add
import P256.Proofs.Sec1.Decompress.Cubic.Support
import P256.Proofs.Sec1.Decompress.Cubic.Constants
import P256.Proofs.Sec1.Decompress.Cubic.AddbSetup
import P256.Proofs.Sec1.Decompress.Cubic.Preservation
import P256.Proofs.Sec1.Decompress.Cubic.Sites

set_option autoImplicit false


namespace P256.Proofs.Sec1.Decompress.Cubic

open P256.Proofs.Program P256.Proofs.Field P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem add_constant [Bindings] {s t : RamState} {boundary : ReturnBoundary} {z : Nat}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : FrameState s t)
    (rip : t.RIP = 0x10fe7d) (base : t.regValue .r15 = stackPtr s - 216)
    (hz : MontgomeryAt t (stackPtr s - 216) z) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = 0x10fece ∧
      u.regValue .r12 = stackPtr s - 80 ∧
      MontgomeryAt u (stackPtr s - 80) ((z+P256.Spec.Operations.domain.b)%P256.Spec.Operations.domain.p) ∧
      PreservesInputs s t u := by
  obtain ⟨n0, a, run0, sa, ipa, ya, fa⟩ := store_b_value pre state rip
  have fa' : AgreesExcept [.reg 0,.reg 1,.rip,.mem (stackPtr s-408) 32] t a :=
    fa.mono (by simp [constantComponents])
  have pa : PreservesInputs s t a := PreservesInputs.of_copy fa'
  have basea : a.regValue .r15 = stackPtr s-216 :=
    (fa.read (n := 64) (r := 15) (by simp [constantComponents])).trans base
  have za : MontgomeryAt a (stackPtr s-216) z := montgomeryAt_of_copy hz
    (fun i hi => copy_byte (s := s) fa' (offset := 216) (len := 32)
      (by unfold OffsetsApart; decide +kernel) (by decide) hi)
  obtain ⟨n1, b, run1, readyb, _, eb⟩ := addB_setup boundary pre.outerBoundary a
    (readyToStep sa.machine sa.bindingsSupported)
    (programText_slice (programLoaded_codeIn sa.loaded) 0xfeb8 addBBytes (by decide +kernel) (by decide +kernel)) ipa
  have fb : AgreesExcept [.reg 12,.reg 2,.reg 7,.reg 6,.rip] a b := eb.agrees
  have mb : b.external = a.external := fb.external (by simp [Component.Covers])
  have sb := sa.after_registers readyb fb (by simp [Component.Covers]) (by simp)
  have pb : PreservesInputs s a b := PreservesInputs.of_registers fb (by simp [Component.Covers]) (by simp) (by simp)
  have xb : MontgomeryAt b (stackPtr s-216) z :=
    montgomeryAt_of_copy za (fun i hi => congrArg (fun m : Ram => m[_]?) mb)
  have yb : MontgomeryAt b (stackPtr s-408) P256.Spec.Operations.domain.b :=
    montgomeryAt_of_copy ya (fun i hi => congrArg (fun m : Ram => m[_]?) mb)
  have wb : (Operand.reg 12 : Operand 64).read b = stackPtr a+328 ∧
      (Operand.reg 2 : Operand 64).read b = stackPtr a ∧
      (Operand.reg 7 : Operand 64).read b = stackPtr a+328 ∧
      (Operand.reg 6 : Operand 64).read b = a.regValue .r15 := eb.writes
  have addr328 : stackPtr a+328 = stackPtr s-80 := input_stack_address sa.rsp (by decide)
  obtain ⟨n2, u, run2, su, ipu, xu, au, bu, _⟩ := FieldCall.binary_call pre sb addBSite
    (op := fun x y => (x+y)%P256.Spec.Operations.domain.p)
    (fun v hp hv hw => field_add_correct hp hv hw) eb.rip
    (wb.2.2.2.trans basea) (wb.2.1.trans sa.rsp) (wb.2.2.1.trans addr328) xb yb
  have pu : PreservesInputs s b u := PreservesInputs.of_call (outputOffset := 80) (by simp) au bu
  exact ⟨n0+n1+n2, u, (run0.trans run1).trans run2, su, ipu,
    (au .r12 (by simp)).trans (wb.1.trans addr328), xu, (pa.trans pb).trans pu⟩

end P256.Proofs.Sec1.Decompress.Cubic
