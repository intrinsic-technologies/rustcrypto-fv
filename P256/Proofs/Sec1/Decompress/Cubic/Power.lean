import P256.Proofs.Field.Montgomery
import P256.Proofs.Sec1.Decompress.Cubic.Support
import P256.Proofs.Sec1.Decompress.Cubic.CopyEntry
import P256.Proofs.Sec1.Decompress.Cubic.SquareSetup
import P256.Proofs.Sec1.Decompress.Cubic.CubeSetup
import P256.Proofs.Sec1.Decompress.Cubic.Preservation
import P256.Proofs.Sec1.Decompress.Cubic.Sites

set_option autoImplicit false


namespace P256.Proofs.Sec1.Decompress.Cubic

open P256.Proofs.Program P256.Proofs.Field P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem power_three [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : FrameState s t)
    (rip : t.RIP = 0x10fdcc) (base : t.regValue .r15 = stackPtr s - 288)
    (hx : MontgomeryAt t (stackPtr s - 288) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = 0x10fe25 ∧
      u.regValue .r13 = stackPtr s - 112 ∧ u.regValue .r15 = stackPtr s - 288 ∧
      MontgomeryAt u (stackPtr s - 112) (x*x%P256.Spec.Operations.domain.p*x%P256.Spec.Operations.domain.p) ∧
      PreservesInputs s t u := by
  obtain ⟨n0, a, run0, sa, ipa, xa, fa⟩ := copy_payload pre state rip hx
  have pa : PreservesInputs s t a := PreservesInputs.of_copy fa
  have basea : a.regValue .r15 = stackPtr s - 288 :=
    (fa.read (n := 64) (r := 15) (by simp [copyComponents])).trans base
  obtain ⟨n1, b, run1, readyb, _, eb⟩ := square_setup boundary pre.outerBoundary a
    (readyToStep sa.machine sa.bindingsSupported)
    (programText_slice (programLoaded_codeIn sa.loaded) 0xfdfc squareBytes (by decide +kernel) (by decide +kernel)) ipa
  have fb : AgreesExcept [.reg 12,.reg 6,.reg 7,.reg 2,.rip] a b := eb.agrees
  have mb : b.external = a.external := fb.external (by simp [Component.Covers])
  have sb := sa.after_registers readyb fb (by simp [Component.Covers]) (by simp)
  have pb : PreservesInputs s a b := PreservesInputs.of_registers fb (by simp [Component.Covers]) (by simp) (by simp)
  have xb : MontgomeryAt b (stackPtr s - 408) x :=
    montgomeryAt_of_copy xa (fun i hi => congrArg (fun m : Ram => m[_]?) mb)
  have yb := pb.montgomery (pa.montgomery hx)
  have wb : (Operand.reg 12 : Operand 64).read b = stackPtr a + 80 ∧
      (Operand.reg 6 : Operand 64).read b = stackPtr a ∧
      (Operand.reg 7 : Operand 64).read b = stackPtr a + 80 ∧
      (Operand.reg 2 : Operand 64).read b = a.regValue .r15 := eb.writes
  have addr80 : stackPtr a + 80 = stackPtr s - 328 := input_stack_address sa.rsp (by decide)
  obtain ⟨n2, c, run2, sc, ipc, xc, ac, bc, _⟩ := FieldCall.binary_call pre sb squareSite
    (op := fun x y => x*y%P256.Spec.Operations.domain.p)
    (fun v hp hv hw => field_mul_correct hp hv hw) eb.rip
    (wb.2.1.trans sa.rsp) (wb.2.2.2.trans basea) (wb.2.2.1.trans addr80) xb yb
  have pc : PreservesInputs s b c := PreservesInputs.of_call (outputOffset := 328) (by simp) ac bc
  have c12 : c.regValue .r12 = stackPtr s-328 := (ac .r12 (by simp)).trans (wb.1.trans addr80)
  have c15 : c.regValue .r15 = stackPtr s-288 :=
    (ac .r15 (by simp)).trans ((fb.read (n := 64) (r := 15) (by simp)).trans basea)
  obtain ⟨n3, d, run3, readyd, _, ed⟩ := cube_setup boundary pre.outerBoundary c
    (readyToStep sc.machine sc.bindingsSupported)
    (programText_slice (programLoaded_codeIn sc.loaded) 0xfe0f cubeBytes (by decide +kernel) (by decide +kernel)) ipc
  have fd : AgreesExcept [.reg 13,.reg 7,.reg 6,.reg 2,.rip] c d := ed.agrees
  have md : d.external = c.external := fd.external (by simp [Component.Covers])
  have sd := sc.after_registers readyd fd (by simp [Component.Covers]) (by simp)
  have pd : PreservesInputs s c d := PreservesInputs.of_registers fd (by simp [Component.Covers]) (by simp) (by simp)
  have xd : MontgomeryAt d (stackPtr s-328) (x*x%P256.Spec.Operations.domain.p) :=
    montgomeryAt_of_copy xc (fun i hi => congrArg (fun m : Ram => m[_]?) md)
  have yd := pd.montgomery (pc.montgomery yb)
  have wd : (Operand.reg 13 : Operand 64).read d = stackPtr c+296 ∧
      (Operand.reg 7 : Operand 64).read d = stackPtr c+296 ∧
      (Operand.reg 6 : Operand 64).read d = c.regValue .r12 ∧
      (Operand.reg 2 : Operand 64).read d = c.regValue .r15 := ed.writes
  have addr296 : stackPtr c+296 = stackPtr s-112 := input_stack_address sc.rsp (by decide)
  obtain ⟨n4, u, run4, su, ipu, xu, au, bu, _⟩ := FieldCall.binary_call pre sd cubeSite
    (op := fun x y => x*y%P256.Spec.Operations.domain.p)
    (fun v hp hv hw => field_mul_correct hp hv hw) ed.rip
    (wd.2.2.1.trans c12) (wd.2.2.2.trans c15) (wd.2.1.trans addr296) xd yd
  have pu : PreservesInputs s d u := PreservesInputs.of_call (outputOffset := 112) (by simp) au bu
  refine ⟨n0+n1+n2+n3+n4, u, (((run0.trans run1).trans run2).trans run3).trans run4,
    su, ipu, (au .r13 (by simp)).trans (wd.1.trans addr296), ?_, xu,
    (((pa.trans pb).trans pc).trans pd).trans pu⟩
  exact (au .r15 (by simp)).trans ((fd.read (n := 64) (r := 15) (by simp)).trans c15)

end P256.Proofs.Sec1.Decompress.Cubic
