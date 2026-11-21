import P256.Proofs.Program.Copy.Prologue
import P256.Proofs.Program.Copy.Loops
import P256.Proofs.Nonce.Update.Absorb.Seeded.Zero.Body
import P256.Proofs.Nonce.Update.Absorb.Seeded.Zero.Return

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded.Zero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.Copy

theorem memcpy_zero_correct [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {reserve : Nat}
    (bindingsSupported : MachineRamUnitStrideDecodable bindings s)
    (machine : SupportedIntegerMachineState bindings.processor s) (loaded : ProgramLoaded s)
    (direction : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS)
    (rip : s.RIP = 0x11c930) (count : s.regValue .rdx = 0)
    (stack : MemReadable s (stackPtr s) 8)
    (low : (returnBoundary s).rip.toNat < 2^32)
    (outside : ¬ InProgram boundary.rip)
    (returnNe : (returnBoundary s).rip ≠ boundary.rip) :
    ∃ t, CalleeResult s t boundary 0 reserve ∧
      AgreesExcept (registerComponents ++ [.reg 4, .rip]) s t ∧
      t.external = s.external := by
  obtain ⟨s1, a1, ready1, code1, rip1, head1, counter1, agrees1⟩ := memcpy_prologue
    (n := 0) (readyToStep machine bindingsSupported) (programLoaded_codeIn loaded)
    outside rip count (by decide)
  simp only [Nat.zero_min] at head1 counter1
  obtain ⟨a2, ready2, rip2, agrees2, _⟩ := P256.Proofs.Common.Memory.Copy.Movsb.rep_movsb_zero boundary 0x11c947 s1 ready1
    (programText_slice code1 0x1c947 _ (by decide) (by decide +kernel)) rip1 counter1
    (boundary_ne_program outside (inProgram_of_textOffset 0x1c949 (by decide)))
  have code2 := agrees2.codeIn (by simp [Component.Covers]) code1
  have count2 : (nextState s1).regValue .rdx = 0 :=
    (agrees2.read (n := 64) (r := 2) (by simp)).trans
      ((agrees1.read (n := 64) (r := 2) (by simp)).trans count)
  have head2 : (nextState s1).regValue .r8 = 0 :=
    (agrees2.read (n := 64) (r := 8) (by simp)).trans head1
  obtain ⟨s3, a3, ready3, code3, rip3, count3, counter3, agrees3⟩ :=
    middle ready2 code2 outside rip2 count2 head2
  obtain ⟨a4, ready4, rip4, agrees4⟩ := P256.Proofs.Program.Copy.rep_movsq_zero boundary 0x11c953 s3 ready3
    (programText_slice code3 0x1c953 _ (by decide) (by decide +kernel)) rip3 counter3
    (boundary_ne_program outside (inProgram_of_textOffset 0x1c956 (by decide)))
  have code4 := agrees4.codeIn (by simp [Component.Covers]) code3
  have count4 : (nextState s3).regValue .rdx = 0 :=
    (agrees4.read (n := 64) (r := 2) (by simp)).trans count3
  obtain ⟨s5, a5, ready5, code5, rip5, counter5, agrees5⟩ :=
    tail ready4 code4 outside rip4 count4
  obtain ⟨a6, ready6, rip6, agrees6, _⟩ := P256.Proofs.Common.Memory.Copy.Movsb.rep_movsb_zero boundary 0x11c95c s5 ready5
    (programText_slice code5 0x1c95c _ (by decide) (by decide +kernel)) rip5 counter5
    (boundary_ne_program outside (inProgram_of_textOffset 0x1c95e (by decide)))
  have agrees : AgreesExcept registerComponents s (nextState s5) :=
    (((((agrees1.trans agrees2).trans agrees3).trans agrees4).trans agrees5).trans agrees6).mono
      (by simp [registerComponents])
  exact finish bindingsSupported machine loaded direction stack low returnNe ready6 agrees rip6
    (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6)

end P256.Proofs.Nonce.Update.Absorb.Seeded.Zero
