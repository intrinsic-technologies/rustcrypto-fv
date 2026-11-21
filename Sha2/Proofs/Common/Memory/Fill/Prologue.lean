import Sha2.Proofs.Common.Memory.Fill.Prologue.Alignment
import Sha2.Proofs.Common.Memory.Fill.Prologue.ZeroProduct

set_option autoImplicit false

open Sha2.Proofs.Program

namespace Sha2.Proofs.Common.Memory.Fill

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prologue [Bindings]
    {s : RamState} {boundary : ReturnBoundary} {n : Nat}
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programSections.toCodeMap s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x10dd10)
    (hzero : (s.regValue .rsi).setWidth 32 = 0) (hn : s.regValue .rdx = BitVec.ofNat 64 n) (bound : n < 2^32) :
    ∃ t, Advances boundary 14 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programSections.toCodeMap t ∧ t.RIP = 0x10dd44 ∧
      t.regValue .rax = 0 ∧ t.regValue .rdx = s.regValue .rdi ∧
      t.regValue .rcx = BitVec.ofNat 64 (min n ((8 - (s.regValue .rdi).toNat % 8) % 8)) ∧
      t.regValue .rsi = BitVec.ofNat 64 ((n - min n ((8 - (s.regValue .rdi).toNat % 8) % 8)) / 8) ∧
      t.regValue .r8 = BitVec.ofNat 64 ((n - min n ((8 - (s.regValue .rdi).toNat % 8) % 8)) % 8) ∧
      AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 6, .reg 8, .flags, .rip] s t := by
  obtain ⟨s1, ha1, hr1, hc1, hip1, hax1, hdx1, h81, hf1⟩ :=
    zeroProduct hready hcode hout hip hzero hn
  obtain ⟨t, ha2, hr2, hc2, hip2, hcx2, hsi2, h82, hf2⟩ :=
    alignment hr1 hc1 hout hip1 h81 bound
  have hax2 : t.regValue .rax = 0 :=
    (hf2.read (n := 64) (r := 0) (by decide)).trans hax1
  have hdx2 : t.regValue .rdx = s.regValue .rdi :=
    (hf2.read (n := 64) (r := 2) (by decide)).trans hdx1
  rw [hdx1] at hcx2 hsi2 h82
  exact ⟨t, ha1.trans ha2, hr2, hc2, hip2, hax2, hdx2, hcx2, hsi2, h82,
    (hf1.trans hf2).mono (by decide)⟩

end Sha2.Proofs.Common.Memory.Fill
