import P256.Proofs.Program.Compare.Execution
import P256.Proofs.Program.Compare.Model

namespace P256.Proofs.Program.Compare

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

theorem inRoutine_inProgram {ip : BitVec 64} (h : InRoutine ip) : InProgram ip := by
  have ho : ip.toNat - 0x100000 < 118431 := by obtain ⟨hl, hh⟩ := h; omega
  have lower : 0x100000 ≤ ip.toNat := by obtain ⟨hl, hh⟩ := h; omega
  have he := congrArg (BitVec.ofNat 64) (Nat.sub_add_cancel lower)
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat] at he
  have address : Extracted.textAddress + BitVec.ofNat 64 (ip.toNat - 0x100000) = ip := by
    rw [BitVec.add_comm]
    exact he
  exact address ▸ inProgram_of_textOffset _ ho

theorem RegisterBoundary.of_outside {boundary : ReturnBoundary} (s : RamState)
    (h : ¬ InProgram boundary.rip) : RegisterBoundary boundary s := by
  apply Or.inr
  intro ip hip he
  apply h
  exact he ▸ inRoutine_inProgram hip

theorem CallBoundary.register {boundary : ReturnBoundary} {s t : RamState}
    (h : CallBoundary boundary s) : RegisterBoundary boundary t :=
  RegisterBoundary.of_outside t h.1

end P256.Proofs.Program.Compare
