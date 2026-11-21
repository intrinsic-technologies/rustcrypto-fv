import Sha2.Proofs.Digest.Absorb.Select
import Sha2.Proofs.Digest.Absorb.CopySetup
import Sha2.Proofs.Wrapper512.Absorb.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Digest.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine
  X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper512

theorem select [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {message : ByteArray} (ctx : Context v initial inputs .digest)
    (input : Buffered v initial s message .digest) (rip : s.RIP = v.pc 0xca .digest) :
    ∃ t, Buffered v initial t message .digest ∧
      (selectEffect (v.pc 0xca .digest) s).Holds s t := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  have inside : BlockInProgram (v.pc 0xca .digest) selectBytes.length := by
    intro i hi
    rw [Variant.pc_add _ _ _ .digest]
    apply Variant.pc_inProgram (form := .digest)
    change i ≤ 6 at hi
    omega
  have target : InProgram (v.pc 0xca .digest + 33) := by
    rw [show (33 : BitVec 64) = BitVec.ofNat 64 33 from rfl, Variant.pc_add _ _ _ .digest]
    exact Variant.pc_inProgram v (by decide) .digest
  obtain ⟨fuel,t,run,ready,_,effect⟩ := select_run (v.pc 0xca .digest)
    (returnBoundary initial) outside inside target s (supportedMachine_readyToStep input.machine)
    (select_code v input.loaded) rip
  have frame : AgreesExcept [.flags,.rip] s t := effect.agrees
  exact ⟨t, Wrapper512.Absorb.buffered_of_agrees ctx input run ready frame
    (by simp [Component.Covers]) (by simp) (by simp) (by simp), effect⟩

theorem copy_setup [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs .digest)
    (input : Preserved v initial s .digest) (tail : Bool)
    (rip : s.RIP = v.pc (if tail then 0x12f else 0xd0) .digest) :
    ∃ t, Preserved v initial t .digest ∧
      (CopySetup.effect (v.pc (if tail then 0x12f else 0xd0) .digest) tail s).Holds s t := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  have inside : BlockInProgram (v.pc (if tail then 0x12f else 0xd0) .digest)
      (CopySetup.bytes tail).length := by
    intro i hi
    rw [Variant.pc_add _ _ _ .digest]
    apply Variant.pc_inProgram (form := .digest)
    cases tail <;> simp only [CopySetup.bytes, List.length_append, List.length_cons,
      List.length_nil, Bool.false_eq_true, ite_false, ite_true] at hi ⊢ <;> omega
  obtain ⟨fuel,t,run,ready,_,effect⟩ := CopySetup.run
    (v.pc (if tail then 0x12f else 0xd0) .digest) tail (returnBoundary initial)
    outside inside s (supportedMachine_readyToStep input.machine)
    (CopySetup.code v tail input.loaded) rip
  have frame : AgreesExcept [.reg 7,.reg 6,.reg 2,.rip] s t := by
    apply effect.agrees.mono
    cases tail <;> simp [CopySetup.effect, Effect.components, Write.component, Operand.component]
  exact ⟨t, Wrapper512.Absorb.preserved_of_agrees ctx input run ready frame
    (by simp [Wrapper512.Absorb.LocalWrites, Component.Covers]) (by simp) (by simp) (by simp), effect⟩

end Sha2.Proofs.Digest.Absorb
