import P256.Proofs.Ecdh.Normalize.Conversion.Core
import P256.Proofs.Ecdh.Normalize.Conversion.Wrapper.Frame

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Conversion

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Wrapper

theorem callee_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : CalleePre s boundary 0x107d00 32 32 40)
    (value : Field.MontgomeryAt s (s.regValue .rsi) x) :
    ∃ u, CalleeResult s u boundary 32 40 ∧ Nat256At u (s.regValue .rdi) x := by
  obtain ⟨t, entry⟩ := entry_correct pre
  obtain ⟨fuel, u, run, ready, body, rip, h0, h1, h2, h3⟩ := core_correct
    pre.outerBoundary entry.ready entry.loaded entry.rip
    (input_readable pre entry) (input_unchanged pre entry value)
  have memory : u.external = t.external := body.external (by simp [registers, Component.Covers])
  have loaded : ProgramLoaded u := by
    intro a b hb
    rw [memory]
    exact entry.loaded a b hb
  have hd : (Operand.reg 7 : Operand 64).read u = s.regValue .rdi :=
    (body.read (by simp [registers])).trans
      (entry.agrees.read (by simp [prologueComponents, sources, pushSequenceFrame]))
  have hx : x < 2^256 := Nat.lt_trans value.1 (by decide +kernel)
  obtain ⟨v, ⟨storeFuel, storeRun⟩, storeReady, storeRip, stores, represented⟩ :=
    store_body pre ready loaded rip (entry.agrees.trans body) hd hx h0 h1 h2 h3
  have stage := return_state pre entry body stores storeReady storeRip
  obtain ⟨w, result, mem⟩ := epilogue_correct pre stage
    ((entry.execution.trans run).trans storeRun)
    (by simp [prologueComponents, sources, pushSequenceFrame, registers])
    (by simp [prologueComponents, sources, pushSequenceFrame, registers])
    (by simp [prologueComponents, sources, pushSequenceFrame, registers])
    (by simp [prologueComponents, sources, pushSequenceFrame, registers])
  exact ⟨w, result, represented.1, fun i hi => by rw [mem]; exact represented.2 i hi⟩

end P256.Proofs.Ecdh.Normalize.Conversion
