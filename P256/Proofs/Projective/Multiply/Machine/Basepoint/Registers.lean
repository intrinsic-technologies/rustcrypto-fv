import P256.Proofs.Projective.Multiply.Machine.Basepoint.Interface
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.EffectCompose.Advance

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame
open P256.Proofs.Common.Field (AdvanceTriple)

variable {outputBytes reserve frameOffset : Nat}

theorem register_block [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {offset : Nat} {bytes : List UInt8} {effect : RamState → Effect}
    (state : FrameState s t outputBytes reserve (BitVec.ofNat 64 frameOffset))
    (block : AdvanceTriple boundary (fun t => t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) (Effect.post effect))
    (bound : offset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (noMem : ∀ c ∈ (effect t).components, ∀ a, ¬ c.Covers a)
    (sp : .reg 4 ∉ (effect t).components)
    (hdf : Component.df ∉ (effect t).components)
    (hmxcsr : Component.mxcsr ∉ (effect t).components)
    (hfcw : Component.fcw ∉ (effect t).components) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u outputBytes reserve (BitVec.ofNat 64 frameOffset) ∧
      (effect t).Holds t u ∧ u.external = t.external := by
  obtain ⟨fuel, u, run, ready, _, result⟩ := block t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset bytes bound code) rip
  exact ⟨fuel, u, run, state.after_registers ready result.agrees noMem sp hdf hmxcsr hfcw,
    result, result.agrees.external noMem⟩

theorem scalar_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi 65, Stack.region s 3352])
    (scalar : SecretKeyFromBytes.Scalar.Nat256At s (s.regValue .rsi) d) :
    SecretKeyFromBytes.Scalar.Nat256At t (s.regValue .rsi) d := by
  refine ⟨scalar.1, fun i hi => (frame _ ?_).trans (scalar.2 i hi)⟩
  intro region hr hin
  have input := memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi
  have cases : region = registerRegion s .rdi 65 ∨ region = Stack.region s 3352 := by simpa using hr
  rcases cases with rfl | rfl
  · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide) _ input hin
  · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ input hin

end P256.Proofs.Projective.Multiply.Machine.Basepoint
