import P256.Proofs.Projective.Add.Copy.Preservation
import P256.Proofs.Program.WrapperMemory
set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.CrossTerms

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem register_block [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {offset : Nat} {bytes : List UInt8} {effect : RamState → Effect}
    (_pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (block : AdvanceTriple boundary (fun t => t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) (Effect.post effect))
    (bound : offset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (noMem : ∀ c ∈ (effect t).components, ∀ a, ¬ c.Covers a)
    (sp : .reg 4 ∉ (effect t).components)
    (hdf : Component.df ∉ (effect t).components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ (effect t).components := by component_not_mem)
    (hfcw : Component.fcw ∉ (effect t).components := by component_not_mem) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧
      (effect t).Holds t u ∧ u.external = t.external := by
  obtain ⟨fuel, u, run, ready, _, result⟩ := block t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset bytes bound code) rip
  exact ⟨fuel, u, run, state.after_registers ready result.agrees noMem sp hdf hmxcsr hfcw,
    result, result.agrees.external noMem⟩

theorem copy_stack_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {offset : Nat} (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (state : FrameState s t 96 920 632) (bound : offset + 32 ≤ 632)
    (agrees : AgreesExcept (Copy32.components (stackPtr t + BitVec.ofNat 64 offset)) t u) :
    MemoryWriteFrame t u #v[Stack.region s 920] := by
  apply agrees.memoryWriteFrame
  intro c hc a ha
  simp only [Copy32.components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  rw [scalar_stack_address (frameOffset := 632) state.rsp (by decide) (by omega)] at ha
  exact ⟨Stack.region s 920, by simp,
    stack_contains pre (by omega) (by omega) ha⟩

theorem copy_stack_value [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {offset target x : Nat} (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (state : FrameState s t 96 920 632) (bound : offset + 32 ≤ 632)
    (targetBound : target ≤ 632) (targetEnd : 32 ≤ target + 8)
    (apart : target + 32 ≤ 632-offset ∨ 632-offset + 32 ≤ target)
    (agrees : AgreesExcept (Copy32.components (stackPtr t + BitVec.ofNat 64 offset)) t u)
    (input : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 target) x) :
    MontgomeryAt u (stackPtr s - BitVec.ofNat 64 target) x := by
  apply input.of_bytes_eq
  intro i hi
  apply agrees.byte
  intro c hc ha
  simp only [Copy32.components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  obtain ⟨j, hj, he⟩ := ha
  rw [scalar_stack_address (frameOffset := 632) state.rsp (by decide) (by omega)] at he
  exact stack_sub_apart pre.stack (by omega) (by omega) (by omega) targetEnd apart j hj i hi he.symm

end P256.Proofs.Projective.Add.CrossTerms
