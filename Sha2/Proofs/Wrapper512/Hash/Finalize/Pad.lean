import Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.Finish

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem pad_loaded [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} {message : ByteArray} (ctx : Context v initial inputs form)
    (input : Pad.Loaded v initial s message form) (eligible : form.canFinalize) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Padded v initial t message form ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      (¬form.isTerminal → v.countValue form initial t = v.countValue form initial s) := by
  obtain ⟨u, ⟨fuelU, runU⟩, setup, _, frameU, countU⟩ := Pad.setup_local ctx input eligible
  obtain ⟨t, ⟨fuelT, runT⟩, padded, _, _, frameT, countT⟩ := Pad.finish_local ctx setup
  exact ⟨fuelU + fuelT, t, runU.trans runT, padded,
    memoryWriteFrame_trans frameU frameT, fun terminal => (countT terminal).trans (countU terminal)⟩

theorem pad_stage [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs form)
    (input : Buffered v initial s (message inputs) form)
    (rip : s.RIP = v.pc (v.dispatchOffset form inputs.isEmpty) form)
    (eligible : form.canFinalize)
    (resetEmptyPointer : form = .reset 1 → inputs.isEmpty = true →
      s.regValue .rax = hashPointer initial form form.finalMemory)
    (resetEmptyWords : form = .reset 1 → inputs.isEmpty = true → ∀ i < 8,
      (.reg (BitVec.ofNat 5 (Dispatch.Store.wordRegister v (.reset 1) i)) : Operand 64).read s = v.initialHash[i]!.toBitVec)
    (finalizeEmpty : form = .finalizeIntoReset false → inputs.isEmpty = true →
      (s.regValue .rax).setWidth 8 = 0 ∧ s.regValue .r14 = 0 ∧ s.regValue (highCountRegister v form) = 0)
    (traitOutput : form = .traitFinalizeIntoReset false →
      if inputs.isEmpty then s.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx
      else memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Padded v initial t (message inputs) form ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      (¬form.isTerminal → v.countValue form initial t = v.countValue form initial s) := by
  obtain ⟨u, loaded, ⟨fuelU, runU⟩, frameU, _, _, _, _, countU⟩ :=
    Pad.load_local ctx input rip eligible resetEmptyPointer resetEmptyWords finalizeEmpty traitOutput
  obtain ⟨fuelT, t, runT, padded, frameT, countT⟩ := pad_loaded ctx loaded eligible
  exact ⟨fuelU + fuelT, t, runU.trans runT, padded,
    memoryWriteFrame_trans frameU frameT, fun terminal => (countT terminal).trans (countU terminal)⟩

theorem pad [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    {message : ByteArray} (ctx : Context v initial inputs form)
    (input : Buffered v initial s message form) (rip : s.RIP = v.pc (if form = .slices then 0x218 else 0x143) form)
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    ∃ t, Padded v initial t message form := by
  obtain ⟨u, loaded⟩ := Pad.load ctx input rip
  obtain ⟨_, t, _, padded, _, _⟩ := pad_loaded ctx loaded (by
    rcases eligible with rfl | rfl <;> trivial)
  exact ⟨t, padded⟩

end Sha2.Proofs.Wrapper512.Hash.Finalize
