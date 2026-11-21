import P256.Proofs.Projective.Double.Products.Pre
import P256.Proofs.Projective.Double.Values
import P256.Proofs.Program.FieldCall.Binary
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall
open P256.Proofs.Field X86 X86.Machine X86.UserProcess X86Proofs

namespace Products

theorem move_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {ip : BitVec 64} {reads writes : List (BitVec 64)}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (rip : t.RIP = ip) (hr : ∀ i ∈ reads, i.toNat + 8 ≤ 728)
    (hw : ∀ i ∈ writes, i.toNat + 8 ≤ 728) : MovePre ip reads writes t := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro i hi
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Operand.read_reg64, stackPtr] using stack_readable (frameOffset := 728) pre state (by decide) (hr i hi)
  · intro i hi
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Operand.read_reg64, stackPtr] using stack_writable (frameOffset := 728) pre state (by decide) (hw i hi) (by decide)
  · intro i hi offset len bound
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Operand.read_reg64, stackPtr] using stack_code (frameOffset := 728) pre state (by decide) (hw i hi) bound

theorem move_writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cs : List Component} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (localWrites : ∀ c ∈ cs, ∀ a, c.Covers a →
      ∃ i < 72, a = stackPtr t + BitVec.ofNat 64 i) :
    WritesWithin cs #v[workRegion s 1016] := by
  intro c hc a ha
  obtain ⟨i, hi, rfl⟩ := localWrites c hc a ha
  refine ⟨workRegion s 1016, by simp, ?_⟩
  rw [scalar_stack_address (frameOffset := 728) state.rsp (by decide) (by omega)]
  apply work_contains pre (offset := 728-i) (len := 1) (by omega) (by omega)
  exact ⟨0, by decide, by simp⟩

theorem move_keep [Bindings] {s t u : RamState}
    {cs : List Component} (state : FrameState s t 96 1016 728) (agrees : AgreesExcept cs t u)
    (localWrites : ∀ c ∈ cs, ∀ a, c.Covers a →
      ∃ i < 72, a = stackPtr t + BitVec.ofNat 64 i)
    {offset x : Nat} (bound : offset ≤ 656) (positive : 32 ≤ offset)
    (input : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) x) :
    MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) x := by
  refine ⟨input.1, input.2.1, fun i hi => ?_⟩
  rw [agrees.byte]
  · exact input.2.2 i hi
  · intro c hc ha
    obtain ⟨j, hj, he⟩ := localWrites c hc _ ha
    have addr : stackPtr s - BitVec.ofNat 64 offset =
        stackPtr t + BitVec.ofNat 64 (728-offset) := by
      rw [scalar_stack_address (frameOffset := 728) state.rsp (by decide) (by omega), Nat.sub_sub_self (by omega)]
    rw [addr] at he
    exact RangeApart.offsets (stackPtr t) (a := 0) (b := 728-offset)
      (len := 72) (count := 32) (by omega) (by omega) (Or.inl (by omega))
      j hj i hi (by simpa only [BitVec.add_zero] using he.symm)

theorem move_run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {pc : Nat} {reads writes : List (BitVec 64)} {bytes : List UInt8} {E : RamState → Effect}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (block : P256.Proofs.Common.Field.AdvanceTriple boundary (MovePre (Extracted.textAddress + BitVec.ofNat 64 pc) reads writes)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 pc) bytes) (Effect.post E))
    (codeBound : pc + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom pc bytes.length = bytes)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 pc)
    (hr : ∀ i ∈ reads, i.toNat + 8 ≤ 728) (hw : ∀ i ∈ writes, i.toNat + 8 ≤ 728)
    (localWrites : ∀ c ∈ (E t).components, ∀ a, c.Covers a →
      ∃ i < 72, a = stackPtr t + BitVec.ofNat 64 i)
    (sp : .reg 4 ∉ (E t).components)
    (hdf : Component.df ∉ (E t).components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ (E t).components := by component_not_mem)
    (hfcw : Component.fcw ∉ (E t).components := by component_not_mem) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧ (E t).Holds t u ∧
      MemoryWriteFrame t u #v[workRegion s 1016] ∧
      (∀ offset x, offset ≤ 656 → 32 ≤ offset →
        MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) x →
        MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) x) := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := block t (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) pc bytes codeBound code)
    (move_pre pre state rip hr hw)
  have writes := move_writes pre state localWrites
  refine ⟨fuel, u, run, FrameState.after_effect pre (by decide) state ready effect.agrees ?_ sp, effect,
    effect.agrees.memoryWriteFrame writes, fun _ _ hb hp hx => move_keep state effect.agrees localWrites hb hp hx⟩
  intro c hc a ha
  obtain ⟨region, hregion, hin⟩ := writes c hc a ha
  have he : region = workRegion s 1016 := by simpa using hregion
  exact ⟨region, by simp [he], hin⟩

theorem copy_words [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {src dst x : Nat}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (agrees : AgreesExcept cs t u) (srcBound : src ≤ 728) (dstBound : dst + 32 ≤ 728)
    (input : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 (728-src)) x)
    (limbs : ∀ j < 4, memLoad u.external (stackPtr t + BitVec.ofNat 64 (dst+8*j)) 64 =
      memLoad t.external (stackPtr t + BitVec.ofNat 64 (src+8*j)) 64) :
    MontgomeryAt u (stackPtr s - BitVec.ofNat 64 (728-dst)) x := by
  have hx : MontgomeryAt t (stackPtr t + BitVec.ofNat 64 src) x := by
    rw [scalar_stack_address (frameOffset := 728) state.rsp (by decide) srcBound]
    exact input
  have result : MontgomeryAt u (stackPtr t + BitVec.ofNat 64 dst) x := by
    apply Field.montgomeryAt_of_memLoad_limbs hx.1
    · intro i hi
      exact agrees.grow _ ((stack_readable (frameOffset := 728) pre state (by decide) dstBound).mem i hi)
    · intro j hj
      rw [← hx.memLoad_limb j hj]
      simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using limbs j hj
  rw [scalar_stack_address (frameOffset := 728) state.rsp (by decide) (by omega)] at result
  exact result

theorem call_keep {s t u : RamState} {outOffset offset x : Nat}
    (bytes : ∀ offset len : Nat, offset ≤ 728 → len ≤ offset + 8 →
      (offset + 32 ≤ outOffset ∨ outOffset + len ≤ offset) →
      ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?)
    (bound : offset ≤ 728) (positive : 32 ≤ offset+8)
    (apart : offset + 32 ≤ outOffset ∨ outOffset + 32 ≤ offset)
    (input : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) x) :
    MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) x :=
  ⟨input.1, input.2.1, fun i hi => (bytes offset 32 bound positive apart i hi).trans (input.2.2 i hi)⟩


end Products
end P256.Proofs.Projective.Double
