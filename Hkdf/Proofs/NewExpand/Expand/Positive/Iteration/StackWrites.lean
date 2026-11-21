import Hkdf.Proofs.NewExpand.Expand.Frame
import Hkdf.Proofs.Common.CallFrame.Push

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine Prelude X86 X86.Machine X86.UserProcess X86Proofs

def StackWrites (components : List Component) (sp : BitVec 64) (ranges : List (Nat × Nat)) : Prop :=
  ∀ c ∈ components, ∀ a, c.Covers a → ∃ r ∈ ranges,
    (Component.mem (sp + BitVec.ofNat 64 r.1) r.2).Covers a

theorem StackWrites.agrees {components : List Component} {s t : RamState} {sp : BitVec 64}
    {ranges : List (Nat × Nat)} (writes : StackWrites components sp ranges)
    (effect : AgreesExcept components s t) {off len : Nat}
    (bounded : off + len ≤ 2^64) (within : ∀ r ∈ ranges, r.1 + r.2 ≤ 2^64)
    (apart : ∀ r ∈ ranges, off + len ≤ r.1 ∨ r.1 + r.2 ≤ off) :
    (Component.mem (sp + BitVec.ofNat 64 off) len).Agrees s t := by
  intro i hi
  apply effect.byte
  intro c hc covers
  obtain ⟨r, hr, j, hj, eq⟩ := writes c hc _ covers
  exact RangeApart.offsets sp bounded (within r hr) (apart r hr) i hi j hj eq

theorem StackWrites.saved [Bindings] {entry s t : RamState} {boundary : ReturnBoundary}
    {length fuel : Nat} {key info : ByteArray} {ptr : BitVec 64}
    {components : List Component} {ranges : List (Nat × Nat)}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (bound : length ≤ 8160)
    (saved : SavedFrame entry s boundary length) (run : Advances boundary fuel s t)
    (ready : ReadyToStep t) (effect : AgreesExcept components s t)
    (writes : StackWrites components (stackPtr s) ranges)
    (within : ∀ r ∈ ranges, r.1 + r.2 ≤ 488 ∧ (r.1 + r.2 ≤ 224 ∨ 232 ≤ r.1))
    (regs : .reg 4 ∉ components ∧ .df ∉ components ∧ .mxcsr ∉ components ∧ .fcw ∉ components) :
    SavedFrame entry t boundary length ∧ MemoryWriteFrame s t #v[Stack.region entry 2264] := by
  have sp : stackPtr s = stackPtr entry - 536 := saved.sp
  have writeStack (c : Component) (hc : c ∈ components) (a : BitVec 64) (ha : c.Covers a) :
      (Stack.region entry 2264).Contains a.toNat := by
    obtain ⟨⟨off,len⟩, hr, covers⟩ := writes c hc a ha
    have fit : off + len ≤ 488 := (within _ hr).1
    have addr : stackPtr s + BitVec.ofNat 64 off = stackPtr entry - BitVec.ofNat 64 (536 - off) := by
      rw [sp, ← BitVec.ofNat_sub_ofNat_of_le 536 off (by omega) (by omega)]
      change stackPtr entry - 536 + _ = stackPtr entry - (536 - _)
      bv_omega
    rw [addr] at covers
    exact stackRegion_contains_sub pre.call.stack.2.2.1 (by omega) (by omega) covers
  have stackFrame := effect.memoryWriteFrame (regions := #v[Stack.region entry 2264])
    (fun c hc a ha ↦ ⟨_, by simp, writeStack c hc a ha⟩)
  have running := saved.toRunning.of_agrees run ready effect
    (fun c hc a ha ↦ ⟨Stack.region entry 2264, by simp, writeStack c hc a ha⟩)
    (by
      simp only [writtenLength, bound, ↓reduceIte]
      exact fun r hr a ha hp ↦ ((pre.separation pos bound).2 r hr).2 a ha (.inl hp))
    regs.2.1
  have capacity (r) (hr : r ∈ ranges) : r.1 + r.2 ≤ 2^64 := by
    have := (within r hr).1
    omega
  have spT : t.regValue .rsp = s.regValue .rsp := effect.read (n := 64) regs.1
  refine ⟨saved.of_agreement running spT ?_ ?_ (effect.mxcsr regs.2.2.1) (effect.fcw regs.2.2.2),
    stackFrame⟩
  · exact writes.agrees effect (off := 488) (by decide) capacity
      (fun r hr ↦ Or.inr (within r hr).1)
  · change memLoad t.external (t.regValue .rsp + 224) 64 = _
    rw [spT]
    exact agrees_memLoad (writes.agrees effect (off := 224) (len := 8)
      (by decide) capacity (fun r hr ↦ (within r hr).2.symm))

end Hkdf.Proofs.NewExpand.Expand
