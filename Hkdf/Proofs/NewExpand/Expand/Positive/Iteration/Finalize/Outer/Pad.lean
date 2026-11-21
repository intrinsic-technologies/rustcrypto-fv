import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.OuterPad
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Outer.Frame
import Hkdf.Proofs.Common.State

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.Outer

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.SHA256
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad (padded)

private theorem padPre [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length : Nat}
    (pre : ExpandPre entry boundary key info ptr length)
    (saved : SavedFrame entry s boundary length) (rip : s.RIP = 0x10f42e)
    (r15 : s.regValue .r15 = stackPtr s + 144) : OuterPad.Pre s := by
  have sp : stackPtr s = stackPtr entry - 536 := saved.sp
  have maxOffset (i : Nat) (member : i ∈ [72,113,121,128,136]) : i ≤ 136 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  have apart (o n : Nat) (fit : o + n ≤ 144) :
      RangeApart (stackPtr s + BitVec.ofNat 64 o) n 0x10f42e 63 :=
    local_codeApart pre.call.stack (fun a ha hp => pre.call.stackAvoid a ha (.inl hp)) sp
      (codeOffset := 0xf42e) (by omega) (by omega) (by decide)
  refine ⟨rip, r15, local_readable pre.call.stack saved.allocated sp
    (offset := 216) (by decide) (by decide), ?_,
    local_writable pre.call.stack pre.call.stackAvoid saved.allocated sp
      (offset := 112) (by decide) (by decide), ?_, ?_⟩
  · intro i member
    exact local_writable pre.call.stack pre.call.stackAvoid saved.allocated sp
      (by have := maxOffset i member; omega) (by decide)
  · intro i member offset n fit
    exact (apart i 8 (by have := maxOffset i member; omega)).sub offset n fit
  · intro offset n fit
    exact (apart 112 1 (by decide)).sub offset n fit

private theorem padWrites (s : RamState) :
    StackWrites (OuterPad.effect s).components (stackPtr s) [(72, 8), (112, 32)] := by
  intro c member a covered
  rcases OuterPad.memory_footprint member covered with head | tail
  · exact ⟨(72, 8), by simp, head⟩
  · exact ⟨(112, 32), by simp, tail⟩

theorem padOuter [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length : Nat} {outerHash : Array UInt32} {digest : ByteArray}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (bound : length ≤ 8160)
    (saved : SavedFrame entry s boundary length) (rip : s.RIP = 0x10f42e)
    (r15 : s.regValue .r15 = stackPtr s + 144) (count : slot s 216 = 1)
    (digestBytes : (⟨(stackPtr s + 80).toNat, 32⟩ : MemoryRegion).HasBytes s.external digest)
    (hashWords : HashStateAt s (stackPtr s + 184) outerHash) :
    ∃ fuel t, Advances boundary fuel s t ∧ SavedFrame entry t boundary length ∧
      t.RIP = 0x10f46d ∧ stackPtr t = stackPtr s ∧ PreservesABI s t ∧
      MemoryWriteFrame s t (writeRegions (stackPtr s)) ∧
      (⟨(stackPtr t + 80).toNat, 64⟩ : MemoryRegion).HasBytes t.external (padded digest) ∧
      slot t 72 = slot t 136 ∧ HashStateAt t (stackPtr t + 184) outerHash := by
  obtain ⟨fuel, t, advance, ready, h, payload, eighth⟩ :=
    OuterPad.execute (supportedMachine_readyToStep saved.machine) saved.loaded pre.call.outerBoundary
      (padPre pre saved rip r15) count digestBytes
      (local_readable pre.call.stack saved.allocated saved.sp (offset := 80) (by decide) (by decide))
  have sp : stackPtr t = stackPtr s := OuterPad.rsp_unchanged h
  have saved' := (padWrites s).saved pre pos bound saved advance ready h.agrees (by decide)
    (by simp [OuterPad.effect, Effect.components, Write.component, Operand.component])
  have abi : PreservesABI s t := by
    apply abi_of_agreement h.agrees saved.directionFlag
    · intro r member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [OuterPad.effect, Effect.components, Write.component, Operand.component]
    all_goals simp [OuterPad.effect, Effect.components, Write.component, Operand.component]
  have frame := local_frame pre.call.stack saved.sp h.agrees (padWrites s) (by decide)
  have words : HashStateAt t (stackPtr t + 184) outerHash := by
    rw [sp]
    exact Hkdf.Proofs.Common.hashState_of_bytes hashWords
      ((padWrites s).agrees h.agrees (off := 184) (by decide) (by decide) (by decide))
  refine ⟨fuel, t, advance, saved'.1, h.rip, sp, abi, frame, ?_, ?_, words⟩
  · rw [sp]
    exact payload
  · change memLoad t.external (stackPtr t + 72) 64 = memLoad t.external (stackPtr t + 136) 64
    rw [sp]
    exact eighth

end Hkdf.Proofs.NewExpand.Expand.Finalize.Outer
