import Hkdf.Proofs.Key.Hash.State
import Hkdf.Proofs.Key.Memory
import Hkdf.Proofs.Common.StreamPadding.Execution.Geometry
import Hkdf.Proofs.Common.StreamPadding.Run

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Hash

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.StreamPadding
open Hkdf.Proofs.Common.SHA256

private theorem working_of_padding [Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} {key : ByteArray}
    (ctx : Context initial boundary key) (state : Working initial boundary s)
    (result : Result .key initial s t boundary key) : Working initial boundary t := by
  have rsp : stackPtr s = base .key initial := state.rsp
  have bounds := Key.stack_bounds ctx.toCalleePre
  change 720 ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2^32 at bounds
  have baseNat : (blockAddress initial).toNat = (stackPtr initial).toNat - 376 :=
    Key.stack_sub_toNat ctx.toCalleePre (by decide)
  have belowNat := Execution.below_toNat .key ctx.toCalleePre 344 (by decide)
  have tailNat := Execution.local_toNat .key ctx.toCalleePre 64 (by decide)
  have hashNat := Execution.local_toNat .key ctx.toCalleePre 128 (by decide)
  have scratchNat := Execution.local_toNat .key ctx.toCalleePre 168 (by decide)
  have savedNat := Key.stack_sub_toNat ctx.toCalleePre (offset := 40) (by decide)
  simp only [Variant.frame, Nat.reduceAdd] at belowNat
  simp only [Variant.frame] at tailNat hashNat scratchNat
  have frame : MemoryWriteFrame s t (writes .key (base .key initial)) := by
    simpa only [rsp] using result.frame
  have apart : ∀ written ∈ writes .key (base .key initial),
      (⟨(blockAddress initial).toNat, 64⟩ : MemoryRegion).Disjoint written ∧
      (⟨(stackPtr initial - 40#64).toNat, 48⟩ : MemoryRegion).Disjoint written := by
    intro written member
    simp only [writes, Variant.tail, Variant.hash, Variant.scratch,
      Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false,
      BitVec.ofNat_eq_ofNat] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals constructor
    all_goals intro a ha hb
    all_goals change _ ≤ a ∧ a < _ at ha hb
    all_goals first | rw [baseNat] at ha | rw [savedNat] at ha
    all_goals first | rw [belowNat] at hb | rw [tailNat] at hb |
      rw [hashNat] at hb | rw [scratchNat] at hb
    all_goals dsimp only at ha hb
    all_goals omega
  have zero := frame_hasBytes frame (fun r hr ↦ (apart r hr).1)
    (by change (blockAddress initial).toNat + 64 ≤ 2^64; rw [baseNat]; omega)
    state.zeroBlock
  have saved := frame_agrees_of_disjoint frame
    (address := stackPtr initial - 40#64) (size := 48)
    (by rw [savedNat]; omega) (fun r hr ↦ (apart r hr).2)
  exact state.of_observations result.running saved result.rsp result.rbx result.rbp
    result.mxcsr result.fcw zero

theorem pad [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key : ByteArray} (ctx : Context initial boundary key)
    (state : Working initial boundary s) (rip : s.RIP = 0x116442)
    (stream : Common.StreamAt s (rspOf s + 64) key) :
    ∃ t, Working initial boundary t ∧ t.RIP = 0x1165c9 ∧
      HashStateAt t (rspOf t + 128)
        (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (bytePadding key)) := by
  have size : key.size < 2^61 := by
    have bound := ctx.inputBounded
    change (initial.regValue .rsi).toNat + key.size < 2^32 at bound
    omega
  obtain ⟨t, result⟩ := Common.StreamPadding.run .key ctx.toCalleePre state.toRunning
    state.rsp rip stream size
  refine ⟨t, working_of_padding ctx state result, result.rip, ?_⟩
  change HashStateAt t (stackPtr t + 128) _
  rw [result.rsp]
  simpa only [Variant.hash, Variant.tail, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    using result.hashWords

end Hkdf.Proofs.Key.Hash
