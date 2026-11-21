import Hkdf.Proofs.NewExpand.Extract.Frame
import Hkdf.Proofs.NewExpand.Extract.Update.Frame
import Hkdf.Proofs.Common.SHA256.Correctness
import Hkdf.Proofs.Common.Memory.Bytes
import Hkdf.Proofs.Common.StreamPadding.Execution.Calls

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Update

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.SHA256
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private def compressionLayout : StackCallLayout 2264 0 32 336 :=
  ⟨464, 0, 272, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

private theorem inputPrefix [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray} (pre : ExtractPre initial boundary salt ikm)
    (running : Running initial boundary #v[Stack.region initial 2264] s)
    (source : s.regValue .rsi = initial.regValue .rcx) :
    let slice := registerRegion s .rsi (64 * (ikm.size / 64))
    slice.Bounded ∧ slice.Allocated s.external ∧
      slice.Disjoint (Stack.region initial 2264) ∧ slice.HasBytes s.external (fullBlocks ikm) := by
  have bound := pre.ikmBytes.1
  change (initial.regValue .rcx).toNat + ikm.size < 2^32 at bound
  have apart := (pre.separation.2 _ (show Stack.region initial 2264 ∈
    #v[registerRegion initial .rdi 176, Stack.region initial 2264] by simp)).1
    (registerRegion initial .rcx ikm.size) (by simp)
  have stored := frame_hasBytes running.frame
    (fun r hr => (Vector.mem_singleton.mp hr) ▸ apart)
    (show (registerRegion initial .rcx ikm.size).start + ikm.size ≤ 2^64 by
      change (initial.regValue .rcx).toNat + ikm.size ≤ 2^64
      omega) pre.ikmBytes.2
  have bytes := Memory.hasBytes_prefix stored (count := 64 * (ikm.size / 64))
    (by change 64 * (ikm.size / 64) ≤ ikm.size; omega)
  simp only [registerRegion, source]
  refine ⟨?_, ?_, ?_, bytes⟩
  · change (initial.regValue .rcx).toNat + 64 * (ikm.size / 64) < 2^32
    omega
  · intro a inside
    rcases inside with ⟨lo,hi⟩
    change (initial.regValue .rcx).toNat ≤ a.toNat at lo
    change a.toNat < (initial.regValue .rcx).toNat + 64 * (ikm.size / 64) at hi
    let i : Fin ikm.size := ⟨a.toNat - (initial.regValue .rcx).toNat, by omega⟩
    have byte := stored.2 i
    change s.external[BitVec.ofNat 64 ((initial.regValue .rcx).toNat + i.val)]? = _ at byte
    have index : (initial.regValue .rcx).toNat + i.val = a.toNat := by dsimp [i]; omega
    rw [index, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
    exact ⟨_, byte⟩
  · intro a inside
    apply apart
    rcases inside with ⟨lo,hi⟩
    exact ⟨lo, Nat.lt_of_lt_of_le hi (by change (initial.regValue .rcx).toNat +
      64 * (ikm.size / 64) ≤ (initial.regValue .rcx).toNat + ikm.size; omega)⟩

theorem compress [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray} {hash : Array UInt32}
    (pre : ExtractPre initial boundary salt ikm) (state : Frame initial s boundary)
    (rip : s.RIP = 0x10fcad) (destination : s.regValue .rdi = base initial + 184)
    (source : s.regValue .rsi = initial.regValue .rcx)
    (count : s.regValue .rdx = BitVec.ofNat 64 (ikm.size / 64))
    (words : HashStateAt s (base initial + 184) hash) :
    ∃ t, Frame initial t boundary ∧ t.RIP = 0x10fcb2 ∧
      Hkdf.Proofs.Program.PreservesABI s t ∧
      HashStateAt t (base initial + 184) (compressBlocks hash ikm) ∧
      (Component.mem (base initial + 216) 48).Agrees s t := by
  have push : pushAddr s = stackPtr initial - 464 := by
    change stackPtr s - 8 = _
    rw [state.rsp, base, BitVec.sub_sub]
    rfl
  have instruction := programText_slice (programLoaded_codeIn state.loaded) 0xfcad
    (encodeCallRel32 0xffff990e) (by decide) (by decide +kernel)
  have step := call_rel32_effect_step 0x10fcad 0xffff990e (by decide +kernel)
  have avoid := stackAvoid pre
  have write : MemWritable s (pushAddr s) 8 := by
    rw [push]
    exact stack_writable8 pre.call.stack pre.call.stackAvoid state.allocated
      (offset := 464) (by decide) (by decide)
  have separate : RangeApart (pushAddr s) 8 0x10fcad 5 := by
    rw [push]
    exact stack_codeApart pre.call.stack (avoid _ (by simp)) (offset := 464)
      (codeOffset := 0xfcad) (by decide) (by decide) (by decide)
  obtain ⟨c, running, call, ret⟩ := state.toRunning.call step instruction ⟨rip, write, separate⟩
    (boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0x95c0 (by decide)))
    (by
      intro comp member a covered
      simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      all_goals try exact covered.elim
      rw [push] at covered
      exact ⟨_, by simp, stackRegion_contains_sub pre.call.stack.2.2.1
        (offset := 464) (by decide) (by decide) covered⟩) avoid
  have rspC : stackPtr c = stackPtr initial - 464 := call.writes.1.trans push
  have outputC : c.regValue .rdi = base initial + 184 :=
    (call.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans destination
  have out : c.regValue .rdi = stackPtr initial - 272 := by
    rw [outputC, base]
    bv_omega
  have src : c.regValue .rsi = initial.regValue .rcx :=
    (call.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans source
  obtain ⟨bounded, allocated, apart, bytes⟩ := inputPrefix pre running src
  have callee := callee_pre_of_stack_output pre.call.stride pre.call.stack pre.call.stackAvoid
    pre.call.outerBoundary running.machine running.directionFlag running.loaded running.allocated
    compressionLayout (show c.RIP = 0x1095c0 from call.rip) rspC out
    (by rw [ret]; exact inProgram_of_textOffset 0xfcb2 (by decide)) bounded allocated apart
  have compression : Hkdf.Proofs.Common.SHA256.CompressionPre c boundary hash (fullBlocks ikm)
      (ikm.size / 64) := by
    refine ⟨callee, ?_, ?_, bytes, ?_⟩
    · rw [out]
      change (stackPtr initial - BitVec.ofNat 64 272).toNat % 4 = 0
      rw [stack_sub_toNat pre.call.stack (offset := 272) (by decide)]
      have aligned : (stackPtr initial).toNat % 16 = 8 := pre.call.stack.2.2.2
      have := (stack_bounds pre.call.stack).1
      omega
    · exact (call.agrees.read (n := 64) (r := 2) (by simp [callEffect, pushEffect_components])).trans count
    · rw [outputC]
      apply hashState_of_bytes words
      rw [← state.rsp]
      exact StreamPadding.Execution.call_local_agrees call 184 32 (by unfold OffsetsApart; decide +kernel) (by decide)
  obtain ⟨t, result⟩ := Hkdf.Proofs.Common.SHA256.compression_correct compression
  have within := stack_layout_within pre.call.stack compressionLayout rspC out
  have runningT := running.of_callee result.toCalleeResult (by
    intro r hr a ha
    exact ⟨_, by simp, within r hr a ha⟩)
  obtain ⟨frame, abi⟩ := call_result callee call result.toCalleeResult state.directionFlag
  have rspT := result.rsp.trans (congrArg ReturnBoundary.rsp ret)
  have preserved (off size : Nat) (h : off + 32 ≤ 272 ∨ 272 + size ≤ off)
      (low : off + 8 ≤ 464) := stack_layout_disjoint pre.call.stack compressionLayout rspC out
        (savedOffset := off) (savedBytes := size) h low
  have saved := preserved 48 56 (by decide) (by decide)
  have op := preserved 376 8 (by decide) (by decide)
  have outputSlot : base initial + 80 = stackPtr initial - 376 := by unfold base; bv_omega
  have stateT := state.of_frame pre.call.stack runningT frame rspT abi.2.2.1 abi.2.2.2
    (fun r hr => ⟨saved r hr, outputSlot ▸ op r hr⟩)
  refine ⟨t, stateT, result.rip.trans (congrArg ReturnBoundary.rip ret), abi, ?_, ?_⟩
  · simpa only [outputC, compressBlocks_fullBlocks] using result.hashWords
  · rw [show base initial + 216 = stackPtr initial - 240 from by unfold base; bv_omega]
    apply frame_agrees_of_disjoint frame _ (preserved 240 48 (by decide) (by decide))
    rw [stack_sub_toNat pre.call.stack (offset := 240) (by decide)]
    have := (stack_bounds pre.call.stack).2
    omega

end Hkdf.Proofs.NewExpand.Extract.Update
