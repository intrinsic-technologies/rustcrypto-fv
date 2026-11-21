import Hkdf.Proofs.NewExpand.Extract.Frame
import Hkdf.Proofs.NewExpand.Extract.Update.Arguments
import Hkdf.Proofs.NewExpand.Extract.Update.Frame
import Hkdf.Proofs.Common.Memory.Copy
import Hkdf.Proofs.Common.Memory.Pointers

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Update

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def CopyPath.copyPc (path : CopyPath) : BitVec 64 := path.pc + 11

private theorem CopyPath.copyPc_eq (path : CopyPath) :
    path.copyPc = Extracted.textAddress + BitVec.ofNat 64 (path.offset + 11) := by
  simp only [CopyPath.copyPc, CopyPath.pc, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]

private def CopyPath.displacement (path : CopyPath) : BitVec 32 :=
  match path with
  | .short => 0xf169e
  | .residual => 0xf164d

private abbrev copyLayout (count : Nat) (small : count < 64) :
    StackCallLayout 2264 0 count 0 :=
  ⟨464, 0, 336, by decide, by decide, by decide, by decide, by decide,
    by omega, .inr (by omega)⟩

private theorem copyInput [Bindings] {initial t : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray} {offset count : Nat}
    (pre : ExtractPre initial boundary salt ikm)
    (frame : MemoryWriteFrame initial t #v[Stack.region initial 2264])
    (source : t.regValue .rsi = initial.regValue .rcx + BitVec.ofNat 64 offset)
    (sourceBound : offset + count ≤ ikm.size) :
    (registerRegion t .rsi count).Bounded ∧
    (registerRegion t .rsi count).Allocated t.external ∧
    (registerRegion t .rsi count).Disjoint (Stack.region initial 2264) ∧
    ∀ (i : Nat) (_hi : i < count), t.external[t.regValue .rsi + BitVec.ofNat 64 i]? =
      some (ikm[offset + i]'(by omega)) := by
  have bound := pre.ikmBytes.1
  change (initial.regValue .rcx).toNat + ikm.size < 2^32 at bound
  have start : (t.regValue .rsi).toNat = (initial.regValue .rcx).toNat + offset := by
    rw [source, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : offset < 2^64), Nat.mod_eq_of_lt (by omega)]
  have apart : (registerRegion initial .rcx ikm.size).Disjoint (Stack.region initial 2264) :=
    (pre.separation.2 _ (by simp)).1 _ (by simp)
  have preserved := frame_hasBytes frame
    (fun region member ↦ by rw [Vector.mem_singleton.mp member]; exact apart)
    (by change (initial.regValue .rcx).toNat + ikm.size ≤ 2^64; omega)
    pre.ikmBytes.2
  have contains (a : Nat) (ha : (registerRegion t .rsi count).Contains a) :
      (registerRegion initial .rcx ikm.size).Contains a := by
    change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + count at ha
    rw [start] at ha
    change (initial.regValue .rcx).toNat ≤ a ∧ a < (initial.regValue .rcx).toNat + ikm.size
    omega
  refine ⟨?_, ?_, fun a ha ↦ apart a (contains a ha), ?_⟩
  · change (t.regValue .rsi).toNat + count < 2^32
    rw [start]
    omega
  · intro a ha
    have mem := contains a.toNat ha
    change (initial.regValue .rcx).toNat ≤ a.toNat ∧
      a.toNat < (initial.regValue .rcx).toNat + ikm.size at mem
    let i : Fin ikm.size := ⟨a.toNat - (initial.regValue .rcx).toNat, by omega⟩
    have byte := preserved.2 i
    have addr : (registerRegion initial .rcx ikm.size).start + i.val = a.toNat := by
      change (initial.regValue .rcx).toNat + (a.toNat - (initial.regValue .rcx).toNat) = _
      omega
    rw [addr, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
    exact ⟨_, byte⟩
  · intro i hi
    have byte := preserved.2 ⟨offset + i, by omega⟩
    simpa only [registerRegion, source, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_assoc] using byte

theorem copy [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray} (pre : ExtractPre initial boundary salt ikm)
    (frame : Frame initial s boundary) (path : CopyPath) (rip : s.RIP = path.copyPc)
    {offset count : Nat} (dest : s.regValue .rdi = base initial + 120)
    (source : s.regValue .rsi = initial.regValue .rcx + BitVec.ofNat 64 offset)
    (len : s.regValue .rdx = BitVec.ofNat 64 count)
    (sourceBound : offset + count ≤ ikm.size) (countSmall : count < 64) :
    ∃ t, Frame initial t boundary ∧ t.RIP = path.copyPc + (6 : BitVec 64) ∧
      t.regValue .r14 = s.regValue .r14 ∧
      (⟨(base initial + 120).toNat, count⟩ : MemoryRegion).HasBytes
        t.external (ikm.extract offset (offset + count)) ∧
      MemoryWriteFrame s t #v[⟨(base initial + 120).toNat, count⟩,
        ⟨(stackPtr initial - 464).toNat, 8⟩] := by
  have avoids := stackAvoid pre
  have push : pushAddr s = stackPtr initial - 464 := by
    rw [pushAddr, frame.rsp, base, BitVec.sub_sub]
    rfl
  have destAddr : base initial + 120 = stackPtr initial - 336 := by
    unfold base
    bv_omega
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [push]
    exact stack_writable8 pre.call.stack pre.call.stackAvoid frame.allocated (by decide) (by decide)
  have separate : RangeApart (pushAddr s) 8 path.copyPc 6 := by
    rw [push, path.copyPc_eq]
    exact stack_codeApart pre.call.stack (avoids _ (by simp))
      (offset := 464) (codeOffset := path.offset + 11) (by decide) (by decide)
      (by cases path <;> decide)
  have pointer := Common.Memory.memcpy_pointer frame.loaded
  have target : callMemPtr path.copyPc (.rip path.displacement) s = 0x10dd60 := by
    cases path <;> exact pointer.2
  have pointerReadable :
      MemReadable s ((AddrMode.rip path.displacement).addr s (path.copyPc + 6)) 8 := by
    cases path <;> exact pointer.1
  have code : CodeIn (codeRange path.copyPc (encodeCallM64 (.rip path.displacement))) s := by
    rw [path.copyPc_eq]
    exact programText_slice (programLoaded_codeIn frame.loaded) (path.offset + 11) _
      (by cases path <;> decide) (by cases path <;> decide +kernel)
  have writes : WritesWithin
      (callEffect (callMemPtr path.copyPc (.rip path.displacement)) (path.copyPc + 6) s).components
      #v[Stack.region initial 2264] := by
    intro c hc a ha
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · rw [push] at ha
      exact ⟨_, by simp, stackRegion_contains_sub pre.call.stack.2.2.1 (by decide) (by decide) ha⟩
    · exact ha.elim
  obtain ⟨u, runningU, call, ret⟩ := frame.toRunning.call
    (call_m64_effect_step path.copyPc (.rip path.displacement) (by cases path <;> decide) rfl rfl) code
    ⟨⟨⟨rip, writable, separate⟩, by rw [target]; decide⟩, pointerReadable⟩
    (by rw [target]
        exact boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0xdd60 (by decide)))
    writes avoids
  have rspU : stackPtr u = stackPtr initial - 464 := call.writes.1.trans push
  have outputU : u.regValue .rdi = stackPtr initial - 336 :=
    (call.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans
      (dest.trans destAddr)
  have sourceU : u.regValue .rsi = initial.regValue .rcx + BitVec.ofNat 64 offset :=
    (call.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans source
  have lenU : u.regValue .rdx = BitVec.ofNat 64 count :=
    (call.agrees.read (n := 64) (r := 2) (by simp [callEffect, pushEffect_components])).trans len
  obtain ⟨bounded, allocated, apart, input⟩ := copyInput pre runningU.frame sourceU sourceBound
  let layout := copyLayout count countSmall
  have copyPre : CalleePre u boundary 0x10dd60 count count 0 :=
    callee_pre_of_stack_output pre.call.stride pre.call.stack pre.call.stackAvoid
      pre.call.outerBoundary runningU.machine runningU.directionFlag runningU.loaded
      runningU.allocated layout (call.rip.trans target) rspU outputU
      (by rw [ret]; cases path
          · exact inProgram_of_textOffset 0xfc7a (by decide)
          · exact inProgram_of_textOffset 0xfccb (by decide))
      bounded allocated apart
  obtain ⟨t, result, copied, _⟩ := Common.Memory.memcpy_correct copyPre lenU (by omega)
  have runningT := runningU.of_callee result (by
    intro region member addr ha
    exact ⟨_, by simp, stack_layout_within pre.call.stack layout rspU outputU region member addr ha⟩)
  obtain ⟨memory, abi⟩ := call_result copyPre call result frame.directionFlag
  have frameT := frame.of_frame pre.call.stack runningT memory
    (result.rsp.trans (congrArg ReturnBoundary.rsp ret)) abi.2.2.1 abi.2.2.2 (by
      intro region member
      constructor
      · exact stack_layout_disjoint pre.call.stack layout rspU outputU
          (savedOffset := 48) (savedBytes := 56) (.inl (by change 48 + count ≤ 336; omega))
          (by change 48 + 8 ≤ 464; decide) region member
      · rw [show base initial + 80 = stackPtr initial - 376 by unfold base; bv_omega]
        exact stack_layout_disjoint pre.call.stack layout rspU outputU
          (savedOffset := 376) (savedBytes := 8) (.inr (by change 336 + 8 ≤ 376; decide))
          (by change 376 + 8 ≤ 464; decide) region member)
  have outputRegion : registerRegion u .rdi count =
      (⟨(base initial + 120).toNat, count⟩ : MemoryRegion) := by
    simp only [registerRegion, outputU, destAddr]
  have pushRegion : Stack.region u 0 = (⟨(stackPtr initial - 464).toNat, 8⟩ : MemoryRegion) := by
    simp only [Stack.region, Nat.sub_zero, Nat.add_sub_cancel_left]
    change (⟨(stackPtr u).toNat, 8⟩ : MemoryRegion) = _
    rw [rspU]
  have r14 := abi.1 .r14 (by simp)
  refine ⟨t, frameT, result.rip.trans (congrArg ReturnBoundary.rip ret), r14, ?_,
    by simpa only [outputRegion, pushRegion] using memory⟩
  have size : (ikm.extract offset (offset + count)).size = count := by
    rw [ByteArray.size_extract]
    omega
  refine ⟨size, ?_⟩
  intro i
  have hi : i.val < count := by have := i.isLt; omega
  have byte := (copied i.val hi).trans (input i.val hi)
  rw [outputU, ← destAddr] at byte
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    ByteArray.getElem_extract] using byte

end Hkdf.Proofs.NewExpand.Extract.Update
