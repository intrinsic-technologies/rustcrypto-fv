import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Standard.Memory

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame

abbrev copyLayout : Hkdf.Proofs.Common.CallFrame.StackCallLayout 1792 144 144 0 :=
  ⟨528, 400, 192, by decide, by decide, by decide, by decide, by decide,
    by decide, .inl (by decide)⟩

abbrev finalizerLayout : Hkdf.Proofs.Common.CallFrame.StackCallLayout 1792 144 176 1264 :=
  ⟨528, 192, 400, by decide, by decide, by decide, by decide, by decide,
    by decide, .inr (by decide)⟩

theorem copy_pre [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs)
    (running : Running initial (returnBoundary initial)
      #v[Stack.region initial hkdfSha256Extract.minStackBytes] s)
    (rip : s.RIP = 0x10dd60)
    (rsp : stackPtr s = stackPtr initial - 528)
    (input : s.regValue .rsi = stackPtr initial - 400)
    (output : s.regValue .rdi = stackPtr initial - 192)
    (ret : InProgram (returnBoundary s).rip) :
    CalleePre s (returnBoundary initial) 0x10dd60 144 144 0 :=
  callee_pre_of_stack ctx.environment.stringStride ctx.call.stack
    ((ctx.call.stackSeparation.2 _ (by simp)).2) (returnBoundary_valid ctx).2.2
    running.machine running.directionFlag running.loaded running.allocated
    copyLayout rip rsp input output ret

theorem finalizer_pre [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs)
    (running : Running initial (returnBoundary initial)
      #v[Stack.region initial hkdfSha256Extract.minStackBytes] s)
    (rip : s.RIP = 0x10dd90)
    (rsp : stackPtr s = stackPtr initial - 528)
    (input : s.regValue .rsi = stackPtr initial - 192)
    (output : s.regValue .rdi = stackPtr initial - 400)
    (ret : InProgram (returnBoundary s).rip) :
    CalleePre s (returnBoundary initial) 0x10dd90 144 176 1264 :=
  callee_pre_of_stack ctx.environment.stringStride ctx.call.stack
    ((ctx.call.stackSeparation.2 _ (by simp)).2) (returnBoundary_valid ctx).2.2
    running.machine running.directionFlag running.loaded running.allocated
    finalizerLayout rip rsp input output ret

theorem copy_regions [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs)
    (rsp : stackPtr s = stackPtr initial - 528)
    (output : s.regValue .rdi = stackPtr initial - 192) :
    ∀ region ∈ #v[registerRegion s .rdi 144, Stack.region s 0],
      ∀ a, region.Contains a →
        (Stack.region initial hkdfSha256Extract.minStackBytes).Contains a :=
  stack_layout_within ctx.call.stack copyLayout rsp output

theorem finalizer_regions [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs)
    (rsp : stackPtr s = stackPtr initial - 528)
    (output : s.regValue .rdi = stackPtr initial - 400) :
    ∀ region ∈ #v[registerRegion s .rdi 176, Stack.region s 1264],
      ∀ a, region.Contains a →
        (Stack.region initial hkdfSha256Extract.minStackBytes).Contains a :=
  stack_layout_within ctx.call.stack finalizerLayout rsp output

theorem copy_saved [Bindings] {initial s t : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi 144, Stack.region s 0])
    (rsp : stackPtr s = stackPtr initial - 528)
    (output : s.regValue .rdi = stackPtr initial - 192) :
    (Component.mem (stackPtr initial - 48) 56).Agrees s t := by
  apply frame_agrees_of_disjoint frame
  · rw [show (stackPtr initial - 48).toNat = (stackPtr initial).toNat - 48 from
      stack_sub_toNat ctx.call.stack (by decide)]
    have bounds := stack_bounds ctx
    omega
  · exact stack_layout_disjoint ctx.call.stack copyLayout rsp output
      (.inl (by decide)) (by decide)

theorem finalizer_saved [Bindings] {initial s t : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi 176, Stack.region s 1264])
    (rsp : stackPtr s = stackPtr initial - 528)
    (output : s.regValue .rdi = stackPtr initial - 400) :
    (Component.mem (stackPtr initial - 48) 56).Agrees s t := by
  apply frame_agrees_of_disjoint frame
  · rw [show (stackPtr initial - 48).toNat = (stackPtr initial).toNat - 48 from
      stack_sub_toNat ctx.call.stack (by decide)]
    have bounds := stack_bounds ctx
    omega
  · exact stack_layout_disjoint ctx.call.stack finalizerLayout rsp output
      (.inl (by decide)) (by decide)

theorem copy_persistent [Bindings] {initial s t : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi 144, Stack.region s 0])
    (rsp : stackPtr s = stackPtr initial - 528)
    (output : s.regValue .rdi = stackPtr initial - 192) :
    ∀ offset ∈ ([8, 96, 104, 112] : List Nat),
      (Component.mem (frameBase initial + BitVec.ofNat 64 offset) 8).Agrees s t := by
  intro offset member
  have limits : 8 ≤ offset ∧ offset ≤ 112 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  have address : frameBase initial + BitVec.ofNat 64 offset =
      stackPtr initial - BitVec.ofNat 64 (520 - offset) := by
    change initial.regValue .rsp - 520 + BitVec.ofNat 64 offset =
      initial.regValue .rsp - BitVec.ofNat 64 (520 - offset)
    rw [← BitVec.ofNat_sub_ofNat_of_le 520 offset (by omega) (by omega)]
    simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg,
      BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
  rw [address]
  apply frame_agrees_of_disjoint frame
  · rw [stack_sub_toNat ctx.call.stack (by change 520 - offset ≤ 1792; omega)]
    have bounds := stack_bounds ctx
    omega
  · exact stack_layout_disjoint ctx.call.stack copyLayout rsp output
      (.inr (by change 192 + 8 ≤ 520 - offset; omega))
      (by change 520 - offset + 8 ≤ 528; omega)

theorem finalizer_persistent [Bindings] {initial s t : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi 176, Stack.region s 1264])
    (rsp : stackPtr s = stackPtr initial - 528)
    (output : s.regValue .rdi = stackPtr initial - 400) :
    ∀ offset ∈ ([8, 96, 104, 112] : List Nat),
      (Component.mem (frameBase initial + BitVec.ofNat 64 offset) 8).Agrees s t := by
  intro offset member
  have limits : 8 ≤ offset ∧ offset ≤ 112 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  have address : frameBase initial + BitVec.ofNat 64 offset =
      stackPtr initial - BitVec.ofNat 64 (520 - offset) := by
    change initial.regValue .rsp - 520 + BitVec.ofNat 64 offset =
      initial.regValue .rsp - BitVec.ofNat 64 (520 - offset)
    rw [← BitVec.ofNat_sub_ofNat_of_le 520 offset (by omega) (by omega)]
    simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg,
      BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
  rw [address]
  apply frame_agrees_of_disjoint frame
  · rw [stack_sub_toNat ctx.call.stack (by change 520 - offset ≤ 1792; omega)]
    have bounds := stack_bounds ctx
    omega
  · exact stack_layout_disjoint ctx.call.stack finalizerLayout rsp output
      (.inr (by change 400 + 8 ≤ 520 - offset; omega))
      (by change 520 - offset + 8 ≤ 528; omega)

theorem copy_state [Bindings] {initial s t : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs) (state : State initial s)
    (result : CalleeResult s t (returnBoundary initial) 144 0)
    (rsp : stackPtr s = stackPtr initial - 528)
    (output : s.regValue .rdi = stackPtr initial - 192) : State initial t := by
  refine ⟨state.toRunning.of_callee result ?_,
    state.saved.of_agrees (copy_saved ctx result.frame rsp output)⟩
  intro region member a contains
  exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp,
    copy_regions ctx rsp output region member a contains⟩

theorem finalizer_state [Bindings] {initial s t : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs) (state : State initial s)
    (result : CalleeResult s t (returnBoundary initial) 176 1264)
    (rsp : stackPtr s = stackPtr initial - 528)
    (output : s.regValue .rdi = stackPtr initial - 400) : State initial t := by
  refine ⟨state.toRunning.of_callee result ?_,
    state.saved.of_agrees (finalizer_saved ctx result.frame rsp output)⟩
  intro region member a contains
  exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp,
    finalizer_regions ctx rsp output region member a contains⟩

end Hkdf.Proofs.Standard.Finalize
