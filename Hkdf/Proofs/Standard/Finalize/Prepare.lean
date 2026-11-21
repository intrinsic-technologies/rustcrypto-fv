import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Standard.Finalize.Setup
import Hkdf.Proofs.Common.Memory.Copy
import Hkdf.Proofs.Common.Memory.Pointers

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common
open Hkdf.Proofs.Common.Machine

theorem prepare_copy [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Context initial salt inputs) (completed : Completed initial s salt inputs) :
    ∃ t, Buffered initial t salt (concatenation inputs) ∧
      t.RIP = 0x101739 ∧
      t.regValue .rbx = frameBase initial + 328 ∧
      t.regValue .rsi = hmacBase initial ∧
      t.regValue .rdx = 144 ∧
      t.regValue .rdi = frameBase initial + 328 := by
  have outside := (returnBoundary_valid ctx).2.2
  obtain ⟨fuel, t, run, ready, _, effect⟩ := copySetup_run (returnBoundary initial) outside s
    (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep completed.machine)
    (copySetup_code completed.loaded) completed.rip
  have frame : AgreesExcept [.reg 3, .reg 6, .reg 2, .reg 7, .rip] s t := effect.agrees
  have memory := frame.external (by simp [Component.Covers])
  have preserved := Preserved.of_noMem ctx completed.toPreserved run ready frame
    (by simp [Component.Covers]) (by simp) (by simp)
  have hmac : HmacAt t (hmacBase initial) (saltKey salt) (concatenation inputs) := by
    apply completed.hmac.of_copy
    intro i hi
    rw [memory]
  have stores := effect.writes
  simp only [copySetupEffect, Write.AllHold] at stores
  change t.regValue .rbx = stackPtr s + 328 ∧ t.regValue .rsi = stackPtr s + 120 ∧
    t.regValue .rdx = 144 ∧ t.regValue .rdi = stackPtr s + 328 at stores
  have sp : stackPtr s = frameBase initial := completed.rsp
  refine ⟨t, ⟨preserved, hmac⟩, effect.rip, ?_, ?_, stores.2.2.1, ?_⟩
  · simpa only [sp] using stores.1
  · simpa only [sp, hmacBase] using stores.2.1
  · simpa only [sp] using stores.2.2.2

theorem call_stack_writes {initial s : RamState} {target : RamState → BitVec 64}
    {ret : BitVec 64} (rsp : stackPtr s = frameBase initial)
    (stack : Stack.Valid initial 1792) :
    WritesWithin (callEffect target ret s).components #v[Stack.region initial 1792] := by
  intro c hc a ha
  simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ha.elim
  · have pushed : pushAddr s = stackPtr initial - 528 := by
      rw [pushAddr, rsp, frameBase, BitVec.sub_sub]
      rfl
    rw [pushed] at ha
    exact ⟨Stack.region initial 1792, by simp,
      Hkdf.Proofs.Common.Machine.stackRegion_contains_sub stack.2.2.1
        (by decide) (by decide) ha⟩
  · exact ha.elim

theorem call_saved {initial s t : RamState} {target : RamState → BitVec 64}
    {ret : BitVec 64} (rsp : stackPtr s = frameBase initial)
    (effect : (callEffect target ret s).Holds s t) {offset size : Nat}
    (apart : OffsetsApart (-BitVec.ofNat 64 offset) size (-528) 8)
    (small : size + 8 < 2^64) :
    (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) size).Agrees s t := by
  intro i hi
  apply effect.agrees.memory
  intro c hc cover
  simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact cover.elim
  · obtain ⟨j, hj, eq⟩ := cover
    apply OffsetsApart.ne apart (stackPtr initial) hi hj small
    have pushed : pushAddr s = stackPtr initial - 528 := by
      rw [pushAddr, rsp, frameBase, BitVec.sub_sub]
      rfl
    simpa only [pushed, BitVec.sub_eq_add_neg] using eq
  · exact cover.elim

theorem call_copy [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Context initial salt inputs) (buffered : Buffered initial s salt (concatenation inputs))
    (rip : s.RIP = 0x101739) :
    ∃ t, State initial t ∧
      (callEffect (callMemPtr 0x101739 (.rip 0xffbd9)) 0x10173f s).Holds s t ∧
      t.RIP = 0x10dd60 ∧ stackPtr t = stackPtr initial - 528 ∧
      returnBoundary t = ⟨0x10173f, frameBase initial⟩ := by
  have outside := (returnBoundary_valid ctx).2.2
  have avoid : (Stack.region initial 1792).Avoids
      (fun a ↦ InProgram a ∨ Hkdf.Proofs.Program.InPageTables a) := by
    change (Stack.region initial hkdfSha256Extract.minStackBytes).Avoids _
    exact (ctx.call.stackSeparation.2 _ (by simp)).2
  have sp : stackPtr s = frameBase initial := buffered.rsp
  have pushed : pushAddr s = stackPtr initial - 528 := by
    rw [pushAddr, sp, frameBase, BitVec.sub_sub]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [pushed]
    exact stack_writable8 ctx.call.stack avoid buffered.allocated (by decide) (by decide)
  have apart : RangeApart (pushAddr s) 8 0x101739 6 := by
    rw [pushed]
    exact Hkdf.Proofs.Standard.stack_codeApart ctx (offset := 528) (len := 8)
      (codeOffset := 0x1739) (codeLen := 6) (by decide) (by decide) (by decide)
  have pointer := Common.Memory.memcpy_pointer buffered.loaded
  have target : callMemPtr 0x101739 (.rip 0xffbd9) s = 0x10dd60 := by
    exact pointer.2
  have instruction := programText_slice (programLoaded_codeIn buffered.loaded) 0x1739
    (encodeCallM64 (.rip 0xffbd9)) (by decide +kernel) (by decide +kernel)
  obtain ⟨t, running, effect, ret⟩ := buffered.toRunning.call
    (call_m64_effect_step 0x101739 (.rip 0xffbd9) (by decide) rfl rfl)
    instruction ⟨⟨⟨rip, writable, apart⟩, by rw [target]; decide⟩, pointer.1⟩
    (by rw [target]; exact boundary_ne_program outside (inProgram_of_textOffset 0xdd60 (by decide)))
    (call_stack_writes buffered.rsp ctx.call.stack)
    (by intro region member a contains inside
        have equal : region = Stack.region initial hkdfSha256Extract.minStackBytes := by simpa using member
        subst region
        exact avoid a contains (.inl inside))
  have saved := buffered.saved.of_agrees
    (call_saved buffered.rsp effect (by unfold OffsetsApart; decide +kernel) (by decide))
  refine ⟨t, ⟨running, saved⟩, effect, effect.rip.trans target, ?_, ?_⟩
  · exact effect.writes.1.trans pushed
  · change returnBoundary t = ⟨0x10173f, stackPtr s⟩ at ret
    simpa only [sp] using ret


theorem call_finalizer [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Context initial salt inputs) (preserved : Preserved initial s)
    (rip : s.RIP = 0x101747) :
    ∃ t, State initial t ∧ (callEffect (fun _ ↦ 0x10dd90) 0x10174c s).Holds s t ∧
      t.RIP = 0x10dd90 ∧ stackPtr t = stackPtr initial - 528 ∧
      returnBoundary t = ⟨0x10174c, frameBase initial⟩ := by
  have outside := (returnBoundary_valid ctx).2.2
  have avoid : (Stack.region initial hkdfSha256Extract.minStackBytes).Avoids
      (fun a ↦ InProgram a ∨ Hkdf.Proofs.Program.InPageTables a) := (ctx.call.stackSeparation.2 _ (by simp)).2
  have sp : stackPtr s = frameBase initial := preserved.rsp
  have pushed : pushAddr s = stackPtr initial - 528 := by
    rw [pushAddr, sp, frameBase, BitVec.sub_sub]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [pushed]
    exact stack_writable8 ctx.call.stack avoid preserved.allocated (by decide) (by decide)
  have apart : RangeApart (pushAddr s) 8 0x101747 5 := by
    rw [pushed]
    exact Hkdf.Proofs.Standard.stack_codeApart ctx (offset := 528) (len := 8)
      (codeOffset := 0x1747) (codeLen := 5) (by decide) (by decide) (by decide)
  have step := call_rel32_effect_step 0x101747 0xc644 (by decide +kernel)
  change StepEffect (PushPre 0x101747 5) (codeRange 0x101747 (encodeCallRel32 0xc644))
    (callEffect (fun _ ↦ 0x10dd90) 0x10174c) at step
  have instruction := programText_slice (programLoaded_codeIn preserved.loaded) 0x1747
    (encodeCallRel32 0xc644) (by decide +kernel) (by decide +kernel)
  obtain ⟨t, running, effect, ret⟩ := preserved.toRunning.call step instruction
    ⟨rip, writable, apart⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0xdd90 (by decide)))
    (call_stack_writes preserved.rsp ctx.call.stack)
    (by intro region member a contains inside
        have equal : region = Stack.region initial hkdfSha256Extract.minStackBytes := by
          simpa using member
        subst region
        exact avoid a contains (.inl inside))
  have saved := preserved.saved.of_agrees
    (call_saved preserved.rsp effect (by unfold OffsetsApart; decide +kernel) (by decide))
  refine ⟨t, ⟨running, saved⟩, effect, effect.rip, effect.writes.1.trans pushed, ?_⟩
  simpa only [sp] using ret

end Hkdf.Proofs.Standard.Finalize
