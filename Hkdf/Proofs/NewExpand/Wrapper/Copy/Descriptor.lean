import Hkdf.Proofs.NewExpand.Wrapper.Copy.State
import Hkdf.Proofs.NewExpand.Wrapper.CalleeFrame
import Hkdf.Proofs.NewExpand.Wrapper.Prologue.Call
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Wrapper.Copy

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Field Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private def descriptorBytes : List UInt8 :=
  [0x4c, 0x89, 0x34, 0x24, 0x48, 0x89, 0x5c, 0x24, 0x08, 0x48, 0x89, 0xe6,
    0xba, 1, 0, 0, 0, 0x4c, 0x89, 0xef, 0x4c, 0x89, 0xf9, 0x4d, 0x89, 0xe0]

private def descriptorEffect (s : RamState) : Effect :=
  { rip := 0x10203f
    writes := [⟨(.mem (rspOf s) : Operand 64), s.regValue .r14⟩,
      ⟨(.mem (rspOf s + 8) : Operand 64), s.regValue .rbx⟩,
      ⟨(.reg 6 : Operand 64), rspOf s⟩, ⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .r13⟩, ⟨(.reg 1 : Operand 64), s.regValue .r15⟩,
      ⟨(.reg 8 : Operand 64), s.regValue .r12⟩] }

private structure DescriptorPre (s : RamState) : Prop where
  rip : s.RIP = 0x102025
  pointer : MemWritable s (rspOf s) 8
  length : MemWritable s (rspOf s + 8) 8
  pointerApart : RangeApart (rspOf s) 8 0x102025 26
  lengthApart : RangeApart (rspOf s + 8) 8 0x102025 26

private theorem descriptor_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary DescriptorPre (codeRange 0x102025 descriptorBytes)
      (Effect.post descriptorEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x102025 0x4c (by simp [RexWPrefix]) 6
    (.sib 4 none 0 .none) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x102025 descriptorBytes 0 4)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact h.pointer
    · x86_norm [BitVec.add_zero]
      intro i hi j hj
      exact h.pointerApart i hi j (show j < 26 by omega)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [BitVec.add_zero]
    exact h.pointerApart
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0x2029 (by decide))
  advance_then (mov_m64_r64_effect_step 0x102029 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x102025 descriptorBytes 4 5)
  case mid =>
    intro s t hp effect obs
    refine ⟨StorePre.of_holds effect (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_,
      boundary_ne_program outside (inProgram_of_textOffset 0x202e (by decide))⟩
    · x86_norm
      exact hp.length
    · x86_norm
      intro i hi j hj
      intro he
      apply hp.lengthApart i hi (4 + j) (by omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc,
        show (0x102025 : BitVec 64) + BitVec.ofNat 64 4 = 0x102029 by decide]
      exact he
    · apply Effect.Local.avoids (by x86_local) (obs true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.lengthApart
  advance_then (mov_r64_r64_effect_step 0x10202e 0x48 0xe6 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x102025 descriptorBytes 9 3)
  case mid =>
    intro s t hp effect obs
    exact ⟨effect.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x2031 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x102031 0xba (by decide) 1)
  try (case sub => exact codeRange_slice_subset 0x102025 descriptorBytes 12 5)
  case mid =>
    intro s t hp effect obs
    exact ⟨effect.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x2036 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x102036 0x4c 0xef (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x102025 descriptorBytes 17 3)
  case mid =>
    intro s t hp effect obs
    exact ⟨effect.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x2039 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x102039 0x4c 0xf9 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x102025 descriptorBytes 20 3)
  case mid =>
    intro s t hp effect obs
    exact ⟨effect.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x203c (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10203c 0x4d 0xe0 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x102025 descriptorBytes 23 3)
  case mid =>
    intro s t hp effect obs
    exact ⟨effect.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x203f (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ effect
  apply effect.weaken
  · x86_norm [descriptorEffect]
  · x86_norm [descriptorEffect, BitVec.add_zero]
    exact ⟨Or.inl rfl, Or.inr rfl, rfl, rfl, rfl, rfl⟩
  · intro i
    cases i <;> x86_norm [descriptorEffect]
  · x86_norm [descriptorEffect, BitVec.add_zero]

private theorem descriptor_store_cover {s : RamState}
    {c : Component} {a : BitVec 64} (hc : c ∈ (descriptorEffect s).components)
    (ha : c.Covers a) :
    (Component.mem (rspOf s) 8).Covers a ∨ (Component.mem (rspOf s + 8) 8).Covers a := by
  simp only [descriptorEffect, Effect.components, List.map_cons, List.map_nil, Write.component_mem,
    Write.component_reg, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl ha
  · exact .inr ha
  all_goals exact ha.elim

private theorem stack_slot_bounds {initial : RamState} {a : BitVec 64}
    (stack : Stack.Valid initial hkdfSha256NewExpandMinStackBytes)
    {offset : Nat} (within : offset ≤ hkdfSha256NewExpandMinStackBytes) (space : 8 ≤ offset)
    (covered : (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) 8).Covers a) :
    (stackPtr initial).toNat - offset ≤ a.toNat ∧
      a.toNat < (stackPtr initial).toNat - offset + 8 := by
  obtain ⟨i, hi, rfl⟩ := covered
  have bounds := stack_bounds stack
  rw [BitVec.toNat_add, stack_sub_toNat stack within, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2^64 by omega), Nat.mod_eq_of_lt (by omega)]
  omega

private theorem stack_word [Bindings] {initial t : RamState} {base : BitVec 64} {v : BitVec 64}
    (stack : Stack.Valid initial hkdfSha256NewExpandMinStackBytes)
    (run : Wrapper.Running initial t) {offset : Nat}
    (within : offset ≤ hkdfSha256NewExpandMinStackBytes)
    (addr : base = stackPtr initial - BitVec.ofNat 64 offset)
    (value : memLoad t.external base 64 = v) : loadBytes t.external base 8 = .ok v := by
  have readable : MemReadable t base 8 := by
    rw [addr]
    exact stack_readable stack run.allocated within (by omega)
  have bytes := Bytes.of_memLoad (n := 64) readable.mem
  simpa only [value] using bytes.loadBytes64

theorem prepareExpand [bindings : Bindings]
    {initial : RamState} {salt : Option ByteArray} {ikm info : ByteArray} {length : Nat}
    (hCall : ValidDeriveKeyCall Extracted.hkdfSha256NewExpandAddress
      hkdfSha256NewExpandMinStackBytes initial salt ikm info length)
    {s : RamState} (start : Copied initial s (RFC5869.extract .sha256 salt ikm)) :
    ∃ t, AtExpand initial t (RFC5869.extract .sha256 salt ikm) := by
  have avoid := (hCall.stackSeparation.2 _ (Vector.mem_singleton_self _)).2
  have avoids : (Stack.region initial hkdfSha256NewExpandMinStackBytes).Avoids InProgram :=
    fun a ha hp ↦ avoid a ha (.inl hp)
  have outside := Wrapper.outerBoundary hCall.returnAddress
  have rsp : rspOf s = stackPtr initial - 360 := start.rsp
  have nextWord : rspOf s + 8 = stackPtr initial - 352 := by rw [rsp]; bv_omega
  have pre : DescriptorPre s := by
    refine ⟨start.rip, ?_, ?_, ?_, ?_⟩
    · rw [rsp]
      exact stack_writable8 hCall.stack avoid start.run.allocated
        (show 360 ≤ hkdfSha256NewExpandMinStackBytes by decide) (by decide)
    · rw [nextWord]
      exact stack_writable8 hCall.stack avoid start.run.allocated
        (show 352 ≤ hkdfSha256NewExpandMinStackBytes by decide) (by decide)
    · rw [rsp]
      exact stack_codeApart hCall.stack avoids
        (show 360 ≤ hkdfSha256NewExpandMinStackBytes by decide) (by decide)
        (show 0x2025 + descriptorBytes.length ≤ 115149 by decide)
    · rw [nextWord]
      exact stack_codeApart hCall.stack avoids
        (show 352 ≤ hkdfSha256NewExpandMinStackBytes by decide) (by decide)
        (show 0x2025 + descriptorBytes.length ≤ 115149 by decide)
  obtain ⟨fuel, u, execution, ready, _, effect⟩ :=
    descriptor_run (returnBoundary initial) outside s
      (supportedMachine_readyToStep start.run.machine)
      (programText_slice (programLoaded_codeIn start.run.loaded) 0x2025 descriptorBytes
        (by decide) (by decide +kernel)) pre
  have run : Wrapper.Running initial u := by
    apply start.run.of_agrees execution ready effect.agrees
    · intro c hc a ha
      refine ⟨_, Vector.mem_singleton_self _, ?_⟩
      rcases descriptor_store_cover hc ha with h | h
      · rw [rsp] at h
        exact stackRegion_contains_sub hCall.stack.2.2.1
          (show 360 ≤ hkdfSha256NewExpandMinStackBytes by decide) (by decide : 8 ≤ 360) h
      · rw [nextWord] at h
        exact stackRegion_contains_sub hCall.stack.2.2.1
          (show 352 ≤ hkdfSha256NewExpandMinStackBytes by decide) (by decide : 8 ≤ 352) h
    · intro r hr
      obtain rfl := Vector.mem_singleton.mp hr
      exact avoids
    · simp [descriptorEffect, Effect.components]
  have rip : u.RIP = 0x10203f := effect.rip
  have sp : stackPtr u = stackPtr initial - 360 :=
    (effect.agrees.read (n := 64) (r := 4) (by simp [descriptorEffect, Effect.components])).trans
      rsp
  have step := call_rel32_effect_step 0x10203f 0xd20c (by decide)
  change StepEffect (PushPre 0x10203f 5) (codeRange 0x10203f (encodeCallRel32 0xd20c))
    (callEffect (fun _ ↦ (0x10f250 : BitVec 64)) 0x102044) at step
  obtain ⟨t, running, called, boundary⟩ := run.call_stack hCall.stack avoid (depth := 360) sp
    (by decide) (by decide) 0x203f 5 (by decide) rip step
    (programText_slice (programLoaded_codeIn run.loaded) 0x203f (encodeCallRel32 0xd20c)
      (by decide) (by decide +kernel)) id
    (boundary_ne_program outside (inProgram_of_textOffset 0xf250 (by decide)))
  have push : pushAddr u = stackPtr initial - 368 := by
    rw [pushAddr, sp, BitVec.sub_sub]
    rfl
  have low : 2632 ≤ (stackPtr initial).toNat := hCall.stack.2.2.1
  have high := (stack_bounds hCall.stack).2
  have frameCall : MemoryWriteFrame u t
      #v[⟨(stackPtr initial).toNat - 368, 8⟩] := by
    apply called.agrees.memoryWriteFrame
    intro c hc a ha
    simp only [callEffect, pushEffect_components, push, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · exact ⟨_, Vector.mem_singleton_self _, stack_slot_bounds hCall.stack
        (show 368 ≤ hkdfSha256NewExpandMinStackBytes by decide) (by decide : 8 ≤ 368) ha⟩
    · exact ha.elim
  let written : MemoryRegion := ⟨(stackPtr initial).toNat - 368, 24⟩
  have withinWritten {a offset : Nat}
      (hmin : 352 ≤ offset) (hmax : offset ≤ 368)
      (bounds : (stackPtr initial).toNat - offset ≤ a ∧
        a < (stackPtr initial).toNat - offset + 8) : written.Contains a := by
    change (stackPtr initial).toNat - 368 ≤ a ∧ a < (stackPtr initial).toNat - 368 + 24
    omega
  have frame : MemoryWriteFrame s t #v[written] := by
    apply memoryWriteFrame_trans (effect.agrees.memoryWriteFrame ?_) (frame_mono frameCall ?_)
    · intro c hc a ha
      refine ⟨_, Vector.mem_singleton_self _, ?_⟩
      rcases descriptor_store_cover hc ha with h | h
      · rw [rsp] at h
        exact withinWritten (by decide : 352 ≤ 360) (by decide)
          (stack_slot_bounds hCall.stack
            (show 360 ≤ hkdfSha256NewExpandMinStackBytes by decide) (by decide) h)
      · rw [nextWord] at h
        exact withinWritten (by decide : 352 ≤ 352) (by decide)
          (stack_slot_bounds hCall.stack
            (show 352 ≤ hkdfSha256NewExpandMinStackBytes by decide) (by decide) h)
    · intro r member a within
      obtain rfl := Vector.mem_singleton.mp member
      refine ⟨_, Vector.mem_singleton_self _, ?_⟩
      exact withinWritten (by decide : 352 ≤ 368) (by decide) within
  have rbp : t.regValue .rbp = s.regValue .rbp :=
    (called.agrees.read (n := 64) (r := 5) (by simp [callEffect, pushEffect_components])).trans
      (effect.agrees.read (n := 64) (r := 5) (by simp [descriptorEffect, Effect.components]))
  have saved : SavedFrame initial t := by
    apply Wrapper.savedFrame_of_frame start.saved rbp hCall.stack frame
    intro a hlo hhi r hr ha
    obtain rfl := Vector.mem_singleton.mp hr
    change (stackPtr initial).toNat - 368 ≤ a ∧ a < (stackPtr initial).toNat - 368 + 24 at ha
    omega
  obtain ⟨ptrRead, lenRead, rsi, rdx, rdi, rcx, r8⟩ := effect.writes
  have view : AgreesExcept [.reg 4, .mem (pushAddr u) 8, .rip] u t := by
    simpa only [callEffect, pushEffect_components] using called.agrees
  have desc : t.regValue .rsi = stackPtr initial - 360 :=
    (view.read (n := 64) (r := 6) (by simp)).trans (rsi.trans rsp)
  have key : t.regValue .rdi = stackPtr initial - 184 :=
    (view.read (n := 64) (r := 7) (by simp)).trans (rdi.trans start.key)
  have keyAddr : (stackPtr initial - (184 : BitVec 64)).toNat = (stackPtr initial).toNat - 184 :=
    stack_sub_toNat hCall.stack (show 184 ≤ hkdfSha256NewExpandMinStackBytes by decide)
  have slotAgrees {offset : Nat} (ho : offset = 360 ∨ offset = 352) :
      (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) 8).Agrees u t := by
    have off : offset ≤ hkdfSha256NewExpandMinStackBytes := by
      rcases ho with rfl | rfl <;> decide
    apply frame_agrees_of_disjoint frameCall
    · rw [stack_sub_toNat hCall.stack off]
      omega
    · intro r hr a ha hb
      obtain rfl := Vector.mem_singleton.mp hr
      change (stackPtr initial - BitVec.ofNat 64 offset).toNat ≤ a ∧
        a < (stackPtr initial - BitVec.ofNat 64 offset).toNat + 8 at ha
      rw [stack_sub_toNat hCall.stack off] at ha
      change (stackPtr initial).toNat - 368 ≤ a ∧ a < (stackPtr initial).toNat - 368 + 8 at hb
      rcases ho with rfl | rfl <;> omega
  refine ⟨t, running, saved, called.rip, called.writes.1.trans push, key, desc, ?_,
    ?_, ?_, (view.read (n := 64) (r := 2) (by simp)).trans rdx,
    (view.read (n := 64) (r := 1) (by simp)).trans (rcx.trans start.args.output),
    (view.read (n := 64) (r := 8) (by simp)).trans (r8.trans start.args.length), boundary⟩
  · rw [key]
    apply start.hmac.of_copy
    apply frame_agrees_of_disjoint frame
    · rw [keyAddr]
      omega
    · intro r hr a ha hb
      obtain rfl := Vector.mem_singleton.mp hr
      change (stackPtr initial - 184).toNat ≤ a ∧
        a < (stackPtr initial - 184).toNat + 144 at ha
      rw [keyAddr] at ha
      change (stackPtr initial).toNat - 368 ≤ a ∧ a < (stackPtr initial).toNat - 368 + 24 at hb
      omega
  · refine ⟨rfl, ?_⟩
    change loadBytes t.external (BitVec.ofNat 64 (t.regValue .rsi).toNat) 8 = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, desc, ← rsp]
    apply stack_word hCall.stack running (show 360 ≤ hkdfSha256NewExpandMinStackBytes by decide) rsp
    have same : (Component.mem (rspOf s) 8).Agrees u t := by
      rw [rsp]
      exact slotAgrees (offset := 360) (.inl rfl)
    rw [agrees_memLoad (width := 64) same]
    exact ptrRead.trans start.args.info
  · refine ⟨rfl, ?_⟩
    change loadBytes t.external (BitVec.ofNat 64 ((t.regValue .rsi).toNat + 8)) 8 = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, desc, ← rsp]
    apply stack_word hCall.stack running (show 352 ≤ hkdfSha256NewExpandMinStackBytes by decide) nextWord
    have same : (Component.mem (rspOf s + 8) 8).Agrees u t := by
      rw [nextWord]
      exact slotAgrees (offset := 352) (.inr rfl)
    rw [agrees_memLoad (width := 64) same]
    exact lenRead.trans start.args.infoLength

end Hkdf.Proofs.NewExpand.Wrapper.Copy
