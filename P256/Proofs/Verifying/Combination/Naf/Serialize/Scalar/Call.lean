import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Frame
import P256.Proofs.Program.ScalarFrame.Memory
import X86Proofs.Instructions.Call.Triple
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice ScalarFrame.stack_contains supportedMachine_of_ready_agrees readyToStep)

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs


theorem call_address [Bindings] {s t : RamState} {cursor : BitVec 64} (state : FrameState s t cursor) :
    pushAddr t = stackPtr s - 368 := by
  rw [pushAddr, state.rsp, BitVec.sub_sub]
  rfl

theorem direct_call [Bindings] {s t : RamState} {cursor point : BitVec 64} {boundary : ReturnBoundary}
    (pre : ScalarPre s boundary cursor point) (state : FrameState s t cursor)
    (offset : Nat) (disp : BitVec 32)
    (hsize : offset + 5 ≤ 118431)
    (hbytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (hlow : (branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64)).toNat < 2^32)
    (htarget : InProgram (branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64)))
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset) :
    ∃ u, Advances boundary 1 t u ∧ ReadyToStep u ∧
      (callEffect (fun _ => branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
        (disp.signExtend 64)) (Extracted.textAddress + BitVec.ofNat 64 offset + 5) t).Holds t u := by
  have hpush : PushPre (Extracted.textAddress + BitVec.ofNat 64 offset) 5 t := by
    refine ⟨rip, ?_, ?_⟩
    · rw [call_address state]
      exact writable_of_grow (stack_sub_writable8 pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
        (offset := 368) (by decide) (by decide)) state.allocated
    · rw [call_address state]
      exact stack_code_apart pre (offset := 368) (codeOffset := offset)
        (by decide) (by decide) hsize
  exact (call_rel32_effect_step _ disp hlow).advances (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset (encodeCallRel32 disp) hsize hbytes)
    hpush (boundary_ne_program pre.outerBoundary htarget)

theorem call_writes [Bindings] {s t : RamState} {cursor point : BitVec 64} {boundary : ReturnBoundary}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : ScalarPre s boundary cursor point) (state : FrameState s t cursor) :
    WritesWithin (callEffect target ret t).components #v[Stack.region s 536] := by
  intro c hc a hv
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hv.elim
  · refine ⟨Stack.region s 536, by simp, ?_⟩
    rw [call_address state] at hv
    exact P256.Proofs.Program.ScalarFrame.stack_contains pre.toCalleePre (offset := 368)
      (by decide) (by decide) hv
  · exact hv.elim

theorem call_loaded [Bindings] {s t u : RamState} {cursor point : BitVec 64} {boundary : ReturnBoundary}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : ScalarPre s boundary cursor point) (state : FrameState s t cursor)
    (effect : (callEffect target ret t).Holds t u) : ProgramLoaded u := by
  intro a b hb
  rw [effect.agrees.memoryWriteFrame (call_writes pre state) a]
  · exact state.loaded a b hb
  · intro region hr hin
    have he : region = Stack.region s 536 := by simpa using hr
    subst region
    exact pre.avoids _ (by simp) a hin (.inl ⟨b, hb⟩)

theorem call_byte [Bindings] {s t u : RamState} {cursor : BitVec 64} {target : RamState → BitVec 64}
    {ret : BitVec 64} (state : FrameState s t cursor)
    (effect : (callEffect target ret t).Holds t u)
    {offset len : Nat} (ho : offset ≤ 360) (hl : len ≤ offset + 8) {i : Nat} (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply effect.agrees.byte
  intro c hc hv
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hv.elim
  · obtain ⟨j, hj, he⟩ := hv
    rw [call_address state] at he
    have ha : stackPtr s - BitVec.ofNat 64 offset =
        (stackPtr s - 368) + BitVec.ofNat 64 (368-offset) := by
      rw [← BitVec.ofNat_sub_ofNat_of_le 368 offset (by omega) (by omega)]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rw [← BitVec.add_assoc (-(368 : BitVec 64)),
        show -(368 : BitVec 64) + 368#64 = 0#64 by decide +kernel, BitVec.zero_add]
    apply RangeApart.offsets (stackPtr s - 368) (a := 0) (b := 368-offset)
      (len := 8) (count := len) (by decide) (by omega) (.inl (by omega)) j hj i hi
    rw [show BitVec.ofNat 64 0 = 0#64 by rfl, BitVec.add_zero, ← ha]
    exact he.symm
  · exact hv.elim

theorem call_read [Bindings] {s t u : RamState} {cursor : BitVec 64} {target : RamState → BitVec 64}
    {ret : BitVec 64} (state : FrameState s t cursor)
    (effect : (callEffect target ret t).Holds t u)
    {offset n : Nat} (ho : offset ≤ 360) (hl : n/8 ≤ offset+8) :
    (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read u =
      (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read t := by
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [call_byte state effect ho hl hi]

theorem FrameState.after_call [Bindings] {s t u : RamState} {cursor point : BitVec 64} {boundary : ReturnBoundary}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : ScalarPre s boundary cursor point) (state : FrameState s t cursor)
    (ready : ReadyToStep u) (effect : (callEffect target ret t).Holds t u) :
    FrameState s u cursor 368 := by
  have hm : MemoryWriteFrame t u #v[registerRegion s .rdi 272, cursorRegion cursor, Stack.region s 536] := by
    intro a ha
    apply effect.agrees.memoryWriteFrame (call_writes pre state) a
    intro region hr
    exact ha region (by simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; exact Or.inr (Or.inr hr))
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees,
    supportedMachine_of_ready_agrees state.machine ready effect.agrees,
    call_loaded pre state effect, effect.agrees.directionFlagClear (by simp) state.directionFlag,
    fun a ha => effect.agrees.grow a (state.allocated a ha),
    memoryWriteFrame_trans state.frame hm, effect.writes.1.trans (call_address state),
    ?_, (effect.agrees.read (n := 64) (r := 5) (by simp)).trans state.rbp,
    (effect.agrees.read (n := 64) (r := 12) (by simp)).trans state.r12,
    (effect.agrees.read (n := 64) (r := 13) (by simp)).trans state.r13,
    (effect.agrees.read (n := 64) (r := 15) (by simp)).trans state.r15,
    ?_, (effect.agrees.mxcsr (by simp)).trans state.mxcsr,
    (effect.agrees.fcw (by simp)).trans state.fp87⟩
  · intro entry he
    have hb : entry.2 ≤ 360 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> decide
    exact (call_read state effect hb (by omega)).trans (state.saved entry he)
  · have h := call_read state effect (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
