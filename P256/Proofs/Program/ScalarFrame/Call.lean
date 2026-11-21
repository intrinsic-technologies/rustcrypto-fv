import P256.Proofs.Program.ScalarFrame.CallStep
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Program (CalleePre boundary_ne_program programLoaded_codeIn programText_slice supportedMachine_of_ready_agrees readyToStep)

namespace P256.Proofs.Program.ScalarFrame

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program
open X86 X86.Machine X86.UserProcess X86Proofs

variable {entry : BitVec 64} {inputBytes outputBytes stackReserve frameOffset : Nat}

variable {inputRegister : Syntax.Reg}

theorem scalar_call_address [Bindings] {s t : RamState} (state : FrameState s t outputBytes stackReserve (BitVec.ofNat 64 frameOffset)) :
    pushAddr t = stackPtr s - BitVec.ofNat 64 (frameOffset + 8) := by
  simp only [pushAddr, state.rsp, BitVec.sub_sub, BitVec.ofNat_add]
  rfl

theorem scalar_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister)
    (hframe : frameOffset + 8 ≤ stackReserve) (halign : (frameOffset + 8) % 8 = 0)
    (state : FrameState s t outputBytes stackReserve (BitVec.ofNat 64 frameOffset))
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
        (disp.signExtend 64)) (Extracted.textAddress + BitVec.ofNat 64 offset + 5) t).Holds t u :=
  call_step pre hframe halign (readyToStep state.machine state.bindingsSupported)
    state.loaded state.allocated state.rsp offset disp hsize hbytes hlow htarget rip

theorem scalar_call_writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister)
    (hframe : frameOffset + 8 ≤ stackReserve)
    (state : FrameState s t outputBytes stackReserve (BitVec.ofNat 64 frameOffset)) :
    WritesWithin (callEffect target ret t).components #v[Stack.region s stackReserve] := by
  intro c hc a hv
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hv.elim
  · refine ⟨Stack.region s stackReserve, by simp, ?_⟩
    rw [scalar_call_address state] at hv
    exact stack_contains pre (offset := frameOffset + 8)
      hframe (by omega) hv
  · exact hv.elim

theorem scalar_call_loaded [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister)
    (hframe : frameOffset + 8 ≤ stackReserve)
    (state : FrameState s t outputBytes stackReserve (BitVec.ofNat 64 frameOffset))
    (effect : (callEffect target ret t).Holds t u) : ProgramLoaded u := by
  intro a b hb
  rw [effect.agrees.memoryWriteFrame (scalar_call_writes pre hframe state) a]
  · exact state.loaded a b hb
  · intro region hr hin
    have he : region = Stack.region s stackReserve := by simpa using hr
    subst region
    exact pre.avoids _ (by simp) a hin (.inl ⟨b, hb⟩)

theorem scalar_call_byte [Bindings] {s t u : RamState} {target : RamState → BitVec 64}
    {ret : BitVec 64}
    (hlow : frameOffset + 16 ≤ 2^64)
    (state : FrameState s t outputBytes stackReserve (BitVec.ofNat 64 frameOffset))
    (effect : (callEffect target ret t).Holds t u)
    {offset len : Nat} (ho : offset ≤ frameOffset) (hl : len ≤ offset + 8) {i : Nat} (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? :=
  call_byte hlow state.rsp effect ho hl hi

theorem scalar_call_read [Bindings] {s t u : RamState} {target : RamState → BitVec 64}
    {ret : BitVec 64}
    (hlow : frameOffset + 16 ≤ 2^64)
    (state : FrameState s t outputBytes stackReserve (BitVec.ofNat 64 frameOffset))
    (effect : (callEffect target ret t).Holds t u)
    {offset n : Nat} (ho : offset ≤ frameOffset) (hl : n/8 ≤ offset+8) :
    (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read u =
      (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read t := by
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [scalar_call_byte hlow state effect ho hl hi]

theorem FrameState.after_call [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister)
    (hframe : frameOffset + 8 ≤ stackReserve) (hsaved : 48 ≤ frameOffset)
    (state : FrameState s t outputBytes stackReserve (BitVec.ofNat 64 frameOffset))
    (ready : ReadyToStep u) (effect : (callEffect target ret t).Holds t u) :
    FrameState s u outputBytes stackReserve (BitVec.ofNat 64 (frameOffset + 8)) := by
  have hm : MemoryWriteFrame t u #v[registerRegion s .rdi outputBytes, Stack.region s stackReserve] := by
    intro a ha
    apply effect.agrees.memoryWriteFrame (scalar_call_writes pre hframe state) a
    intro region hr
    exact ha region (by simpa using Or.inr hr)
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees,
    supportedMachine_of_ready_agrees state.machine ready effect.agrees,
    scalar_call_loaded pre hframe state effect, effect.agrees.directionFlagClear (by simp) state.directionFlag,
    fun a ha => effect.agrees.grow a (state.allocated a ha),
    memoryWriteFrame_trans state.frame hm, effect.writes.1.trans (scalar_call_address state),
    ?_, ?_, (effect.agrees.mxcsr (by simp)).trans state.mxcsr,
    (effect.agrees.fcw (by simp)).trans state.fp87⟩
  · intro entry he
    have hb : entry.2 ≤ frameOffset := by
      simp only [P256.Proofs.Program.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega
    exact (scalar_call_read (by have := stack_bounds pre.stack; omega) state effect hb (by omega)).trans (state.saved entry he)
  · have h := scalar_call_read (by have := stack_bounds pre.stack; omega) state effect (offset := 0) (n := 64) (by omega) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

end P256.Proofs.Program.ScalarFrame
