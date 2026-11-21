import Hkdf.Proofs.NewExpand.Expand.Frame
import Hkdf.Proofs.Common.CallFrame.Stack

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Counter

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine

abbrev regions (entry : RamState) (length : Nat) : Vector MemoryRegion 2 :=
  #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264]

abbrev RunningFrame [Bindings] (entry : RamState) (boundary : ReturnBoundary)
    (length : Nat) (s : RamState) : Prop := Running entry boundary (regions entry length) s

def base (entry : RamState) : BitVec 64 := stackPtr entry - 536

structure StackContext (entry : RamState) (boundary : ReturnBoundary) (length : Nat) : Prop where
  stack : Stack.Valid entry 2264
  stackAvoid : (Stack.region entry 2264).Avoids (fun a ↦ InProgram a ∨ InPageTables a)
  outside : ¬ InProgram boundary.rip
  avoids : ∀ r ∈ regions entry length, r.Avoids InProgram

theorem StackContext.of_pre [Bindings] {entry : RamState} {boundary : ReturnBoundary}
    {length : Nat} {key info : ByteArray} {ptr : BitVec 64}
    (pre : ExpandPre entry boundary key info ptr length) (positive : 0 < length) (limit : length ≤ 8160) :
    StackContext entry boundary length := by
  refine ⟨pre.call.stack, pre.call.stackAvoid, pre.call.outerBoundary, ?_⟩
  intro r hr a ha hp
  have member : r ∈ #v[registerRegion entry .rcx length, Stack.region entry 2264] := by
    simpa only [regions, writtenLength, limit, ↓reduceIte] using hr
  exact (pre.separation positive limit).2 r member |>.2 a ha (.inl hp)

theorem base_add {entry : RamState} {off : Nat} (le : off ≤ 536) :
    base entry + BitVec.ofNat 64 off = stackPtr entry - BitVec.ofNat 64 (536 - off) := by
  rw [base, ← BitVec.ofNat_sub_ofNat_of_le 536 off (by omega) le]
  change stackPtr entry - 536 + _ = stackPtr entry - (536 - _)
  bv_omega

theorem read_stack [Bindings] {entry s : RamState} {length off size : Nat}
    {boundary : ReturnBoundary} (ctx : StackContext entry boundary length)
    (running : RunningFrame entry boundary length s)
    (offBound : off ≤ 536) (sizeBound : off + size ≤ 544) :
    MemReadable s (base entry + BitVec.ofNat 64 off) size := by
  rw [base_add offBound]
  exact stack_readable ctx.stack running.allocated (by omega) (by omega)

theorem write_byte [Bindings] {entry s : RamState} {length off : Nat}
    {boundary : ReturnBoundary} (ctx : StackContext entry boundary length)
    (running : RunningFrame entry boundary length s) (bound : off ≤ 536) :
    MemWritable s (base entry + BitVec.ofNat 64 off) 1 := by
  rw [base_add bound]
  exact stack_writable1 ctx.stack ctx.stackAvoid running.allocated (by omega)

theorem stack_apart {entry : RamState} {length off size codeOff codeSize : Nat}
    {boundary : ReturnBoundary} (ctx : StackContext entry boundary length)
    (bound : off ≤ 536) (fit : off + size ≤ 544) (codeBound : codeOff + codeSize ≤ 115149) :
    RangeApart (base entry + BitVec.ofNat 64 off) size
      (Extracted.textAddress + BitVec.ofNat 64 codeOff) codeSize := by
  rw [base_add bound]
  exact stack_codeApart ctx.stack (fun a ha hp ↦ ctx.stackAvoid a ha (.inl hp))
    (by omega) (by omega) codeBound

theorem stack_writes {entry : RamState} {length off size : Nat}
    {boundary : ReturnBoundary} (ctx : StackContext entry boundary length)
    (bound : off ≤ 536) (fit : off + size ≤ 536) :
    WritesWithin [.mem (base entry + BitVec.ofNat 64 off) size, .rip] (regions entry length) := by
  intro c hc a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · rw [base_add bound] at ha
    exact ⟨_, by simp [regions], stackRegion_contains_sub ctx.stack.2.2.1 (by omega) (by omega) ha⟩
  · exact ha.elim

theorem enter_call [Bindings] {entry s : RamState} {boundary : ReturnBoundary} {length : Nat}
    {pre : RamState → Prop} {code : CodeMap} {target : RamState → BitVec 64} {ret : BitVec 64}
    (ctx : StackContext entry boundary length) (running : RunningFrame entry boundary length s)
    (sp : stackPtr s = base entry) (off len : Nat) (bound : off + len ≤ 115149)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 off)
    (step : StepEffect pre code (callEffect target ret)) (loaded : CodeIn code s)
    (precondition : PushPre (Extracted.textAddress + BitVec.ofNat 64 off) len s → pre s)
    (continues : target s ≠ boundary.rip) :
    ∃ c, RunningFrame entry boundary length c ∧ (callEffect target ret s).Holds s c ∧
      returnBoundary c = ⟨ret, base entry⟩ := by
  have push : pushAddr s = stackPtr entry - 544 := by
    rw [pushAddr, sp, base, BitVec.sub_sub]
    rfl
  have write : MemWritable s (pushAddr s) 8 := by
    rw [push]
    exact stack_writable8 ctx.stack ctx.stackAvoid running.allocated (by decide) (by decide)
  have apart : RangeApart (pushAddr s) 8 (Extracted.textAddress + BitVec.ofNat 64 off) len := by
    rw [push]
    exact stack_codeApart ctx.stack (fun a ha hp ↦ ctx.stackAvoid a ha (.inl hp))
      (by decide) (by decide) bound
  obtain ⟨c, rc, effect, returned⟩ := running.call step loaded (precondition ⟨rip, write, apart⟩)
    continues (by
      intro comp hm a ha
      simp only [callEffect, pushEffect_components, push, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact ha.elim
      · exact ⟨_, by simp [regions], stackRegion_contains_sub ctx.stack.2.2.1 (by decide) (by decide) ha⟩
      · exact ha.elim) ctx.avoids
  exact ⟨c, rc, effect, by rw [returned, sp]⟩

theorem no_memory {components : List Component} {entry s t : RamState}
    {boundary : ReturnBoundary} {length fuel : Nat} [Bindings]
    (ctx : StackContext entry boundary length) (running : RunningFrame entry boundary length s)
    (run : Advances boundary fuel s t) (ready : ReadyToStep t)
    (effect : AgreesExcept components s t)
    (memory : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (df : .df ∉ components) : RunningFrame entry boundary length t :=
  running.of_agrees run ready effect (fun c hc a ha ↦ (memory c hc a ha).elim) ctx.avoids df

end Hkdf.Proofs.NewExpand.Expand.Counter
