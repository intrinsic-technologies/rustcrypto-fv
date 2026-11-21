import Hkdf.Proofs.NewExpand.Expand.Entry.Prologue
import Hkdf.Proofs.NewExpand.Expand.Entry.Branch
import Hkdf.Proofs.Common.Encoding.Serialize.Convert.SavePointer
import Hkdf.Proofs.Common.CallFrame.Stack

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem prologue_write {s : RamState} {c : Component} {a : BitVec 64}
    (hc : c ∈ (Prologue.effect s).components) (ha : c.Covers a) :
    ∃ off : Nat, 8 ≤ off ∧ off ≤ 312 ∧
      (Component.mem (stackPtr s - BitVec.ofNat 64 off) 8).Covers a := by
  simp only [Effect.components, Prologue.effect, BitVec.ofNat_eq_ofNat, List.map_cons,
    Write.component_reg, Write.component_mem, Nat.reduceDiv, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ha.elim | exact ⟨_, by decide, by decide, ha⟩

variable [Bindings] {entry : RamState} {boundary : ReturnBoundary}
  {key info : ByteArray} {ptr : BitVec 64} {length : Nat}

theorem dispatch (pre : ExpandPre entry boundary key info ptr length) :
    ∃ s, DispatchState entry s boundary length := by
  obtain ⟨fuel, s, advance, ready, eff⟩ := Prologue.run pre
  have inStack : WritesWithin (Prologue.effect entry).components #v[Stack.region entry 2264] := by
    intro c hc a ha
    obtain ⟨off, low, high, touched⟩ := prologue_write hc ha
    exact ⟨_, by simp, stackRegion_contains_sub pre.call.stack.2.2.1 (by omega) low touched⟩
  have avoids : ∀ r ∈ #v[Stack.region entry 2264], r.Avoids InProgram := by
    intro r hr a hin inp
    rcases Vector.mem_singleton.mp hr with rfl
    exact pre.call.stackAvoid a hin (.inl inp)
  have initial : CallFrame.Running entry boundary #v[Stack.region entry 2264] entry :=
    .initial pre.call.machine pre.call.loaded pre.call.directionFlag
  have prologue := initial.of_agrees advance ready eff.agrees inStack avoids
    (by simp [Prologue.effect, Effect.components])
  obtain ⟨t, branch, readyT, pc, same⟩ :=
    length_branch ready prologue.loaded eff.rip pre.call.outerBoundary
  have run := prologue.of_agrees branch readyT same
    (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Component.Covers])
    avoids (by simp)
  have r8 : s.regValue .r8 = entry.regValue .r8 :=
    eff.agrees.read (r := 8) (n := 64) (by simp [Prologue.effect, Effect.components])
  rw [r8, pre.lengthArg] at pc
  have all := eff.agrees.trans same
  have agreeSlot (a : BitVec 64) : (Operand.mem a : Operand 64).read t = (Operand.mem a : Operand 64).read s :=
    Encoding.Serialize.read_mem_of_agrees same a (by simp [Component.Covers])
  have sp : t.regValue .rsp = entry.regValue .rsp - 536 :=
    (same.read (r := 4) (n := 64) (by decide)).trans eff.writes.1
  have saved (o d : BitVec 64) (hd : -536 + o = -d) :
      slot t o = (Operand.mem (entry.regValue .rsp - d) : Operand 64).read s := by
    unfold slot
    rw [sp, BitVec.sub_eq_add_neg, BitVec.add_assoc, hd]
    simpa only [BitVec.sub_eq_add_neg] using agreeSlot (entry.regValue .rsp - d)
  have ret : (Operand.mem (stackPtr entry) : Operand 64).read s = (returnBoundary entry).rip := by
    apply Encoding.Serialize.read_mem_of_agrees eff.agrees
    intro i hi c hc touched
    obtain ⟨off, lo, high, j, hj, eq⟩ := prologue_write hc touched
    have h₁ : i < 8 := hi
    have h₂ : j < 8 := hj
    have h := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_add, CallFrame.stack_sub_toNat pre.call.stack (offset := off) (by omega),
      BitVec.toNat_ofNat] at h
    have bound := CallFrame.stack_bounds pre.call.stack
    omega
  obtain ⟨_, hb, h15, h14, h13, h12, hbx, hcnt, hdesc, hctx, hlen⟩ := eff.writes
  refine ⟨t, {
    toRunning := { run with frame := CallFrame.frame_mono run.frame (by
      intro r hr a ha
      rcases Vector.mem_singleton.mp hr with rfl
      exact ⟨_, by simp, ha⟩) }
    sp := sp
    rbx := (saved 488 48 rfl).trans hbx
    r12 := (saved 496 40 rfl).trans h12
    r13 := (saved 504 32 rfl).trans h13
    r14 := (saved 512 24 rfl).trans h14
    r15 := (saved 520 16 rfl).trans h15
    rbp := (saved 528 8 rfl).trans hb
    ret := by
      unfold slot
      rw [sp, BitVec.sub_add_cancel]
      exact (agreeSlot _).trans ret
    size := (saved 224 312 rfl).trans (hlen.trans (by rw [← pre.lengthArg, BitVec.ofNat_toNat, BitVec.setWidth_eq]))
    mxcsr := all.mxcsr (by simp [Prologue.effect, Effect.components])
    fcw := all.fcw (by simp [Prologue.effect, Effect.components])
    pc := pc
    outputPtr := all.read (r := 1) (n := 64) (by simp [Prologue.effect, Effect.components])
    descriptors := (saved 232 304 rfl).trans hdesc
    contextPtr := (saved 240 296 rfl).trans hctx
    count := (saved 248 288 rfl).trans hcnt
    stackFrame := run.frame }⟩

end Hkdf.Proofs.NewExpand.Expand
