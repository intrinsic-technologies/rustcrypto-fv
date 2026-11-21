import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Copy
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_byte {s t : RamState} {cs : List Component} {offset len : Nat}
    (agrees : AgreesExcept cs s t)
    (memory : ∀ address size, Component.mem address size ∈ cs →
      ∃ off : Nat, address = stackPtr s + BitVec.ofNat 64 off ∧
        off ∈ [16, 24, 32, 40] ∧ size = 8)
    (bound : offset + len < 2^64) (apart : offset + len ≤ 16 ∨ 48 ≤ offset)
    {i : Nat} (hi : i < len) :
    t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc ha
  cases c <;> try exact ha.elim
  case mem address size =>
    obtain ⟨off, rfl, member, rfl⟩ := memory address size hc
    obtain ⟨j, hj, he⟩ := ha
    apply RangeApart.offsets (stackPtr s) (a := off) (b := offset) (len := 8) (count := len)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega)
      (Nat.le_of_lt bound) _ j hj i hi he.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    omega

theorem copyY_bytes {s t : RamState} (effect : (copyYEffect s).Holds s t)
    {offset len : Nat} (bound : offset + len < 2^64)
    (apart : offset + len ≤ 16 ∨ 48 ≤ offset) {i : Nat} (hi : i < len) :
    t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply copy_byte effect.agrees _ bound apart hi
  intro address size member
  simp only [copyYEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil,
    or_false, Component.mem.injEq, reduceCtorEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨16, rfl, by simp, rfl⟩
  · exact ⟨24, rfl, by simp, rfl⟩
  · exact ⟨32, rfl, by simp, rfl⟩
  · exact ⟨40, rfl, by simp, rfl⟩

theorem copyX_bytes {s t : RamState} (effect : (copyXEffect s).Holds s t)
    {offset len : Nat} (bound : offset + len < 2^64)
    (apart : offset + len ≤ 16 ∨ 48 ≤ offset) {i : Nat} (hi : i < len) :
    t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply copy_byte effect.agrees _ bound apart hi
  intro address size member
  simp only [copyXEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil,
    or_false, Component.mem.injEq, reduceCtorEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨16, rfl, by simp, rfl⟩
  · exact ⟨24, rfl, by simp, rfl⟩
  · exact ⟨32, rfl, by simp, rfl⟩
  · exact ⟨40, rfl, by simp, rfl⟩


def preservedWindows : List (Nat × Nat) := [(280, 32), (312, 32), (748, 1)]

def PreservesInputs (s t u : RamState) : Prop :=
  (∀ r ∈ [Syntax.Reg.rbx, .r15], u.regValue r = t.regValue r) ∧
  (∀ window ∈ preservedWindows, ∀ i < window.2,
    u.external[stackPtr s - BitVec.ofNat 64 window.1 + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 window.1 + BitVec.ofNat 64 i]?)

theorem PreservesInputs.trans {s t u v : RamState}
    (h : PreservesInputs s t u) (h' : PreservesInputs s u v) : PreservesInputs s t v :=
  ⟨fun r hr => (h'.1 r hr).trans (h.1 r hr),
    fun w hw i hi => (h'.2 w hw i hi).trans (h.2 w hw i hi)⟩

theorem PreservesInputs.of_registers {s t u : RamState} {cs : List Component}
    (h : AgreesExcept cs t u)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (rbx : .reg 3 ∉ cs) (r15 : .reg 15 ∉ cs) :
    PreservesInputs s t u := by
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.read (n := 64) rbx
    · exact h.read (n := 64) r15
  · intro w hw i hi
    rw [h.external memory]

theorem PreservesInputs.of_call {s t u : RamState} {outputOffset : Nat}
    (hout : outputOffset ∈ [184, 384, 480, 416])
    (regs : ∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
      u.regValue r = t.regValue r)
    (bytes : ∀ offset len : Nat, offset ≤ 760 → len ≤ offset+8 →
      (offset+32 ≤ outputOffset ∨ outputOffset+len ≤ offset) → ∀ i < len,
      u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?) :
    PreservesInputs s t u := by
  refine ⟨?_, ?_⟩
  · intro r hr
    apply regs r
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro w hw i hi
    simp only [preservedWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
    rcases hw with rfl | rfl | rfl
    all_goals apply bytes _ _ (by decide) (by decide) _ i hi
    all_goals rcases hout with rfl | rfl | rfl | rfl <;> decide

theorem PreservesInputs.montgomery {s t u : RamState} {x offset : Nat}
    (h : PreservesInputs s t u) (offsetIn : (offset, 32) ∈ preservedWindows)
    (hx : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) x) :
    MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) x :=
  hx.of_bytes_eq (h.2 (offset, 32) offsetIn)

theorem PreservesInputs.of_copyY [Bindings] {s t u : RamState}
    (state : Frame s t) (effect : (copyYEffect t).Holds t u) : PreservesInputs s t u := by
  refine ⟨?_, ?_⟩
  · intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp [copyYEffect, Effect.components])
    · exact effect.agrees.read (n := 64) (r := 15) (by simp [copyYEffect, Effect.components])
  · intro w member i hi
    simp only [preservedWindows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · have addr := ScalarFrame.scalar_stack_address (frameOffset := 760) state.rsp (offset := 480) (by decide) (by decide)
      simpa only [addr] using copyY_bytes effect (offset := 480) (len := 32) (by decide) (by decide) hi
    · have addr := ScalarFrame.scalar_stack_address (frameOffset := 760) state.rsp (offset := 448) (by decide) (by decide)
      simpa only [addr] using copyY_bytes effect (offset := 448) (len := 32) (by decide) (by decide) hi
    · have addr := ScalarFrame.scalar_stack_address (frameOffset := 760) state.rsp (offset := 12) (by decide) (by decide)
      simpa only [addr] using copyY_bytes effect (offset := 12) (len := 1) (by decide) (by decide) hi

theorem PreservesInputs.of_copyX [Bindings] {s t u : RamState}
    (state : Frame s t) (effect : (copyXEffect t).Holds t u) : PreservesInputs s t u := by
  refine ⟨?_, ?_⟩
  · intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp [copyXEffect, Effect.components])
    · exact effect.agrees.read (n := 64) (r := 15) (by simp [copyXEffect, Effect.components])
  · intro w member i hi
    simp only [preservedWindows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · have addr := ScalarFrame.scalar_stack_address (frameOffset := 760) state.rsp (offset := 480) (by decide) (by decide)
      simpa only [addr] using copyX_bytes effect (offset := 480) (len := 32) (by decide) (by decide) hi
    · have addr := ScalarFrame.scalar_stack_address (frameOffset := 760) state.rsp (offset := 448) (by decide) (by decide)
      simpa only [addr] using copyX_bytes effect (offset := 448) (len := 32) (by decide) (by decide) hi
    · have addr := ScalarFrame.scalar_stack_address (frameOffset := 760) state.rsp (offset := 12) (by decide) (by decide)
      simpa only [addr] using copyX_bytes effect (offset := 12) (len := 1) (by decide) (by decide) hi

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
