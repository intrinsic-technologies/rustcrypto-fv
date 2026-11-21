import P256.Proofs.Verifying.Message.Initialize

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem constants_preserve_lower {s t : RamState} (effect : (constantsEffect s).Holds s t)
    {offset width : Nat} (bound : offset + width / 8 ≤ 535) :
    memLoad t.external (stackPtr s + BitVec.ofNat 64 offset) width =
      memLoad s.external (stackPtr s + BitVec.ofNat 64 offset) width := by
  apply memLoad_congr
  intro i hi
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [effect.agrees.memory _]
  intro c hc covered
  simp only [constantsEffect, Effect.components, Write.component, Operand.component,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  all_goals
    obtain ⟨j, hj, eq⟩ := covered
    rw [BitVec.add_assoc, BitVec.add_assoc] at eq
    have eqn := congrArg BitVec.toNat ((BitVec.add_right_inj (stackPtr s)).mp eq)
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at eqn
    simp only [BitVec.reduceToNat] at eqn
    omega

theorem initialized_saved [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (state : Initialized initial s boundary) :
    memLoad s.external (frameBase initial + 456) 64 = initial.regValue .rsi ∧
    memLoad s.external (frameBase initial + 384) 64 = initial.regValue .rdi ∧
    memLoad s.external (frameBase initial + 464) 64 = initial.regValue .r8 := by
  obtain ⟨u, saved, effect⟩ := state.arguments
  have rsp : stackPtr u = frameBase initial := saved.rsp
  refine ⟨?_, ?_, ?_⟩
  · have h := constants_preserve_lower effect (offset := 456) (width := 64) (by decide)
    have h' : memLoad s.external (frameBase initial + 456) 64 =
        memLoad u.external (frameBase initial + 456) 64 := by
      simpa only [rsp, BitVec.ofNat_eq_ofNat] using h
    exact h'.trans saved.savedKey
  · have h := constants_preserve_lower effect (offset := 384) (width := 64) (by decide)
    have h' : memLoad s.external (frameBase initial + 384) 64 =
        memLoad u.external (frameBase initial + 384) 64 := by
      simpa only [rsp, BitVec.ofNat_eq_ofNat] using h
    exact h'.trans saved.savedOutput
  · have h := constants_preserve_lower effect (offset := 464) (width := 64) (by decide)
    have h' : memLoad s.external (frameBase initial + 464) 64 =
        memLoad u.external (frameBase initial + 464) 64 := by
      simpa only [rsp, BitVec.ofNat_eq_ofNat] using h
    exact h'.trans saved.savedSignature

theorem initialized_registers [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (state : Initialized initial s boundary) :
    s.regValue .rcx = initial.regValue .rcx ∧ s.regValue .rdx = initial.regValue .rdx := by
  obtain ⟨u, saved, effect⟩ := state.arguments
  constructor
  · exact (effect.agrees.read (n := 64) (r := 1) (by
      simp [constantsEffect, Effect.components, Write.component, Operand.component])).trans saved.count
  · exact (effect.agrees.read (n := 64) (r := 2) (by
      simp [constantsEffect, Effect.components, Write.component, Operand.component])).trans saved.descriptors

theorem descriptor_read [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (frame : MemoryWriteFrame initial s #v[Stack.region initial 9992])
    {offset : Nat} (bound : offset + 8 ≤ 16) :
    memLoad s.external (initial.regValue .rdx + BitVec.ofNat 64 offset) 64 =
      memLoad initial.external (initial.regValue .rdx + BitVec.ofNat 64 offset) 64 := by
  have bounded : (initial.regValue .rdx).toNat + 16 < 2^32 := pre.descriptorBounded
  apply frame_memLoad frame (region := registerRegion initial .rdx 16)
  · intro other member
    have eq : other = Stack.region initial 9992 := by simpa using member
    simpa only [eq] using pre.descriptorStack
  · exact pre.descriptorBounded
  · change (initial.regValue .rdx).toNat ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64), Nat.mod_eq_of_lt (by omega)]
    omega
  · change _ + 64 / 8 ≤ (initial.regValue .rdx).toNat + 16
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64), Nat.mod_eq_of_lt (by omega)]
    omega

end P256.Proofs.Verifying.Message.Hash
