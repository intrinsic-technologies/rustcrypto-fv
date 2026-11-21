import P256.Proofs.Sec1Serialize.Tail.Initialize.State
import P256.Proofs.Program.WrapperMemory
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {infinity : Bool}

theorem Preparing.of_second_store (pre : CalleePre s boundary 0x110d70 72 65 328)
    (h : Preparing s t boundary bytes infinity) {offset len : Nat} {e : Effect}
    (ho : offset ≤ 312) (hl : len + 192 ≤ offset)
    (step : Machine.step t = some (.next u)) (ready : ReadyToStep u) (effect : e.Holds t u)
    (components : e.components = [.mem (stackPtr s - BitVec.ofNat 64 offset) len, .rip])
    (next : InProgram e.rip) : Preparing s u boundary bytes infinity := by
  have agrees := effect.agrees
  rw [components] at agrees
  have writes : WritesWithin [.mem (stackPtr s - BitVec.ofNat 64 offset) len, .rip]
      #v[registerRegion s .rdi 65, workRegion s 328] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨workRegion s 328, by simp, work_contains pre (by omega) (by omega) ha⟩
    · exact ha.elim
  have apart (b n : Nat) (hb : b ≤ 192) (hn : n ≤ b + 8) :
      ∀ a m, Component.mem a m ∈ [.mem (stackPtr s - BitVec.ofNat 64 offset) len, .rip] →
        RangeApart a m (stackPtr s - BitVec.ofNat 64 b) n := by
    intro a m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, Component.mem.injEq,
      reduceCtorEq, or_false] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact stack_sub_apart pre.stack (by omega) (by omega) (by omega) hn (.inl (by omega))
  obtain ⟨fuel, execution⟩ := h.execution
  have run := Advances.of_step step (.inl (by
    rw [effect.rip]
    exact boundary_ne_program pre.outerBoundary next))
  refine ⟨h.state.after_effect pre (by decide) ready agrees writes (by simp),
    ⟨fuel + 1, execution.trans run⟩,
    (agrees.read (n := 64) (r := 5) (by simp)).trans h.destination,
    hasBytes_agrees_apart agrees (apart 113 65 (by decide) (by decide)) h.source,
    (memLoad_agrees_apart agrees (apart 192 8 (by decide) (by decide))).trans h.savedInput,
    ?_, hasBytes_agrees_apart agrees (apart 184 65 (by decide) (by decide)) h.zeroSource⟩
  rw [agrees.byte]
  · exact h.inputFlag
  · intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · have hs := stack_contains pre (by omega) (by omega) ha
      have hi : (registerRegion s .rsi 72).Contains (s.regValue .rsi + 64).toNat :=
        memoryRegion_contains_add pre.inputBounded (len := 72)
          (Nat.le_refl _) (Nat.le_refl _) (i := 64) (by decide)
      exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ hi hs
    · exact ha

end P256.Proofs.Sec1Serialize
