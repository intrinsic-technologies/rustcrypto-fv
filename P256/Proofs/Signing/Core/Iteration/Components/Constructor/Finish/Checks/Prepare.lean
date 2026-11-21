import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Frame
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks.Stores
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stores_scalar {t u : RamState} {p : BitVec 64} {off d : Nat}
    (effect : (storesEffect p t).Holds t u) (low : 32 ≤ off) (bound : off + 32 ≤ 216)
    (scalar : Nat256At t (stackPtr t + BitVec.ofNat 64 off) d) :
    Nat256At u (stackPtr t + BitVec.ofNat 64 off) d := by
  refine ⟨scalar.1, fun i hi => ?_⟩
  rw [effect.agrees.byte]
  · exact scalar.2 i hi
  · intro c hc hv
    simp only [storesEffect, Effect.components, List.map_cons, List.map_nil,
      List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false, Write.component] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    all_goals obtain ⟨j, hj, he⟩ := hv
    · exact RangeApart.offsets (stackPtr t) (a := 24) (b := off)
        (by decide) (by omega) (.inl (by omega)) j hj i hi he.symm
    · exact RangeApart.offsets (stackPtr t) (a := 16) (b := off)
        (by decide) (by omega) (.inl (by omega)) j hj i hi he.symm
    · exact RangeApart.offsets (stackPtr t) (a := 8) (b := off)
        (by decide) (by omega) (.inl (by omega)) j hj i hi he.symm
    · exact RangeApart.offsets (stackPtr t) (a := 0) (b := off)
        (by decide) (by omega) (.inl (by omega)) j hj i hi he.symm

theorem zero_buffer [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Stage s t boundary)
    (start : Nat) (bound : start + 35 < 118431)
    (bytes : Extracted.textBytes.toListFrom start 35 = storesBytes)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 start) :
    ∃ u, Stage s u boundary ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 start + 35#64 ∧
      Nat256At u (stackPtr u + 0#64) 0 ∧
      (∀ (off d : Nat), 32 ≤ off → off + 32 ≤ 216 →
        Nat256At t (stackPtr t + BitVec.ofNat 64 off) d →
        Nat256At u (stackPtr u + BitVec.ofNat 64 off) d) := by
  let p := Extracted.textAddress + BitVec.ofNat 64 start
  have hp : StoresPre p t := by
    refine ⟨rip, ?_, ?_⟩
    · intro off hoff
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl
      all_goals exact stack_writable pre state.toFrame (by decide) (by decide)
    · intro off hoff k len hlen
      have hc : RangeApart (stackPtr t + off) 8
          (Extracted.textAddress + BitVec.ofNat 64 (start+k)) len := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl | rfl | rfl
        all_goals exact stack_code pre state.toFrame (by decide) (by omega)
      simpa only [p, BitVec.ofNat_add, BitVec.add_assoc] using hc
  have safe : ∀ k ∈ ([9#64,18#64,27#64,35#64] : List (BitVec 64)), p + k ≠ boundary.rip := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · simpa only [p, BitVec.ofNat_add, BitVec.add_assoc] using
        boundary_ne_program pre.outerBoundary (inProgram_of_textOffset (start+9) (by omega))
    · simpa only [p, BitVec.ofNat_add, BitVec.add_assoc] using
        boundary_ne_program pre.outerBoundary (inProgram_of_textOffset (start+18) (by omega))
    · simpa only [p, BitVec.ofNat_add, BitVec.add_assoc] using
        boundary_ne_program pre.outerBoundary (inProgram_of_textOffset (start+27) (by omega))
    · simpa only [p, BitVec.ofNat_add, BitVec.add_assoc] using
        boundary_ne_program pre.outerBoundary (inProgram_of_textOffset (start+35) bound)
  obtain ⟨n, u, hu, ru, _, eu⟩ := stores_correct boundary p safe t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) start storesBytes (by exact Nat.le_of_lt bound) bytes) hp
  have w : WritesWithin (storesEffect p t).components
      #v[registerRegion s .rdi 72, workRegion s] := by
    intro c hc a hv
    simp only [storesEffect, Effect.components, List.map_cons, List.map_nil,
      List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false, Write.component] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    all_goals refine ⟨workRegion s, by simp, ?_⟩
    · change (Component.mem (stackPtr t + 24#64) 8).Covers a at hv
      rw [Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (offset := 24) (by decide)] at hv
      exact Program.ScalarFrame.Work.contains pre (offset := 192) (by decide) (by decide) hv
    · change (Component.mem (stackPtr t + 16#64) 8).Covers a at hv
      rw [Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (offset := 16) (by decide)] at hv
      exact Program.ScalarFrame.Work.contains pre (offset := 200) (by decide) (by decide) hv
    · change (Component.mem (stackPtr t + 8#64) 8).Covers a at hv
      rw [Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (offset := 8) (by decide)] at hv
      exact Program.ScalarFrame.Work.contains pre (offset := 208) (by decide) (by decide) hv
    · change (Component.mem (stackPtr t + 0#64) 8).Covers a at hv
      rw [Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (offset := 0) (by decide)] at hv
      exact Program.ScalarFrame.Work.contains pre (offset := 216) (by decide) (by decide) hv
  have sp : stackPtr u = stackPtr t := eu.agrees.read (n := 64) (r := 4)
    (by simp [storesEffect, Effect.components])
  have ust := state.after pre hu ru eu.agrees w (sp.trans state.rsp)
    (by simp [storesEffect, Effect.components])
  have words := eu.writes
  change memLoad u.external (stackPtr t + 24) 64 = 0 ∧
    memLoad u.external (stackPtr t + 16) 64 = 0 ∧
    memLoad u.external (stackPtr t + 8) 64 = 0 ∧
    memLoad u.external (stackPtr t + 0) 64 = 0 at words
  refine ⟨u, ust, eu.rip, ?_, ?_⟩
  · apply P256.Proofs.SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs (by decide)
    · exact (stack_readable pre ust.toFrame (offset := 0) (len := 32) (by decide)).mem
    · intro j hj
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      all_goals simp only [sp, Nat.zero_div, BitVec.add_assoc]
      · exact words.2.2.2
      · exact words.2.2.1
      · exact words.2.1
      · exact words.1
  · intro off d hlo hb scalar
    rw [sp]
    exact stores_scalar eu hlo hb scalar

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks
