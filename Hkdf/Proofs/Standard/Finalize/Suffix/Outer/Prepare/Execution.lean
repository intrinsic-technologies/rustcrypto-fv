import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Geometry
import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Serialize
import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Machine

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary}

theorem serialize_pre (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10df0d) :
    Serialize.Pre s := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact readable pre state _ 4 (by decide)
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact writable pre state _ 4 (by decide) (by decide)
  · intro slot member ip len low high
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact codeApart pre state _ 4 ip len (by decide) (by omega) (by omega)

theorem serialize_writes (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) :
    WritesWithin (Serialize.effect s).components (writes initial) := by
  intro c member a covered
  simp only [Serialize.effect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  all_goals exact writes_component pre state _ 4 (by decide) (by decide) a covered

theorem serialize
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10df0d) :
    ∃ t, Suffix.State initial boundary t ∧ (Serialize.effect s).Holds s t := by
  have outside : ∀ ip : Nat, 0x10df0d ≤ ip → ip ≤ 0x10df89 →
      BitVec.ofNat 64 ip ≠ boundary.rip := by
    intro ip low high
    exact boundary_ne_program pre.outerBoundary
      (by simpa only [BitVec.add_zero] using code_span ip 1 (by omega) (by omega) 0 (by decide))
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Serialize.run boundary outside s
    (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep state.running.machine)
    (Serialize.code state.running.loaded) (serialize_pre pre state rip)
  refine ⟨t, state_of_local pre state run ready effect.agrees (serialize_writes pre state) ?_, effect⟩
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Serialize.effect, Effect.components, Write.component, Operand.component]


theorem pad_pre (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10df89) : Pad.Pre s := by
  refine ⟨rip, readable pre state 208 8 (by decide), ?_, ?_,
    writable pre state 104 1 (by decide) (by decide), ?_, ?_⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact readable pre state _ 8 (by decide)
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact writable pre state _ 8 (by decide) (by decide)
  · intro slot member offset len bound
    have apart := codeApart pre state slot 8 (0x10df89 + offset) len
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl
        all_goals decide) (by omega) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat,
      show rspOf s = stackPtr s from Operand.read_reg64 s 4] using apart
  · intro offset len bound
    have apart := codeApart pre state 104 1 (0x10df89 + offset) len
      (by decide) (by omega) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat,
      show rspOf s = stackPtr s from Operand.read_reg64 s 4] using apart

theorem pad_writes (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) {a : RamState}
    (mark : (Pad.Mark.effect s).Holds s a) :
    WritesWithin ((Pad.Mark.effect s).components ++ (Pad.Copy.effect a).components)
      (writes initial) := by
  have rspA : rspOf a = stackPtr s := mark.agrees.read (n := 64) (r := 4)
    (by simp [Pad.Mark.effect, Effect.components, Write.component, Operand.component])
  intro c member p covered
  rw [List.mem_append] at member
  rcases member with member | member
  · simp only [Pad.Mark.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    · exact writes_component pre state 104 1 (by decide) (by decide) p covered
    · exact writes_component pre state 120 8 (by decide) (by decide) p covered
    · exact writes_component pre state 113 8 (by decide) (by decide) p covered
    · exact writes_component pre state 105 8 (by decide) (by decide) p covered
    · exact writes_component pre state 128 8 (by decide) (by decide) p covered
  · simp only [Pad.Copy.effect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component,
      Operand.component, List.mem_cons, List.not_mem_nil, or_false, rspA] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals exact writes_component pre state _ 8 (by decide) (by decide) p covered

theorem pad
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10df89) :
    ∃ a t, Suffix.State initial boundary t ∧
      (Pad.Mark.effect s).Holds s a ∧ (Pad.Copy.effect a).Holds a t := by
  obtain ⟨fuel, t, run, ready, _, a, mark, copy⟩ := Pad.run_steps boundary pre.outerBoundary s
    (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep state.running.machine)
    (Pad.code state.running.loaded) (pad_pre pre state rip)
  refine ⟨a, t, state_of_local pre state run ready (mark.agrees.trans copy.agrees)
    (pad_writes pre state mark) ?_, mark, copy⟩
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Pad.Mark.effect, Pad.Copy.effect, Effect.components, Write.component,
    Operand.component]

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare
