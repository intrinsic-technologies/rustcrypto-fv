import Sha1.Proofs.Buffered.Finalize.Geometry
import Sha1.Proofs.Compress.Machine.Execution
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

namespace Sha1.Proofs.Buffered.Finalize.Digest.Normalize

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

def bytesA : List UInt8 :=
  [0x44, 0x0f, 0xb6, 0x7c, 0x24, 0x57, 0x4c, 0x8b, 0x64, 0x24, 0x58,
    0x41, 0x8b, 0x46, 0x10, 0x89, 0x44, 0x24, 0x10]

def bytesB : List UInt8 :=
  [0x49, 0x8b, 0x06, 0x49, 0x8b, 0x4e, 0x08, 0x48, 0x89, 0x4c, 0x24, 0x08,
    0x48, 0x89, 0x04, 0x24]

structure RunPre (p : BitVec 64) (s : RamState) : Prop extends Storage .digestCopy s where
  rip : s.RIP = p
  state : (Operand.reg 14 : Operand 64).read s = stackPtr s + 256

def effectA (s : RamState) : Effect :=
  { rip := 0x100102
    writes := [
      ⟨(.reg 15 : Operand 64), ((Operand.mem (stackPtr s + 87) : Operand 8).read s).setWidth 64⟩,
      ⟨(.reg 12 : Operand 64), (Operand.mem (stackPtr s + 88) : Operand 64).read s⟩,
      ⟨(.reg 0 : Operand 64), ((Operand.mem (stackPtr s + 272) : Operand 32).read s).setWidth 64⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 32),
        (Operand.mem (stackPtr s + 272) : Operand 32).read s⟩] }

def effectB (s : RamState) : Effect :=
  { rip := 0x100112
    writes := [
      ⟨(.reg 0 : Operand 64), (Operand.mem (stackPtr s + 256) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (Operand.mem (stackPtr s + 264) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64),
        (Operand.mem (stackPtr s + 264) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s) : Operand 64),
        (Operand.mem (stackPtr s + 256) : Operand 64).read s⟩] }

set_option maxHeartbeats 1000000 in
theorem executionA [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (RunPre 0x1000ef) (codeRange 0x1000ef bytesA) effectA := by
  unfold bytesA
  md5_run_begin movzx_r_m8_rex_effect_step 0x1000ef 0x44 (by unfold RexPrefix; decide)
    32 (.inr rfl) (fun _ ↦ rfl) 7 (.sib 4 none 0 (.d8 87))
    (by decide) (by decide) (by decide)
  case pre => intro s h; exact ⟨h.rip, (h.toStorage.stackWritable 87 1 (by decide)).readable⟩
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xf5 (by decide +kernel)
  md5_run_then mov_r64_m64_effect_step 0x1000f5 0x4c (by unfold RexWPrefix; decide)
    4 (.sib 4 none 0 (.d8 88)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1000ef) 6 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact (h.toStorage.stackWritable 88 8 (by decide)).readable
    · x86_avoid
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xfa (by decide +kernel)
  md5_run_then mov_r32_m32_effect_step 0x1000fa 0x41 (by unfold RexNoWPrefix; decide)
    0 (.base 14 (.d8 16)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1000ef) 11 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      change MemReadable s ((Operand.reg 14 : Operand 64).read s + 16) 4
      rw [h.state, BitVec.add_assoc]
      exact (h.toStorage.stackWritable 272 4 (by decide)).readable
    · x86_avoid
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xfe (by decide +kernel)
  md5_run_then Common.Instructions.MovStore.mov_m32_r32_low_effect_step 0x1000fe
    0 (.sib 4 none 0 (.d8 16)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1000ef) 15 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨storePre_of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 16 4 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := 16) (len := 4) (codeOffset := 0xfe)
        (codeLen := 4) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip (by rfl)
      x86_norm
      change RangeApart (stackPtr t + 16) 4 0x1000ef 19
      rw [hsp]
      exact h.toStorage.stackApart (offset := 16) (len := 4) (codeOffset := 0xef)
        (codeLen := 19) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x102 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t h hE
  have h16 : (Operand.reg 14 : Operand 64).read s + 16#64 = stackPtr s + 272 := by
    rw [h.state, BitVec.add_assoc]
    rfl
  have h16' : Operand.read s (Operand.reg (14#5) : Operand 64) + 16#64 =
      stackPtr s + 272#64 := h16
  apply hE.weaken
  · x86_norm [effectA]
  · x86_norm [effectA]
    rw [h16']
    refine ⟨.inl rfl, .inr (.inr (.inr ?_))⟩
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    rfl
  · intro i; cases i <;> x86_norm [effectA]
  · x86_norm [effectA, stackPtr]
    rfl

set_option maxHeartbeats 1000000 in
theorem executionB [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (RunPre 0x100102) (codeRange 0x100102 bytesB) effectB := by
  unfold bytesB
  md5_run_begin mov_r64_m64_effect_step 0x100102 0x49 (by unfold RexWPrefix; decide)
    0 (.base 14 .none) (by decide) (by decide) (by decide)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    simp only [BitVec.add_zero]
    change MemReadable s ((Operand.reg 14 : Operand 64).read s) 8
    rw [h.state]
    exact (h.toStorage.stackWritable 256 8 (by decide)).readable
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x105 (by decide +kernel)
  md5_run_then mov_r64_m64_effect_step 0x100105 0x49 (by unfold RexWPrefix; decide)
    1 (.base 14 (.d8 8)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100102) 3 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      change MemReadable s ((Operand.reg 14 : Operand 64).read s + 8) 8
      rw [h.state, BitVec.add_assoc]
      exact (h.toStorage.stackWritable 264 8 (by decide)).readable
    · x86_avoid
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x109 (by decide +kernel)
  md5_run_then Common.Instructions.MovStore.mov_m64_r64_effect_step 0x100109 0x48
    (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d8 8))
    (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100102) 7 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨storePre_of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 8 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := 8) (len := 8) (codeOffset := 0x109)
        (codeLen := 5) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip (movM64R64Effect_components _ _ _ _)
      x86_norm
      change RangeApart (stackPtr t + 8) 8 0x100102 16
      rw [hsp]
      exact h.toStorage.stackApart (offset := 8) (len := 8) (codeOffset := 0x102)
        (codeLen := 16) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x10e (by decide +kernel)
  md5_run_then Common.Instructions.MovStore.mov_m64_r64_effect_step 0x10010e 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 .none)
    (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100102) 12 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨storePre_of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 0 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := 0) (len := 8) (codeOffset := 0x10e)
        (codeLen := 4) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip (movM64R64Effect_components _ _ _ _)
      x86_norm
      change RangeApart (stackPtr t + 0) 8 0x100102 16
      rw [hsp]
      exact h.toStorage.stackApart (offset := 0) (len := 8) (codeOffset := 0x102)
        (codeLen := 16) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x112 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t h hE
  have h0 : (Operand.reg 14 : Operand 64).read s + 0#64 = stackPtr s + 256 := by
    rw [h.state, BitVec.add_zero]
  have h8 : (Operand.reg 14 : Operand 64).read s + 8#64 = stackPtr s + 264 := by
    rw [h.state, BitVec.add_assoc]
    rfl
  apply hE.weaken
  · x86_norm [effectB]
  · x86_norm [effectB, stackPtr]
    refine ⟨?_, ?_, .inl ⟨rfl, ?_⟩, .inr ⟨(BitVec.add_zero _).symm, ?_⟩⟩
    · exact congrArg (fun a ↦ (Operand.mem a : Operand 64).read s) h0.symm
    · exact congrArg (fun a ↦ (Operand.mem a : Operand 64).read s) h8.symm
    · exact congrArg (fun a ↦ (Operand.mem a : Operand 64).read s) h8.symm
    · exact congrArg (fun a ↦ (Operand.mem a : Operand 64).read s) h0.symm
  · intro i; cases i <;> x86_norm [effectB]
  · x86_norm [effectB, stackPtr]
    exact ⟨.inl rfl, .inr (BitVec.add_zero _)⟩

theorem effectA_avoids {s : RamState} (h : Storage .digestCopy s) :
    (effectA s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  simp only [effectA, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  exact h.stackAvoids x.1 (h.stackCover (offset := 16) (len := 4) (by decide) ha)
    (.inl ⟨x.2, hx⟩)

theorem effectB_avoids {s : RamState} (h : Storage .digestCopy s) :
    (effectB s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  simp only [effectB, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact h.stackAvoids x.1 (h.stackCover (offset := 8) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 0) (len := 8) (by decide)
      (by simpa only [BitVec.add_zero] using ha)) (.inl ⟨x.2, hx⟩)

theorem effectA_rsp {s t : RamState} (h : (effectA s).Holds s t) :
    stackPtr t = stackPtr s := by
  apply h.agrees.read (n := 64) (r := 4)
  simp [effectA, Effect.components]

theorem effectB_rsp {s t : RamState} (h : (effectB s).Holds s t) :
    stackPtr t = stackPtr s := by
  apply h.agrees.read (n := 64) (r := 4)
  simp [effectB, Effect.components]

theorem run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : ¬ InProgram boundary.rip) (h : RunPre 0x1000ef s) :
    ∃ fuel u t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effectA s).Holds s u ∧ (effectB u).Holds u t := by
  have hc : CodeIn (codeRange 0x1000ef bytesA) s :=
    program_text_slice hCode 0xef 19 (by decide +kernel)
  obtain ⟨n, u, ha, hr, _, he⟩ := executionA boundary hOutside s hReady hc h
  have huc := he.codeIn (effectA_avoids h.toStorage) hCode
  have hsp := effectA_rsp he
  have hu : RunPre 0x100102 u := by
    refine ⟨h.toStorage.of_agrees he.agrees hsp, he.rip, ?_⟩
    rw [he.agrees.read (n := 64) (r := 14) (by simp [effectA, Effect.components]), h.state, hsp]
  have hc' : CodeIn (codeRange 0x100102 bytesB) u :=
    program_text_slice huc 0x102 16 (by decide +kernel)
  obtain ⟨m, t, hb, hr', _, he'⟩ := executionB boundary hOutside u hr hc' hu
  exact ⟨n + m, u, t, ha.trans hb, hr', he'.codeIn (effectB_avoids hu.toStorage) huc, he, he'⟩

theorem effects_agrees {s u t : RamState} (hs : Storage .digestCopy s)
    (ha : (effectA s).Holds s u) (hb : (effectB u).Holds u t) :
    AgreesExcept (Kind.digestCopy.changes s) s t := by
  have hsp := effectA_rsp ha
  have h1 : AgreesExcept (Kind.digestCopy.changes s) s u := by
    apply agrees_changes ha.agrees
    · intro c hc hm
      simp only [effectA, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
    · intro x c hc hcover
      simp only [effectA, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      exact hs.localWithin (offset := 16) (len := 4) (by decide) hcover
  have h2 : AgreesExcept (Kind.digestCopy.changes s) u t := by
    rw [← Kind.changes_eq_of_rsp _ hsp (by decide)]
    apply agrees_changes hb.agrees
    · intro c hc hm
      simp only [effectB, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
    · intro x c hc hcover
      simp only [effectB, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      · exact (hs.of_agrees ha.agrees hsp).localWithin (offset := 8) (len := 8) (by decide) hcover
      · exact (hs.of_agrees ha.agrees hsp).localWithin (offset := 0) (len := 8) (by decide)
          (by simpa only [BitVec.add_zero] using hcover)
  exact (h1.trans h2).mono (by simp)

end Sha1.Proofs.Buffered.Finalize.Digest.Normalize
