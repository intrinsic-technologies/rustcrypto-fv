import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Buffered.Update.ResetFirst.Prefix
import Md5.Proofs.Block.Rounds.Store.Compose
import Md5.Proofs.Buffered.FinalizeReset.Export.Bytes
import Md5.Proofs.Buffered.Update.Memory

namespace Md5.Proofs.Buffered.Finalize.Digest.Normalize

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

def bytes : List UInt8 :=
  [0x4c, 0x8b, 0x7c, 0x24, 0x68, 0x44, 0x0f, 0xb6, 0x64, 0x24, 0x57,
    0x49, 0x8b, 0x06, 0x49, 0x8b, 0x4e, 0x08, 0x48, 0x89, 0x4c, 0x24, 0x10,
    0x48, 0x89, 0x44, 0x24, 0x08]

structure RunPre (s : RamState) : Prop extends Storage .digest s where
  rip : s.RIP = 0x1000e4
  state : (Operand.reg 14 : Operand 64).read s = stackPtr s + 240

def effect (s : RamState) : Effect :=
  { rip := 0x100100
    writes := [
      ⟨(.reg 15 : Operand 64), (Operand.mem (stackPtr s + 104) : Operand 64).read s⟩,
      ⟨(.reg 12 : Operand 64), ((Operand.mem (stackPtr s + 87) : Operand 8).read s).setWidth 64⟩,
      ⟨(.reg 0 : Operand 64), (Operand.mem (stackPtr s + 240) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (Operand.mem (stackPtr s + 248) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 64),
        (Operand.mem (stackPtr s + 248) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64),
        (Operand.mem (stackPtr s + 240) : Operand 64).read s⟩] }

set_option maxHeartbeats 600000 in
theorem execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary RunPre (codeRange 0x1000e4 bytes) effect := by
  unfold bytes
  md5_run_begin mov_r64_m64_effect_step 0x1000e4 0x4c (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 104)) (by decide) (by decide) (by decide)
  case pre => intro s h; exact ⟨h.rip, (h.toStorage.stackWritable 104 8 (by decide)).readable⟩
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe9 (by decide +kernel)
  md5_run_then movzx_r_m8_rex_effect_step 0x1000e9 0x44 (by unfold RexPrefix; decide)
    32 (.inr rfl) (fun _ ↦ rfl) 4 (.sib 4 none 0 (.d8 87))
    (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1000e4) 5 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact (h.toStorage.stackWritable 87 1 (by decide)).readable
    · x86_avoid
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xef (by decide +kernel)
  md5_run_then mov_r64_m64_effect_step 0x1000ef 0x49 (by unfold RexWPrefix; decide)
    0 (.base 14 .none) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1000e4) 11 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      simp only [BitVec.add_zero]
      change MemReadable s ((Operand.reg 14 : Operand 64).read s) 8
      rw [h.state]
      exact (h.toStorage.stackWritable 240 8 (by decide)).readable
    · x86_avoid
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xf2 (by decide +kernel)
  md5_run_then mov_r64_m64_effect_step 0x1000f2 0x49 (by unfold RexWPrefix; decide)
    1 (.base 14 (.d8 8)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1000e4) 14 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      change MemReadable s ((Operand.reg 14 : Operand 64).read s + 8) 8
      rw [h.state]
      rw [BitVec.add_assoc]
      exact (h.toStorage.stackWritable 248 8 (by decide)).readable
    · x86_avoid
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xf6 (by decide +kernel)
  md5_run_then Stores.mov_m64_r64_effect_step 0x1000f6 0x48
    (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d8 16))
    (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1000e4) 18 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 16 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := 16) (len := 8) (codeOffset := 0xf6)
        (codeLen := 5) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip (movM64R64Effect_components _ _ _ _)
      change RangeApart (stackPtr t + 16) 8 0x1000e4 28
      rw [hsp]
      exact h.toStorage.stackApart (offset := 16) (len := 8) (codeOffset := 0xe4)
        (codeLen := 28) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xfb (by decide +kernel)
  md5_run_then Stores.mov_m64_r64_effect_step 0x1000fb 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 8))
    (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1000e4) 23 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 8 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := 8) (len := 8) (codeOffset := 0xfb)
        (codeLen := 5) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip (movM64R64Effect_components _ _ _ _)
      change RangeApart (stackPtr t + 8) 8 0x1000e4 28
      rw [hsp]
      exact h.toStorage.stackApart (offset := 8) (len := 8) (codeOffset := 0xe4)
        (codeLen := 28) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x100 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t h hE
  have h0 : (Operand.reg 14 : Operand 64).read s + 0#64 = stackPtr s + 240 := by
    rw [h.state, BitVec.add_zero]
  have h8 : (Operand.reg 14 : Operand 64).read s + 8#64 = stackPtr s + 248 := by
    rw [h.state, BitVec.add_assoc]
    rfl
  apply hE.weaken
  · x86_norm [effect]
  · x86_norm [effect, stackPtr]
    refine ⟨rfl, rfl, ?_, ?_, .inl ⟨rfl, ?_⟩, .inr ⟨rfl, ?_⟩⟩
    · exact congrArg (fun a ↦ (Operand.mem a : Operand 64).read s) h0.symm
    · exact congrArg (fun a ↦ (Operand.mem a : Operand 64).read s) h8.symm
    · exact congrArg (fun a ↦ (Operand.mem a : Operand 64).read s) h8.symm
    · exact congrArg (fun a ↦ (Operand.mem a : Operand 64).read s) h0.symm
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect, stackPtr]
    exact ⟨.inl rfl, .inr rfl⟩


theorem effect_rsp {s t : RamState} (h : (effect s).Holds s t) :
    stackPtr t = stackPtr s := by
  apply h.agrees.read (n := 64) (r := 4)
  simp [effect, Effect.components]

theorem effect_avoids {s : RamState} (h : Storage .digest s) :
    (effect s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact h.stackAvoids x.1 (h.stackCover (offset := 16) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 8) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)

theorem run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : ¬ InProgram boundary.rip) (h : RunPre s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect s).Holds s t := by
  have hc : CodeIn (codeRange 0x1000e4 bytes) s :=
    program_text_slice hCode 0xe4 28 (by decide +kernel)
  obtain ⟨fuel, t, ha, hr, _, he⟩ := execution boundary hOutside s hReady hc h
  exact ⟨fuel, t, ha, hr, he.codeIn (effect_avoids h.toStorage) hCode, he⟩

theorem effect_buffer {s t : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (hs : Storage .digest s) (h : (effect s).Holds s t)
    (hb : (⟨(stackPtr s + 240).toNat, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨buffer.toBytes.toArray⟩) :
    (⟨(stackPtr t + 8).toNat, 16⟩ : MemoryRegion).HasBytes
      t.external ⟨buffer.toBytes.toArray⟩ := by
  rw [effect_rsp h]
  have hw := h.writes
  simp only [effect, Write.AllHold] at hw
  have ha : ∀ i < 16, (t.external[stackPtr s + 8 + BitVec.ofNat 64 i]?).isSome :=
    fun i hi ↦ h.agrees.grow _ ((hs.stackWritable 8 16 (by decide)).bytes i hi)
  apply FinalizeReset.Export.hasBytes_of_halves
    (lo := (Operand.mem (stackPtr s + 240) : Operand 64).read s)
    (hi := (Operand.mem (stackPtr s + 248) : Operand 64).read s) ha hw.2.2.2.2.2
    (by rw [BitVec.add_assoc]; exact hw.2.2.2.2.1)
  · intro i
    simpa only [BitVec.add_zero, Nat.zero_add] using
      FinalizeReset.Export.digest_half hb 0 (by decide) i
  · intro i
    have hh := FinalizeReset.Export.digest_half hb 8 (by decide) i
    rw [BitVec.add_assoc] at hh
    exact hh

theorem effect_position {s t : RamState} {message : ByteArray}
    (h : (effect s).Holds s t) (ha : Absorbed (stackPtr s + 24) message s) :
    (Operand.reg 12 : Operand 64).read t = BitVec.ofNat 64 (message.size % 64) := by
  have hp := ha.position
  change (Operand.mem (stackPtr s + 24 + 63) : Operand 8).read s = _ at hp
  rw [BitVec.add_assoc] at hp
  have hp' : (Operand.mem (stackPtr s + 87) : Operand 8).read s =
      BitVec.ofNat 8 (message.size % 64) := hp
  have hw := h.writes.2.1
  change (Operand.reg 12 : Operand 64).read t =
    ((Operand.mem (stackPtr s + 87) : Operand 8).read s).setWidth 64 at hw
  rw [hw, hp']
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem effect_blocks {s t : RamState} {message : ByteArray}
    (h : (effect s).Holds s t) (ha : Absorbed (stackPtr s + 24) message s) :
    (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 (message.size / 64) := by
  have hb := ha.blocks
  change (Operand.mem (stackPtr s + 24 + 80) : Operand 64).read s = _ at hb
  rw [BitVec.add_assoc] at hb
  exact h.writes.1.trans hb


theorem effect_tail {s t : RamState} {message : ByteArray}
    (h : (effect s).Holds s t) (ha : Absorbed (stackPtr s + 24) message s) :
    (⟨(stackPtr t + 24).toNat, (tailBytes message).size⟩ : MemoryRegion).HasBytes
      t.external (tailBytes message) := by
  rw [effect_rsp h]
  apply hasBytes_of_copy ?_ ha.tail
  intro i hi
  have hn : (tailBytes message).size < 64 := tailBytes_lt message
  apply h.agrees.byte
  intro c hc hcover
  simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  all_goals obtain ⟨j, hj, hjx⟩ := hcover
  · exact (RangeApart.offsets (stackPtr s) (a := 24) (len := (tailBytes message).size)
      (b := 16) (count := 8) (by omega) (by decide) (by omega)) i hi j hj hjx
  · exact (RangeApart.offsets (stackPtr s) (a := 24) (len := (tailBytes message).size)
      (b := 8) (count := 8) (by omega) (by decide) (by omega)) i hi j hj hjx


theorem effect_agrees {s t : RamState} (h : (effect s).Holds s t) :
    AgreesExcept (Kind.digest.changes s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
  · intro a c hc hcover
    simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    all_goals refine ⟨.mem (stackPtr s + 8) 168, by simp [Kind.changes, Kind.localChanges], ?_⟩
    · apply FinalizeReset.Export.covers_shift (offset := 8) (len := 8) (by
        simpa [BitVec.add_assoc] using hcover) (by decide)
    · exact FinalizeReset.Export.covers_shift (offset := 0) (len := 8)
        (by simpa only [BitVec.add_zero] using hcover) (by decide)

end Md5.Proofs.Buffered.Finalize.Digest.Normalize
