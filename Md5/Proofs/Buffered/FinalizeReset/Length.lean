import Md5.Proofs.Buffered.FinalizeReset.Length.Execution
import Md5.Proofs.Buffered.FinalizeReset.Arithmetic

namespace Md5.Proofs.Buffered.FinalizeReset.Length

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block Md5.Spec.Program

set_option maxRecDepth 2048 in
theorem shift_position (n : Nat) (hn : n < 64) :
    ((BitVec.ofNat 32 n <<< 3).setWidth 64) = BitVec.ofNat 64 n <<< 3 := by
  have h : ∀ i : Fin 64,
      ((BitVec.ofNat 32 i.val <<< 3).setWidth 64) = BitVec.ofNat 64 i.val <<< 3 := by
    decide +kernel
  exact h ⟨n, hn⟩

theorem value_eq {s : RamState} {message : ByteArray}
    (hp : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64))
    (hb : (Operand.reg 14 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64) <<< 9) :
    value s = BitVec.ofNat 64 (message.size * 8) := by
  have hp32 : (Operand.reg 15 : Operand 32).read s = BitVec.ofNat 32 (message.size % 64) := by
    change ((Operand.reg 15 : Operand 64).read s).setWidth 32 = _
    rw [hp, BitVec.setWidth_ofNat_of_le (by decide)]
  rw [value, hp32, hb, shift_position _ (by omega), BitVec.or_comm]
  exact bitLength message.size

theorem effect_avoids {variant : Variant} {s : RamState} (h : Storage s variant) :
    (effect s variant).Avoids Extracted.programImage := by
  intro x hx c hc ha
  simp only [effect, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact h.stackAvoids x.1 (Export.stack_cover h (by cases variant <;> decide : 64 + 8 ≤ variant.stackBytes) ha) (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (Export.stack_cover h (by cases variant <;> decide : 152 + 8 ≤ variant.stackBytes) ha) (.inl ⟨x.2, hx⟩)

theorem run {variant : Variant} [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hStorage : Storage s variant) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = (variant.address 0x1008a2)) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect s variant).Holds s t := by
  have hBytes : CodeIn (codeRange (variant.address 0x1008a2) bytes) s :=
    by have haddr := program_text_slice hCode (0x8a2 + (if variant = .saved then 0 else 0x6b0)) 20 (by cases variant <;> decide +kernel); cases variant <;> exact haddr
  obtain ⟨fuel, t, hRun, hReady', _, hEffect⟩ :=
    execution boundary hOutside s hReady hBytes ⟨hStorage, hRip⟩
  exact ⟨fuel, t, hRun, hReady', hEffect.codeIn (effect_avoids hStorage) hCode, hEffect⟩

end Md5.Proofs.Buffered.FinalizeReset.Length
