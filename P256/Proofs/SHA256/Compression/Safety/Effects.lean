import P256.Proofs.SHA256.Compression.Safety.Basic
import P256.Proofs.Common.SHA256.Compression.Frame
import P256.Proofs.Program.Entry

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Safety

open P256.Proofs.Common.SHA256.Compression

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

section

variable [Bindings]

theorem next_read (instruction : CheckedInstruction) (model : RamState)
    {n : Nat} (op : Operand n) :
    op.read (instruction.next model) = op.read (applyWrites model (instruction.effect model).writes) := by
  change op.read { (instruction.effect model).after model true with RIP := _ } = _
  have h : op.read { (instruction.effect model).after model true with RIP := (instruction.effect model).rip } =
      op.read ((instruction.effect model).after model true) := by cases op <;> rfl
  exact h.trans (Effect.read_after _ _ _ _)

theorem next_register {initial model : RamState} {before after : Position}
    (instruction : CheckedInstruction) (state : State initial model before)
    (dst : BitVec 5) (value : BitVec 64)
    (writes : (instruction.effect model).writes = [⟨.reg dst, value⟩])
    (rip : (instruction.effect model).rip = after.rip)
    (rsp : dst ≠ 4)
    (saved : after.saved = true → before.saved = true)
    (pointers : ∀ r ∈ after.pointers,
      (dst = r ∧ value = initial.regValue .rsi) ∨ (dst ≠ r ∧ r ∈ before.pointers)) :
    State initial (instruction.next model) after := by
  constructor
  · exact rip
  · rw [next_read, writes]
    simpa only [applyWrites_cons, applyWrites_nil, Write.apply_mk,
      Operand.read_reg_write_reg, ite_eq_right rsp] using state.rsp
  · intro hs
    rw [next_read, writes]
    simpa only [applyWrites_cons, applyWrites_nil, Write.apply_mk,
      Operand.read_mem_write_reg] using state.saved (saved hs)
  · intro r hr
    rw [next_read, writes]
    simp only [applyWrites_cons, applyWrites_nil, Write.apply_mk, Operand.read_reg_write_reg]
    rcases pointers r hr with ⟨same, value⟩ | ⟨different, member⟩
    · simp only [same, ↓reduceIte, BitVec.setWidth_eq, value]
    · simpa only [ite_eq_right different] using state.pointers r member

theorem next_memory {initial model : RamState} {before after : Position}
    (instruction : CheckedInstruction) (state : State initial model before)
    {n : Nat} (addr : BitVec 64) (value : BitVec n)
    (writes : (instruction.effect model).writes = [⟨.mem addr, value⟩])
    (rip : (instruction.effect model).rip = after.rip)
    (saved : after.saved = true →
      memLoad (memStore model.external addr value) (stackPtr initial + 24) 64 = initial.regValue .rsi)
    (pointers : ∀ r ∈ after.pointers, r ∈ before.pointers) :
    State initial (instruction.next model) after := by
  constructor
  · exact rip
  · rw [next_read, writes]
    simpa only [applyWrites_cons, applyWrites_nil, Write.apply_mk,
      Operand.read_reg_write_mem'] using state.rsp
  · intro hs
    rw [next_read, writes]
    simpa only [applyWrites_cons, applyWrites_nil, Write.apply_mk,
      Operand.read_mem_write_mem] using saved hs
  · intro r hr
    rw [next_read, writes]
    simpa only [applyWrites_cons, applyWrites_nil, Write.apply_mk,
      Operand.read_reg_write_mem'] using state.pointers r (pointers r hr)

end

theorem Footprint.effect {initial : RamState} (effect : Effect)
    (writes : Footprint initial (effect.writes.map Write.component)) :
    Footprint initial effect.components := by
  apply Footprint.append (Footprint.append writes ?_) ?_
  · cases effect.flags <;> constructor <;>
      simp [blockComponents, Component.Covers, Component.isMem]
  · constructor <;> simp [blockComponents, Component.Covers, Component.isMem]

theorem Footprint.register (initial : RamState) (dst : BitVec 5)
    (allowed : Component.reg dst ∈ blockComponents initial) :
    Footprint initial [.reg dst] := by
  constructor
  · intro c hc _
    obtain rfl := List.mem_singleton.mp hc
    exact allowed
  · simp [Component.Covers]

theorem Footprint.memoryRange (initial : RamState) (off count : Nat)
    (bound : off + count ≤ 192 ∨ 208 ≤ off ∧ off + count ≤ 288) :
    Footprint initial [.mem (stackPtr initial + BitVec.ofNat 64 off) count] := by
  constructor
  · simp [Component.isMem]
  · intro x c hc covers
    rcases List.mem_singleton.mp hc with rfl
    obtain ⟨i, hi, rfl⟩ := covers
    rcases bound with bound | ⟨lo, bound⟩
    · refine ⟨.mem (stackPtr initial) 192, by simp [blockComponents], off + i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.add_assoc]
    · refine ⟨.mem (stackPtr initial + 208) 80, by simp [blockComponents], off - 208 + i, by omega, ?_⟩
      have h : off = 208 + (off - 208) := by omega
      have he : BitVec.ofNat 64 off = 208 + BitVec.ofNat 64 (off - 208) := by
        calc
          BitVec.ofNat 64 off = BitVec.ofNat 64 (208 + (off - 208)) := congrArg _ h
          _ = _ := BitVec.ofNat_add _ _
      rw [he]
      simp only [BitVec.ofNat_add, BitVec.add_assoc]

theorem block_covers {initial : RamState} {c : Component} {x : BitVec 64}
    (member : c ∈ blockComponents initial) (covers : c.Covers x) :
    ∃ i < 288, x = stackPtr initial + BitVec.ofNat 64 i := by
  simp only [blockComponents, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact False.elim covers
  · obtain ⟨i, hi, hx⟩ := covers
    exact ⟨i, by omega, hx⟩
  · obtain ⟨i, hi, hx⟩ := covers
    refine ⟨208 + i, by omega, ?_⟩
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using hx

theorem Footprint.avoids {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (pre : BlockPre initial hash block) (effect : Effect)
    (footprint : Footprint initial effect.components) :
    effect.Avoids Extracted.programSections.toCodeMap := by
  intro x hx c hc covers
  obtain ⟨c', hc', covers'⟩ := footprint.memory x.1 c hc covers
  obtain ⟨i, hi, addr⟩ := block_covers hc' covers'
  apply pre.frameAvoids i hi
  refine ⟨x.2, ?_⟩
  rw [← addr]
  exact P256.Proofs.Program.programSections_fetchByte_of_mem hx

theorem frame_writable8 {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (pre : BlockPre initial hash block) (off : Nat)
    (bound : off + 8 ≤ 288) (aligned : off % 8 = 0) :
    MemWritable initial (stackPtr initial + BitVec.ofNat 64 off) 8 := by
  have read := frame_readable pre.stack off 8 bound
  have addr := frame_offset_toNat pre.stack off 8 bound
  have stackAlign := pre.stack.align
  have bottom := pre.stack.tables
  change MemWritable initial (rspOf initial + BitVec.ofNat 64 off) 8
  refine ⟨read.low, read.mem, ?_⟩
  unfold PageTableEntriesApart
  rw [addr]
  omega

end P256.Proofs.SHA256.Compression.Safety
