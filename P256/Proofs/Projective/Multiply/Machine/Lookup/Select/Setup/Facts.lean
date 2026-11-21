import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Setup.Effect

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

open P256.Proofs.Program (CalleePre memoryRegion_contains_add stack_region_end)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open P256.Proofs.Field P256.Proofs.Program P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem setup_memory_component {s : RamState} {c : Component} {a : BitVec 64}
    (hc : c ∈ (setupEffect s).components) (ha : c.Covers a) :
    ∃ offset ∈ [8, 16, 24, 32, 40], ∃ i < 8,
      a = stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i := by
  simp only [setupEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨i, hi, rfl⟩ := ha
  · exact ⟨8, by simp, i, hi, rfl⟩
  · exact ⟨40, by simp, i, hi, rfl⟩
  · refine ⟨32, by simp, i, hi, ?_⟩
    apply congrArg (fun a : BitVec 64 => a + BitVec.ofNat 64 i)
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · refine ⟨24, by simp, i, hi, ?_⟩
    apply congrArg (fun a : BitVec 64 => a + BitVec.ofNat 64 i)
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · refine ⟨16, by simp, i, hi, ?_⟩
    apply congrArg (fun a : BitVec 64 => a + BitVec.ofNat 64 i)
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary}

theorem setup_writes_within (pre : CalleePre s boundary 0x114380 32 32 128) :
    WritesWithin (setupEffect s).components #v[Stack.region s 128] := by
  intro c hc a ha
  obtain ⟨offset, ho, i, hi, rfl⟩ := setup_memory_component hc ha
  have hb : offset ≤ 128 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨Stack.region s 128, by simp, ?_⟩
  apply memoryRegion_contains_add pre.stack.1 (len := 8) _ _ hi
  · rw [P256.Proofs.Program.stack_sub_toNat pre.stack hb]
    change (stackPtr s).toNat - 128 ≤ (stackPtr s).toNat - offset
    omega
  · rw [stack_region_end, P256.Proofs.Program.stack_sub_toNat pre.stack hb]
    have := (P256.Proofs.Program.stack_bounds pre.stack).1
    omega

omit [Bindings] in
theorem setup_return_word (effect : (setupEffect s).Holds s t) :
    (Operand.mem (stackPtr s) : Operand 64).read t = (X86Proofs.returnBoundary s).rip := by
  apply memLoad_congr
  intro i hi
  have hb : t.external[stackPtr s + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 i]? := by
    apply effect.agrees.byte
    intro c hc ha
    obtain ⟨offset, ho, j, hj, heq⟩ := setup_memory_component hc ha
    have hap : OffsetsApart (-BitVec.ofNat 64 offset) 8 0 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl <;>
        (unfold OffsetsApart; decide +kernel)
    have hn := hap.ne (stackPtr s) hj hi (by decide)
    apply hn
    simpa [BitVec.sub_eq_add_neg] using heq.symm
  simp only [memByte, PhysicalMemory.read, hb]

theorem setup_copied (pre : CalleePre s boundary 0x114380 32 32 128)
    (effect : (setupEffect s).Holds s t) :
    ∀ i < 32, t.external[scratch s + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rsi + BitVec.ofNat 64 i]? := by
  have hw := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  rcases hw with ⟨_, _, _, _, _, _, _, _, h0, h8, h16, h24⟩
  intro i hi
  have hread : memLoad t.external (scratch s + BitVec.ofNat 64 (i / 8 * 8)) 64 =
      memLoad s.external (s.regValue .rsi + BitVec.ofNat 64 (i / 8 * 8)) 64 := by
    have hdiv : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 := by omega
    rcases hdiv with h | h | h | h
    · simpa [h, memLoad_external, Write.AllHold] using h0
    · simpa [h, memLoad_external, Write.AllHold] using h8
    · simpa [h, memLoad_external, Write.AllHold] using h16
    · simpa [h, memLoad_external, Write.AllHold] using h24
  have hbytes := memByte_of_memLoad_eq hread (i % 8) (by omega)
  have hi' : i / 8 * 8 + i % 8 = i := by omega
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, hi'] at hbytes
  have hsource := pre.inputAllocated _
    (memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
  have hdest := effect.agrees.grow _
    ((P256.Proofs.Program.stack_sub_readable pre.stack (offset := 40) (len := 32) (by decide) (by decide)).mem i hi)
  obtain ⟨a, ha⟩ := hsource
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hdest
  change t.external[scratch s + BitVec.ofNat 64 i]? = some b at hb
  have hab : b = a := by
    simpa only [memByte, PhysicalMemory.read, hb, ha, Option.getD_some] using hbytes
  rw [hb, ha, hab]

theorem setup_state {select : Bool} (pre : BinaryFieldPre s boundary 0x114380 128)
    (choice : (s.regValue .rcx).setWidth 8 = if select then 1 else 0)
    (ready : ReadyToStep t) (effect : (setupEffect s).Holds s t) :
    CallState s t select := by
  have hw := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  rcases hw with ⟨_, hcx, hbx, hsp, hsi, hdi, h8, hsaved, _, _, _, _⟩
  have frame := effect.agrees.memoryWriteFrame (setup_writes_within pre.toCalleePre)
  refine {
    bindingsSupported := bindingsSupported_of_ready_agrees pre.bindingsSupported ready effect.agrees
    machine := P256.Proofs.Program.supportedMachine_of_ready_agrees pre.machine ready effect.agrees
    loaded := ?_
    allocated := effect.agrees.grow
    frame := frame
    registers := ?_
    directionFlag := effect.agrees.directionFlagClear (by component_not_mem) pre.directionFlag
    mxcsr := effect.agrees.mxcsr (by component_not_mem)
    fp87 := effect.agrees.fcw (by component_not_mem)
    rsp := hsp
    rbx := hbx
    savedRbx := hsaved
    returnWord := setup_return_word effect
    rip := effect.rip
    rdi := hdi
    rsi := hsi
    rdx := ?_
    rcx := hcx
    r8 := ?_
    copied := setup_copied pre.toCalleePre effect
    source := ?_ }
  · intro a b hfetch
    rw [frame a]
    · exact pre.loaded a b hfetch
    · intro region hr hin
      have hr' : region = Stack.region s 128 := by simpa using hr
      subst region
      exact pre.avoids _ (by simp) a hin (.inl ⟨b, hfetch⟩)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact effect.agrees.read (n := 64) (r := 5) (by simp [setupEffect, Effect.components])
      | exact effect.agrees.read (n := 64) (r := 12) (by simp [setupEffect, Effect.components])
      | exact effect.agrees.read (n := 64) (r := 13) (by simp [setupEffect, Effect.components])
      | exact effect.agrees.read (n := 64) (r := 14) (by simp [setupEffect, Effect.components])
      | exact effect.agrees.read (n := 64) (r := 15) (by simp [setupEffect, Effect.components])
  · exact effect.agrees.read (n := 64) (r := 2) (by simp [setupEffect, Effect.components])
  · change t.regValue .r8 = ((s.regValue .rcx).setWidth 32).setWidth 64 at h8
    rw [h8, BitVec.setWidth_setWidth_of_le _ (by decide),
      BitVec.setWidth_setWidth_of_le _ (by decide)]
    exact choice
  · intro i hi
    apply frame
    intro region hr hin
    have hr' : region = Stack.region s 128 := by simpa using hr
    subst region
    apply pre.rightStack _ _ hin
    exact memoryRegion_contains_add pre.rightBounded (Nat.le_refl _) (Nat.le_refl _) hi

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
