import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Prologue
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Common
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Interface
import P256.Proofs.Program.Frame
import P256.Proofs.Common.Instructions.CrossPageStore.Range

set_option autoImplicit false

open P256.Proofs.Program (CalleePre memoryRegion_contains_add memoryRegion_memReadable)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Program
open P256.Proofs.Common.Field.SquareRoot.Multiply
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {entry : BitVec 64}

omit [Bindings] in
theorem scratch_address (s : RamState) {offset : Nat} (ho : offset ≤ 160) :
    stackPtr s - 160 + BitVec.ofNat 64 offset =
      stackPtr s - BitVec.ofNat 64 (160-offset) := by
  have he : (160 : BitVec 64) = BitVec.ofNat 64 (160-offset) + BitVec.ofNat 64 offset := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel ho]
    rfl
  rw [he, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem scratch_inside (pre : CalleePre s boundary entry 32 32 160)
    {offset len : Nat} (h : offset+len ≤ 160) {a : BitVec 64}
    (ha : (Component.mem (stackPtr s-160+BitVec.ofNat 64 offset) len).Covers a) :
    (Stack.region s 160).Contains a.toNat := by
  rw [scratch_address s (by omega)] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  apply memoryRegion_contains_add pre.stack.1 (len := len) _ _ hi
  · rw [stack_sub_toNat pre.stack (by omega)]
    change (stackPtr s).toNat - 160 ≤ (stackPtr s).toNat - (160-offset)
    omega
  · rw [stack_region_end, stack_sub_toNat pre.stack (by omega)]
    have := (stack_bounds pre.stack).1
    omega

theorem output_writable (pre : CalleePre s boundary entry 32 32 160)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi) 32 := by
  have hr : MemReadable t (s.regValue .rdi) 32 :=
    P256.Proofs.Program.readable_of_grow
      (memoryRegion_memReadable pre.outputBounded pre.outputAllocated
        (Nat.le_refl _) (Nat.le_refl _)) grow
  refine ⟨hr, tables_of_not_reserved (by decide) hr.low ?_⟩
  intro i hi hin
  exact pre.avoids _ (by simp) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) (.inr hin)

theorem memoryPre (pre : CalleePre s boundary entry 32 32 160)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (rsp : stackPtr t = stackPtr s-160) (rdi : t.regValue .rdi = s.regValue .rdi) :
    Reduction.MemoryPre t := by
  constructor
  · intro offset len hbound halign hlen
    rw [rsp, scratch_address s (by omega)]
    have hw : MemWritable t (stackPtr s-BitVec.ofNat 64 (160-offset)) 8 :=
      P256.Proofs.Program.writable_of_grow (stack_sub_writable8 pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by omega) (by omega)) grow
    exact ⟨by have := hw.low; omega,
      fun i hi => hw.mem i (by omega), by rcases hw.tables with h | h <;> omega⟩
  · rw [rdi]
    exact output_writable pre grow
  · intro a ha hin
    rw [rsp] at ha
    have ha' : (Component.mem (stackPtr s-160+BitVec.ofNat 64 0) 112).Covers a := by
      simpa only [BitVec.add_zero] using ha
    exact pre.avoids _ (by simp) _ (scratch_inside pre (by decide) ha') (.inl hin)
  · intro a ha hin
    rw [rdi] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact pre.avoids _ (by simp) _
      (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) (.inl hin)

def frame (s : RamState) : List Component :=
  (List.range 16).map (fun i => Component.reg (BitVec.ofNat 5 i)) ++
    [.flags, .rip, .mem (stackPtr s-160) 160, .mem (s.regValue .rdi) 32]

theorem frame_within (pre : CalleePre s boundary entry 32 32 160) :
    WritesWithin (frame s) #v[registerRegion s .rdi 32, Stack.region s 160] := by
  intro c hc a ha
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    exact ha.elim
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ha.elim
    · exact ha.elim
    · refine ⟨Stack.region s 160, by simp, ?_⟩
      apply scratch_inside pre (offset := 0) (len := 160) (by decide)
      simpa only [BitVec.add_zero] using ha
    · obtain ⟨i, hi, rfl⟩ := ha
      exact ⟨registerRegion s .rdi 32, by simp,
        memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi⟩

theorem loaded_of_frame (pre : CalleePre s boundary entry 32 32 160)
    (h : AgreesExcept (frame s) s t) : ProgramLoaded t := by
  intro a b hb
  rw [h.memory a]
  · exact pre.loaded a b hb
  · intro c hc ha
    obtain ⟨r, hr, hin⟩ := frame_within pre c hc a ha
    apply pre.avoids r _ a hin (.inl ⟨b, hb⟩)
    simpa using hr

omit [Bindings] in
theorem prologue_frame {s t : RamState}
    (h : AgreesExcept (prologueComponents s) s t) : AgreesExcept (frame s) s t := by
  apply h.widen
  · intro c hc hm
    simp only [prologueComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [frame, List.range_succ, Component.isMem]
  · intro a c hc ha
    simp only [prologueComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals
      refine ⟨.mem (stackPtr s-160) 160, by simp [frame], ?_⟩
      obtain ⟨i, hi, rfl⟩ := ha
    · exact ⟨152+i, by omega, by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rw [scratch_address s (offset := 152) (by decide)]
        rfl⟩
    · exact ⟨144+i, by omega, by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rw [scratch_address s (offset := 144) (by decide)]
        rfl⟩
    · exact ⟨136+i, by omega, by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rw [scratch_address s (offset := 136) (by decide)]
        rfl⟩
    · exact ⟨128+i, by omega, by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rw [scratch_address s (offset := 128) (by decide)]
        rfl⟩
    · exact ⟨120+i, by omega, by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rw [scratch_address s (offset := 120) (by decide)]
        rfl⟩
    · exact ⟨112+i, by omega, by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rw [scratch_address s (offset := 112) (by decide)]
        rfl⟩

omit [Bindings] in
theorem components_frame {s t u : RamState}
    (rsp : stackPtr t = stackPtr s-160) (rdi : t.regValue .rdi = s.regValue .rdi)
    (h : AgreesExcept (Reduction.components t) t u) : AgreesExcept (frame s) t u := by
  apply h.widen
  · intro c hc hm
    simp only [Reduction.components, Reduction.scratchComponents, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals simp_all [frame, List.range_succ, Component.isMem]
  · intro a c hc ha
    simp only [Reduction.components, Reduction.scratchComponents, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    · rw [rsp] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact ⟨.mem (stackPtr s-160) 160, by simp [frame], i, by omega, rfl⟩
    · rw [rdi] at ha
      exact ⟨.mem (s.regValue .rdi) 32, by simp [frame], ha⟩

theorem input_bytes (pre : Field.BinaryFieldPre s boundary entry 160)
    (h : AgreesExcept (frame s) s t) {i : Nat} (hi : i < 32) :
    t.external[s.regValue .rsi+BitVec.ofNat 64 i]? =
      s.external[s.regValue .rsi+BitVec.ofNat 64 i]? := by
  apply h.memoryWriteFrame (frame_within pre.toCalleePre)
  intro r hr
  have hin : (registerRegion s .rsi 32).Contains
      (s.regValue .rsi+BitVec.ofNat 64 i).toNat :=
    memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi
  have hr' : r = registerRegion s .rdi 32 ∨ r = Stack.region s 160 := by simpa using hr
  rcases hr' with rfl | rfl
  · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide) _ hin
  · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ hin

theorem right_bytes (pre : Field.BinaryFieldPre s boundary entry 160)
    (h : AgreesExcept (frame s) s t) {i : Nat} (hi : i < 32) :
    t.external[s.regValue .rdx+BitVec.ofNat 64 i]? =
      s.external[s.regValue .rdx+BitVec.ofNat 64 i]? := by
  apply h.memoryWriteFrame (frame_within pre.toCalleePre)
  intro r hr
  have hin : (registerRegion s .rdx 32).Contains
      (s.regValue .rdx+BitVec.ofNat 64 i).toNat :=
    memoryRegion_contains_add pre.rightBounded (Nat.le_refl _) (Nat.le_refl _) hi
  have hr' : r = registerRegion s .rdi 32 ∨ r = Stack.region s 160 := by simpa using hr
  rcases hr' with rfl | rfl
  · exact pre.rightOutput _ hin
  · exact pre.rightStack _ hin

theorem modulus_bytes (pre : MontgomeryPre s boundary entry) (h : AgreesExcept (frame s) s t)
    {i : Nat} (hi : i < 32) :
    t.external[s.regValue .rcx+BitVec.ofNat 64 i]? =
      s.external[s.regValue .rcx+BitVec.ofNat 64 i]? := by
  apply h.memoryWriteFrame (frame_within pre.toCalleePre)
  intro r hr
  have hin : (registerRegion s .rcx 32).Contains
      (s.regValue .rcx+BitVec.ofNat 64 i).toNat :=
    memoryRegion_contains_add pre.modulusBounded (Nat.le_refl _) (Nat.le_refl _) hi
  have hr' : r = registerRegion s .rdi 32 ∨ r = Stack.region s 160 := by simpa using hr
  rcases hr' with rfl | rfl
  · exact pre.modulusOutput _ hin
  · exact pre.modulusStack _ hin

end P256.Proofs.Sec1.SquareRoot.Montgomery
