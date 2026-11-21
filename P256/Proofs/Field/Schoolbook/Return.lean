import P256.Proofs.Field.Schoolbook.Execution
import P256.Proofs.Field.Schoolbook.Epilogue
import P256.Proofs.Field.Schoolbook.Store

set_option autoImplicit false

open P256.Proofs.Common.Field.SquareRoot.Multiply (prologueComponents savedMemory savedMemory_registers savedMemory_return)
open P256.Proofs.Program (CalleePre CalleeResult inProgram_of_textOffset memoryRegion_contains_add memoryRegion_memReadable programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Program
open P256.Proofs.Field.Montgomery (wordBase)

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s entry t u : RamState} {boundary : ReturnBoundary}
  {ctx : ExecutionContext s boundary entry}

theorem output_contains (pre : SchoolbookPre s boundary)
    (c : BitVec 64) {len i : Nat} (hc : c.toNat+len ≤ 64) (hi : i < len) :
    (registerRegion s .rdi 64).Contains (s.regValue .rdi+c+BitVec.ofNat 64 i).toNat := by
  have h := memoryRegion_contains_add pre.outputBounded (len := 64)
    (Nat.le_refl _) (Nat.le_refl _) (by omega : c.toNat+i < 64)
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.add_assoc] using h

theorem BodyState.saved_memory (h : BodyState ctx t) {off : Nat} (hoff : off ≤ 48) :
    memLoad t.external (stackPtr s-BitVec.ofNat 64 off) 64 =
      memLoad (savedMemory s) (stackPtr s-BitVec.ofNat 64 off) 64 := by
  have hc : OffsetsApart 0 88 (BitVec.ofNat 64 (136-off)) 8 := by
    change OffsetsApart 0#64 88 (BitVec.ofNat 64 (136-off)) 8
    simp only [OffsetsApart, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hh := scratch_saved h.agrees hc
  have he : stackPtr s-136+BitVec.ofNat 64 (136-off) = stackPtr s-BitVec.ofNat 64 off := by
    rw [← BitVec.ofNat_sub_ofNat_of_le 136 off (by omega) (by omega)]
    change (stackPtr s-136#64)+(136#64-BitVec.ofNat 64 off) = _
    rw [BitVec.sub_eq_add_neg (136#64), ← BitVec.add_assoc, BitVec.sub_add_cancel,
      ← BitVec.sub_eq_add_neg]
  rw [he, ctx.memory] at hh
  exact hh

theorem BodyState.saved_registers (h : BodyState ctx t) :
    ∀ item ∈ P256.Proofs.Common.Encoding.Serialize.savedRegisters,
      (Operand.mem (stackPtr s-BitVec.ofNat 64 item.2) : Operand 64).read t = s.regValue item.1 := by
  intro item hi
  have hn : item.2 ≤ 48 := by
    simp only [P256.Proofs.Common.Encoding.Serialize.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact (h.saved_memory hn).trans (savedMemory_registers s item hi)

theorem BodyState.return_word (h : BodyState ctx t) :
    (Operand.mem (stackPtr s) : Operand 64).read t = (returnBoundary s).rip := by
  have hh := h.saved_memory (off := 0) (by decide)
  change memLoad t.external (stackPtr s-0#64) 64 = memLoad (savedMemory s) (stackPtr s-0#64) 64 at hh
  simp only [BitVec.sub_zero] at hh
  exact hh.trans (savedMemory_return s)

theorem BodyState.storePre (h : BodyState ctx t) (rip : t.RIP = 0x11cb43) : StorePre t := by
  have dest : (Operand.reg 7 : Operand 64).read t = s.regValue .rdi := h.destination
  have hr : MemReadable t (s.regValue .rdi) 64 := readable_of_grow
    (memoryRegion_memReadable ctx.pre.outputBounded ctx.pre.outputAllocated
      (Nat.le_refl _) (Nat.le_refl _)) h.grow
  have hw : P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi) 64 := by
    refine ⟨hr, tables_of_not_reserved (by decide) hr.low ?_⟩
    intro i hi hin
    exact ctx.pre.avoids _ (by simp) _
      (memoryRegion_contains_add ctx.pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) (.inr hin)
  refine ⟨rip, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    all_goals exact (scratch_slot_writable ctx.pre h.rsp h.grow _ (by decide)).readable
  · intro c hc
    rw [dest]
    have hn : c.toNat+8 ≤ 64 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hw.add c.toNat hn
  · intro c hc i hi j hj he
    rw [dest] at he
    have hn : c.toNat+8 ≤ 64 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hin := output_contains ctx.pre c hn hi
    apply ctx.pre.avoids _ (by simp) _ hin
    rw [he]
    left
    change InProgram ((Extracted.textAddress+BitVec.ofNat 64 0x1cb43)+BitVec.ofNat 64 j)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (0x1cb43+j) (by omega)
  · intro i hi j hj he
    rw [dest] at he
    have hout := memoryRegion_contains_add ctx.pre.outputBounded (len := 64)
      (Nat.le_refl _) (Nat.le_refl _) (show i < 64 by omega)
    have hstack := scratch_slot_contains ctx.pre h.rsp 24 (by decide) hj
    rw [← he] at hstack
    exact ctx.pre.separation (1 : Fin 3) 2 (by decide) _ hout hstack

theorem store_within (h : BodyState ctx t) :
    WritesWithin (storeEffect t).components #v[registerRegion s .rdi 64] := by
  intro c hc a ha
  simp only [storeEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, or_assoc, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact False.elim ha
  all_goals obtain ⟨i, hi, rfl⟩ := ha
  all_goals refine ⟨registerRegion s .rdi 64, by simp, ?_⟩
  all_goals change (registerRegion s .rdi 64).Contains _
  all_goals rw [show (Operand.reg 7 : Operand 64).read t = s.regValue .rdi from h.destination]
  · exact memoryRegion_contains_add ctx.pre.outputBounded (len := 64)
      (Nat.le_refl _) (Nat.le_refl _) (by omega)
  · exact output_contains ctx.pre 8 (by decide) hi
  · exact output_contains ctx.pre 16 (by decide) hi
  · exact output_contains ctx.pre 24 (by decide) hi
  · exact output_contains ctx.pre 32 (by decide) hi
  · exact output_contains ctx.pre 40 (by decide) hi
  · exact output_contains ctx.pre 48 (by decide) hi
  · exact output_contains ctx.pre 56 (by decide) hi

theorem output_frame_stackWord (pre : SchoolbookPre s boundary)
    (frame : MemoryWriteFrame t u #v[registerRegion s .rdi 64]) {off : Nat} (ho : off ≤ 136) :
    memLoad u.external (stackPtr s-BitVec.ofNat 64 off) 64 =
      memLoad t.external (stackPtr s-BitVec.ofNat 64 off) 64 := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun x : Option UInt8 => x.getD 0)
  apply frame
  intro region hr hin
  have he : region = registerRegion s .rdi 64 := by simpa using hr
  subst region
  exact pre.separation (1 : Fin 3) 2 (by decide) _ hin
    (stack_contains pre ho (by omega) hi)

theorem finish (h : BodyState ctx t) (rip : t.RIP = 0x11cb43) :
    ∃ u, CalleeResult s u boundary 64 136 ∧
      Bytes u.external (s.regValue .rdi) 64
        (fun i => UInt8.ofNat (packEight ((outputLimbs t).map BitVec.toNat) / 256^i % 256)) := by
  have hcode : CodeIn (codeRange 0x11cb43 storeBytes) t :=
    programText_slice (programLoaded_codeIn h.loaded) 0x1cb43 _
      (by decide) (by decide +kernel)
  obtain ⟨fuel, v, run, ready, _, he⟩ :=
    store_correct boundary ctx.pre.outerBoundary t h.ready hcode (h.storePre rip)
  have vf := he.agrees.memoryWriteFrame (store_within h)
  have sf : MemoryWriteFrame t v #v[registerRegion s .rdi 64, Stack.region s 136] := by
    intro a ha
    apply vf a
    intro r hr hin
    have hr' : r = registerRegion s .rdi 64 := by simpa using hr
    subst r
    exact ha _ (by simp) hin
  have wholeFrame := memoryWriteFrame_trans h.frame sf
  have wholeAgrees := (ctx.agrees.trans h.agrees).trans he.agrees
  have ep : EpiloguePre s v (prologueComponents s ++ scratchComponents (stackPtr s-136) ++ (storeEffect t).components) := by
    refine ⟨ready, ?_, he.rip,
      ?_, ?_, ?_, ?_, wholeAgrees⟩
    · intro a b ha
      rw [wholeFrame a]
      · exact ctx.pre.loaded a b ha
      · intro r hr hc
        exact ctx.pre.avoids r (by simpa using hr) a hc (.inl ⟨b, ha⟩)
    · exact (he.agrees.read (n := 64) (r := 4) (by simp [storeEffect, Effect.components])).trans h.rsp
    · exact (he.agrees.read (n := 64) (r := 7) (by simp [storeEffect, Effect.components])).trans h.destination
    · intro item hi
      have hn : item.2 ≤ 136 := by
        simp only [P256.Proofs.Common.Encoding.Serialize.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (output_frame_stackWord ctx.pre vf hn).trans (h.saved_registers item hi)
    · have hh := output_frame_stackWord ctx.pre vf (off := 0) (by decide)
      change memLoad v.external (stackPtr s-0#64) 64 = memLoad t.external (stackPtr s-0#64) 64 at hh
      simp only [BitVec.sub_zero] at hh
      exact hh.trans h.return_word
  obtain ⟨u, eu⟩ := epilogue_correct ctx.pre ep
  obtain ⟨prior, oldrun⟩ := h.execution
  refine ⟨u, ⟨⟨prior+fuel+9, (oldrun.trans run).trans eu.execution⟩,
    eu.rip, eu.rsp, eu.bindingsSupported, eu.machine, eu.calleeSaved,
    eu.directionFlag, eu.mxcsr, eu.fp87, ?_, eu.loaded,
    (wholeAgrees.trans eu.agrees).grow⟩, ?_⟩
  · intro a ha
    rw [eu.external]
    exact wholeFrame a ha
  · rw [eu.external, ← h.destination]
    apply storeEffect_bytes he ((outputLimbs t).map BitVec.toNat)
    · intro i
      change ((outputLimbs t).map BitVec.toNat)[i.val] < wordBase
      rw [Vector.getElem_map]
      exact ((outputLimbs t)[i.val]).isLt
    · intro i hi
      have hr : MemReadable t (s.regValue .rdi) 64 := readable_of_grow
        (memoryRegion_memReadable ctx.pre.outputBounded ctx.pre.outputAllocated
          (Nat.le_refl _) (Nat.le_refl _)) h.grow
      change (t.external[t.regValue .rdi+BitVec.ofNat 64 i]?).isSome
      rw [h.destination]
      exact hr.mem i hi
    · intro j hj
      simp only [Vector.getElem_map, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end P256.Proofs.Field.Schoolbook
