import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Prologue
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Code
import P256.Proofs.Program.Copy.Return
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Program (CalleePre boundary_ne_program)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Program
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def epilogueComponents : List Component :=
  [.reg 0, .reg 3, .reg 4, .reg 5, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip]

structure EpiloguePre [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (entry : BitVec 64) : Prop where
  pre : CalleePre s boundary entry 32 32 160
  ready : ReadyToStep t
  loaded : ProgramLoaded t
  rip : t.RIP = entry + (0x5ab : BitVec 64)
  rsp : stackPtr t = stackPtr s - 160
  grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  saved : ∀ item ∈ P256.Proofs.Common.Encoding.Serialize.savedRegisters,
    memLoad t.external (stackPtr s - BitVec.ofNat 64 item.2) 64 = s.regValue item.1
  returnAddress : memLoad t.external (stackPtr s) 64 = memLoad s.external (stackPtr s) 64

theorem epilogue_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} (hentry : Entry entry) (h : EpiloguePre s t boundary entry) :
    ∃ u, Advances boundary 9 t u ∧ ReadyToStep u ∧
      AgreesExcept epilogueComponents t u ∧
      u.RIP = (returnBoundary s).rip ∧ stackPtr u = (returnBoundary s).rsp ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
        u.regValue r = s.regValue r) := by
  obtain ⟨t1, e1, ready1, effect1⟩ :=
    (mov_r64_r64_effect_step (entry + (0x5ab : BitVec 64)) 0x48 0xf8
      (by simp [RexWPrefix]) (by decide)).advances h.ready
      (code_slice hentry h.loaded 0x5ab _ (by decide) (by decide +kernel)) h.rip
      (by
        change (entry + (0x5ab : BitVec 64)) + 3 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact instruction_ne_boundary hentry h.pre.outerBoundary 0x5ae (by decide))
  change (movR64R64Effect (entry + (0x5ab : BitVec 64)) 0 7 t).Holds t t1 at effect1
  have m1 : t1.external = t.external := effect1.agrees.external (by simp [Component.Covers])
  have loaded1 : ProgramLoaded t1 := fun a b hb => m1 ▸ h.loaded a b hb
  have ip1 : t1.RIP = entry + (0x5ae : BitVec 64) := by
    have he : t1.RIP = (entry + (0x5ab : BitVec 64)) + (3 : BitVec 64) := effect1.rip
    rw [BitVec.add_assoc] at he
    exact he
  have sp1 : stackPtr t1 = stackPtr s - 160 :=
    (effect1.agrees.read (n := 64) (r := 4) (by simp)).trans h.rsp
  obtain ⟨t2, e2, ready2, effect2⟩ :=
    (add_r64_imm8_effect_step (entry + (0x5ae : BitVec 64)) 0x48 0xc4 0x70
      (by simp [RexWPrefix]) (by decide) (by decide)).advances ready1
      (code_slice hentry loaded1 0x5ae _ (by decide) (by decide +kernel)) ip1
      (by
        change (entry + (0x5ae : BitVec 64)) + 4 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact instruction_ne_boundary hentry h.pre.outerBoundary 0x5b2 (by decide))
  change (addR64Imm8Effect (entry + (0x5ae : BitVec 64)) 4 0x70 t1).Holds t1 t2 at effect2
  have m2 : t2.external = t.external :=
    (effect2.agrees.external (by simp [Component.Covers])).trans m1
  have loaded2 : ProgramLoaded t2 := fun a b hb => m2 ▸ h.loaded a b hb
  have ip2 : t2.RIP = entry + (0x5b2 : BitVec 64) := by
    have he : t2.RIP = (entry + (0x5ae : BitVec 64)) + (4 : BitVec 64) := effect2.rip
    rw [BitVec.add_assoc] at he
    exact he
  have sp2 : stackPtr t2 = stackPtr s - 48 := by
    have he : stackPtr t2 = stackPtr t1 + 112 := effect2.writes
    rw [he, sp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have read2 : MemReadable t2 (stackPtr t2) 8 := by
    rw [sp2]
    exact P256.Proofs.Program.readable_of_grow
      (P256.Proofs.Program.stack_sub_readable h.pre.stack (offset := 48) (by decide) (by decide))
      (fun a ha => m2 ▸ h.grow a ha)
  obtain ⟨t3, e3, ready3, effect3⟩ :=
    (pop_r64_effect_step (entry + (0x5b2 : BitVec 64)) 0x5b
      (by decide) (by decide)).advances ready2
      (code_slice hentry loaded2 0x5b2 _ (by decide) (by decide +kernel))
      ⟨ip2, read2⟩
      (by
        change (entry + (0x5b2 : BitVec 64)) + 1 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact instruction_ne_boundary hentry h.pre.outerBoundary 0x5b3 (by decide))
  change (popR64Effect (entry + (0x5b2 : BitVec 64)) 1 3 t2).Holds t2 t3 at effect3
  have f3 : AgreesExcept [.reg 3, .reg 4, .rip] t2 t3 := effect3.agrees
  have m3 : t3.external = t.external :=
    (f3.external (by simp [Component.Covers])).trans m2
  have loaded3 : ProgramLoaded t3 := fun a b hb => m3 ▸ h.loaded a b hb
  have ip3 : t3.RIP = entry + (0x5b3 : BitVec 64) := by
    have he : t3.RIP = (entry + (0x5b2 : BitVec 64)) + (1 : BitVec 64) := effect3.rip
    rw [BitVec.add_assoc] at he
    exact he
  have sp3 : stackPtr t3 = stackPtr s - 40 := by
    have he : stackPtr t3 = stackPtr t2 + 8 := effect3.writes.2
    rw [he, sp2]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have read3 : MemReadable t3 (stackPtr t3) 8 := by
    rw [sp3]
    exact P256.Proofs.Program.readable_of_grow
      (P256.Proofs.Program.stack_sub_readable h.pre.stack (offset := 40) (by decide) (by decide))
      (fun a ha => m3 ▸ h.grow a ha)
  obtain ⟨t4, e4, ready4, effect4⟩ :=
    (pop_r64_rex_effect_step (entry + (0x5b3 : BitVec 64)) 0x41 0x5c
      (by simp [RexPrefix]) (by decide) (by decide)).advances ready3
      (code_slice hentry loaded3 0x5b3 _ (by decide) (by decide +kernel))
      ⟨ip3, read3⟩
      (by
        change (entry + (0x5b3 : BitVec 64)) + 2 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact instruction_ne_boundary hentry h.pre.outerBoundary 0x5b5 (by decide))
  change (popR64Effect (entry + (0x5b3 : BitVec 64)) 2 12 t3).Holds t3 t4 at effect4
  have f4 : AgreesExcept [.reg 12, .reg 4, .rip] t3 t4 := effect4.agrees
  have m4 : t4.external = t.external :=
    (f4.external (by simp [Component.Covers])).trans m3
  have loaded4 : ProgramLoaded t4 := fun a b hb => m4 ▸ h.loaded a b hb
  have ip4 : t4.RIP = entry + (0x5b5 : BitVec 64) := by
    have he : t4.RIP = (entry + (0x5b3 : BitVec 64)) + (2 : BitVec 64) := effect4.rip
    rw [BitVec.add_assoc] at he
    exact he
  have sp4 : stackPtr t4 = stackPtr s - 32 := by
    have he : stackPtr t4 = stackPtr t3 + 8 := effect4.writes.2
    rw [he, sp3]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have read4 : MemReadable t4 (stackPtr t4) 8 := by
    rw [sp4]
    exact P256.Proofs.Program.readable_of_grow
      (P256.Proofs.Program.stack_sub_readable h.pre.stack (offset := 32) (by decide) (by decide))
      (fun a ha => m4 ▸ h.grow a ha)
  obtain ⟨t5, e5, ready5, effect5⟩ :=
    (pop_r64_rex_effect_step (entry + (0x5b5 : BitVec 64)) 0x41 0x5d
      (by simp [RexPrefix]) (by decide) (by decide)).advances ready4
      (code_slice hentry loaded4 0x5b5 _ (by decide) (by decide +kernel))
      ⟨ip4, read4⟩
      (by
        change (entry + (0x5b5 : BitVec 64)) + 2 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact instruction_ne_boundary hentry h.pre.outerBoundary 0x5b7 (by decide))
  change (popR64Effect (entry + (0x5b5 : BitVec 64)) 2 13 t4).Holds t4 t5 at effect5
  have f5 : AgreesExcept [.reg 13, .reg 4, .rip] t4 t5 := effect5.agrees
  have m5 : t5.external = t.external :=
    (f5.external (by simp [Component.Covers])).trans m4
  have loaded5 : ProgramLoaded t5 := fun a b hb => m5 ▸ h.loaded a b hb
  have ip5 : t5.RIP = entry + (0x5b7 : BitVec 64) := by
    have he : t5.RIP = (entry + (0x5b5 : BitVec 64)) + (2 : BitVec 64) := effect5.rip
    rw [BitVec.add_assoc] at he
    exact he
  have sp5 : stackPtr t5 = stackPtr s - 24 := by
    have he : stackPtr t5 = stackPtr t4 + 8 := effect5.writes.2
    rw [he, sp4]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have read5 : MemReadable t5 (stackPtr t5) 8 := by
    rw [sp5]
    exact P256.Proofs.Program.readable_of_grow
      (P256.Proofs.Program.stack_sub_readable h.pre.stack (offset := 24) (by decide) (by decide))
      (fun a ha => m5 ▸ h.grow a ha)
  obtain ⟨t6, e6, ready6, effect6⟩ :=
    (pop_r64_rex_effect_step (entry + (0x5b7 : BitVec 64)) 0x41 0x5e
      (by simp [RexPrefix]) (by decide) (by decide)).advances ready5
      (code_slice hentry loaded5 0x5b7 _ (by decide) (by decide +kernel))
      ⟨ip5, read5⟩
      (by
        change (entry + (0x5b7 : BitVec 64)) + 2 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact instruction_ne_boundary hentry h.pre.outerBoundary 0x5b9 (by decide))
  change (popR64Effect (entry + (0x5b7 : BitVec 64)) 2 14 t5).Holds t5 t6 at effect6
  have f6 : AgreesExcept [.reg 14, .reg 4, .rip] t5 t6 := effect6.agrees
  have m6 : t6.external = t.external :=
    (f6.external (by simp [Component.Covers])).trans m5
  have loaded6 : ProgramLoaded t6 := fun a b hb => m6 ▸ h.loaded a b hb
  have ip6 : t6.RIP = entry + (0x5b9 : BitVec 64) := by
    have he : t6.RIP = (entry + (0x5b7 : BitVec 64)) + (2 : BitVec 64) := effect6.rip
    rw [BitVec.add_assoc] at he
    exact he
  have sp6 : stackPtr t6 = stackPtr s - 16 := by
    have he : stackPtr t6 = stackPtr t5 + 8 := effect6.writes.2
    rw [he, sp5]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have read6 : MemReadable t6 (stackPtr t6) 8 := by
    rw [sp6]
    exact P256.Proofs.Program.readable_of_grow
      (P256.Proofs.Program.stack_sub_readable h.pre.stack (offset := 16) (by decide) (by decide))
      (fun a ha => m6 ▸ h.grow a ha)
  obtain ⟨t7, e7, ready7, effect7⟩ :=
    (pop_r64_rex_effect_step (entry + (0x5b9 : BitVec 64)) 0x41 0x5f
      (by simp [RexPrefix]) (by decide) (by decide)).advances ready6
      (code_slice hentry loaded6 0x5b9 _ (by decide) (by decide +kernel))
      ⟨ip6, read6⟩
      (by
        change (entry + (0x5b9 : BitVec 64)) + 2 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact instruction_ne_boundary hentry h.pre.outerBoundary 0x5bb (by decide))
  change (popR64Effect (entry + (0x5b9 : BitVec 64)) 2 15 t6).Holds t6 t7 at effect7
  have f7 : AgreesExcept [.reg 15, .reg 4, .rip] t6 t7 := effect7.agrees
  have m7 : t7.external = t.external :=
    (f7.external (by simp [Component.Covers])).trans m6
  have loaded7 : ProgramLoaded t7 := fun a b hb => m7 ▸ h.loaded a b hb
  have ip7 : t7.RIP = entry + (0x5bb : BitVec 64) := by
    have he : t7.RIP = (entry + (0x5b9 : BitVec 64)) + (2 : BitVec 64) := effect7.rip
    rw [BitVec.add_assoc] at he
    exact he
  have sp7 : stackPtr t7 = stackPtr s - 8 := by
    have he : stackPtr t7 = stackPtr t6 + 8 := effect7.writes.2
    rw [he, sp6]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have read7 : MemReadable t7 (stackPtr t7) 8 := by
    rw [sp7]
    exact P256.Proofs.Program.readable_of_grow
      (P256.Proofs.Program.stack_sub_readable h.pre.stack (offset := 8) (by decide) (by decide))
      (fun a ha => m7 ▸ h.grow a ha)
  obtain ⟨t8, e8, ready8, effect8⟩ :=
    (pop_r64_effect_step (entry + (0x5bb : BitVec 64)) 0x5d
      (by decide) (by decide)).advances ready7
      (code_slice hentry loaded7 0x5bb _ (by decide) (by decide +kernel))
      ⟨ip7, read7⟩
      (by
        change (entry + (0x5bb : BitVec 64)) + 1 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact instruction_ne_boundary hentry h.pre.outerBoundary 0x5bc (by decide))
  change (popR64Effect (entry + (0x5bb : BitVec 64)) 1 5 t7).Holds t7 t8 at effect8
  have f8 : AgreesExcept [.reg 5, .reg 4, .rip] t7 t8 := effect8.agrees
  have m8 : t8.external = t.external :=
    (f8.external (by simp [Component.Covers])).trans m7
  have loaded8 : ProgramLoaded t8 := fun a b hb => m8 ▸ h.loaded a b hb
  have ip8 : t8.RIP = entry + (0x5bc : BitVec 64) := by
    have he : t8.RIP = (entry + (0x5bb : BitVec 64)) + (1 : BitVec 64) := effect8.rip
    rw [BitVec.add_assoc] at he
    exact he
  have sp8 : stackPtr t8 = stackPtr s := by
    have he : stackPtr t8 = stackPtr t7 + 8 := effect8.writes.2
    rw [he, sp7]
    exact BitVec.sub_add_cancel _ _
  have top : stackTop t8 = (returnBoundary s).rip := by
    change memLoad t8.external (stackPtr t8) 64 = memLoad s.external (stackPtr s) 64
    rw [sp8, m8]
    exact h.returnAddress
  have readable : MemReadable t8 (stackPtr t8) 8 := by
    rw [sp8]
    simpa using P256.Proofs.Program.readable_of_grow
      (P256.Proofs.Program.stack_sub_readable h.pre.stack (offset := 0) (len := 8) (by decide) (by decide))
      (fun a ha => m8 ▸ h.grow a ha)
  obtain ⟨u, step9, ready9, effect9⟩ := ret_effect_step (entry + (0x5bc : BitVec 64))
    t8 ready8 (code_slice hentry loaded8 0x5bc _ (by decide) (by decide +kernel))
    ⟨⟨ip8, readable⟩, top ▸ P256.Proofs.Program.inProgram_low h.pre.returnInProgram⟩
  have rip9 : u.RIP = (returnBoundary s).rip := effect9.rip.trans top
  have rsp9 : stackPtr u = (returnBoundary s).rsp := by
    have he : stackPtr u = stackPtr t8 + 8 := effect9.writes
    rw [he, sp8]
    rfl
  have e9 : Advances boundary 1 t8 u := Advances.of_step step9 (.inl
    (rip9 ▸ boundary_ne_program h.pre.outerBoundary h.pre.returnInProgram))
  refine ⟨u, (((((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans e7).trans e8).trans e9,
    ready9, ?_, rip9, rsp9, ?_⟩
  · apply (((((((effect1.agrees.trans effect2.agrees).trans f3).trans f4).trans f5).trans f6).trans f7).trans f8 |>.trans effect9.agrees).mono
    simp [epilogueComponents, Effect.components, Write.component, Operand.component,
      movR64R64Effect, addR64Imm8Effect, retEffect]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (Operand.reg 3 : Operand 64).read u = _
      rw [effect9.agrees.read (by simp)]
      rw [f8.read (n := 64) (r := 3) (by simp)]
      rw [f7.read (n := 64) (r := 3) (by simp)]
      rw [f6.read (n := 64) (r := 3) (by simp)]
      rw [f5.read (n := 64) (r := 3) (by simp)]
      rw [f4.read (n := 64) (r := 3) (by simp)]
      have value : (Operand.reg 3 : Operand 64).read t3 =
          memLoad t2.external (stackPtr t2) 64 := effect3.writes.1
      rw [value, sp2, m2]
      exact h.saved (Syntax.Reg.rbx, 48) (by simp [P256.Proofs.Common.Encoding.Serialize.savedRegisters])
    · change (Operand.reg 5 : Operand 64).read u = _
      rw [effect9.agrees.read (by simp)]
      have value : (Operand.reg 5 : Operand 64).read t8 =
          memLoad t7.external (stackPtr t7) 64 := effect8.writes.1
      rw [value, sp7, m7]
      exact h.saved (Syntax.Reg.rbp, 8) (by simp [P256.Proofs.Common.Encoding.Serialize.savedRegisters])
    · change (Operand.reg 12 : Operand 64).read u = _
      rw [effect9.agrees.read (by simp)]
      rw [f8.read (n := 64) (r := 12) (by simp)]
      rw [f7.read (n := 64) (r := 12) (by simp)]
      rw [f6.read (n := 64) (r := 12) (by simp)]
      rw [f5.read (n := 64) (r := 12) (by simp)]
      have value : (Operand.reg 12 : Operand 64).read t4 =
          memLoad t3.external (stackPtr t3) 64 := effect4.writes.1
      rw [value, sp3, m3]
      exact h.saved (Syntax.Reg.r12, 40) (by simp [P256.Proofs.Common.Encoding.Serialize.savedRegisters])
    · change (Operand.reg 13 : Operand 64).read u = _
      rw [effect9.agrees.read (by simp)]
      rw [f8.read (n := 64) (r := 13) (by simp)]
      rw [f7.read (n := 64) (r := 13) (by simp)]
      rw [f6.read (n := 64) (r := 13) (by simp)]
      have value : (Operand.reg 13 : Operand 64).read t5 =
          memLoad t4.external (stackPtr t4) 64 := effect5.writes.1
      rw [value, sp4, m4]
      exact h.saved (Syntax.Reg.r13, 32) (by simp [P256.Proofs.Common.Encoding.Serialize.savedRegisters])
    · change (Operand.reg 14 : Operand 64).read u = _
      rw [effect9.agrees.read (by simp)]
      rw [f8.read (n := 64) (r := 14) (by simp)]
      rw [f7.read (n := 64) (r := 14) (by simp)]
      have value : (Operand.reg 14 : Operand 64).read t6 =
          memLoad t5.external (stackPtr t5) 64 := effect6.writes.1
      rw [value, sp5, m5]
      exact h.saved (Syntax.Reg.r14, 24) (by simp [P256.Proofs.Common.Encoding.Serialize.savedRegisters])
    · change (Operand.reg 15 : Operand 64).read u = _
      rw [effect9.agrees.read (by simp)]
      rw [f8.read (n := 64) (r := 15) (by simp)]
      have value : (Operand.reg 15 : Operand 64).read t7 =
          memLoad t6.external (stackPtr t6) 64 := effect7.writes.1
      rw [value, sp6, m6]
      exact h.saved (Syntax.Reg.r15, 16) (by simp [P256.Proofs.Common.Encoding.Serialize.savedRegisters])

end P256.Proofs.Sec1.SquareRoot.Montgomery
