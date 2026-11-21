import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Start.Memory
import P256.Proofs.Verifying.Combination.Naf.Machine.LoopPrefix
import P256.Proofs.Verifying.Combination.Naf.Machine.Constants
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Program (writable_of_grow stack_sub_writable8)

theorem start_recoding [Bindings] {s : RamState} {boundary : ReturnBoundary} {n : Nat}
    (pre : Pre s boundary) (input : Nat256At s (s.regValue .rdx) n)
    (zeroes : Bytes s.external (s.regValue .rdi) 257 (fun _ => 0)) :
    ∃ fuel w, Advances boundary fuel s w ∧ LoopState s w n 0 0 0 [] := by
  obtain ⟨n0, t, run0, initial, _, zeroT⟩ := initialize_correct pre input zeroes
  have addr24 := stack_address initial.rsp (offset := 24) (by decide)
  have prefixPre : LoopPrefixPre t := by
    refine ⟨initial.rip, ?_, ?_⟩
    · change MemWritable t (stackPtr t+24#64) 8
      rw [addr24]
      exact writable_of_grow (stack_sub_writable8 pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide)) initial.allocated
    · exact stack_code pre.toCalleePre initial.toFrameState (offset := 24) (len := 8)
        (codeOffset := 0xf38a) (codeLen := 11) (by decide) (by decide)
  obtain ⟨n1, a, run1, readyA, _, effectA⟩ := loop_prefix_block boundary pre.outerBoundary t
    (readyToStep initial.machine initial.bindingsSupported)
    (programText_slice (programLoaded_codeIn initial.loaded) 0xf38a loopPrefixBytes
      (by decide) (by decide +kernel)) prefixPre
  have rawA : AgreesExcept [.reg 14, .mem (stackPtr s-112) 8, .flags, .rip] t a := by
    have h : AgreesExcept [.reg 14, .mem (stackPtr t+24) 8, .flags, .rip] t a := by
      simpa [loopPrefixEffect, Effect.components, rspOf, stackPtr] using effectA.agrees
    have addr : stackPtr t+24 = stackPtr s-112 := addr24
    rw [addr] at h
    exact h
  have agreesA : AgreesExcept (Start.components s [(112,8)]) t a := rawA.mono (by simp [Start.components])
  have stateA := after pre.toCalleePre initial.toFrameState readyA agreesA
    (Start.writes pre (by simp)) (by simp [Start.components])
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have h := effectA.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = (t.regValue .r13 == 0#64) at h
    rw [initial.r13] at h
    exact h
  have branchNext : (jccEffect 0x10f395 6 4 ((0x15a : BitVec 32).signExtend 64) a).rip = 0x10f39b := by
    simp [jccEffect, branchEffect, condHolds, zf]
  obtain ⟨b, run2, readyB, effectB⟩ := (jcc_rel32_effect_step 0x10f395 4 0x15a).advances readyA
    (programText_slice (programLoaded_codeIn stateA.loaded) 0xf395 [0x0f,0x84,0x5a,1,0,0]
      (by decide) (by decide +kernel)) ⟨effectA.rip, by intro h; decide +kernel⟩
    (by rw [branchNext]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf39b (by decide)))
  have rawB : AgreesExcept [.rip] a b := effectB.agrees
  have stateB := stateA.after_registers readyB rawB (by simp [Component.Covers]) (by simp)
  have memoryB : b.external = a.external := rawB.external (by simp [Component.Covers])
  have constantsPre : ConstantsPre b := by
    refine ⟨effectB.rip.trans branchNext, ?_, ?_⟩
    · have h := stack_writable pre.toCalleePre stateB (offset := 0) (len := 48) (by decide) (by decide)
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable b (stackPtr b) 48
      simpa only [BitVec.add_zero] using h
    · have h := stack_code pre.toCalleePre stateB (offset := 0) (len := 48)
        (codeOffset := 0xf39b) (codeLen := 39) (by decide) (by decide)
      change RangeApart (stackPtr b) 48 (Extracted.textAddress+BitVec.ofNat 64 0xf39b) 39
      simpa only [BitVec.add_zero] using h
  obtain ⟨n3, c, run3, readyC, _, effectC⟩ := constants_block boundary pre.outerBoundary b readyB
    (programText_slice (programLoaded_codeIn stateB.loaded) 0xf39b constantsBytes
      (by decide) (by decide +kernel)) constantsPre
  have addr0 : rspOf b = stackPtr s-136 := stateB.rsp
  have addr12 : rspOf b+12 = stackPtr s-124 := stack_address stateB.rsp (offset := 12) (by decide)
  have addr32 : rspOf b+32 = stackPtr s-104 := stack_address stateB.rsp (offset := 32) (by decide)
  have addr40 : rspOf b+40 = stackPtr s-96 := stack_address stateB.rsp (offset := 40) (by decide)
  have agreesC : AgreesExcept (Start.components s [(136,8),(96,8),(104,8),(124,4)]) b c := by
    apply effectC.agrees.mono
    simp only [constantsEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append,
      addr0]
    simp (config := {decide := true}) [Start.components, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have stateC := after pre.toCalleePre stateB readyC agreesC (Start.writes pre (by simp)) (by simp [Start.components])
  obtain ⟨w, run4, readyW, effectW⟩ := (jmp_rel8_effect_step 0x10f3c2 0x23 (by decide +kernel)).advances readyC
    (programText_slice (programLoaded_codeIn stateC.loaded) 0xf3c2 [0xeb,0x23]
      (by decide) (by decide +kernel)) effectC.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf3e7 (by decide)))
  have rawW : AgreesExcept [.rip] c w := effectW.agrees
  have stateW := stateC.after_registers readyW rawW (by simp [Component.Covers]) (by simp)
  have memoryW : w.external = c.external := rawW.external (by simp [Component.Covers])
  have total : AgreesExcept (Start.components s [(112,8),(136,8),(96,8),(104,8),(124,4)]) t w :=
    (((agreesA.trans rawB).trans agreesC).trans rawW).mono (by simp [Start.components])
  have keep (off len : Nat) (ho : off ≤ 168) (hl : len ≤ off+8)
      (apart : ∀ cell ∈ [(112,8),(136,8),(96,8),(104,8),(124,4)],
        off+cell.2 ≤ cell.1 ∨ cell.1+len ≤ off) {i : Nat} (hi : i<len) :=
    Start.byte pre total (by simp) ho hl apart hi
  have pointer : memLoad w.external (stackPtr s-120) 64 = s.regValue .rdi :=
    (Start.read pre total (by simp) (off := 120) (n := 64) (by decide) (by decide) (by simp)).trans initial.outputPointer
  have iterator : Iterator.StateAt w (stackPtr s-88) (s.regValue .rdx) n 0 :=
    initial.iterator.of_copy (fun i hi => keep 88 40 (by decide) (by decide) (by simp) hi)
  have output : DigitsAt w (s.regValue .rdi) [] := by
    apply digitsAt_nil
    intro i hi
    rw [total.byte]
    · exact zeroT i hi
    · intro component hc cover
      simp only [Start.components, List.mem_append, List.mem_map] at hc
      rcases hc with hc | ⟨cell, hcell, rfl⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact cover.elim
      · have bounds : cell.1 ≤ 168 ∧ cell.2 ≤ cell.1 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcell
          rcases hcell with rfl | rfl | rfl | rfl | rfl <;> decide
        exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _
          (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
          (ScalarFrame.stack_contains pre.toCalleePre bounds.1 (by omega) cover)
  have rbxB : b.regValue .rbx = 32 :=
    (rawB.read (n := 64) (r := 3) (by simp)).trans
      ((rawA.read (n := 64) (r := 3) (by simp)).trans initial.rbx)
  have r15B : b.regValue .r15 = 257 :=
    (rawB.read (n := 64) (r := 15) (by simp)).trans
      ((rawA.read (n := 64) (r := 15) (by simp)).trans initial.r15)
  have valuesC := effectC.writes
  change memLoad c.external (rspOf b) 64 = b.regValue .r15 ∧
    memLoad c.external (rspOf b+40) 64 = b.regValue .rbx+(-1) ∧
    memLoad c.external (rspOf b+32) 64 = b.regValue .rbx >>> 1 ∧
    c.regValue .rax = ((b.regValue .rbx).setWidth 8).setWidth 64 ∧
    memLoad c.external (rspOf b+12) 32 = ((b.regValue .rbx).setWidth 8).setWidth 32 ∧
    c.regValue .rbp = 0 ∧ c.regValue .r15 = 0 ∧ c.regValue .r13 = 0 at valuesC
  rw [addr40, addr32, addr12, addr0, rbxB, r15B] at valuesC
  have bitsA : memLoad a.external (stackPtr s-112) 64 = 256 := by
    have h : memLoad a.external (stackPtr t+24) 64 = t.regValue .r13 := effectA.writes.2
    have addr : stackPtr t+24 = stackPtr s-112 := addr24
    rw [addr, initial.r13] at h
    exact h
  have bitsW : memLoad w.external (stackPtr s-112) 64 = 256 := by
    rw [memoryW]
    exact (Start.read pre agreesC (by simp) (off := 112) (n := 64)
      (by decide) (by decide) (by simp)).trans (by rw [memoryB]; exact bitsA)
  have r14W : w.regValue .r14 = 0 := by
    apply (rawW.read (n := 64) (r := 14) (by simp)).trans
    apply (effectC.agrees.read (n := 64) (r := 14) (by simp [constantsEffect, Effect.components])).trans
    exact (rawB.read (n := 64) (r := 14) (by simp)).trans effectA.writes.1
  refine ⟨n0+n1+1+n3+1, w, (((run0.trans run1).trans run2).trans run3).trans run4,
    stateW, effectW.rip, by decide, by decide, Or.inl rfl, rfl, ?_,
    source_preserved pre stateW input, output, iterator,
    (total.read (n := 64) (r := 12) (by simp [Start.components])).trans initial.r12,
    (rawW.read (n := 64) (r := 13) (by simp)).trans valuesC.2.2.2.2.2.2.2,
    r14W, (rawW.read (n := 64) (r := 15) (by simp)).trans valuesC.2.2.2.2.2.2.1,
    (rawW.read (n := 64) (r := 5) (by simp)).trans valuesC.2.2.2.2.2.1,
    ?_, pointer, bitsW, ?_, ?_, ?_⟩
  · simp only [digits, List.nil_append, Nat.pow_zero, Nat.div_one]
  · rw [memoryW]
    exact valuesC.1
  · rw [memoryW]
    exact valuesC.2.2.1
  · rw [memoryW]
    exact valuesC.2.1
  · rw [memoryW]
    exact valuesC.2.2.2.2.1

end P256.Proofs.Verifying.Combination.Naf.Machine
