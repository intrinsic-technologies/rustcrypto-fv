import Hkdf.Proofs.NewExpand.Expand.LoopState
import Hkdf.Proofs.Common.CallFrame.Push
import Hkdf.Proofs.Common.Memory.Copy.RegisterOps.Cmov
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.Instructions
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem roundLength [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length n : Nat}
    (pre : ExpandPre entry boundary key info ptr length)
    (state : LoopState entry s boundary key info length n)
    (more : 32 * n < length) (bound : length ≤ 8160) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ t.RIP = 0x10f5a0 ∧
      slot t 8 = BitVec.ofNat 64 (length - 32 * n) ∧
      slot t 264 = BitVec.ofNat 64 (min (length - 32 * n) 32) ∧
      AgreesExcept [.reg 1, .flags, .mem (stackPtr s + 8) 8,
        .mem (stackPtr s + 264) 8, .rip] s t := by
  have pc := state.pc
  simp only [more, ↓reduceIte] at pc
  have outside := pre.call.outerBoundary
  have stack := pre.call.stack
  have avoid : (Stack.region entry 2264).Avoids InProgram :=
    fun a ha hp ↦ pre.call.stackAvoid a ha (.inl hp)
  have code := programLoaded_codeIn state.loaded
  obtain ⟨a, r₁, readyA, cmp⟩ := (cmp_r64_imm8_effect_step 0x10f586 0x48 0xfd 32
    (by simp [RexWPrefix]) rfl rfl).advances (supportedMachine_readyToStep state.machine)
    (programText_slice code 0xf586 _ (by decide) (by decide +kernel)) pc
    (boundary_ne_program outside (inProgram_of_textOffset 0xf58a (by decide)))
  have f₁ : AgreesExcept [.flags,.rip] s a := cmp.agrees
  have carry : (StatusFlags.ofRFLAGS a.RFLAGS).CF = decide ((s.regValue .rbp).toNat < 32) :=
    cmp.flags.1
  obtain ⟨b, r₂, readyB, mov⟩ := (mov_r32_imm32_effect_step 0x10f58a 0xb9 (by decide) 32).advances
    readyA (programText_slice (f₁.codeIn (by simp [Component.Covers]) code) 0xf58a _
      (by decide) (by decide +kernel)) cmp.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xf58f (by decide)))
  have f₂ : AgreesExcept [.reg 1,.rip] a b := mov.agrees
  have ab : AgreesExcept [.flags,.reg 1,.rip] s b := (f₁.trans f₂).mono (by simp)
  have spB : stackPtr b = stackPtr s := ab.read (n := 64) (r := 4) (by decide)
  have sp : stackPtr s = stackPtr entry - 536 := state.sp
  have addr₁ : stackPtr b + 8 = stackPtr entry - BitVec.ofNat 64 528 := by
    rw [spB, sp]; bv_omega
  have codeB := ab.codeIn (by simp [Component.Covers]) code
  have st₁ := mov_m64_r64_effect_step 0x10f58f 0x48 (by simp [RexWPrefix]) 5
    (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl
  obtain ⟨c, r₃, readyC, stored₁⟩ := st₁.advances readyB
    (programText_slice codeB 0xf58f _ (by decide) (by decide +kernel)) ⟨mov.rip, by
      change MemWritable b (stackPtr b + 8) 8
      rw [addr₁]
      exact CallFrame.stack_writable8 stack pre.call.stackAvoid
        (fun x hx ↦ ab.grow x (state.allocated x hx)) (by decide) (by decide), by
      change RangeApart (stackPtr b + 8) 8 0x10f58f 5
      rw [addr₁]
      exact CallFrame.stack_codeApart (codeOffset := 0xf58f) stack avoid (by decide) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0xf594 (by decide)))
  have f₃ : AgreesExcept [.mem (stackPtr b + 8) 8,.rip] b c := by
    have frame := stored₁.agrees
    simp only [movM64R64Effect, storeEffect_components] at frame
    exact frame
  have wr₁ := CallFrame.stack_slot_within stack (offset := 528) (len := 8)
    (by decide) (by decide) [.mem (stackPtr b + 8) 8,.rip] (by
      intro k hk x hx
      rcases List.mem_cons.mp hk with rfl | hk
      · rwa [addr₁] at hx
      · have eq : k = .rip := by simpa using hk
        subst k
        exact hx.elim)
  have loadedC := CallFrame.programLoaded_of_memoryWriteFrame (f₃.memoryWriteFrame wr₁)
    (show ProgramLoaded b from fun x v h ↦ by rw [ab.external (by simp [Component.Covers])]; exact state.loaded x v h)
    (CallFrame.stack_avoids pre.call.stackAvoid)
  have codeC := programLoaded_codeIn loadedC
  obtain ⟨d, r₄, readyD, cmov⟩ := (Hkdf.Proofs.Common.Instructions.cmov_r64_r64_effect_step
    0x10f594 0x48 0x42 0xcd (by simp [RexWPrefix]) (.inl rfl) rfl).advances readyC
    (programText_slice codeC 0xf594 _ (by decide) (by decide +kernel)) stored₁.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xf598 (by decide)))
  have f₄ : AgreesExcept [.reg 1,.rip] c d := cmov.agrees
  have bc := f₂.trans f₃
  have cf : StatusFlags.ofRFLAGS c.RFLAGS = StatusFlags.ofRFLAGS a.RFLAGS :=
    bc.agree .flags (by simp) rfl
  have rbpB : b.regValue .rbp = s.regValue .rbp := ab.read (n := 64) (r := 5) (by decide)
  have rbpC : c.regValue .rbp = b.regValue .rbp := f₃.read (n := 64) (r := 5) (by simp)
  have rcxC : c.regValue .rcx = b.regValue .rcx := f₃.read (n := 64) (r := 1) (by simp)
  have rcxB : b.regValue .rcx = 32 := mov.writes
  have rcxD : d.regValue .rcx = BitVec.ofNat 64 (min (length - 32 * n) 32) := by
    have value : d.regValue .rcx =
        (if (StatusFlags.ofRFLAGS c.RFLAGS).CF then c.regValue .rbp else c.regValue .rcx) :=
      cmov.writes
    rw [value, cf, carry, rcxC, rcxB, rbpC, rbpB, state.remaining]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show length - 32 * n < 2^64 by omega),
      decide_eq_true_eq]
    split
    · rw [Nat.min_eq_left (by omega)]
    · rw [Nat.min_eq_right (by omega)]; rfl
  have cd := f₃.trans f₄
  have spD : stackPtr d = stackPtr b := cd.read (n := 64) (r := 4) (by simp)
  have addr₂ : stackPtr d + 264 = stackPtr entry - BitVec.ofNat 64 272 := by
    rw [spD, spB, sp]; bv_omega
  have st₂ := mov_m64_r64_effect_step 0x10f598 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 264)) (by decide) rfl rfl
  obtain ⟨t, r₅, readyT, stored₂⟩ := st₂.advances readyD
    (programText_slice (f₄.codeIn (by simp [Component.Covers]) codeC) 0xf598 _
      (by decide) (by decide +kernel)) ⟨cmov.rip, by
      change MemWritable d (stackPtr d + 264) 8
      rw [addr₂]
      exact CallFrame.stack_writable8 stack pre.call.stackAvoid
        (fun x hx ↦ cd.grow x (ab.grow x (state.allocated x hx))) (by decide) (by decide), by
      change RangeApart (stackPtr d + 264) 8 0x10f598 8
      rw [addr₂]
      exact CallFrame.stack_codeApart (codeOffset := 0xf598) stack avoid (by decide) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0xf5a0 (by decide)))
  have f₅ : AgreesExcept [.mem (stackPtr d + 264) 8,.rip] d t := by
    have frame := stored₂.agrees
    simp only [movM64R64Effect, storeEffect_components] at frame
    exact frame
  have spT : stackPtr t = stackPtr d := f₅.read (n := 64) (r := 4) (by simp)
  have got₁ : memLoad c.external (stackPtr b + 8) 64 = b.regValue .rbp := stored₁.writes
  have got₂ : memLoad t.external (stackPtr d + 264) 64 = d.regValue .rcx := stored₂.writes
  have tail := f₄.trans f₅
  have kept : (Component.mem (stackPtr b + 8) 8).Agrees c t := by
    intro i hi
    apply tail.byte
    intro k hk
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with (rfl | rfl) | (rfl | rfl)
    · exact False.elim
    · exact False.elim
    · rintro ⟨j,hj,he⟩
      rw [spD] at he
      have apart := RangeApart.offsets (stackPtr b) (a := 8) (b := 264) (len := 8)
        (count := 8) (by decide) (by decide) (by decide)
      exact apart i hi j hj (by first | exact he | exact he.symm)
    · exact False.elim
  refine ⟨t, (((r₁.trans r₂).trans r₃).trans r₄).trans r₅, readyT, stored₂.rip, ?_, ?_, ?_⟩
  · change memLoad t.external (stackPtr t + 8) 64 = _
    rw [spT, spD, CallFrame.agrees_memLoad kept, got₁, rbpB, state.remaining]
  · change memLoad t.external (stackPtr t + 264) 64 = _
    rw [spT, got₂, rcxD]
  · have frame := (ab.trans f₃).trans tail
    rw [spD, spB] at frame
    exact frame.mono (by simp)

end Hkdf.Proofs.NewExpand.Expand
