import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Interface
import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.LoopBody
import P256.Proofs.Common.Memory.Readable
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)
open P256.Proofs.Common.Memory (memReadable_sub)

namespace P256.Proofs.SecretKeyFromBytes.Scalar.Equal

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def limb (s : RamState) (r : Syntax.Reg) (i : Nat) : BitVec 64 :=
  memLoad s.external (s.regValue r + BitVec.ofNat 64 (8*i)) 64

def prefixEqual (s : RamState) : Nat → Bool
  | 0 => true
  | i+1 => prefixEqual s i && (limb s .rdi i == limb s .rdx i)

theorem prefixEqual_iff (s : RamState) (n : Nat) :
    prefixEqual s n = true ↔ ∀ i < n, limb s .rdi i = limb s .rdx i := by
  induction n with
  | zero => simp [prefixEqual]
  | succ n ih =>
    simp only [prefixEqual, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      by_cases he : i = n
      · exact he ▸ hn
      · exact h i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

structure LoopState [Bindings] (s t : RamState) (boundary : ReturnBoundary) (i : Nat) : Prop
    extends Stage s t boundary where
  rip : t.RIP = if i < 4 then 0x119290 else 0x1192aa
  right : t.regValue .rdx = s.regValue .rdx
  zero : t.regValue .rcx = 0
  counter : t.regValue .r8 = BitVec.ofNat 64 i
  accumulator : (t.regValue .rax).setWidth 8 = if prefixEqual s i then 1 else 0

theorem LoopState.left [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i : Nat}
    (h : LoopState s t boundary i) : t.regValue .rdi = s.regValue .rdi :=
  h.agrees.read (n := 64) (r := 7) (by simp [clobbers])

theorem LoopState.length [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i : Nat}
    (pre : Pre s boundary) (h : LoopState s t boundary i) : t.regValue .rsi = 4 :=
  (h.agrees.read (n := 64) (r := 6) (by simp [clobbers])).trans pre.leftLength

theorem LoopState.address [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i : Nat}
    (h : LoopState s t boundary i) (hi : i < 4) :
    loopAddress t 7 = s.regValue .rdi + BitVec.ofNat 64 (8*i) ∧
    loopAddress t 2 = s.regValue .rdx + BitVec.ofNat 64 (8*i) := by
  change t.regValue .rdi + ((t.regValue .r8 <<< 3) + 0) = _ ∧
    t.regValue .rdx + ((t.regValue .r8 <<< 3) + 0) = _
  rw [h.left, h.right, h.counter]
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem loop_iteration [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i : Nat}
    (pre : Pre s boundary) (h : LoopState s t boundary i) (hi : i < 4) :
    ∃ u, LoopState s u boundary (i+1) := by
  have addresses := h.address hi
  have hp : LoopBodyPre t := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hi, ite_eq_left] using h.rip
    · rw [addresses.1]
      exact (memReadable_sub pre.left (8*i) 8 (by omega)).of_external_eq h.memory
    · rw [addresses.2]
      exact (memReadable_sub pre.right (8*i) 8 (by omega)).of_external_eq h.memory
  have code := programText_slice (programLoaded_codeIn (h.loaded pre.loaded))
    0x19290 loopBytes (by decide +kernel) (by decide +kernel)
  obtain ⟨fuel, v, run, ready, _, effect⟩ := loop_body boundary pre.outerBoundary t h.ready code hp
  have stage := h.toStage.extend run ready effect (by simp [loopEffect, Effect.components, clobbers])
  have limbs : loopLimb t 7 = limb s .rdi i ∧ loopLimb t 2 = limb s .rdx i := by
    simp only [loopLimb, addresses.1, addresses.2]
    change memLoad t.external _ 64 = _ ∧ memLoad t.external _ 64 = _
    rw [h.memory]
    exact ⟨rfl, rfl⟩
  have hv : (v.regValue .rax).setWidth 8 = if prefixEqual s (i+1) then 1 else 0 := by
    have hw : v.regValue .rax = loopValue t := effect.writes.2.2.2
    rw [hw]
    simp only [loopValue, limbs.1, limbs.2]
    change (if limb s .rdi i = limb s .rdx i then (t.regValue .rax).setWidth 8 |>.setWidth 64
      else t.regValue .rcx).setWidth 8 = _
    rw [h.accumulator, h.zero]
    cases he : prefixEqual s i <;> by_cases hl : limb s .rdi i = limb s .rdx i <;>
      simp [he, hl, prefixEqual]
  have hn : v.regValue .r8 = BitVec.ofNat 64 (i+1) := by
    have hw : v.regValue .r8 = t.regValue .r8 + 1 := effect.writes.1
    rw [hw, h.counter]
    exact (BitVec.ofNat_add i 1).symm
  have hz : (StatusFlags.ofRFLAGS v.RFLAGS).ZF = decide (i+1 = 4) := by
    have hf := effect.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS v.RFLAGS).ZF =
      (cmpSpec (t.regValue .rsi) (t.regValue .r8 + 1)).ZF at hf
    rw [h.length pre, h.counter] at hf
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> exact hf
  have branchRip : (jccEffect 0x1192a8 2 5 ((0xe6 : BitVec 8).signExtend 64) v).rip =
      if i+1 < 4 then 0x119290 else 0x1192aa := by
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [jccEffect, branchEffect, condHolds, hz, branchTarget]
  have bcode := programText_slice (programLoaded_codeIn (stage.loaded pre.loaded))
    0x192a8 [0x75,0xe6] (by decide +kernel) (by decide +kernel)
  obtain ⟨u, run', ready', effect'⟩ := (jcc_rel8_effect_step 0x1192a8 5 0xe6).advances ready bcode
    ⟨effect.rip, fun _ => by decide +kernel⟩ (by
      rw [branchRip]
      split
      · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x19290 (by decide))
      · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x192aa (by decide)))
  have stage' := stage.extend run' ready' effect' (by simp [jccEffect, clobbers])
  have agrees : AgreesExcept ((loopEffect t).components ++
      (jccEffect 0x1192a8 2 5 ((0xe6 : BitVec 8).signExtend 64) v).components) t u :=
    effect.agrees.trans effect'.agrees
  refine ⟨u, stage', effect'.rip.trans branchRip, ?_, ?_, ?_, ?_⟩
  · exact (agrees.read (n := 64) (r := 2) (by simp [loopEffect, Effect.components, jccEffect, branchEffect])).trans h.right
  · exact (agrees.read (n := 64) (r := 1) (by simp [loopEffect, Effect.components, jccEffect, branchEffect])).trans h.zero
  · exact (effect'.agrees.read (n := 64) (r := 8) (by simp [jccEffect])).trans hn
  · exact (effect'.agrees.read (n := 8) (r := 0) (by simp [jccEffect])).trans hv

theorem loop_four [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (h : LoopState s t boundary 0) :
    ∃ u, LoopState s u boundary 4 := by
  obtain ⟨t1, h1⟩ := loop_iteration pre h (by decide)
  obtain ⟨t2, h2⟩ := loop_iteration pre h1 (by decide)
  obtain ⟨t3, h3⟩ := loop_iteration pre h2 (by decide)
  exact loop_iteration pre h3 (by decide)

end P256.Proofs.SecretKeyFromBytes.Scalar.Equal
