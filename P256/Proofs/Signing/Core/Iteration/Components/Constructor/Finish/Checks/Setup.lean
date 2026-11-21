import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks.Prepare
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks.Arguments

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem setup [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Stage s t boundary)
    (which : Bool) (rip : t.RIP = if which then 0x1099c5 else 0x10997d)
    (first : Nat256At t (stackPtr t + 64#64) x)
    (second : Nat256At t (stackPtr t + 96#64) y) :
    ∃ u, Stage s u boundary ∧ u.RIP = (if which then 0x1099fa else 0x1099b2) ∧
      u.regValue .rdi = stackPtr u + BitVec.ofNat 64 (if which then 96 else 64) ∧
      u.regValue .rdx = stackPtr u + 0#64 ∧ u.regValue .rsi = 4 ∧ u.regValue .rcx = 4 ∧
      Nat256At u (stackPtr u + 0#64) 0 ∧
      Nat256At u (stackPtr u + 64#64) x ∧ Nat256At u (stackPtr u + 96#64) y := by
  let start : Nat := if which then 0x99c5 else 0x997d
  obtain ⟨a, ast, arip, zero, preserved⟩ := zero_buffer pre state start
    (by cases which <;> decide) (by cases which <;> decide +kernel)
    (by cases which <;> exact rip)
  have ax := preserved 64 x (by decide) (by decide) first
  have ay := preserved 96 y (by decide) (by decide) second
  let p : BitVec 64 := Extracted.textAddress + BitVec.ofNat 64 (if which then 0x99e8 else 0x99a0)
  let am : AddrMode := .sib 4 none 0 (if which then .d8 96 else .d8 64)
  obtain ⟨b, hb, rb, eb⟩ := (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7 am
    (by cases which <;> decide +kernel) rfl rfl).advances
    (readyToStep ast.machine ast.bindingsSupported)
    (programText_slice (programLoaded_codeIn ast.loaded) (if which then 0x99e8 else 0x99a0) _
      (by cases which <;> decide) (by cases which <;> decide +kernel))
    (by cases which <;> exact arip)
    (by cases which
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x99a5 (by decide))
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x99ed (by decide)))
  have fb : AgreesExcept [.reg 7, .rip] a b := by cases which <;> exact eb.agrees
  have bst := ast.after_registers hb rb fb (by simp [Component.Covers]) (by simp)
  have spb : stackPtr b = stackPtr a := fb.read (n := 64) (r := 4) (by simp)
  have mb := fb.external (by simp [Component.Covers])
  have bdi : b.regValue .rdi = stackPtr b + BitVec.ofNat 64 (if which then 96 else 64) := by
    rw [spb]
    cases which <;> exact eb.writes
  let tailOffset : Nat := if which then 0x99ed else 0x99a5
  let tail : BitVec 64 := Extracted.textAddress + BitVec.ofNat 64 tailOffset
  have brip : b.RIP = tail := by cases which <;> exact eb.rip
  have safe : ∀ k ∈ ([3#64,8#64,13#64] : List (BitVec 64)), tail + k ≠ boundary.rip := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · simpa only [tail, BitVec.ofNat_add, BitVec.add_assoc] using
        boundary_ne_program pre.outerBoundary (inProgram_of_textOffset (tailOffset+3)
          (by cases which <;> decide))
    · simpa only [tail, BitVec.ofNat_add, BitVec.add_assoc] using
        boundary_ne_program pre.outerBoundary (inProgram_of_textOffset (tailOffset+8)
          (by cases which <;> decide))
    · simpa only [tail, BitVec.ofNat_add, BitVec.add_assoc] using
        boundary_ne_program pre.outerBoundary (inProgram_of_textOffset (tailOffset+13)
          (by cases which <;> decide))
  obtain ⟨n, u, hu, ru, _, eu⟩ := argument_correct boundary tail safe b rb
    (programText_slice (programLoaded_codeIn bst.loaded) tailOffset argumentBytes
      (by cases which <;> decide) (by cases which <;> decide +kernel)) brip
  have ust := bst.after_registers hu ru eu.agrees
    (by simp [argumentEffect, Effect.components, Component.Covers])
    (by simp [argumentEffect, Effect.components])
  have spu : stackPtr u = stackPtr b := eu.agrees.read (n := 64) (r := 4)
    (by simp [argumentEffect, Effect.components])
  have mu := eu.agrees.external (by simp [argumentEffect, Effect.components, Component.Covers])
  refine ⟨u, ust, ?_, ?_, ?_, eu.writes.2.1, eu.writes.2.2, ?_, ?_, ?_⟩
  · cases which <;> exact eu.rip
  · rw [spu]
    exact (eu.agrees.read (n := 64) (r := 7)
      (by simp [argumentEffect, Effect.components])).trans bdi
  · rw [spu]
    simpa only [BitVec.add_zero] using (show u.regValue .rdx = stackPtr b from eu.writes.1)
  · simpa only [Nat256At, mu, mb, spu, spb] using zero
  · simpa only [Nat256At, mu, mb, spu, spb] using ax
  · simpa only [Nat256At, mu, mb, spu, spb] using ay

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks
