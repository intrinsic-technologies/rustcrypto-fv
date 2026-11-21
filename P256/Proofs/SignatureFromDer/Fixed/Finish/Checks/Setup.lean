import P256.Proofs.SignatureFromDer.Fixed.Finish.Checks.Prepare
import P256.Proofs.SignatureFromDer.Fixed.Finish.Checks.Arguments

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.SignatureFromDer.Fixed.Finish.Checks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem setup [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Stage s t boundary)
    (which : Bool) (rip : t.RIP = if which then 0x109c09 else 0x109bbe)
    (first : Nat256At t (stackPtr t + 104#64) x)
    (second : Nat256At t (stackPtr t + 136#64) y) :
    ∃ u, Stage s u boundary ∧ u.RIP = (if which then 0x109c44 else 0x109bf6) ∧
      u.regValue .rdi = stackPtr u + BitVec.ofNat 64 (if which then 136 else 104) ∧
      u.regValue .rdx = stackPtr u + 8#64 ∧ u.regValue .rsi = 4 ∧ u.regValue .rcx = 4 ∧
      Nat256At u (stackPtr u + 8#64) 0 ∧
      Nat256At u (stackPtr u + 104#64) x ∧ Nat256At u (stackPtr u + 136#64) y := by
  let start : Nat := if which then 0x9c09 else 0x9bbe
  obtain ⟨a, ast, arip, zero, preserved⟩ := zero_buffer pre state start
    (by cases which <;> decide) (by cases which <;> decide +kernel)
    (by cases which <;> exact rip)
  have ax := preserved 104 x (by decide) (by decide) first
  have ay := preserved 136 y (by decide) (by decide) second
  let p : BitVec 64 := Extracted.textAddress + BitVec.ofNat 64 (if which then 0x9c2d else 0x9be2)
  let am : AddrMode := .sib 4 none 0 (if which then .d32 136 else .d8 104)
  obtain ⟨b, hb, rb, eb⟩ := (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7 am
    (by cases which <;> decide +kernel) rfl rfl).advances
    (readyToStep ast.machine ast.bindingsSupported)
    (programText_slice (programLoaded_codeIn ast.loaded) (if which then 0x9c2d else 0x9be2) _
      (by cases which <;> decide) (by cases which <;> decide +kernel))
    (by cases which <;> exact arip)
    (by cases which
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9be7 (by decide))
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9c35 (by decide)))
  have fb : AgreesExcept [.reg 7, .rip] a b := by cases which <;> exact eb.agrees
  have bst := ast.after_registers hb rb fb (by simp [Component.Covers]) (by simp)
  have spb : stackPtr b = stackPtr a := fb.read (n := 64) (r := 4) (by simp)
  have mb := fb.external (by simp [Component.Covers])
  have bdi : b.regValue .rdi = stackPtr b + BitVec.ofNat 64 (if which then 136 else 104) := by
    rw [spb]
    cases which <;> exact eb.writes
  let tailOffset : Nat := if which then 0x9c35 else 0x9be7
  let tail : BitVec 64 := Extracted.textAddress + BitVec.ofNat 64 tailOffset
  have brip : b.RIP = tail := by cases which <;> exact eb.rip
  have safe : ∀ k ∈ ([5#64,10#64,15#64] : List (BitVec 64)), tail + k ≠ boundary.rip := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · simpa only [tail, BitVec.ofNat_add, BitVec.add_assoc] using
        boundary_ne_program pre.outerBoundary (inProgram_of_textOffset (tailOffset+5)
          (by cases which <;> decide))
    · simpa only [tail, BitVec.ofNat_add, BitVec.add_assoc] using
        boundary_ne_program pre.outerBoundary (inProgram_of_textOffset (tailOffset+10)
          (by cases which <;> decide))
    · simpa only [tail, BitVec.ofNat_add, BitVec.add_assoc] using
        boundary_ne_program pre.outerBoundary (inProgram_of_textOffset (tailOffset+15)
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
    exact eu.writes.1
  · simpa only [Nat256At, mu, mb, spu, spb] using zero
  · simpa only [Nat256At, mu, mb, spu, spb] using ax
  · simpa only [Nat256At, mu, mb, spu, spb] using ay

end P256.Proofs.SignatureFromDer.Fixed.Finish.Checks
