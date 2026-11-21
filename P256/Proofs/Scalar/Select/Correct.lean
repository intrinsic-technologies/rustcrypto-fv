import P256.Proofs.Scalar.Select.Choice
import P256.Proofs.Scalar.Select.Body
import P256.Proofs.Scalar.Select.Store
set_option autoImplicit false
namespace P256.Proofs.Scalar.Select
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem correct [Bindings] {v : RamState} {boundary : ReturnBoundary} {nonce : Nat}
    (pre : CalleePre v boundary 0x113260 32 32 16)
    (readable : MemReadable v (v.regValue .rdx) 32)
    (apart : RangeApart (stackPtr v - 1) 1 (v.regValue .rdx) 32)
    (input : Nat256At v (v.regValue .rdx) nonce)
    (choice : (v.regValue .rcx).setWidth 8 = 1) :
    ∃ w, CalleeResult v w boundary 32 16 ∧ Nat256At w (v.regValue .rdi) nonce := by
  obtain ⟨n, a, runA, readyA, _, ea⟩ := prefix_correct boundary v
    (readyToStep pre.machine pre.bindingsSupported)
    (programText_slice (programLoaded_codeIn pre.loaded) 0x13260 prefixBytes (by decide +kernel) (by decide +kernel)) pre
  have spA : stackPtr a = stackPtr v - 1 := ea.writes.1
  have axA : a.regValue .rax = v.regValue .rdi := ea.writes.2.1
  have dxA : a.regValue .rdx = v.regValue .rdx := ea.agrees.read (r := 2) (n := 64) (by simp [prefixEffect, Effect.components])
  have cxA : (a.regValue .rcx).setWidth 8 = 1 :=
    (congrArg (BitVec.setWidth 8) (ea.agrees.read (r := 1) (n := 64) (by simp [prefixEffect, Effect.components]))).trans choice
  have extA : a.external = v.external := ea.agrees.external (by simp [prefixEffect, Effect.components, Component.Covers])
  have frameA : AgreesExcept (clobbers v) v a := ea.agrees.mono (by simp [prefixEffect, Effect.components, clobbers])
  have writableA : MemWritable a (stackPtr a) 1 := by
    rw [spA]
    apply P256.Proofs.Program.writable_of_grow _ ea.agrees.grow
    apply P256.Proofs.Program.stack_sub_writable pre.stack
      (fun a ha ht ↦ pre.avoids _ (by simp) a ha (.inr ht)) (offset := 1) (len := 1) (by decide) (by decide) (by decide)
    have := Nat.mod_lt (stackPtr v - 1).toNat (by decide : 0 < 4096)
    omega
  obtain ⟨m, b, runB, readyB, _, eb⟩ := choice_correct boundary pre.outerBoundary a readyA
    (programText_slice (programLoaded_codeIn (loaded_of_agrees pre frameA)) 0x13276 choiceBytes (by decide +kernel) (by decide +kernel))
    ⟨ea.rip, writableA, by rw [spA]; exact stack_code_apart pre 0x13276 10 (by decide)⟩
  have frameB : AgreesExcept (clobbers v) v b := (frameA.trans eb.agrees).mono (by simp [choiceEffect, Effect.components, spA, clobbers])
  have axB : b.regValue .rax = v.regValue .rdi :=
    (eb.agrees.read (r := 0) (n := 64) (by simp [choiceEffect, Effect.components])).trans axA
  have dxB : b.regValue .rdx = v.regValue .rdx :=
    (eb.agrees.read (r := 2) (n := 64) (by simp [choiceEffect, Effect.components])).trans dxA
  have spB : stackPtr b = stackPtr v - 1 :=
    (eb.agrees.read (r := 4) (n := 64) (by simp [choiceEffect, Effect.components])).trans spA
  have cxB : (Operand.reg 1 : Operand 8).read b = 1 := by
    have hw : b.regValue .rcx = ((a.regValue .rcx).setWidth 8).setWidth 64 := eb.writes.1
    change (b.regValue .rcx).setWidth 8 = 1
    rw [hw, cxA]
    rfl
  have sourceB (i : Nat) (hi : i < 32) :
      b.external[v.regValue .rdx + BitVec.ofNat 64 i]? = v.external[v.regValue .rdx + BitVec.ofNat 64 i]? := by
    rw [← extA]
    apply eb.agrees.byte
    intro c hc cover
    simp only [choiceEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact cover.elim
    · obtain ⟨j, hj, eq⟩ := cover
      rw [spA] at eq
      exact apart j hj i hi eq.symm
    · exact cover.elim
  have readB : MemReadable b (b.regValue .rdx) 32 := by
    rw [dxB]
    exact P256.Proofs.Program.readable_of_grow readable frameB.grow
  obtain ⟨k, c, runC, readyC, _, ec⟩ := body_correct boundary pre.outerBoundary b readyB
    (programText_slice (programLoaded_codeIn (loaded_of_agrees pre frameB)) 0x13280 bodyBytes (by decide +kernel) (by decide +kernel)) ⟨eb.rip, readB⟩
  have frameC : AgreesExcept (clobbers v) v c := (frameB.trans ec.agrees).mono (by simp [bodyEffect, Effect.components, clobbers])
  have axC : c.regValue .rax = v.regValue .rdi :=
    (ec.agrees.read (r := 0) (n := 64) (by simp [bodyEffect, Effect.components])).trans axB
  have spC : stackPtr c = stackPtr v - 1 :=
    (ec.agrees.read (r := 4) (n := 64) (by simp [bodyEffect, Effect.components])).trans spB
  obtain ⟨l, d, runD, readyD, _, ed⟩ := output_correct boundary pre.outerBoundary c readyC
    (programText_slice (programLoaded_codeIn (loaded_of_agrees pre frameC)) 0x132a7 outputBytes (by decide +kernel) (by decide +kernel))
    ⟨ec.rip, by
      intro i hi; rw [axC]; apply output_writable pre frameC i
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide,
    by
      intro i hi off len bound; rw [axC]; apply output_code_apart pre i _ off len bound
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide⟩
  have outputFrame : AgreesExcept [.mem (v.regValue .rdi) 32, .rip] c d := by
    have ax : (Operand.reg 0 : Operand 64).read c = v.regValue .rdi := axC
    refine ⟨?_, ?_, ed.agrees.rest, ed.agrees.grow⟩
    · intro component absent nonmem
      apply ed.agrees.agree component _ nonmem
      intro member
      simp only [outputEffect, Effect.components, List.map_cons, List.map_nil,
        Write.component_mem, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      all_goals first | contradiction | exact absent (by simp)
    · intro address outside
      apply ed.agrees.byte
      intro component member cover
      simp only [outputEffect, Effect.components, List.map_cons, List.map_nil,
        Write.component_mem, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      all_goals try exact cover.elim
      all_goals obtain ⟨i, hi, eq⟩ := cover
      all_goals apply outside (.mem (v.regValue .rdi) 32) (by simp)
      · exact ⟨i, by omega, by simpa only [ax, BitVec.add_zero] using eq⟩
      · exact ⟨8+i, by omega, by rw [ax] at eq; simp only [BitVec.ofNat_add, ← BitVec.add_assoc]; exact eq⟩
      · exact ⟨16+i, by omega, by rw [ax] at eq; simp only [BitVec.ofNat_add, ← BitVec.add_assoc]; exact eq⟩
      · exact ⟨24+i, by omega, by rw [ax] at eq; simp only [BitVec.ofNat_add, ← BitVec.add_assoc]; exact eq⟩
  have frameD : AgreesExcept (clobbers v) v d :=
    (frameC.trans outputFrame).mono (by simp [clobbers])
  have spD : stackPtr d = stackPtr v - 1 :=
    (ed.agrees.read (r := 4) (n := 64) (by simp [outputEffect, Effect.components])).trans spC
  have words (j : Nat) (hj : j < 4) :
      memLoad d.external (v.regValue .rdi + BitVec.ofNat 64 (8*j)) 64 =
      memLoad b.external (v.regValue .rdx + BitVec.ofNat 64 (8*j)) 64 := by
    have cw := ec.writes
    have dw := ed.writes
    simp only [bodyEffect, Write.AllHold, cxB, show (1 : BitVec 8) ≠ 0 by decide, ite_false] at cw
    change _ ∧ _ ∧ _ ∧ _ at dw
    have hax : (Operand.reg 0 : Operand 64).read c = v.regValue .rdi := axC
    have hdx : (Operand.reg 2 : Operand 64).read b = v.regValue .rdx := dxB
    rcases cw with ⟨_, _, _, w0, w8, w16, w24⟩
    rcases dw with ⟨o0,o8,o16,o24⟩
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases casesJ with rfl | rfl | rfl | rfl
    all_goals simp only [Write.AllHold, hax] at o0 o8 o16 o24
    · exact o0.trans (hdx ▸ w0)
    · exact o8.trans (hdx ▸ w8)
    · exact o16.trans (hdx ▸ w16)
    · exact o24.trans (hdx ▸ w24)
  have scalarD : Nat256At d (v.regValue .rdi) nonce := by
    refine ⟨input.1, fun i hi => ?_⟩
    have word := words (i/8) (by omega)
    have byte := memByte_of_memLoad_eq word (i%8) (by omega)
    have index : 8*(i/8)+i%8 = i := by omega
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add, index] at byte
    have allocated := frameD.grow _ (Option.isSome_iff_exists.mpr (pre.outputAllocated _ (output_contains pre hi)))
    obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp allocated
    have original := (sourceB i hi).trans (input.2 i hi)
    rw [hx]
    congr 1
    simpa only [memByte, PhysicalMemory.read, hx, original, Option.getD_some] using byte
  obtain ⟨u, result, ext⟩ := epilogue pre frameD readyD ed.rip spD
    ⟨n+m+k+l, ((runA.trans runB).trans runC).trans runD⟩
  exact ⟨u, result, scalarD.1, fun i hi => by rw [ext]; exact scalarD.2 i hi⟩
end P256.Proofs.Scalar.Select
