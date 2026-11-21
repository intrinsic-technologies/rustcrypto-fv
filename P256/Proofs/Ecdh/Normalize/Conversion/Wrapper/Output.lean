import P256.Proofs.Common.Memory.Readable
import P256.Proofs.Ecdh.Normalize.Conversion.Wrapper.Entry
import P256.Proofs.Ecdh.Normalize.Conversion.Wrapper.Stores
import P256.Proofs.Sec1Serialize.Conversion.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Conversion.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Sec1Serialize (canonicalLimb)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem output_contains [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x107d00 32 32 40) {i : Nat} (hi : i < 32) :
    (registerRegion s .rdi 32).Contains (s.regValue .rdi + BitVec.ofNat 64 i).toNat :=
  memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem output_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cs : List Component} (pre : CalleePre s boundary 0x107d00 32 32 40)
    (g : AgreesExcept cs s t) (i : Nat) (hi : i+8 ≤ 32) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi + BitVec.ofNat 64 i) 8 := by
  have hr : MemReadable s (s.regValue .rdi) 32 :=
    memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _)
  have sub := P256.Proofs.Common.Memory.memReadable_sub hr i 8 hi
  refine ⟨readable_of_grow sub g.grow, ?_⟩
  apply tables_of_not_reserved (by decide) sub.low
  intro j hj hinside
  apply pre.avoids (registerRegion s .rdi 32) (by simp) _ _ (.inr hinside)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact output_contains pre (by omega)

theorem output_code_apart [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x107d00 32 32 40) (i : Nat) (hi : i+8 ≤ 32)
    (offset len : Nat) (hc : offset+len ≤ 118431) :
    RangeApart (s.regValue .rdi + BitVec.ofNat 64 i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro j hj k hk he
  apply pre.avoids (registerRegion s .rdi 32) (by simp)
    (s.regValue .rdi + BitVec.ofNat 64 i + BitVec.ofNat 64 j) _ (.inl ?_)
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact output_contains pre (by omega)
  · rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (offset+k) (by omega)

theorem stores_frame {s t u : RamState}
    (hd : (Operand.reg 7 : Operand 64).read t = s.regValue .rdi)
    (h : (storeLimbsEffect t).Holds t u) :
    AgreesExcept [.mem (s.regValue .rdi) 32, .rip] t u := by
  simp only [BitVec.ofNat_eq_ofNat] at hd
  refine ⟨?_, ?_, h.agrees.rest, h.agrees.grow⟩
  · intro c hc hm
    apply h.agrees.agree c ?_ hm
    intro hin
    simp only [storeLimbsEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, List.append_nil, List.nil_append, List.cons_append,
      List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl <;> simp_all [Component.isMem]
  · intro address outside
    apply h.agrees.memory address
    intro c hc hv
    simp only [storeLimbsEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, List.append_nil, List.nil_append, List.cons_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    apply outside (.mem (s.regValue .rdi) 32) (by simp)
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    all_goals obtain ⟨j, hj, rfl⟩ := hv
    · refine ⟨0+j, by omega, ?_⟩
      simp only [hd, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.zero_add]
    · refine ⟨8+j, by omega, ?_⟩
      simp only [hd, BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
    · refine ⟨16+j, by omega, ?_⟩
      simp only [hd, BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
    · refine ⟨24+j, by omega, ?_⟩
      simp only [hd, BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]

theorem store_body [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {x : Nat}
    (pre : Pre s boundary) (ready : ReadyToStep u) (loaded : ProgramLoaded u)
    (rip : u.RIP = 0x107e15) (agrees : AgreesExcept cs s u)
    (hd : (Operand.reg 7 : Operand 64).read u = s.regValue .rdi)
    (hx : x < 2^256)
    (h0 : u.regValue .rsi = canonicalLimb x 0)
    (h1 : u.regValue .rcx = canonicalLimb x 1)
    (h2 : u.regValue .rax = canonicalLimb x 2)
    (h3 : u.regValue .rdx = canonicalLimb x 3) :
    ∃ v, (∃ fuel, Advances boundary fuel u v) ∧ ReadyToStep v ∧
      v.RIP = 0x107e24 ∧ AgreesExcept [.mem (s.regValue .rdi) 32, .rip] u v ∧
      Nat256At v (s.regValue .rdi) x := by
  have hp : StoreLimbsPre u := by
    refine ⟨rip, ?_, ?_⟩
    · intro i hi
      rw [hd]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact output_writable pre agrees _ (by decide)
    · intro i hi offset len hc
      rw [hd]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact output_code_apart pre _ (by decide) offset len hc
  obtain ⟨fuel, v, run, rv, _, hv⟩ := store_limbs_correct boundary pre.outerBoundary u ready
    (programText_slice (programLoaded_codeIn loaded) 0x7e15 storeLimbsBytes
      (by decide) storeLimbs_bytes) hp
  have fs := stores_frame hd hv
  refine ⟨v, ⟨fuel, run⟩, rv, hv.rip, fs, ?_⟩
  apply nat256At_of_memLoad_limbs hx
  · intro i hi
    exact (agrees.trans fs).grow _ (Option.isSome_iff_exists.mpr
      (pre.outputAllocated _ (output_contains pre hi)))
  · intro j hj
    have ws := hv.writes
    simp only [storeLimbsEffect, Write.AllHold, hd] at ws
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact (show memLoad v.external (s.regValue .rdi + 0) 64 = u.regValue .rsi from ws.1).trans h0
    · exact ws.2.1.trans h1
    · exact ws.2.2.1.trans h2
    · exact ws.2.2.2.trans h3

end P256.Proofs.Ecdh.Normalize.Conversion.Wrapper
