import P256.Proofs.Verifying.Combination.Naf.Iterator.Interface
import P256.Proofs.Verifying.Combination.Naf.Iterator.InitializeStore
import P256.Proofs.Verifying.Combination.Naf.Iterator.Support
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Pop.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator.Advance

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Instructions.CrossPageStore

variable [Bindings] {boundary : ReturnBoundary}

theorem step_nomem {s : RamState} {P : RamState → Prop} {E : RamState → Effect}
    {bytes : List UInt8} {offset : Nat}
    (step : StepEffect P (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) E)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (pre : P s)
    (size : offset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (next : (E s).rip ≠ boundary.rip)
    (noMem : ∀ c ∈ (E s).components, ∀ a, ¬ c.Covers a) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧ (E s).Holds s t := by
  obtain ⟨t, run, readyT, effect⟩ := step.advances ready
    (programText_slice (programLoaded_codeIn loaded) offset bytes size code) pre next
  refine ⟨t, run, readyT, ?_, effect⟩
  have mem := effect.agrees.external noMem
  intro a b hf
  rw [mem]
  exact loaded a b hf

omit [Bindings] in
theorem store_loaded {s t : RamState} {a : BitVec 64} {E : Effect}
    (loaded : ProgramLoaded s) (effect : E.Holds s t)
    (components : E.components = [.mem a 8, .rip])
    (apart : ∀ i < 8, ¬ InProgram (a + BitVec.ofNat 64 i)) : ProgramLoaded t := by
  intro address byte fetch
  rw [effect.agrees.memory address]
  · exact loaded address byte fetch
  · intro c hc cover
    rw [components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := cover
      exact apart i hi ⟨byte, fetch⟩
    · exact cover

theorem load64 {s : RamState} {offset : Nat} (dst : BitVec 3) (am : AddrMode)
    (valid : am.Valid) (x : am.rexX = 0) (b : am.rexB = 0)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (readable : MemReadable s (am.addr s
      (Extracted.textAddress + BitVec.ofNat 64 offset + BitVec.ofNat 64 (3 + am.tail.length))) 8)
    (size : offset + (0x48 :: 0x8b :: am.modrm dst :: am.tail).length < 118431)
    (code : Extracted.textBytes.toListFrom offset (0x48 :: 0x8b :: am.modrm dst :: am.tail).length =
      0x48 :: 0x8b :: am.modrm dst :: am.tail)
    (outer : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      (movR64M64Effect (Extracted.textAddress + BitVec.ofNat 64 offset) (gprNumber 0 0 dst) am s).Holds s t := by
  apply step_nomem (mov_r64_m64_effect_step _ 0x48 (by simp [RexWPrefix]) dst am valid x.symm b.symm)
    ready loaded ⟨rip, readable⟩ (by omega) code
  · change (Extracted.textAddress + BitVec.ofNat 64 offset) + BitVec.ofNat 64 (3 + am.tail.length) ≠ _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    apply boundary_ne_program outer (inProgram_of_textOffset _ _)
    simp only [List.length_cons] at size
    omega
  · simp [Component.Covers]

theorem store64 {s : RamState} {offset : Nat} (src : BitVec 3) (am : AddrMode)
    (valid : am.Valid) (x : am.rexX = 0) (b : am.rexB = 0)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (writable : Writable s (am.addr s
      (Extracted.textAddress + BitVec.ofNat 64 offset + BitVec.ofNat 64 (3 + am.tail.length))) 8)
    (avoid : ∀ i < 8, ¬ InProgram (am.addr s
      (Extracted.textAddress + BitVec.ofNat 64 offset + BitVec.ofNat 64 (3 + am.tail.length)) + BitVec.ofNat 64 i))
    (size : offset + (0x48 :: 0x89 :: am.modrm src :: am.tail).length < 118431)
    (code : Extracted.textBytes.toListFrom offset (0x48 :: 0x89 :: am.modrm src :: am.tail).length =
      0x48 :: 0x89 :: am.modrm src :: am.tail)
    (outer : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      (movM64R64Effect (Extracted.textAddress + BitVec.ofNat 64 offset) (gprNumber 0 0 src) am s).Holds s t := by
  have apart : RangeApart (am.addr s
      (Extracted.textAddress + BitVec.ofNat 64 offset + BitVec.ofNat 64 (3 + am.tail.length))) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) (3 + am.tail.length) := by
    intro i hi j hj he
    apply avoid i hi
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset _ (by simp only [List.length_cons] at size; omega)
  have next : (movM64R64Effect (Extracted.textAddress + BitVec.ofNat 64 offset)
      (gprNumber 0 0 src) am s).rip ≠ boundary.rip := by
    change (Extracted.textAddress + BitVec.ofNat 64 offset) + BitVec.ofNat 64 (3 + am.tail.length) ≠ _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact boundary_ne_program outer (inProgram_of_textOffset _ (by simp only [List.length_cons] at size; omega))
  obtain ⟨t, run, readyT, effect⟩ :=
    (mov_m64_r64_effect_step_any _ 0x48 (by simp [RexWPrefix]) src am valid x.symm b.symm).advances
      ready (programText_slice (programLoaded_codeIn loaded) offset _ (by omega) code)
      ⟨rip, writable, apart⟩ next
  exact ⟨t, run, readyT, store_loaded loaded effect (by simp [movM64R64Effect, storeEffect, Effect.components]) avoid, effect⟩

end P256.Proofs.Verifying.Combination.Naf.Iterator.Advance
