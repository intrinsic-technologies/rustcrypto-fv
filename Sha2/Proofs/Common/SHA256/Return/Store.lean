import Sha2.Proofs.Common.SHA256.Frame
import Sha2.Proofs.Common.SHA256.Words
import Sha2.Proofs.Common.Encoding.Serialize.Store32

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

structure OutputState [Bindings] (initial current : RamState) (hash : Array UInt32)
    (written : List Nat) : Prop extends FrameState initial current where
  registers : RegistersAt current hash
  pointer : current.regValue .rdi = initial.regValue .rdi
  words : ∀ i < 8, i ∈ written →
    Bytes current.external (initial.regValue .rdi + BitVec.ofNat 64 (4 * i)) 4
      (storedByte hash[i]!.toBitVec)

theorem RegistersAt.after_output {s t : RamState} {hash : Array UInt32} {cs : List Component}
    (state : RegistersAt s hash) (frame : AgreesExcept cs s t)
    (regs : ∀ r ∈ [3,14,0,9,8,10,2,1], Component.reg r ∉ cs) :
    RegistersAt t hash := by
  refine ⟨state.size, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (frame.read (n := 32) (r := 3) (regs 3 (by simp))).trans state.a
  · exact (frame.read (n := 32) (r := 14) (regs 14 (by simp))).trans state.b
  · exact (frame.read (n := 32) (r := 0) (regs 0 (by simp))).trans state.c
  · exact (frame.read (n := 32) (r := 9) (regs 9 (by simp))).trans state.d
  · exact (frame.read (n := 32) (r := 8) (regs 8 (by simp))).trans state.e
  · exact (frame.read (n := 32) (r := 10) (regs 10 (by simp))).trans state.f
  · exact (frame.read (n := 32) (r := 2) (regs 2 (by simp))).trans state.g
  · exact (frame.read (n := 32) (r := 1) (regs 1 (by simp))).trans state.h

theorem output_contains [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray} {count offset i : Nat}
    (pre : CompressionPre initial boundary hash input count)
    (ho : offset + 4 ≤ 32) (hi : i < 4) :
    (registerRegion initial .rdi 32).Contains
      (initial.regValue .rdi + BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (by change offset + i < 32; omega)

theorem output_writable [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray} {count i : Nat}
    (pre : CompressionPre initial boundary hash input count)
    (frame : FrameState initial current) (hi : i < 8) :
    MemWritable current (initial.regValue .rdi + BitVec.ofNat 64 (4 * i)) 4 := by
  have hb : (initial.regValue .rdi).toNat + 32 < 2^32 := pre.outputBounded
  have ha : (initial.regValue .rdi + BitVec.ofNat 64 (4 * i)).toNat =
      (initial.regValue .rdi).toNat + 4 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  apply MemWritable.of_not_reserved (by decide)
  · rw [ha]
    omega
  · intro j hj
    exact frame.allocated _ (Option.isSome_iff_exists.mpr
      (pre.outputAllocated _ (output_contains pre (by omega) hj)))
  · intro j hj ht
    exact pre.avoids _ (by simp) _ (output_contains pre (by omega) hj) (.inr ht)

theorem OutputState.after_store [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {originalHash hash : Array UInt32} {input : ByteArray} {count i : Nat} {written : List Nat}
    (pre : CompressionPre initial boundary originalHash input count)
    (state : OutputState initial s hash written) (hi : i < 8)
    (ready : ReadyToStep t)
    (frame : AgreesExcept [.mem (initial.regValue .rdi + BitVec.ofNat 64 (4 * i)) 4, .rip] s t)
    (value : memLoad t.external (initial.regValue .rdi + BitVec.ofNat 64 (4 * i)) 32 =
      hash[i]!.toBitVec) : OutputState initial t hash (i :: written) := by
  have saved : FrameState initial t := state.toFrameState.after_agrees pre ready frame (by simp)
    (by
      intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := ha
        exact .inl (output_contains pre (by omega) hj)
      · exact ha.elim) (by simp) (by simp) (by simp)
  have bytes : Bytes t.external (initial.regValue .rdi + BitVec.ofNat 64 (4 * i)) 4
      (storedByte hash[i]!.toBitVec) := by
    have h := Bytes.of_memLoad (n := 32) (output_writable pre saved hi).mem
    rwa [value] at h
  refine ⟨saved, state.registers.after_output frame (by simp),
    (frame.read (n := 64) (r := 7) (by simp)).trans state.pointer, ?_⟩
  intro j hj hw
  by_cases he : j = i
  · subst j
    exact bytes
  · have hjw : j ∈ written := (List.mem_cons.mp hw).resolve_left he
    apply (state.words j hj hjw).of_agreesExcept frame
    intro k hk c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨l, hl, heq⟩ := hcov
      exact RangeApart.offsets (initial.regValue .rdi) (a := 4 * i) (b := 4 * j)
        (by omega) (by omega) (by omega) l hl k hk heq.symm
    · exact hcov

theorem output_store [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
    {originalHash hash : Array UInt32} {input : ByteArray} {count i pc : Nat}
    {written : List Nat} {reg : BitVec 5} {bytes : List UInt8}
    (pre : CompressionPre initial boundary originalHash input count)
    (state : OutputState initial current hash written) (hi : i < 8)
    (rip : current.RIP = Extracted.textAddress + BitVec.ofNat 64 pc)
    (value : (Operand.reg reg : Operand 32).read current = hash[i]!.toBitVec)
    (code : Extracted.textBytes.toListFrom pc bytes.length = bytes)
    (bound : pc + bytes.length < 71757)
    (step : StepEffect
      (StorePre (Extracted.textAddress + BitVec.ofNat 64 pc) bytes.length
        (fun s => s.regValue .rdi + BitVec.ofNat 64 (4 * i)) 4)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 pc) bytes)
      (storeEffect (Extracted.textAddress + BitVec.ofNat 64 pc) bytes.length
        (fun s => s.regValue .rdi + BitVec.ofNat 64 (4 * i))
        (fun s => (Operand.reg reg : Operand 32).read s))) :
    ∃ next, Advances boundary 1 current next ∧
      OutputState initial next hash (i :: written) ∧
      next.RIP = Extracted.textAddress + BitVec.ofNat 64 (pc + bytes.length) := by
  have writable := output_writable pre state.toFrameState hi
  have apart : RangeApart (current.regValue .rdi + BitVec.ofNat 64 (4 * i)) 4
      (Extracted.textAddress + BitVec.ofNat 64 pc) bytes.length := by
    rw [state.pointer]
    intro j hj k hk he
    apply pre.avoids _ (by simp) _ (output_contains pre (offset := 4 * i) (by omega) hj)
    left
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (pc + k) (by omega)
  obtain ⟨next, run, ready, effect⟩ := step.advances
    (supportedMachine_readyToStep state.machine)
    (programText_slice (programLoaded_codeIn state.loaded) pc bytes (by omega) code)
    ⟨rip, state.pointer ▸ writable, apart⟩
    (by
      rw [show (storeEffect (Extracted.textAddress + BitVec.ofNat 64 pc) bytes.length
          (fun s => s.regValue .rdi + BitVec.ofNat 64 (4 * i))
          (fun s => (Operand.reg reg : Operand 32).read s) current).rip =
        Extracted.textAddress + BitVec.ofNat 64 (pc + bytes.length) from
          by simp only [storeEffect, BitVec.ofNat_add, BitVec.add_assoc]]
      exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset _ (by omega)))
  have agrees : AgreesExcept
      [.mem (initial.regValue .rdi + BitVec.ofNat 64 (4 * i)) 4, .rip] current next := by
    simpa only [storeEffect_components, state.pointer] using effect.agrees
  refine ⟨next, run, state.after_store pre hi ready agrees ?_, ?_⟩
  · have hw := effect.writes
    change memLoad next.external (current.regValue .rdi + BitVec.ofNat 64 (4 * i)) 32 =
      (Operand.reg reg : Operand 32).read current at hw
    rwa [state.pointer, value] at hw
  · simpa only [storeEffect, BitVec.ofNat_add, BitVec.add_assoc] using effect.rip

end Sha2.Proofs.Common.SHA256
