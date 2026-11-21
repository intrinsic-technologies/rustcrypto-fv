import P256.Proofs.Program.ScalarFrame.Copy32Bytes
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Projective.Preserve
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Memory.Readable
set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Copy

open P256.Proofs.Program.ScalarFrame.Copy32
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stack_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {source destination : RamState → BitVec 64} {offset : Nat}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (bound : offset + 32 ≤ 632) (dst : destination t = stackPtr t + BitVec.ofNat 64 offset)
    (rip : t.RIP = entry) (readable : MemReadable t (source t) 32)
    (apart : RangeApart (destination t) 32 (source t) 32) : Pre entry source destination t := by
  refine ⟨rip, ?_, ?_, apart, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact P256.Proofs.Common.Memory.memReadable_sub readable _ 8 (by decide)
  · intro i hi
    rw [dst]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals
      first
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_writable (frameOffset := 632) pre state (by decide) (offset := offset + 0) (len := 8) (by omega) (by decide)
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_writable (frameOffset := 632) pre state (by decide) (offset := offset + 8) (len := 8) (by omega) (by decide)
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_writable (frameOffset := 632) pre state (by decide) (offset := offset + 16) (len := 8) (by omega) (by decide)
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_writable (frameOffset := 632) pre state (by decide) (offset := offset + 24) (len := 8) (by omega) (by decide)
  · intro i hi off len hc
    rw [dst]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals
      first
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_code (frameOffset := 632) pre state (by decide) (offset := offset + 0) (len := 8) (by omega) hc
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_code (frameOffset := 632) pre state (by decide) (offset := offset + 8) (len := 8) (by omega) hc
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_code (frameOffset := 632) pre state (by decide) (offset := offset + 16) (len := 8) (by omega) hc
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_code (frameOffset := 632) pre state (by decide) (offset := offset + 24) (len := 8) (by omega) hc

theorem source_readable {s : RamState} {ip : BitVec 64}
    {source destination : RamState → BitVec 64} (pre : Pre ip source destination s) :
    MemReadable s (source s) 32 := by
  have lo := (pre.readable 0 (by simp)).low
  have hi := (pre.readable 24 (by simp)).low
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at lo
  have add : (source s + 24).toNat = (source s).toNat + 24 := by
    simp only [BitVec.toNat_add, show (24 : BitVec 64).toNat = 24 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  rw [add] at hi
  refine ⟨hi, ?_⟩
  intro i bound
  have chunk : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 := by omega
  have read := pre.readable (BitVec.ofNat 64 (8*(i/8))) (by
    rcases chunk with h|h|h|h <;> simp [h])
  have h := read.mem (i%8) (by omega)
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add,
    show 8*(i/8)+i%8=i by omega] using h

theorem execute_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entryOffset offset x : Nat} {endIP : BitVec 64} {source destination : RamState → BitVec 64}
    {bytes : List UInt8}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (block : AdvanceTriple boundary (Pre (Extracted.textAddress + BitVec.ofNat 64 entryOffset) source destination)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 entryOffset) bytes)
      (Effect.post (effect endIP source destination)))
    (codeBound : entryOffset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom entryOffset bytes.length = bytes)
    (bound : offset + 32 ≤ 584) (dst : destination t = stackPtr t + BitVec.ofNat 64 offset)
    (input : Pre (Extracted.textAddress + BitVec.ofNat 64 entryOffset) source destination t)
    (hx : MontgomeryAt t (source t) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧ u.RIP = endIP ∧
      MontgomeryAt u (destination t) x ∧ AgreesExcept (components (destination t)) t u := by
  obtain ⟨fuel, u, run, ready, _, result⟩ := block t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) entryOffset bytes codeBound code) input
  have agrees := frame result
  have dst' : destination t = stackPtr s - BitVec.ofNat 64 (632-offset) :=
    dst.trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (by omega))
  have writes : WritesWithin (components (destination t))
      #v[registerRegion s .rdi 96, workRegion s 920] := by
    intro c hc a ha
    simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    rw [dst'] at ha
    exact ⟨workRegion s 920, by simp, work_contains pre (by omega) (by omega) ha⟩
  have next := state.after_effect pre (by decide) ready agrees writes (by simp [components])
  refine ⟨fuel, u, run, next, result.rip, hx.of_bytes_eq (copy_bytes result (source_readable input) ?_), agrees⟩
  have readable := stack_readable (frameOffset := 632) pre next (by decide) (offset := offset) (len := 32) (by omega)
  have sp : stackPtr u = stackPtr t := agrees.read (n := 64) (r := 4) (by simp [components])
  rw [sp, ← dst] at readable
  exact readable

end P256.Proofs.Projective.Add.Copy
