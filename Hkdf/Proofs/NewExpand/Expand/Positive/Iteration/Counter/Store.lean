import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Frame
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Counter

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine

theorem store_stack [Bindings] {entry s : RamState} {length off codeOff codeSize width : Nat}
    {boundary : ReturnBoundary} {address : RamState → BitVec 64} {value : RamState → BitVec width}
    {bytes : List UInt8}
    (ctx : StackContext entry boundary length) (running : RunningFrame entry boundary length s)
    (pc : s.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOff)
    (addr : address s = base entry + BitVec.ofNat 64 off)
    (bound : off + width / 8 ≤ 536) (codeBound : codeOff + codeSize < 115149)
    (writable : MemWritable s (base entry + BitVec.ofNat 64 off) (width / 8))
    (step : StepEffect (StorePre (Extracted.textAddress + BitVec.ofNat 64 codeOff) codeSize address (width / 8))
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 codeOff) bytes)
      (storeEffect (Extracted.textAddress + BitVec.ofNat 64 codeOff) codeSize address value))
    (code : CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 codeOff) bytes) s) :
    ∃ t, RunningFrame entry boundary length t ∧ ReadyToStep t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOff + BitVec.ofNat 64 codeSize ∧
      memLoad t.external (base entry + BitVec.ofNat 64 off) width = value s ∧
      AgreesExcept [.mem (base entry + BitVec.ofNat 64 off) (width / 8), .rip] s t := by
  obtain ⟨t, run, ready, effect⟩ := step.advances (supportedMachine_readyToStep running.machine) code
    ⟨pc, addr ▸ writable, addr ▸ stack_apart ctx (by omega) (by omega) (by omega)⟩ (by
      change Extracted.textAddress + BitVec.ofNat 64 codeOff + BitVec.ofNat 64 codeSize ≠ boundary.rip
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact boundary_ne_program ctx.outside (inProgram_of_textOffset _ codeBound))
  have frame : AgreesExcept [.mem (base entry + BitVec.ofNat 64 off) (width / 8), .rip] s t := by
    simpa only [storeEffect_components, addr] using effect.agrees
  have write : memLoad t.external (address s) width = value s := effect.writes
  exact ⟨t, running.of_agrees run ready frame (stack_writes ctx (by omega) bound)
    ctx.avoids (by simp), ready, effect.rip, addr ▸ write, frame⟩

theorem byte_of_load {s : RamState} {a : BitVec 64} {b : UInt8}
    (read : MemReadable s a 1) (val : memLoad s.external a 8 = b.toBitVec) :
    s.external[a]? = some b := by
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, val, storedByte, Nat.mul_zero,
    Nat.shiftRight_zero, UInt8.ofNat_toNat, UInt8.toNat_toBitVec] using
    Bytes.of_memLoad (n := 8) read.mem 0 (by decide)

theorem word_unchanged {s t : RamState} {a b : BitVec 64} {n : Nat}
    (frame : AgreesExcept [.mem b n, .rip] s t) (apart : OffsetsApart 0 8 (b - a) n)
    (small : 8 + n < 2^64) : memLoad t.external a 64 = memLoad s.external a 64 := by
  apply agrees_memLoad
  intro i hi
  apply frame.byte
  intro c hc cover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, eq⟩ := cover
    apply OffsetsApart.ne apart a hi hj small
    bv_omega
  · exact cover.elim

end Hkdf.Proofs.NewExpand.Expand.Counter
