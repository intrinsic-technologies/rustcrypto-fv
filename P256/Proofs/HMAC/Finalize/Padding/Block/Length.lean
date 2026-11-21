import P256.Proofs.HMAC.Interface
import P256.Proofs.HMAC.Finalize.Copy
import P256.Proofs.HMAC.Finalize.Padding.Interface
import P256.Proofs.HMAC.Finalize.Length
import P256.Proofs.HMAC.Finalize.Length.Outer

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Padding.Block

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Field (AdvanceTriple)

def storeStart (outer : Bool) : BitVec 64 := if outer then 0x10134a else 0x1010ac

def positionIndex (outer : Bool) : BitVec 5 := if outer then 12 else 13

def countIndex (outer : Bool) : BitVec 5 := if outer then 13 else 5

def encodingEffect (outer : Bool) (s : RamState) : Effect :=
  { rip := storeStart outer
    writes := [⟨(.reg (countIndex outer) : Operand 64),
        (.reg (countIndex outer) : Operand 64).read s <<< 9⟩,
      ⟨(.reg (positionIndex outer) : Operand 64), bswap64
        (((.reg (positionIndex outer) : Operand 32).read s <<< 3).setWidth 64 |||
          ((.reg (countIndex outer) : Operand 64).read s <<< 9))⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

structure Encoded [Bindings] (initial s : RamState) (message : ByteArray) (outer : Bool) : Prop
    extends ScalarFrame.FrameState initial s 0 672 328 where
  outputPointer : s.regValue .rbx = initial.regValue .rsi
  hashPointer : s.regValue (hashRegister outer) = stackPtr initial - 192#64
  length : (Operand.reg (positionIndex outer) : Operand 64).read s =
    bswap64 (BitVec.ofNat 64 (8 * message.size))
  buffer : (MemoryRegion.mk (stackPtr initial - 256#64).toNat 64).HasBytes
    s.external (SHA256.paddedBuffer message)
  hash : SHA256.HashStateAt s (stackPtr initial - 192#64)
    (SHA256.compressBlocks P256.Proofs.SHA256.initialHash message)

theorem encode [Bindings] (outer : Bool)
    {initial s : RamState} {boundary : ReturnBoundary} {message : ByteArray}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : Padded initial s message outer) (rip : s.RIP = lengthStart outer) :
    ∃ fuel t, Advances boundary fuel s t ∧ Encoded initial t message outer ∧
      t.RIP = storeStart outer ∧ t.external = s.external := by
  have run : AdvanceTriple boundary (fun s => s.RIP = lengthStart outer)
      (codeRange (lengthStart outer) (if outer then Length.Outer.bytes else Length.bytes))
      (Effect.post (encodingEffect outer)) := by
    cases outer
    · exact Length.run boundary pre.outerBoundary
    · exact Length.Outer.run boundary pre.outerBoundary
  have code : CodeIn (codeRange (lengthStart outer)
      (if outer then Length.Outer.bytes else Length.bytes)) s := by
    cases outer
    · exact Length.code state.loaded
    · exact Length.Outer.code state.loaded
  obtain ⟨fuel, t, advances, ready, _, effect⟩ := run s
    (readyToStep state.machine state.bindingsSupported) code rip
  have agrees : AgreesExcept
      [.reg (countIndex outer), .reg (positionIndex outer), .flags, .rip] s t := effect.agrees
  have memory : t.external = s.external := agrees.external (by simp [Component.Covers])
  have frame : ScalarFrame.FrameState initial t 0 672 328 := state.toFrameState.after_registers ready
    agrees (by simp [Component.Covers])
    (by cases outer <;> decide)
  refine ⟨fuel, t, advances, ⟨frame, ?_, ?_, ?_, ?_, ?_⟩, effect.rip, memory⟩
  · exact (agrees.read (n := 64) (r := 3) (by cases outer <;> decide)).trans state.outputPointer
  · cases outer
    · exact (agrees.read (n := 64) (r := 15) (by decide)).trans state.hashPointer
    · exact (agrees.read (n := 64) (r := 14) (by decide)).trans state.hashPointer
  · have written := effect.writes.2
    have position : (Operand.reg (positionIndex outer) : Operand 64).read s =
        BitVec.ofNat 64 (message.size % 64) := by cases outer <;> exact state.position
    have count : (Operand.reg (countIndex outer) : Operand 64).read s =
        BitVec.ofNat 64 (message.size / 64) := by cases outer <;> exact state.count
    change (Operand.reg (positionIndex outer) : Operand 64).read t = bswap64
      ((((Operand.reg (positionIndex outer) : Operand 64).read s).setWidth 32 <<< 3).setWidth 64 |||
        ((Operand.reg (countIndex outer) : Operand 64).read s <<< 9)) at written
    rw [position, count, SHA256.length_word] at written
    exact written
  · simpa only [memory] using state.buffer
  · exact state.hash.copy (fun i hi => by rw [memory])

end P256.Proofs.HMAC.Finalize.Padding.Block
