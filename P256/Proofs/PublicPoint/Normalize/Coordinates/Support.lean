import P256.Proofs.PublicPoint.Normalize.Coordinates.Copy
import P256.Proofs.Projective.Add.Copy.Preservation

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.Coordinates

open P256.Spec.Program P256.Spec.Program.Routines Program Program.ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

theorem copy_coordinate [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entryOffset sourceOffset value : Nat} {endIP : BitVec 64}
    {source destination : RamState → BitVec 64} {bytes : List UInt8}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352) (state : FrameState s t 65 3352 1944)
    (block : AdvanceTriple boundary
      (Copy32.Pre (Extracted.textAddress + BitVec.ofNat 64 entryOffset) source destination)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 entryOffset) bytes)
      (Effect.post (Copy32.effect endIP source destination)))
    (codeBound : entryOffset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom entryOffset bytes.length = bytes)
    (sourceUpper : sourceOffset + 32 ≤ 264)
    (src : source t = stackPtr t + BitVec.ofNat 64 sourceOffset)
    (dst : destination t = stackPtr t + 264)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 entryOffset)
    (valueAt : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 (1944-sourceOffset)) value) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 65 3352 1944 ∧ u.RIP = endIP ∧
      MontgomeryAt u (stackPtr s - 1680) value ∧
      AgreesExcept (Copy32.components (stackPtr s - 1680)) t u := by
  have sourceAddr : source t = stackPtr s - BitVec.ofNat 64 (1944-sourceOffset) :=
    src.trans (scalar_stack_address (frameOffset := 1944) state.rsp (by decide) (by omega))
  have destAddr : destination t = stackPtr s - 1680 :=
    dst.trans (scalar_stack_address (frameOffset := 1944) state.rsp (by decide) (by decide))
  have input : Copy32.Pre (Extracted.textAddress + BitVec.ofNat 64 entryOffset) source destination t := by
    apply stack_pre pre state (offset := 264) (by decide) dst rip
    · rw [src]
      exact stack_readable (frameOffset := 1944) pre state (by decide) (by omega)
    · rw [src,dst]
      exact RangeApart.offsets (stackPtr t) (a := 264) (b := sourceOffset)
        (by decide) (by omega) (.inr sourceUpper)
  obtain ⟨fuel,u,run,st,ip,value,agrees⟩ := execute_stack pre state block codeBound code
    (offset := 264) (by decide) dst input (by rwa [sourceAddr])
  rw [destAddr] at value agrees
  exact ⟨fuel,u,run,st,ip,value,agrees⟩

theorem copy_preserves {s t u : RamState} {offset value : Nat}
    (agrees : AgreesExcept (Copy32.components (stackPtr s - 1680)) t u)
    (apart : OffsetsApart (-1680) 32 (-BitVec.ofNat 64 offset) 32)
    (input : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) value) :
    MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) value :=
  Projective.Add.Copy.stack_preserves agrees rfl apart input

end P256.Proofs.PublicPoint.Normalize.Coordinates
