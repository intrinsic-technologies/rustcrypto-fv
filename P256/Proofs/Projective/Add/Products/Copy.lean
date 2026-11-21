import P256.Proofs.Projective.Add.Copy.Preservation
set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Products

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_coordinate [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entryOffset offset coordinate x : Nat} {endIP : BitVec 64}
    {source destination : RamState → BitVec 64} {bytes : List UInt8}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (block : AdvanceTriple boundary
      (Copy32.Pre (Extracted.textAddress + BitVec.ofNat 64 entryOffset) source destination)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 entryOffset) bytes)
      (Effect.post (Copy32.effect endIP source destination)))
    (codeBound : entryOffset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom entryOffset bytes.length = bytes)
    (bound : offset + 32 ≤ 584) (r : Syntax.Reg) (hr : r = .rdi ∨ r = .rsi)
    (pointBound : coordinate + 32 ≤ 96)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 entryOffset)
    (src : source t = s.regValue r + BitVec.ofNat 64 coordinate)
    (dst : destination t = stackPtr t + BitVec.ofNat 64 offset)
    (hx : MontgomeryAt t (s.regValue r + BitVec.ofNat 64 coordinate) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧ u.RIP = endIP ∧
      MontgomeryAt u (stackPtr s - BitVec.ofNat 64 (632-offset)) x ∧
      AgreesExcept (Copy32.components (destination t)) t u := by
  have cp : Copy32.Pre (Extracted.textAddress + BitVec.ofNat 64 entryOffset) source destination t := by
    apply Copy.stack_pre pre state (by omega) dst rip
    · rw [src]
      exact Copy.point_readable pre state r hr pointBound
    · rw [src, dst]
      exact Copy.stack_point_apart pre state r hr pointBound (by omega)
  obtain ⟨fuel, u, run, next, ip, value, agrees⟩ :=
    Copy.execute_stack pre state block codeBound code bound dst cp (src ▸ hx)
  refine ⟨fuel, u, run, next, ip, ?_, agrees⟩
  simpa only [dst, scalar_stack_address (frameOffset := 632) state.rsp (by decide) (by omega : offset ≤ 632)] using value

end P256.Proofs.Projective.Add.Products
