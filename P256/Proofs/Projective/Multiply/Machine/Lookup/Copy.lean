import P256.Proofs.Projective.Multiply.Machine.Lookup.Memory
import P256.Proofs.Projective.Copy

set_option autoImplicit false

open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_to_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) (state : FrameState s t)
    (codeOffset : Nat) (codeBound : codeOffset + 3 < 118431)
    (codeBytes : Extracted.textBytes.toListFrom codeOffset 3 = [0xf3, 0x48, 0xa5])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (destination : Nat) (destBound : destination ≤ 360) (destSaved : 144 ≤ destination)
    (dst : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 destination)
    (count : t.regValue .rcx = 12)
    (source : MemReadable t (t.regValue .rsi) 96)
    (disjoint : (t.regValue .rsi).toNat + 96 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 96 ≤ (t.regValue .rsi).toNat)
    (input : ProjectiveAt t (t.regValue .rsi) point) :
    ∃ u, Advances boundary 12 t u ∧ FrameState s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (3 : BitVec 64) ∧
      ProjectiveAt u (stackPtr s - BitVec.ofNat 64 destination) point ∧
      AgreesExcept [.reg 6, .reg 7, .reg 1,
        .mem (stackPtr s - BitVec.ofNat 64 destination) 96, .rip] t u := by
  exact Projective.Copy.copy_to_stack pre state codeOffset codeBound codeBytes rip destination
    (by omega) destSaved dst count source disjoint input

theorem stack_sources_disjoint [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1044a0 768 96 496)
    {srcOffset dstOffset len : Nat} (srcBound : srcOffset ≤ 496) (dstBound : dstOffset ≤ 496)
    (src : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 srcOffset)
    (dst : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 dstOffset)
    (apart : srcOffset + len ≤ dstOffset ∨ dstOffset + len ≤ srcOffset) :
    (t.regValue .rsi).toNat + len ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + len ≤ (t.regValue .rsi).toNat := by
  have bounds := P256.Proofs.Program.stack_bounds pre.stack
  rw [src, dst, P256.Proofs.Program.stack_sub_toNat pre.stack srcBound, P256.Proofs.Program.stack_sub_toNat pre.stack dstBound]
  omega

end P256.Proofs.Projective.Multiply.Machine.Lookup
