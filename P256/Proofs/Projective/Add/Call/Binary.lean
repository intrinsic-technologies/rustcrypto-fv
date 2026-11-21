import P256.Proofs.Program.FieldCall.Binary
import P256.Proofs.Projective.Add.Call.Memory

set_option autoImplicit false

namespace P256.Proofs.Projective.Add.Call

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open X86 X86.Machine X86.UserProcess X86Proofs

abbrev BinaryCallSite (entry : BitVec 64) (reserve : Nat) :=
  Program.FieldCall.BinaryCallSite 920 632 entry reserve

theorem binary_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {reserve x y : Nat} {op : Nat → Nat → Nat}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (site : BinaryCallSite entry reserve)
    (routine : ∀ (v : RamState), BinaryFieldPre v boundary entry reserve →
      MontgomeryAt v (v.regValue .rsi) x → MontgomeryAt v (v.regValue .rdx) y →
      ∃ u, CalleeResult v u boundary 32 reserve ∧ MontgomeryAt u (v.regValue .rdi) (op x y))
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 site.layout.inputOffset)
    (right : t.regValue .rdx = stackPtr s - BitVec.ofNat 64 site.rightOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 site.layout.outputOffset)
    (hx : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 site.layout.inputOffset) x)
    (hy : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 site.rightOffset) y) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) ∧
      MontgomeryAt u (stackPtr s - BitVec.ofNat 64 site.layout.outputOffset) (op x y) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 632 → len ≤ offset + 8 →
        (offset + 32 ≤ site.layout.outputOffset ∨ site.layout.outputOffset + len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) ∧
      MemoryWriteFrame t u #v[workRegion s 920] := by
  exact Program.FieldCall.binary_call pre state site routine rip input right output hx hy

end P256.Proofs.Projective.Add.Call
