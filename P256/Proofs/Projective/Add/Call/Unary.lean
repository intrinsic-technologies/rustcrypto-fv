import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.Projective.Add.Call.Memory

set_option autoImplicit false

namespace P256.Proofs.Projective.Add.Call

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open X86 X86.Machine X86.UserProcess X86Proofs

theorem unary_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {outputBytes reserve x : Nat} {resultAt : RamState → BitVec 64 → Prop}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (layout : StackCallLayout 920 32 outputBytes reserve) (layoutStack : layout.stackOffset = 640)
    (outputSaved : outputBytes + 48 ≤ layout.outputOffset)
    (codeOffset : Nat) (disp : BitVec 32) (codeBound : codeOffset + 5 < 118431)
    (bytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 5 (disp.signExtend 64) = entry)
    (entryLow : entry.toNat < 2^32) (entryProgram : InProgram entry)
    (routine : ∀ (v : RamState), CalleePre v boundary entry 32 outputBytes reserve →
      MontgomeryAt v (v.regValue .rsi) x →
      ∃ u, CalleeResult v u boundary outputBytes reserve ∧ resultAt u (v.regValue .rdi))
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 layout.inputOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 layout.outputOffset)
    (hx : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 layout.inputOffset) x)
 :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64) ∧
      resultAt u (stackPtr s - BitVec.ofNat 64 layout.outputOffset) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 632 → len ≤ offset + 8 →
        (offset + outputBytes ≤ layout.outputOffset ∨ layout.outputOffset + len ≤ offset) →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) ∧
      MemoryWriteFrame t u #v[workRegion s 920] := by
  exact Program.FieldCall.unary_call pre state layout layoutStack outputSaved codeOffset disp codeBound bytes target entryLow entryProgram routine rip input output hx

end P256.Proofs.Projective.Add.Call
