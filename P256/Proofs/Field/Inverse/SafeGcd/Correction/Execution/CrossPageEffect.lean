import P256.Proofs.Common.Instructions.CrossPageStore.Mov
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage

open X86 X86.Machine X86.UserProcess X86Proofs

structure StorePre (p : BitVec 64) (codeLen : Nat) (addr : RamState → BitVec 64) (len : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  read : MemReadable s (addr s) len
  tables : PageTableEntriesApart (addr s).toNat len
  code : RangeApart (addr s) len p codeLen

theorem mov_m64_r64_effect_step_any [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 8)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM64R64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s ready code h
  exact P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    p rex hrex reg am hv hx hb s ready code ⟨h.rip, ⟨h.read, h.tables⟩, h.code⟩

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
