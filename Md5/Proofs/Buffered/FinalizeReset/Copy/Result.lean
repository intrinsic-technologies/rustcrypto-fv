import Md5.Proofs.Buffered.FinalizeReset.Copy.Properties

namespace Md5.Proofs.Buffered.FinalizeReset.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Result [Bindings] (kind : Kind) (s t : RamState) (variant : Variant := .saved) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = kind.exit variant
  rsp : stackPtr t = stackPtr s
  rdi : (Operand.reg 7 : Operand 64).read t = stackPtr s + 0xe8
  rsi : (Operand.reg 6 : Operand 64).read t = stackPtr s + 0x60
  rdx : (Operand.reg 2 : Operand 64).read t = 1
  copied : ∀ i < kind.length, t.external[stackPtr s + 96 + BitVec.ofNat 64 i]? =
    s.external[stackPtr s + 8 + BitVec.ofNat 64 i]?
  agrees : AgreesExcept (changes kind s) s t
  effect : (Copy.effect kind s variant).Holds s t

end Md5.Proofs.Buffered.FinalizeReset.Copy
