import Hkdf.Proofs.Standard.State

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Update

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common

structure PreparedInput [Bindings] (initial s : RamState) (salt : Option ByteArray)
    (inputs : Array Input) (index : Nat) (short : Bool) : Prop extends
    Buffered initial s salt (prefixConcatenation inputs index) where
  remaining : index < inputs.size
  rip : s.RIP = if short then 0x101620 else 0x101674
  pointer : s.regValue .r13 = (inputs[index]'remaining).address
  length : s.regValue .rbx = BitVec.ofNat 64 (inputs[index]'remaining).bytes.size
  tail : s.regValue .r15 = BitVec.ofNat 64 ((prefixConcatenation inputs index).size % 64)
  capacity : s.regValue .rdx = BitVec.ofNat 64
    (64 - (prefixConcatenation inputs index).size % 64)
  rest : s.regValue .rbp = BitVec.ofNat 64 (inputs[index]'remaining).bytes.size -
    BitVec.ofNat 64 (64 - (prefixConcatenation inputs index).size % 64)
  indexRegister : s.regValue .r14 = BitVec.ofNat 64 index
  copyRegister : s.regValue .r12 = 0x10dd60
  branch : if short then
      (inputs[index]'remaining).bytes.size < 64 - (prefixConcatenation inputs index).size % 64
    else 64 - (prefixConcatenation inputs index).size % 64 ≤ (inputs[index]'remaining).bytes.size

structure InputDone [Bindings] (initial s : RamState) (salt : Option ByteArray)
    (inputs : Array Input) (index : Nat) (short : Bool) : Prop extends
    Buffered initial s salt (prefixConcatenation inputs (index + 1)) where
  remaining : index < inputs.size
  rip : s.RIP = if short then 0x10163b else 0x101706
  indexRegister : s.regValue .r14 = BitVec.ofNat 64 index
  copyRegister : s.regValue .r12 = 0x10dd60

structure BulkInput [Bindings] (initial s : RamState) (salt : Option ByteArray)
    (inputs : Array Input) (i : Fin inputs.size) (consumed : Nat) (direct : Bool) : Prop extends
    Buffered initial s salt (prefixConcatenation inputs i.val ++
      inputs[i].bytes.extract 0 consumed) where
  consumedBound : consumed ≤ inputs[i].bytes.size
  aligned : (prefixConcatenation inputs i.val ++ inputs[i].bytes.extract 0 consumed).size % 64 = 0
  rip : s.RIP = if direct then 0x101719 else 0x1016b9
  pointer : s.regValue .r13 = inputs[i].address + BitVec.ofNat 64 consumed
  length : s.regValue .rbp = BitVec.ofNat 64 (inputs[i].bytes.size - consumed)
  indexRegister : s.regValue .r14 = BitVec.ofNat 64 i.val
  copyRegister : s.regValue .r12 = 0x10dd60

end Hkdf.Proofs.Standard.Update
