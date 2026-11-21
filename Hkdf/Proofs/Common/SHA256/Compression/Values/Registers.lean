import Hkdf.Proofs.Common.SHA256.ValueRefinement
import Hkdf.Proofs.Common.SHA256.Compression.Interface
import Hkdf.Proofs.Common.SHA256.Mathematics.BitVecModel

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Values

open Hkdf.Spec Hkdf.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

def hashState (values : Values) : BitVecState :=
  ⟨(values.regs 3).setWidth 32, (values.regs 14).setWidth 32,
    (values.regs 0).setWidth 32, (values.regs 9).setWidth 32,
    (values.regs 8).setWidth 32, (values.regs 10).setWidth 32,
    (values.regs 2).setWidth 32, (values.regs 1).setWidth 32⟩

theorem hashState_ofRam {s : RamState} {hash : Array UInt32}
    (registers : RegistersAt s hash) :
    hashState (ofRam s) = BitVecState.ofState (SHA256.State.ofArray hash) := by
  change BitVecState.mk _ _ _ _ _ _ _ _ = _
  rw [show ((ofRam s).regs 3).setWidth 32 = hash[0]!.toBitVec from registers.a,
    show ((ofRam s).regs 14).setWidth 32 = hash[1]!.toBitVec from registers.b,
    show ((ofRam s).regs 0).setWidth 32 = hash[2]!.toBitVec from registers.c,
    show ((ofRam s).regs 9).setWidth 32 = hash[3]!.toBitVec from registers.d,
    show ((ofRam s).regs 8).setWidth 32 = hash[4]!.toBitVec from registers.e,
    show ((ofRam s).regs 10).setWidth 32 = hash[5]!.toBitVec from registers.f,
    show ((ofRam s).regs 2).setWidth 32 = hash[6]!.toBitVec from registers.g,
    show ((ofRam s).regs 1).setWidth 32 = hash[7]!.toBitVec from registers.h]
  rfl

theorem Represents.hashState_eq {context : ValueContext} {values : Values} {s : RamState}
    (rep : Represents context values s) : hashState values = hashState (ofRam s) := by
  simp only [hashState, rep.regs, ofRam]

theorem Represents.registersAt {context : ValueContext} {values : Values} {s : RamState}
    {hash : Array UInt32} (rep : Represents context values s) (size : hash.size = 8)
    (words : hashState values = BitVecState.ofState (SHA256.State.ofArray hash)) :
    RegistersAt s hash := by
  rw [rep.hashState_eq] at words
  exact ⟨size, congrArg BitVecState.a words, congrArg BitVecState.b words,
    congrArg BitVecState.c words, congrArg BitVecState.d words,
    congrArg BitVecState.e words, congrArg BitVecState.f words,
    congrArg BitVecState.g words, congrArg BitVecState.h words⟩

end Hkdf.Proofs.Common.SHA256.Compression.Values
