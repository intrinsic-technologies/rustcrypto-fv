import Hkdf.Proofs.Common.Pad.Layout
import Hkdf.Proofs.Common.Refine

namespace Hkdf.Proofs.Common.Pad

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program

structure Pre [bindings : Bindings] (v : Variant) (boundary : ReturnBoundary) (s : RamState)
    (pointer : BitVec 64) (bytes : ByteArray) : Prop where
  machine : Hkdf.Proofs.Program.SupportedMachine bindings s
  loaded : ProgramLoaded s
  directionFlag : RFLAGS.DirectionFlagClear s.RFLAGS
  outside : ¬ InProgram boundary.rip
  rip : s.RIP = v.entry
  index : s.regValue .rax = BitVec.ofNat 64 (layout v).first
  base : pointer = s.regValue .rsp + BitVec.ofNat 64 (layout v).bufferOffset
  bytes : (⟨pointer.toNat, 64⟩ : MemoryRegion).HasBytes s.external bytes
  writable : Hkdf.Proofs.Refine.Writable Extracted.programImage s.external pointer 64

def Contract [Bindings] (v : Variant) (boundary : ReturnBoundary) (s : RamState)
    (pointer : BitVec 64) (bytes : ByteArray) : Prop :=
  ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
    t.RIP = v.exit ∧ t.regValue .rax = BitVec.ofNat 64 ((layout v).first + 64) ∧
    AgreesExcept (components pointer) s t ∧
    (⟨pointer.toNat, 64⟩ : MemoryRegion).HasBytes t.external
      (HMAC.xorPad bytes (layout v).mask)

end Hkdf.Proofs.Common.Pad
