import K256.Proofs.Generate.Generator.Multiply.Constants
import K256.Proofs.Generate.Generator.Multiply.State
import K256.Proofs.Generate.LIR.Fn11c510.Frame

namespace K256.Proofs.Generate.Generator.Multiply.Lookup

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field
  Standards.SECG.ECC

def stage : Nat → Label
  | 0 => .l11c55b
  | 1 => .l11c591
  | 2 => .l11c5c0
  | 3 => .l11c5f2
  | 4 => .l11c624
  | 5 => .l11c656
  | 6 => .l11c688
  | 7 => .l11c6ba
  | _ => .l11c6ed

def choice (digit : Int) (i : Nat) : Bool :=
  if i < 8 then decide (digit.natAbs = i + 1) else decide (digit < 0)

def window (fr : Activation) : MemoryRegion := ⟨(fr.rsp - 0x1f0).toNat, 0x1f0⟩

structure Scanning (fr : Activation) (entry : Ram) (digit : Int) (i : Nat)
    (a : Registers) (m : Ram) (point : Projective) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn11c510.frameAt .l11c6ed fr)
  accumulator : a[14].get 64 = fr.rsp - 0x198
  temporary : 0 < i → i < 8 → a[12].get 64 = fr.rsp - 0xa8
  table : i < 8 → a[15].get 64 = fr.rsi
  digitByte : i < 8 → (a[5].get 64).setWidth 8 = BitVec.ofInt 8 digit
  magnitudeByte : i < 8 → (a[13].get 64).setWidth 8 = BitVec.ofNat 8 digit.natAbs
  flag : (a[0].get 64).setWidth 8 = (if choice digit i then 1 else 0)
  stored : point.Stored m (fr.rsp - 0x198)
  writes : RamWriteFrame entry m [window fr]

end K256.Proofs.Generate.Generator.Multiply.Lookup
