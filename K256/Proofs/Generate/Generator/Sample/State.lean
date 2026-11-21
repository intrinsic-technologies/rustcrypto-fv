import K256.Proofs.Generate.Sampling
import K256.Proofs.Generate.SigningKey
import K256.Proofs.Generate.Memory
import K256.Proofs.Generate.LIR.Fn105f30.Frame

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

abbrev Registers := Vector Value Reg.count

def regions (fr : Activation) : List MemoryRegion :=
  [fr.region, ⟨fr.rsi.toNat, 16⟩]

structure Entry (s : RamState) (fr : Activation) (a : Registers) : Prop where
  atoms : Atom.All Extracted.programImage a fr.original (Fn105f30.frameAt .l105f30 fr)
  rsp : fr.rsp = s.regValue .rsp - 288
  low : fr.low = s.regValue .rsp - 10584
  descriptor : fr.rsi = s.regValue .rsp - 208
  base : memLoad fr.original fr.rsi 64 = s.regValue .rsi
  length : memLoad fr.original (fr.rsi + 8) 64 = s.regValue .rdx
  writes : RamWriteFrame s.external fr.original [Stack.region s signingKeyGenerateFromRng.minStackBytes]

def cursor (s : RamState) (block : Nat) : BitVec 64 :=
  s.regValue .rsi + BitVec.ofNat 64 (32 * (block + 1))

def remaining (random : ByteArray) (block : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (random.size - 32 * block)

def word (s : RamState) (block i : Nat) : BitVec 64 :=
  Common.scalarWord s.external (BitVec.ofNat 64 ((s.regValue .rsi).toNat + 32 * block)) i

structure Frame (label : Label) (fr : Activation) (a : Registers) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn105f30.frameAt label fr)
  writes : RamWriteFrame fr.original m (regions fr)

structure AtBlock (s : RamState) (random : ByteArray) (fr : Activation) (block : Nat)
    (a : Registers) (m : Ram) : Prop extends Frame .l106020 fr a m where
  rdxWidth : a[2].width = 64
  r8Width : a[8].width = 64
  r9Width : a[9].width = 64
  cursorReg : a[5] = ⟨64, cursor s block⟩
  remainingReg : a[13] = ⟨64, remaining random block⟩
  scratch : a[12] = ⟨64, fr.rsp - 288⟩
  decoded : a[15] = ⟨64, fr.rsp - 168⟩

structure AfterDecode (s : RamState) (random : ByteArray) (fr : Activation) (block : Nat)
    (a : Registers) (m : Ram) : Prop extends Frame .l10605d fr a m where
  rdxWidth : a[2].width = 64
  r8Width : a[8].width = 64
  r9Width : a[9].width = 64
  cursorReg : a[5] = ⟨64, cursor s block⟩
  remainingReg : a[13] = ⟨64, remaining random block⟩
  nextLength : a[3] = ⟨64, remaining random (block+1)⟩
  scratch : a[12] = ⟨64, fr.rsp - 288⟩
  decoded : a[15] = ⟨64, fr.rsp - 168⟩
  limbs : WordsAt m (fr.rsp - 168) 64 (Vector.ofFn fun i : Fin 4 => word s block i.val)
  flag : memLoad m (fr.rsp - 136) 8 =
    (Sampling.orderFlag (word s block 0) (word s block 1) (word s block 2) (word s block 3)).setWidth 8

structure Accepted (fr : Activation) (d : Nat) (a : Registers) (m : Ram) :
    Prop extends Frame .l10607d fr a m where
  widths : ∀ r : Fin Reg.count, r.val ∈ [2, 3, 5, 8, 9, 12, 13, 15] → a[r].width = 64
  limbs : WordsAt m (fr.rsp - 352) 64
    (Vector.ofFn fun i : Fin 4 => BitVec.ofNat 64 (d / 2^(64*i.val)))

end K256.Proofs.Generate.Generator.Sample
