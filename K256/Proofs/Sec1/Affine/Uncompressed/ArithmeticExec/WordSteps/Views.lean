import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.WordSteps.Schedule

namespace K256.Proofs.Sec1.Affine.Uncompressed

open K256.Proofs.Common.Field

def ArithmeticState.xWords (s : ArithmeticState) : Limbs :=
  #v[s.slots 10, s.slots 6, s.slots 11, s.slots 7, s.slots 4]

def ArithmeticState.yWords (s : ArithmeticState) : Limbs :=
  #v[s.slots 23, s.slots 21, s.slots 18, s.slots 20, s.slots 22]

def ArithmeticState.squareYWords (s : ArithmeticState) : Limbs :=
  #v[s.slots 19, s.slots 17, s.slots 16, s.slots 13, s.slots 14]

def ArithmeticState.squareXWords (s : ArithmeticState) : Limbs :=
  #v[s.slots 3, s.slots 2, s.slots 9, s.slots 5, s.slots 0]

def ArithmeticState.yRegs (s : ArithmeticState) : Limbs :=
  #v[s.regs 15, s.regs 13, s.regs 12, s.regs 5, s.regs 14]

def ArithmeticState.productWords (s : ArithmeticState) : Limbs :=
  #v[s.slots 8, s.regs 14, s.regs 8, s.regs 10, (s.regs 7 &&& 0xffffffffffff) + s.regs 2]

end K256.Proofs.Sec1.Affine.Uncompressed
