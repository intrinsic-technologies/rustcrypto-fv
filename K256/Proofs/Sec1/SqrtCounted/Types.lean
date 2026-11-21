import K256.Proofs.Sec1.Sqrt.Rounds
import K256.Proofs.Sec1.Parser.Control
import K256.Proofs.Sec1.LIR.Fn115950.Frame

namespace K256.Proofs.Sec1.Sqrt.SquareLoop

open X86Proofs Lift LIR

def head : SquareLoop → LIR.Label
  | .first44 => .l118040
  | .middle88 => .l1184d0
  | .last44 => .l118950

def resume : SquareLoop → LIR.Label
  | .first44 => .l11804b
  | .middle88 => .l1184db
  | .last44 => .l11895b

def exit : SquareLoop → LIR.Label
  | .first44 => .l118081
  | .middle88 => .l118511
  | .last44 => .l118991

def countReg : SquareLoop → Fin Reg.count
  | .first44 => 3
  | _ => 15

def srcReg : SquareLoop → Fin Reg.count
  | .first44 => 15
  | _ => 14

def dstReg : SquareLoop → Fin Reg.count
  | .first44 => 14
  | _ => 3

end K256.Proofs.Sec1.Sqrt.SquareLoop
