import K256.Proofs.Sec1.Square.Program
import K256.Proofs.Sec1.LIR.Fn1145f0.Frame

namespace K256.Proofs.Sec1.Square

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude

def core : LayoutCore program Square.dialect LIR.lifted Unit where
  start _ := .g0 .l1145f0
  Params _ := Store
  args _ _ := #v[]
  store _ s := s
  atoms _ _ fr s := [.words fr.rsi 64 s.1, .readable fr.rsi 40, .words fr.rdi 64 s.2,
    .writable fr.rdi 40, .fact (fr.rdi.toNat % 8 = 0),
    .fact (fr.rdi.toNat + 40 ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 40 ≤ fr.rdi.toNat),
    .fact (fr.rsi.toNat + 40 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rsi.toNat),
    .fact (fr.rdi.toNat + 40 ≤ 0x1145f0 ∨ 0x1148c4 ≤ fr.rdi.toNat),
    .fact (fr.rsp.toNat + 8 ≤ 0x1145f0 ∨ 0x1148c4 ≤ fr.low.toNat),
    .fact (fr.rdi.toNat + 40 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat)]
  Result := Store
  output s := ⟨#v[], none, s⟩
  done _ fr s := [.gpr 0 fr.rdi, .words fr.rsi 64 s.1, .words fr.rdi 64 s.2]
  footprint _ fr := [⟨fr.rdi.toNat, 40⟩]

def layout := Layout.withFrame LIR.Fn1145f0.frameAt LIR.Fn1145f0.doneAt core

end K256.Proofs.Sec1.Square
