import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Decrypt
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn1001f0.Part1
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn1001f0.Part2
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part1
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part2
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part3
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part4
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn101ce0
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn101e30
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Functions

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

theorem Label.G0.liftedBlock [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    ∀ l : Label.G0, LiftedBlock code lifted (.g0 l)
  | .l1001f0 => block_l1001f0 code hcode
  | .l10024c => block_l10024c code hcode
  | .l1002e5 => block_l1002e5 code hcode
  | .l100384 => block_l100384 code hcode
  | .l10038c => block_l10038c code hcode
  | .l1003ae => block_l1003ae hstride code hcode
  | .l1003e3 => block_l1003e3 code hcode
  | .l100417 => block_l100417 code hcode
  | .l100420 => block_l100420 code hcode
  | .l10042c => block_l10042c code hcode
  | .l100435 => block_l100435 code hcode
  | .l10043a => block_l10043a code hcode
  | .l10045a => block_l10045a code hcode
  | .l10046e => block_l10046e code hcode
  | .l100479 => block_l100479 code hcode
  | .l10049a => block_l10049a code hcode
  | .l1004a0 => block_l1004a0 code hcode
  | .l1004ac => block_l1004ac code hcode
  | .l1004b5 => block_l1004b5 code hcode
  | .l1004c2 => block_l1004c2 code hcode
  | .l1004dd => block_l1004dd code hcode
  | .l1004f1 => block_l1004f1 code hcode
  | .l1004fc => block_l1004fc code hcode
  | .l100520 => block_l100520 code hcode
  | .l100577 => block_l100577 code hcode
  | .l1005d2 => block_l1005d2 code hcode
  | .l1005e4 => block_l1005e4 code hcode
  | .l1005e8 => block_l1005e8 code hcode
  | .l1005ea => block_l1005ea code hcode
  | .l1005fc => block_l1005fc code hcode
  | .l100620 => block_l100620 code hcode
  | .l100a80 => block_l100a80 code hcode
  | .l100aae => block_l100aae code hcode
  | .l100ad0 => block_l100ad0 code hcode
  | .l100b04 => block_l100b04 code hcode
  | .l100b10 => block_l100b10 code hcode
  | .l100b14 => block_l100b14 code hcode
  | .l100b30 => block_l100b30 code hcode
  | .l100b76 => block_l100b76 code hcode
  | .l100b7b => block_l100b7b code hcode
  | .l100b90 => block_l100b90 code hcode
  | .l100ba5 => block_l100ba5 code hcode
  | .l100bde => block_l100bde code hcode
  | .l100c70 => block_l100c70 code hcode
  | .l100cd0 => block_l100cd0 code hcode
  | .l100d02 => block_l100d02 code hcode
  | .l100d26 => block_l100d26 code hcode
  | .l100d4a => block_l100d4a code hcode
  | .l100d72 => block_l100d72 code hcode
  | .l100d94 => block_l100d94 code hcode
  | .l100dba => block_l100dba code hcode
  | .l100dea => block_l100dea code hcode
  | .l100e0e => block_l100e0e code hcode
  | .l100e19 => block_l100e19 code hcode
  | .l100e8c => block_l100e8c code hcode
  | .l100efe => block_l100efe code hcode
  | .l100f8e => block_l100f8e code hcode
  | .l100fd0 => block_l100fd0 code hcode
  | .l101036 => block_l101036 code hcode
  | .l1010b3 => block_l1010b3 code hcode
  | .l1010cc => block_l1010cc code hcode
  | .l1010d5 => block_l1010d5 code hcode
  | .l10111d => block_l10111d code hcode
  | .l101174 => block_l101174 code hcode

theorem Label.G1.liftedBlock [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    ∀ l : Label.G1, LiftedBlock code lifted (.g1 l)
  | .l101180 => block_l101180 code hcode
  | .l1011be => block_l1011be code hcode
  | .l1011e7 => block_l1011e7 code hcode
  | .l10120f => block_l10120f code hcode
  | .l101233 => block_l101233 code hcode
  | .l10125b => block_l10125b code hcode
  | .l101281 => block_l101281 code hcode
  | .l1012b0 => block_l1012b0 code hcode
  | .l1012d8 => block_l1012d8 code hcode
  | .l1012e3 => block_l1012e3 code hcode
  | .l10133c => block_l10133c code hcode
  | .l101386 => block_l101386 code hcode
  | .l1013bf => block_l1013bf code hcode
  | .l1013e3 => block_l1013e3 code hcode
  | .l101420 => block_l101420 code hcode
  | .l101467 => block_l101467 code hcode
  | .l10146c => block_l10146c code hcode
  | .l101490 => block_l101490 code hcode
  | .l1014a4 => block_l1014a4 code hcode
  | .l1014a8 => block_l1014a8 code hcode
  | .l1014aa => block_l1014aa code hcode
  | .l1014c0 => block_l1014c0 code hcode
  | .l101526 => block_l101526 code hcode
  | .l10152c => block_l10152c code hcode
  | .l10153a => block_l10153a code hcode
  | .l101552 => block_l101552 code hcode
  | .l101562 => block_l101562 code hcode
  | .l101572 => block_l101572 code hcode
  | .l10158b => block_l10158b code hcode
  | .l101596 => block_l101596 code hcode
  | .l1015d4 => block_l1015d4 code hcode
  | .l1015d8 => block_l1015d8 code hcode
  | .l1015e5 => block_l1015e5 code hcode
  | .l1015ed => block_l1015ed code hcode
  | .l1015ff => block_l1015ff code hcode
  | .l10160d => block_l10160d code hcode
  | .l101611 => block_l101611 code hcode
  | .l101616 => block_l101616 code hcode
  | .l101625 => block_l101625 code hcode
  | .l101639 => block_l101639 code hcode
  | .l10163b => block_l10163b code hcode
  | .l101aa0 => block_l101aa0 code hcode
  | .l101ce0 => block_l101ce0 code hcode
  | .l101d20 => block_l101d20 code hcode
  | .l101d69 => block_l101d69 code hcode
  | .l101db0 => block_l101db0 code hcode
  | .l101dec => block_l101dec code hcode
  | .l101e24 => block_l101e24 code hcode
  | .l101ab0 => block_l101ab0 code hcode
  | .l101af1 => block_l101af1 code hcode
  | .l101b40 => block_l101b40 code hcode
  | .l101b85 => block_l101b85 code hcode
  | .l101bcd => block_l101bcd code hcode
  | .l101c13 => block_l101c13 code hcode
  | .l101c63 => block_l101c63 code hcode
  | .l101ca5 => block_l101ca5 code hcode
  | .l101e30 => block_l101e30 code hcode
  | .l101e40 => block_l101e40 code hcode
  | .l102020 => block_l102020 code hcode
  | .l102026 => block_l102026 code hcode
  | .l10202a => block_l10202a code hcode
  | .l102d70 => block_l102d70 hstride code hcode
  | .l102dc0 => block_l102dc0 hstride code hcode

theorem blocks [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    ∀ l : Label, LiftedBlock code lifted l
  | .g0 l => Label.G0.liftedBlock hstride code hcode l
  | .g1 l => Label.G1.liftedBlock hstride code hcode l

theorem simulation [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code)
    {boundary : ReturnBoundary} (hout : ReturnOutside boundary code) :
    Simulation (machineAnyReturn boundary) (lifted.program.sem (dialect code))
      (Rel code lifted) (RetRel code lifted) :=
  ChaCha20Poly1305.Proofs.Lift.Lifted.simulation (P := lifted) (blocks hstride code hcode) hout

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
