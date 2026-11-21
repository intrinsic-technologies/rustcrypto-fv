import ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Program

namespace ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound.TailRounds
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open Standards.RFC.ChaCha20Poly1305
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

def layout : Layout program dialect lifted Activation where
  start
    | .q0 => .l101180
    | .q1 => .l1011be
    | .q2 => .l1011e7
    | .q3 => .l10120f
    | .q4 => .l101233
    | .q5 => .l10125b
    | .q6 => .l101281
    | .q7 => .l1012b0
    | .count => .l1012d8
    | .finish => .l1012e3
  Params := fun _ => Data
  args := fun _ p => #v[p]
  store := fun _ _ => ()
  atoms := fun l fr p =>
    [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩,
     .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
     .writable fr.rsp 128,
     .fact (fr.rsp.toNat + 128 ≤ 0x101180 ∨ 0x1012e3 ≤ fr.rsp.toNat),
     .mem (fr.rsp + 88) 64 p.count] ++ match l with
    | .q0 | .q7 | .count | .finish =>
      [.mem (fr.rsp + 8) 32 p.words[0].toBitVec,
       .low 13 32 p.words[1].toBitVec,
       .low 0 32 p.words[2].toBitVec,
       .low 7 32 p.words[3].toBitVec,
       .low 9 32 p.words[4].toBitVec,
       .low 5 32 p.words[5].toBitVec,
       .low 15 32 p.words[6].toBitVec,
       .low 6 32 p.words[7].toBitVec,
       .mem (fr.rsp + 4) 32 p.words[8].toBitVec,
       .low 10 32 p.words[9].toBitVec,
       .low 14 32 p.words[10].toBitVec,
       .low 12 32 p.words[11].toBitVec,
       .low 1 32 p.words[12].toBitVec,
       .low 2 32 p.words[13].toBitVec,
       .low 8 32 p.words[14].toBitVec,
       .low 11 32 p.words[15].toBitVec]
    | .q1 =>
      [.low 3 32 p.words[0].toBitVec,
       .low 13 32 p.words[1].toBitVec,
       .low 0 32 p.words[2].toBitVec,
       .low 7 32 p.words[3].toBitVec,
       .low 9 32 p.words[4].toBitVec,
       .low 5 32 p.words[5].toBitVec,
       .low 15 32 p.words[6].toBitVec,
       .low 6 32 p.words[7].toBitVec,
       .mem (fr.rsp + 4) 32 p.words[8].toBitVec,
       .low 10 32 p.words[9].toBitVec,
       .low 14 32 p.words[10].toBitVec,
       .low 12 32 p.words[11].toBitVec,
       .low 1 32 p.words[12].toBitVec,
       .low 2 32 p.words[13].toBitVec,
       .low 8 32 p.words[14].toBitVec,
       .low 11 32 p.words[15].toBitVec]
    | .q2 | .q3 | .q4 =>
      [.low 3 32 p.words[0].toBitVec,
       .low 13 32 p.words[1].toBitVec,
       .low 0 32 p.words[2].toBitVec,
       .low 7 32 p.words[3].toBitVec,
       .low 9 32 p.words[4].toBitVec,
       .low 5 32 p.words[5].toBitVec,
       .low 15 32 p.words[6].toBitVec,
       .low 6 32 p.words[7].toBitVec,
       .mem (fr.rsp + 4) 32 p.words[8].toBitVec,
       .mem (fr.rsp + 20) 32 p.words[9].toBitVec,
       .low 14 32 p.words[10].toBitVec,
       .low 12 32 p.words[11].toBitVec,
       .low 1 32 p.words[12].toBitVec,
       .low 2 32 p.words[13].toBitVec,
       .low 8 32 p.words[14].toBitVec,
       .low 11 32 p.words[15].toBitVec]
    | .q5 | .q6 =>
      [.mem (fr.rsp + 8) 32 p.words[0].toBitVec,
       .low 13 32 p.words[1].toBitVec,
       .low 0 32 p.words[2].toBitVec,
       .low 7 32 p.words[3].toBitVec,
       .low 9 32 p.words[4].toBitVec,
       .low 5 32 p.words[5].toBitVec,
       .low 15 32 p.words[6].toBitVec,
       .low 6 32 p.words[7].toBitVec,
       .mem (fr.rsp + 4) 32 p.words[8].toBitVec,
       .mem (fr.rsp + 20) 32 p.words[9].toBitVec,
       .low 14 32 p.words[10].toBitVec,
       .low 12 32 p.words[11].toBitVec,
       .low 1 32 p.words[12].toBitVec,
       .low 2 32 p.words[13].toBitVec,
       .low 8 32 p.words[14].toBitVec,
       .low 11 32 p.words[15].toBitVec]
  Result := Unit
  output := fun _ => ⟨#v[], none, ()⟩
  done := fun _ _ => []
  retAddr := fun fr => fr.ret
  original := fun fr => fr.original
  regions := fun fr => [⟨fr.rsp.toNat + 4, 4⟩, ⟨fr.rsp.toNat + 8, 4⟩, ⟨fr.rsp.toNat + 20, 4⟩, ⟨fr.rsp.toNat + 88, 8⟩, ⟨fr.rsp.toNat + 120, 4⟩]

end ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound.TailRounds
