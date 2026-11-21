import ChaCha20Poly1305.Proofs.Decrypt.Stream
import ChaCha20Poly1305.Proofs.Decrypt.TailRounds
import ChaCha20Poly1305.Proofs.Decrypt.Refine

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Tail
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Standards.RFC.ChaCha20Poly1305

inductive Label | setup | loads | save | round | feed | counter | store | one | four

def rem64 (n : BitVec 64) := (n.setWidth 32 &&& 63).setWidth 64
def base64 (n : BitVec 64) := n &&& 18446744073709551552

def program (x : Input) : Program (fun _ => _root_.Empty) Label (fun _ => 0) 0 := ⟨fun
  | .setup => .terminate (.br ⟨.loads,#v[]⟩)
  | .loads => .terminate (.br ⟨.save,#v[]⟩)
  | .save => .terminate (.br ⟨.round,#v[]⟩)
  | .round => .terminate (.br ⟨.feed,#v[]⟩)
  | .feed => .terminate (.br ⟨.counter,#v[]⟩)
  | .counter => .terminate (.br ⟨.store,#v[]⟩)
  | .store => .terminate (.br ⟨if (rem64 x.n).toNat < 4 then .one else .four,#v[]⟩)
  | _ => .terminate (.ret #v[])⟩

@[refine_layout] def common (x : Input) (fr : Activation) : List Atom :=
  [.writable fr.rsp 176,.writable fr.rdi 128,
   .fact (fr.rsp.toNat+176 ≤ 0x1010d5 ∨ 0x101420 ≤ fr.rsp.toNat),
   .fact (fr.rdi.toNat+128 ≤ 0x1010d5 ∨ 0x101420 ≤ fr.rdi.toNat),
   .fact (fr.rsp.toNat+176 ≤ fr.rdi.toNat ∨ fr.rdi.toNat+128 ≤ fr.rsp.toNat),
   .mem (fr.rsp+72) 64 fr.rdi,.mem (fr.rsp+160) 64 (rem64 x.n),.mem (fr.rsp+168) 64 x.n]

@[refine_layout] def registers (fr : Activation) : List Atom :=
  [.gpr 4 fr.rsp, .reg 22 ⟨1,0⟩,.reg 39 ⟨32,fr.mxcsr⟩,.reg 50 ⟨16,fr.ftw⟩,.reg 51 ⟨16,fr.fcw⟩]

@[refine_layout] def keep (x : Input) (fr : Activation) : List Atom :=
  common x fr ++ [.mem (fr.rsp + 56) 32 x.w[0].toBitVec,
    .mem (fr.rsp + 96) 32 x.w[1].toBitVec,
    .mem (fr.rsp + 104) 32 x.w[2].toBitVec,
    .mem (fr.rsp + 12) 32 x.w[3].toBitVec,
    .mem (fr.rsp + 80) 32 x.w[4].toBitVec,
    .mem (fr.rsp + 112) 32 x.w[5].toBitVec,
    .mem (fr.rsp + 60) 32 x.w[6].toBitVec,
    .mem (fr.rsp + 16) 32 x.w[7].toBitVec,
    .mem (fr.rsp + 24) 32 x.w[8].toBitVec,
    .mem (fr.rsp + 28) 32 x.w[9].toBitVec,
    .mem (fr.rsp + 32) 32 x.w[10].toBitVec,
    .mem (fr.rsp + 36) 32 x.w[11].toBitVec,
    .mem (fr.rsp + 52) 32 x.w[12].toBitVec,
    .mem (fr.rsp + 40) 32 x.w[13].toBitVec,
    .mem (fr.rsp + 44) 32 x.w[14].toBitVec,
    .mem (fr.rsp + 48) 32 x.w[15].toBitVec,
    .mem (fr.rsp + 64) 64 (base64 x.n)]

@[refine_layout] def roundAtoms (fr : Activation) (w : Vector UInt32 16) (n : BitVec 64) : List Atom :=
  registers fr ++ [.writable fr.rsp 128,
    .fact (fr.rsp.toNat+128 ≤ 0x101180 ∨ 0x1012e3 ≤ fr.rsp.toNat),
    .mem (fr.rsp + 88) 64 (n),
    .mem (fr.rsp + 8) 32 (w[0].toBitVec),
    .low 13 32 (w[1].toBitVec),
    .low 0 32 (w[2].toBitVec),
    .low 7 32 (w[3].toBitVec),
    .low 9 32 (w[4].toBitVec),
    .low 5 32 (w[5].toBitVec),
    .low 15 32 (w[6].toBitVec),
    .low 6 32 (w[7].toBitVec),
    .mem (fr.rsp + 4) 32 (w[8].toBitVec),
    .low 10 32 (w[9].toBitVec),
    .low 14 32 (w[10].toBitVec),
    .low 12 32 (w[11].toBitVec),
    .low 1 32 (w[12].toBitVec),
    .low 2 32 (w[13].toBitVec),
    .low 8 32 (w[14].toBitVec),
    .low 11 32 (w[15].toBitVec)]

def layout (x : Input) : Layout (program x) Empty.semantics lifted Activation where
  start
    | .setup => .l1010d5
    | .loads => .l10111d
    | .save => .l101174
    | .round => .l101180
    | .feed => .l1012e3
    | .counter => .l10133c
    | .store => .l101386
    | .one => .l1013bf
    | .four => .l1013e3
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms l fr _ := match l with
    | .setup => registers fr ++ common x fr ++ [.gpr 7 fr.rdi,
    .gpr 11 x.n,
    .mem fr.rdi 32 x.w[0].toBitVec,
    .mem (fr.rdi + 4) 32 x.w[1].toBitVec,
    .mem (fr.rdi + 8) 32 x.w[2].toBitVec,
    .mem (fr.rdi + 12) 32 x.w[3].toBitVec,
    .mem (fr.rdi + 16) 32 x.w[4].toBitVec,
    .mem (fr.rdi + 20) 32 x.w[5].toBitVec,
    .mem (fr.rdi + 24) 32 x.w[6].toBitVec,
    .mem (fr.rdi + 28) 32 x.w[7].toBitVec,
    .mem (fr.rdi + 32) 32 x.w[8].toBitVec,
    .mem (fr.rdi + 36) 32 x.w[9].toBitVec,
    .mem (fr.rdi + 40) 32 x.w[10].toBitVec,
    .mem (fr.rdi + 44) 32 x.w[11].toBitVec,
    .mem (fr.rdi + 48) 32 x.w[12].toBitVec,
    .mem (fr.rdi + 52) 32 x.w[13].toBitVec,
    .mem (fr.rdi + 56) 32 x.w[14].toBitVec,
    .mem (fr.rdi + 60) 32 x.w[15].toBitVec]
    | .loads => registers fr ++ common x fr ++ [.mem (fr.rsp + 64) 64 (base64 x.n),
    .mem (fr.rsp + 12) 32 x.w[3].toBitVec,
    .mem (fr.rsp + 16) 32 x.w[7].toBitVec,
    .low 6 32 (x.w[2].toBitVec),
    .low 3 32 (x.w[0].toBitVec),
    .low 13 32 (x.w[1].toBitVec),
    .low 9 32 (x.w[4].toBitVec),
    .low 5 32 (x.w[5].toBitVec),
    .low 15 32 (x.w[6].toBitVec),
    .low 0 32 (x.w[8].toBitVec),
    .low 10 32 (x.w[9].toBitVec),
    .low 14 32 (x.w[10].toBitVec),
    .low 12 32 (x.w[11].toBitVec),
    .low 1 32 (x.w[12].toBitVec),
    .low 2 32 (x.w[13].toBitVec),
    .low 8 32 (x.w[14].toBitVec),
    .low 11 32 (x.w[15].toBitVec)]
    | .save => registers fr ++ common x fr ++ [.mem (fr.rsp + 56) 32 x.w[0].toBitVec,
    .mem (fr.rsp + 96) 32 x.w[1].toBitVec,
    .mem (fr.rsp + 104) 32 x.w[2].toBitVec,
    .mem (fr.rsp + 12) 32 x.w[3].toBitVec,
    .mem (fr.rsp + 80) 32 x.w[4].toBitVec,
    .mem (fr.rsp + 112) 32 x.w[5].toBitVec,
    .mem (fr.rsp + 60) 32 x.w[6].toBitVec,
    .mem (fr.rsp + 16) 32 x.w[7].toBitVec,
    .mem (fr.rsp + 24) 32 x.w[8].toBitVec,
    .mem (fr.rsp + 28) 32 x.w[9].toBitVec,
    .mem (fr.rsp + 32) 32 x.w[10].toBitVec,
    .mem (fr.rsp + 52) 32 x.w[12].toBitVec,
    .mem (fr.rsp + 40) 32 x.w[13].toBitVec,
    .mem (fr.rsp + 44) 32 x.w[14].toBitVec,
    .mem (fr.rsp + 48) 32 x.w[15].toBitVec,
    .mem (fr.rsp + 64) 64 (base64 x.n),
    .mem (fr.rsp + 88) 64 (10),
    .mem (fr.rsp + 8) 32 (x.w[0].toBitVec),
    .low 13 32 (x.w[1].toBitVec),
    .low 0 32 (x.w[2].toBitVec),
    .low 7 32 (x.w[3].toBitVec),
    .low 9 32 (x.w[4].toBitVec),
    .low 5 32 (x.w[5].toBitVec),
    .low 15 32 (x.w[6].toBitVec),
    .low 6 32 (x.w[7].toBitVec),
    .mem (fr.rsp + 4) 32 (x.w[8].toBitVec),
    .low 10 32 (x.w[9].toBitVec),
    .low 14 32 (x.w[10].toBitVec),
    .low 12 32 (x.w[11].toBitVec),
    .low 1 32 (x.w[12].toBitVec),
    .low 2 32 (x.w[13].toBitVec),
    .low 8 32 (x.w[14].toBitVec),
    .low 11 32 (x.w[15].toBitVec)]
    | .round => roundAtoms fr x.w 10 ++ keep x fr
    | .feed => roundAtoms fr (ChaChaRound.rounds 10 x.w) 0 ++ keep x fr
    | .counter => registers fr ++ common x fr ++ [.mem (fr.rsp + 64) 64 (base64 x.n),
    .mem (fr.rsp + 52) 32 x.w[12].toBitVec,
    .mem (fr.rsp + 8) 32 (((ChaChaRound.rounds 10 x.w)[0].toBitVec + x.w[0].toBitVec)),
    .mem (fr.rsp + 20) 32 (((ChaChaRound.rounds 10 x.w)[1].toBitVec + x.w[1].toBitVec)),
    .mem (fr.rsp + 4) 32 (((ChaChaRound.rounds 10 x.w)[8].toBitVec + x.w[8].toBitVec)),
    .low 1 32 ((ChaChaRound.rounds 10 x.w)[12].toBitVec),
    .low 0 32 (((ChaChaRound.rounds 10 x.w)[2].toBitVec + x.w[2].toBitVec)),
    .low 7 32 (((ChaChaRound.rounds 10 x.w)[3].toBitVec + x.w[3].toBitVec)),
    .low 9 32 (((ChaChaRound.rounds 10 x.w)[4].toBitVec + x.w[4].toBitVec)),
    .low 5 32 (((ChaChaRound.rounds 10 x.w)[5].toBitVec + x.w[5].toBitVec)),
    .low 15 32 (((ChaChaRound.rounds 10 x.w)[6].toBitVec + x.w[6].toBitVec)),
    .low 6 32 (((ChaChaRound.rounds 10 x.w)[7].toBitVec + x.w[7].toBitVec)),
    .low 10 32 (((ChaChaRound.rounds 10 x.w)[9].toBitVec + x.w[9].toBitVec)),
    .low 14 32 (((ChaChaRound.rounds 10 x.w)[10].toBitVec + x.w[10].toBitVec)),
    .low 12 32 (((ChaChaRound.rounds 10 x.w)[11].toBitVec + x.w[11].toBitVec)),
    .low 2 32 (((ChaChaRound.rounds 10 x.w)[13].toBitVec + x.w[13].toBitVec)),
    .low 8 32 (((ChaChaRound.rounds 10 x.w)[14].toBitVec + x.w[14].toBitVec)),
    .low 11 32 (((ChaChaRound.rounds 10 x.w)[15].toBitVec + x.w[15].toBitVec))]
    | .store => registers fr ++ common x fr ++ [.mem (fr.rsp + 64) 64 (base64 x.n),
    .mem (fr.rdi + 48) 32 (x.w[12].toBitVec + 1),
    .gpr 3 (fr.rdi),
    .gpr 9 (fr.rdi),
    .low 0 32 (((ChaChaRound.rounds 10 x.w)[8].toBitVec + x.w[8].toBitVec)),
    .mem (fr.rdi + 64) 32 ((ChaChaRound.rounds 10 x.w)[0].toBitVec + x.w[0].toBitVec),
    .mem (fr.rdi + 68) 32 ((ChaChaRound.rounds 10 x.w)[1].toBitVec + x.w[1].toBitVec),
    .mem (fr.rdi + 72) 32 ((ChaChaRound.rounds 10 x.w)[2].toBitVec + x.w[2].toBitVec),
    .mem (fr.rdi + 76) 32 ((ChaChaRound.rounds 10 x.w)[3].toBitVec + x.w[3].toBitVec),
    .mem (fr.rdi + 80) 32 ((ChaChaRound.rounds 10 x.w)[4].toBitVec + x.w[4].toBitVec),
    .mem (fr.rdi + 84) 32 ((ChaChaRound.rounds 10 x.w)[5].toBitVec + x.w[5].toBitVec),
    .mem (fr.rdi + 88) 32 ((ChaChaRound.rounds 10 x.w)[6].toBitVec + x.w[6].toBitVec),
    .mem (fr.rdi + 92) 32 ((ChaChaRound.rounds 10 x.w)[7].toBitVec + x.w[7].toBitVec),
    .low 10 32 (((ChaChaRound.rounds 10 x.w)[9].toBitVec + x.w[9].toBitVec)),
    .low 14 32 (((ChaChaRound.rounds 10 x.w)[10].toBitVec + x.w[10].toBitVec)),
    .low 12 32 (((ChaChaRound.rounds 10 x.w)[11].toBitVec + x.w[11].toBitVec)),
    .low 1 32 (((ChaChaRound.rounds 10 x.w)[12].toBitVec + x.w[12].toBitVec)),
    .low 2 32 (((ChaChaRound.rounds 10 x.w)[13].toBitVec + x.w[13].toBitVec)),
    .low 8 32 (((ChaChaRound.rounds 10 x.w)[14].toBitVec + x.w[14].toBitVec)),
    .low 11 32 (((ChaChaRound.rounds 10 x.w)[15].toBitVec + x.w[15].toBitVec))]
    | .one => registers fr ++ common x fr ++ [.mem (fr.rsp + 64) 64 (base64 x.n),
    .mem (fr.rdi + 48) 32 (x.w[12].toBitVec + 1),
    .gpr 9 (fr.rdi),
    .gpr 10 (x.n),
    .gpr 14 (rem64 x.n),
    .gpr 0 (((x.n.setWidth 32 &&& 3).setWidth 64)),
    .mem (fr.rdi + 64) 32 ((ChaChaRound.rounds 10 x.w)[0].toBitVec + x.w[0].toBitVec),
    .mem (fr.rdi + 68) 32 ((ChaChaRound.rounds 10 x.w)[1].toBitVec + x.w[1].toBitVec),
    .mem (fr.rdi + 72) 32 ((ChaChaRound.rounds 10 x.w)[2].toBitVec + x.w[2].toBitVec),
    .mem (fr.rdi + 76) 32 ((ChaChaRound.rounds 10 x.w)[3].toBitVec + x.w[3].toBitVec),
    .mem (fr.rdi + 80) 32 ((ChaChaRound.rounds 10 x.w)[4].toBitVec + x.w[4].toBitVec),
    .mem (fr.rdi + 84) 32 ((ChaChaRound.rounds 10 x.w)[5].toBitVec + x.w[5].toBitVec),
    .mem (fr.rdi + 88) 32 ((ChaChaRound.rounds 10 x.w)[6].toBitVec + x.w[6].toBitVec),
    .mem (fr.rdi + 92) 32 ((ChaChaRound.rounds 10 x.w)[7].toBitVec + x.w[7].toBitVec),
    .mem (fr.rdi + 96) 32 ((ChaChaRound.rounds 10 x.w)[8].toBitVec + x.w[8].toBitVec),
    .mem (fr.rdi + 100) 32 ((ChaChaRound.rounds 10 x.w)[9].toBitVec + x.w[9].toBitVec),
    .mem (fr.rdi + 104) 32 ((ChaChaRound.rounds 10 x.w)[10].toBitVec + x.w[10].toBitVec),
    .mem (fr.rdi + 108) 32 ((ChaChaRound.rounds 10 x.w)[11].toBitVec + x.w[11].toBitVec),
    .mem (fr.rdi + 112) 32 ((ChaChaRound.rounds 10 x.w)[12].toBitVec + x.w[12].toBitVec),
    .mem (fr.rdi + 116) 32 ((ChaChaRound.rounds 10 x.w)[13].toBitVec + x.w[13].toBitVec),
    .mem (fr.rdi + 120) 32 ((ChaChaRound.rounds 10 x.w)[14].toBitVec + x.w[14].toBitVec),
    .mem (fr.rdi + 124) 32 ((ChaChaRound.rounds 10 x.w)[15].toBitVec + x.w[15].toBitVec)]
    | .four => registers fr ++ common x fr ++ [.mem (fr.rsp + 64) 64 (base64 x.n),
    .mem (fr.rdi + 48) 32 (x.w[12].toBitVec + 1),
    .gpr 9 (fr.rdi),
    .gpr 10 (x.n),
    .gpr 14 (rem64 x.n),
    .gpr 0 (((x.n.setWidth 32 &&& 3).setWidth 64)),
    .mem (fr.rdi + 64) 32 ((ChaChaRound.rounds 10 x.w)[0].toBitVec + x.w[0].toBitVec),
    .mem (fr.rdi + 68) 32 ((ChaChaRound.rounds 10 x.w)[1].toBitVec + x.w[1].toBitVec),
    .mem (fr.rdi + 72) 32 ((ChaChaRound.rounds 10 x.w)[2].toBitVec + x.w[2].toBitVec),
    .mem (fr.rdi + 76) 32 ((ChaChaRound.rounds 10 x.w)[3].toBitVec + x.w[3].toBitVec),
    .mem (fr.rdi + 80) 32 ((ChaChaRound.rounds 10 x.w)[4].toBitVec + x.w[4].toBitVec),
    .mem (fr.rdi + 84) 32 ((ChaChaRound.rounds 10 x.w)[5].toBitVec + x.w[5].toBitVec),
    .mem (fr.rdi + 88) 32 ((ChaChaRound.rounds 10 x.w)[6].toBitVec + x.w[6].toBitVec),
    .mem (fr.rdi + 92) 32 ((ChaChaRound.rounds 10 x.w)[7].toBitVec + x.w[7].toBitVec),
    .mem (fr.rdi + 96) 32 ((ChaChaRound.rounds 10 x.w)[8].toBitVec + x.w[8].toBitVec),
    .mem (fr.rdi + 100) 32 ((ChaChaRound.rounds 10 x.w)[9].toBitVec + x.w[9].toBitVec),
    .mem (fr.rdi + 104) 32 ((ChaChaRound.rounds 10 x.w)[10].toBitVec + x.w[10].toBitVec),
    .mem (fr.rdi + 108) 32 ((ChaChaRound.rounds 10 x.w)[11].toBitVec + x.w[11].toBitVec),
    .mem (fr.rdi + 112) 32 ((ChaChaRound.rounds 10 x.w)[12].toBitVec + x.w[12].toBitVec),
    .mem (fr.rdi + 116) 32 ((ChaChaRound.rounds 10 x.w)[13].toBitVec + x.w[13].toBitVec),
    .mem (fr.rdi + 120) 32 ((ChaChaRound.rounds 10 x.w)[14].toBitVec + x.w[14].toBitVec),
    .mem (fr.rdi + 124) 32 ((ChaChaRound.rounds 10 x.w)[15].toBitVec + x.w[15].toBitVec)]
  Result := Unit
  output := fun _ => ⟨#v[],none,()⟩
  done := fun _ _ => []
  retAddr := fun fr => fr.ret
  original := fun fr => fr.original
  regions := fun fr => [⟨fr.rsp.toNat,120+4⟩,⟨fr.rdi.toNat+48,4⟩,⟨fr.rdi.toNat+64,64⟩]

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Tail
