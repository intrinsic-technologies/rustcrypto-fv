import ChaCha20Poly1305.Proofs.Decrypt.Stream
import ChaCha20Poly1305.Proofs.Decrypt.FullRounds
import ChaCha20Poly1305.Proofs.Decrypt.Refine

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Full
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Standards.RFC.ChaCha20Poly1305

inductive Label | setup | round | feed | second | finished

def program : Program (fun _ => _root_.Empty) Label (fun _ => 0) 0 := ⟨fun
  | .setup => .terminate (.br ⟨.round,#v[]⟩)
  | .round => .terminate (.br ⟨.feed,#v[]⟩)
  | .feed => .terminate (.br ⟨.second,#v[]⟩)
  | .second => .terminate (.br ⟨.finished,#v[]⟩)
  | .finished => .terminate (.ret #v[])⟩

@[refine_layout] def registers (fr : Activation) : List Atom :=
  [.gpr 4 fr.rsp,.reg 22 ⟨1,0⟩,.reg 39 ⟨32,fr.mxcsr⟩,.reg 50 ⟨16,fr.ftw⟩,.reg 51 ⟨16,fr.fcw⟩]

@[refine_layout] def common (fr : Activation) : List Atom :=
  [.writable fr.rsp 368,.fact (fr.rsp.toNat + 368 ≤ 0x100c70 ∨ 0x100efe ≤ fr.rsp.toNat)]

@[refine_layout] def keep (x : Input) (j : BitVec 64) (fr : Activation) : List Atom :=
  common fr ++ [.mem (fr.rsp + 112) 64 (j),
     .mem (fr.rsp + 88) 32 (x.w[0].toBitVec),
     .mem (fr.rsp + 16) 32 (x.w[1].toBitVec),
     .mem (fr.rsp + 12) 32 (x.w[2].toBitVec),
     .mem (fr.rsp + 64) 32 (x.w[3].toBitVec),
     .mem (fr.rsp + 56) 32 (x.w[4].toBitVec),
     .mem (fr.rsp + 52) 32 (x.w[5].toBitVec),
     .mem (fr.rsp + 48) 32 (x.w[6].toBitVec),
     .mem (fr.rsp + 44) 32 (x.w[7].toBitVec),
     .mem (fr.rsp + 132) 32 (x.w[8].toBitVec),
     .mem (fr.rsp + 40) 32 (x.w[9].toBitVec),
     .mem (fr.rsp + 36) 32 (x.w[10].toBitVec),
     .mem (fr.rsp + 32) 32 (x.w[11].toBitVec),
     .mem (fr.rsp + 60) 32 (x.w[12].toBitVec),
     .mem (fr.rsp + 128) 32 (x.w[13].toBitVec),
     .mem (fr.rsp + 28) 32 (x.w[14].toBitVec),
     .mem (fr.rsp + 24) 32 (x.w[15].toBitVec)]

@[refine_layout] def roundAtoms (fr : Activation) (w : Vector UInt32 16) (n : BitVec 64) : List Atom :=
  registers fr ++ [.writable fr.rsp 128,
     .fact (fr.rsp.toNat +128 ≤ 0x100cd0 ∨ 0x100e19 ≤ fr.rsp.toNat),
     .mem (fr.rsp + 120) 64 (n),
     .low 3 32 (w[0].toBitVec),
     .low 13 32 (w[1].toBitVec),
     .low 12 32 (w[2].toBitVec),
     .low 10 32 (w[3].toBitVec),
     .low 5 32 (w[4].toBitVec),
     .low 1 32 (w[5].toBitVec),
     .low 2 32 (w[6].toBitVec),
     .low 11 32 (w[7].toBitVec),
     .mem (fr.rsp + 4) 32 (w[8].toBitVec),
     .low 0 32 (w[9].toBitVec),
     .low 6 32 (w[10].toBitVec),
     .low 8 32 (w[11].toBitVec),
     .low 9 32 (w[12].toBitVec),
     .low 7 32 (w[13].toBitVec),
     .low 14 32 (w[14].toBitVec),
     .low 15 32 (w[15].toBitVec)]

def layout (x : Input) (j : BitVec 64) : Layout program Empty.semantics lifted Activation where
  start | .setup => .l100c70 | .round => .l100cd0 | .feed => .l100e19 | .second => .l100e8c | .finished => .l100efe
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms l fr _ := match l with
    | .round => roundAtoms fr x.w 10 ++ keep x j fr
    | .feed => roundAtoms fr (ChaChaRound.rounds 10 x.w) 0 ++ keep x j fr
    | .setup => registers fr ++ common fr ++ [.gpr 7 (j),
     .low 10 32 (x.w[4].toBitVec),
     .low 11 32 (x.w[8].toBitVec),
     .low 8 32 (x.w[13].toBitVec),
     .low 12 32 (x.w[12].toBitVec),
     .mem (fr.rsp + 88) 32 (x.w[0].toBitVec),
     .mem (fr.rsp + 16) 32 (x.w[1].toBitVec),
     .mem (fr.rsp + 12) 32 (x.w[2].toBitVec),
     .mem (fr.rsp + 64) 32 (x.w[3].toBitVec),
     .mem (fr.rsp + 56) 32 (x.w[4].toBitVec),
     .mem (fr.rsp + 52) 32 (x.w[5].toBitVec),
     .mem (fr.rsp + 48) 32 (x.w[6].toBitVec),
     .mem (fr.rsp + 44) 32 (x.w[7].toBitVec),
     .mem (fr.rsp + 132) 32 (x.w[8].toBitVec),
     .mem (fr.rsp + 40) 32 (x.w[9].toBitVec),
     .mem (fr.rsp + 36) 32 (x.w[10].toBitVec),
     .mem (fr.rsp + 32) 32 (x.w[11].toBitVec),
     .mem (fr.rsp + 128) 32 (x.w[13].toBitVec),
     .mem (fr.rsp + 28) 32 (x.w[14].toBitVec),
     .mem (fr.rsp + 24) 32 (x.w[15].toBitVec)]
    | .second => registers fr ++ keep x j fr ++ [.mem (fr.rsp + 240) 32 (((ChaChaRound.rounds 10 x.w)[0].toBitVec + x.w[0].toBitVec)),
     .mem (fr.rsp + 244) 32 (((ChaChaRound.rounds 10 x.w)[1].toBitVec + x.w[1].toBitVec)),
     .mem (fr.rsp + 248) 32 (((ChaChaRound.rounds 10 x.w)[2].toBitVec + x.w[2].toBitVec)),
     .mem (fr.rsp + 252) 32 (((ChaChaRound.rounds 10 x.w)[3].toBitVec + x.w[3].toBitVec)),
     .mem (fr.rsp + 256) 32 (((ChaChaRound.rounds 10 x.w)[4].toBitVec + x.w[4].toBitVec)),
     .mem (fr.rsp + 260) 32 (((ChaChaRound.rounds 10 x.w)[5].toBitVec + x.w[5].toBitVec)),
     .mem (fr.rsp + 264) 32 (((ChaChaRound.rounds 10 x.w)[6].toBitVec + x.w[6].toBitVec)),
     .mem (fr.rsp + 268) 32 (((ChaChaRound.rounds 10 x.w)[7].toBitVec + x.w[7].toBitVec)),
     .low 1 32 (((ChaChaRound.rounds 10 x.w)[8].toBitVec + x.w[8].toBitVec)),
     .low 0 32 ((ChaChaRound.rounds 10 x.w)[9].toBitVec),
     .low 6 32 ((ChaChaRound.rounds 10 x.w)[10].toBitVec),
     .low 8 32 ((ChaChaRound.rounds 10 x.w)[11].toBitVec),
     .low 9 32 ((ChaChaRound.rounds 10 x.w)[12].toBitVec),
     .low 7 32 ((ChaChaRound.rounds 10 x.w)[13].toBitVec),
     .low 14 32 ((ChaChaRound.rounds 10 x.w)[14].toBitVec),
     .low 15 32 ((ChaChaRound.rounds 10 x.w)[15].toBitVec),
     .low 10 32 (x.w[4].toBitVec),
     .low 11 32 (x.w[8].toBitVec)]
    | .finished => registers fr ++ keep x j fr ++ [.mem (fr.rsp + 240) 32 (((ChaChaRound.rounds 10 x.w)[0].toBitVec + x.w[0].toBitVec)),
     .mem (fr.rsp + 244) 32 (((ChaChaRound.rounds 10 x.w)[1].toBitVec + x.w[1].toBitVec)),
     .mem (fr.rsp + 248) 32 (((ChaChaRound.rounds 10 x.w)[2].toBitVec + x.w[2].toBitVec)),
     .mem (fr.rsp + 252) 32 (((ChaChaRound.rounds 10 x.w)[3].toBitVec + x.w[3].toBitVec)),
     .mem (fr.rsp + 256) 32 (((ChaChaRound.rounds 10 x.w)[4].toBitVec + x.w[4].toBitVec)),
     .mem (fr.rsp + 260) 32 (((ChaChaRound.rounds 10 x.w)[5].toBitVec + x.w[5].toBitVec)),
     .mem (fr.rsp + 264) 32 (((ChaChaRound.rounds 10 x.w)[6].toBitVec + x.w[6].toBitVec)),
     .mem (fr.rsp + 268) 32 (((ChaChaRound.rounds 10 x.w)[7].toBitVec + x.w[7].toBitVec)),
     .mem (fr.rsp + 272) 32 (((ChaChaRound.rounds 10 x.w)[8].toBitVec + x.w[8].toBitVec)),
     .mem (fr.rsp + 276) 32 (((ChaChaRound.rounds 10 x.w)[9].toBitVec + x.w[9].toBitVec)),
     .mem (fr.rsp + 280) 32 (((ChaChaRound.rounds 10 x.w)[10].toBitVec + x.w[10].toBitVec)),
     .mem (fr.rsp + 284) 32 (((ChaChaRound.rounds 10 x.w)[11].toBitVec + x.w[11].toBitVec)),
     .mem (fr.rsp + 288) 32 (((ChaChaRound.rounds 10 x.w)[12].toBitVec + x.w[12].toBitVec)),
     .mem (fr.rsp + 292) 32 (((ChaChaRound.rounds 10 x.w)[13].toBitVec + x.w[13].toBitVec)),
     .mem (fr.rsp + 296) 32 (((ChaChaRound.rounds 10 x.w)[14].toBitVec + x.w[14].toBitVec)),
     .mem (fr.rsp + 300) 32 (((ChaChaRound.rounds 10 x.w)[15].toBitVec + x.w[15].toBitVec)),
     .gpr 7 (j),
     .gpr 0 (j <<< 6),
     .low 10 32 (x.w[4].toBitVec),
     .low 11 32 (x.w[8].toBitVec),
     .low 12 32 (x.w[12].toBitVec),
     .low 8 32 (x.w[13].toBitVec)]
  Result := Unit
  output := fun _ => ⟨#v[],none,()⟩
  done := fun _ _ => []
  retAddr := fun fr => fr.ret
  original := fun fr => fr.original
  regions := fun fr => [⟨fr.rsp.toNat+4,8⟩,⟨fr.rsp.toNat+20,4⟩,⟨fr.rsp.toNat+60,4⟩,⟨fr.rsp.toNat+112,16⟩,⟨fr.rsp.toNat+240,64⟩]
end ChaCha20Poly1305.Proofs.Decrypt.Stream.Full
