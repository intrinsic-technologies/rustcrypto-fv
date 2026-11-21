import ChaCha20Poly1305.Proofs.Decrypt.ActiveFrames
import ChaCha20Poly1305.Proofs.Decrypt.Cipher
import ChaCha20Poly1305.Proofs.Decrypt.Empty
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Frame

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted

structure Input where
  w : Vector UInt32 16
  buf : BitVec 64
  n : BitVec 64
  len : n.toNat < 2^32

inductive Label | entry | bounds | used | base

def program : Program (fun _ => _root_.Empty) Label (fun _ => 0) 0 := ⟨fun
  | .entry => .terminate (.br ⟨.bounds,#v[]⟩)
  | .bounds => .terminate (.br ⟨.used,#v[]⟩)
  | .used => .terminate (.br ⟨.base,#v[]⟩)
  | .base => .terminate (.ret #v[])⟩

@[refine_layout] def geometry (x : Input) (fr : Activation) : List Atom :=
  [.writable fr.rdi 128,.readable fr.rsi 24,.writable x.buf x.n.toNat,
   .fact (fr.rsp.toNat ≤ 0x100a80 ∨ 0x1014bc + 416 ≤ fr.rsp.toNat),
   .fact (fr.rdi.toNat + 128 ≤ 0x100a80 ∨ 0x1014bc ≤ fr.rdi.toNat),
   .fact (fr.rdi.toNat + 128 ≤ fr.rsp.toNat-416 ∨ fr.rsp.toNat+8 ≤ fr.rdi.toNat),
   .fact (fr.rsi.toNat + 24 ≤ fr.rsp.toNat-416 ∨ fr.rsp.toNat+8 ≤ fr.rsi.toNat),
   .fact (fr.rdi.toNat + 128 ≤ fr.rsi.toNat ∨ fr.rsi.toNat+24 ≤ fr.rdi.toNat),
   .fact (x.buf.toNat + x.n.toNat ≤ fr.rsp.toNat-416 ∨ fr.rsp.toNat+8 ≤ x.buf.toNat),
   .fact (x.buf.toNat + x.n.toNat ≤ fr.rdi.toNat ∨ fr.rdi.toNat+128 ≤ x.buf.toNat),
   .fact (x.buf.toNat + x.n.toNat ≤ fr.rsi.toNat ∨ fr.rsi.toNat+24 ≤ x.buf.toNat),
   .fact (x.buf.toNat + x.n.toNat ≤ 0x100a80 ∨ 0x1014bc ≤ x.buf.toNat)]

@[refine_layout] def state (x : Input) (base : BitVec 64) : List Atom :=
  [.mem base 32 x.w[0].toBitVec,
   .mem (base + 4) 32 x.w[1].toBitVec,
   .mem (base + 8) 32 x.w[2].toBitVec,
   .mem (base + 12) 32 x.w[3].toBitVec,
   .mem (base + 16) 32 x.w[4].toBitVec,
   .mem (base + 20) 32 x.w[5].toBitVec,
   .mem (base + 24) 32 x.w[6].toBitVec,
   .mem (base + 28) 32 x.w[7].toBitVec,
   .mem (base + 32) 32 x.w[8].toBitVec,
   .mem (base + 36) 32 x.w[9].toBitVec,
   .mem (base + 40) 32 x.w[10].toBitVec,
   .mem (base + 44) 32 x.w[11].toBitVec,
   .mem (base + 48) 32 x.w[12].toBitVec,
   .mem (base + 52) 32 x.w[13].toBitVec,
   .mem (base + 56) 32 x.w[14].toBitVec,
   .mem (base + 60) 32 x.w[15].toBitVec]

@[refine_layout] def core (x : Input) : LayoutCore program Empty.semantics lifted Unit where
  start | .entry => .l100a80 | .bounds => .l100aae | .used => .l100ad0 | .base => .l100ba5
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms l _ fr _ := geometry x fr ++ state x fr.rdi ++
    [.mem (fr.rdi + 64) 8 64, .mem fr.rsi 64 x.buf,
     .mem (fr.rsi + 8) 64 x.buf, .mem (fr.rsi + 16) 64 x.n] ++ match l with
    | .entry => []
    | .bounds => [.gpr 0 x.n,.gpr 1 64,.gpr 10 0,.gpr 11 x.n,.gpr 12 (x.w[12].toBitVec.setWidth 64)]
    | .used => [.gpr 1 64,.gpr 10 0,.gpr 11 x.n,.gpr 12 (x.w[12].toBitVec.setWidth 64)]
    | .base => [.gpr 3 x.buf,.gpr 14 x.buf,.gpr 10 0,.gpr 11 x.n,
        .gpr 15 (BitVec.setWidth 64 (x.n.setWidth 32 &&& 63)),
        .gpr 12 (x.w[12].toBitVec.setWidth 64),
        .mem (fr.rsp - 336) 64 (x.n >>> 6)]
  Result := Unit
  output := fun _ => ⟨#v[],none,()⟩
  done := fun _ _ _ => []
  footprint := fun _ fr => [⟨fr.rdi.toNat+64,1⟩]

end ChaCha20Poly1305.Proofs.Decrypt.Stream
