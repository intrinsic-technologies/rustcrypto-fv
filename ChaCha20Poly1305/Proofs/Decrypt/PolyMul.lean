import ChaCha20Poly1305.Proofs.Decrypt.ActiveFrames
import ChaCha20Poly1305.Proofs.Decrypt.Empty
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn101e30.Frame

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Mul
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

structure Input where
  r : Vector (BitVec 32) 5
  acc : Vector (BitVec 32) 5
  block : BitVec 128

def v101ae9 (x : Input) : BitVec 32 := x.r[2] + (x.r[2] <<< 2)

def v101af1 (x : Input) : BitVec 32 := x.r[3] + (x.r[3] <<< 2)

def v101af9 (x : Input) : BitVec 32 := x.r[4] + (x.r[4] <<< 2)

def v101b02 (x : Input) : BitVec 32 := 67108863 &&& (x.block.extractLsb' 0 32)

def v101b05 (x : Input) : BitVec 32 := (v101b02 x) + x.acc[0]

def v101b10 (x : Input) : BitVec 32 := (x.block.extractLsb' 24 32) >>> 2

def v101b13 (x : Input) : BitVec 32 := (v101b10 x) &&& 67108863

def v101b19 (x : Input) : BitVec 32 := (v101b13 x) + x.acc[1]

def v101b1d (x : Input) : BitVec 32 := (x.block.extractLsb' 48 32) >>> 4

def v101b21 (x : Input) : BitVec 32 := (v101b1d x) &&& 67108863

def v101b28 (x : Input) : BitVec 32 := (v101b21 x) + x.acc[2]

def v101b2f (x : Input) : BitVec 32 := (x.block.extractLsb' 72 32) >>> 6

def v101b32 (x : Input) : BitVec 32 := (v101b2f x) + x.acc[3]

def v101b39 (x : Input) : BitVec 32 := (x.block.extractLsb' 96 32) >>> 8

def v101b3c (x : Input) : BitVec 32 := 16777216 + x.acc[4]

def v101b40 (x : Input) : BitVec 32 := (v101b3c x) + (v101b39 x)

def v101b45 (x : Input) : BitVec 64 := ((v101b05 x) : BitVec 32).setWidth 64 * (x.r[0] : BitVec 32).setWidth 64

def v101b4c (x : Input) : BitVec 64 := ((v101b19 x) : BitVec 32).setWidth 64 * ((v101af9 x) : BitVec 32).setWidth 64

def v101b50 (x : Input) : BitVec 64 := (v101b4c x) + (v101b45 x)

def v101b56 (x : Input) : BitVec 64 := ((v101b28 x) : BitVec 32).setWidth 64 * ((v101af1 x) : BitVec 32).setWidth 64

def v101b5d (x : Input) : BitVec 64 := ((v101b32 x) : BitVec 32).setWidth 64 * ((v101ae9 x) : BitVec 32).setWidth 64

def v101b61 (x : Input) : BitVec 64 := (v101b5d x) + (v101b56 x)

def v101b64 (x : Input) : BitVec 64 := (v101b61 x) + (v101b50 x)

def v101b6b (x : Input) : BitVec 32 := x.r[1] + (x.r[1] <<< 2)

def v101b70 (x : Input) : BitVec 64 := ((v101b6b x) : BitVec 32).setWidth 64 * ((v101b40 x) : BitVec 32).setWidth 64

def v101b74 (x : Input) : BitVec 64 := (v101b70 x) + (v101b64 x)

def v101b7a (x : Input) : BitVec 64 := ((v101b05 x) : BitVec 32).setWidth 64 * (x.r[1] : BitVec 32).setWidth 64

def v101b81 (x : Input) : BitVec 64 := ((v101b19 x) : BitVec 32).setWidth 64 * (x.r[0] : BitVec 32).setWidth 64

def v101b88 (x : Input) : BitVec 64 := (v101b81 x) + (v101b7a x)

def v101b8e (x : Input) : BitVec 64 := ((v101b28 x) : BitVec 32).setWidth 64 * ((v101af9 x) : BitVec 32).setWidth 64

def v101b99 (x : Input) : BitVec 64 := ((v101b32 x) : BitVec 32).setWidth 64 * ((v101af1 x) : BitVec 32).setWidth 64

def v101b9d (x : Input) : BitVec 64 := (v101b99 x) + (v101b8e x)

def v101ba0 (x : Input) : BitVec 64 := (v101b9d x) + (v101b88 x)

def v101ba8 (x : Input) : BitVec 64 := ((v101ae9 x) : BitVec 32).setWidth 64 * ((v101b40 x) : BitVec 32).setWidth 64

def v101bac (x : Input) : BitVec 64 := (v101ba8 x) + (v101ba0 x)

def v101bbc (x : Input) : BitVec 64 := ((v101b05 x) : BitVec 32).setWidth 64 * (x.r[2] : BitVec 32).setWidth 64

def v101bc3 (x : Input) : BitVec 64 := ((v101b19 x) : BitVec 32).setWidth 64 * (x.r[1] : BitVec 32).setWidth 64

def v101bc7 (x : Input) : BitVec 64 := (v101bc3 x) + (v101bbc x)

def v101bcd (x : Input) : BitVec 64 := ((v101b28 x) : BitVec 32).setWidth 64 * (x.r[0] : BitVec 32).setWidth 64

def v101bd4 (x : Input) : BitVec 64 := ((v101b32 x) : BitVec 32).setWidth 64 * ((v101af9 x) : BitVec 32).setWidth 64

def v101bd8 (x : Input) : BitVec 64 := (v101bd4 x) + (v101bcd x)

def v101bdb (x : Input) : BitVec 64 := (v101bd8 x) + (v101bc7 x)

def v101be1 (x : Input) : BitVec 64 := ((v101af1 x) : BitVec 32).setWidth 64 * ((v101b40 x) : BitVec 32).setWidth 64

def v101be5 (x : Input) : BitVec 64 := (v101be1 x) + (v101bdb x)

def v101bf4 (x : Input) : BitVec 64 := ((v101b05 x) : BitVec 32).setWidth 64 * (x.r[3] : BitVec 32).setWidth 64

def v101bfb (x : Input) : BitVec 64 := ((v101b19 x) : BitVec 32).setWidth 64 * (x.r[2] : BitVec 32).setWidth 64

def v101bff (x : Input) : BitVec 64 := (v101bfb x) + (v101bf4 x)

def v101c05 (x : Input) : BitVec 64 := ((v101b28 x) : BitVec 32).setWidth 64 * (x.r[1] : BitVec 32).setWidth 64

def v101c0c (x : Input) : BitVec 64 := ((v101b32 x) : BitVec 32).setWidth 64 * (x.r[0] : BitVec 32).setWidth 64

def v101c10 (x : Input) : BitVec 64 := (v101c0c x) + (v101c05 x)

def v101c13 (x : Input) : BitVec 64 := (v101c10 x) + (v101bff x)

def v101c16 (x : Input) : BitVec 64 := ((v101af9 x) : BitVec 32).setWidth 64 * ((v101b40 x) : BitVec 32).setWidth 64

def v101c1a (x : Input) : BitVec 64 := (v101c16 x) + (v101c13 x)

def v101c1d (x : Input) : BitVec 64 := ((v101b05 x) : BitVec 32).setWidth 64 * (x.r[4] : BitVec 32).setWidth 64

def v101c23 (x : Input) : BitVec 64 := ((v101b19 x) : BitVec 32).setWidth 64 * (x.r[3] : BitVec 32).setWidth 64

def v101c27 (x : Input) : BitVec 64 := (v101c23 x) + (v101c1d x)

def v101c2a (x : Input) : BitVec 64 := ((v101b28 x) : BitVec 32).setWidth 64 * (x.r[2] : BitVec 32).setWidth 64

def v101c2e (x : Input) : BitVec 64 := ((v101b32 x) : BitVec 32).setWidth 64 * (x.r[1] : BitVec 32).setWidth 64

def v101c32 (x : Input) : BitVec 64 := (v101c2e x) + (v101c2a x)

def v101c35 (x : Input) : BitVec 64 := (v101c32 x) + (v101c27 x)

def v101c38 (x : Input) : BitVec 64 := ((v101b40 x) : BitVec 32).setWidth 64 * (x.r[0] : BitVec 32).setWidth 64

def v101c3c (x : Input) : BitVec 64 := (v101c38 x) + (v101c35 x)

def v101c42 (x : Input) : BitVec 64 := (v101b74 x) >>> 26

def v101c46 (x : Input) : BitVec 32 := ((v101b74 x) : BitVec 64).setWidth 32 &&& 67108863

def v101c50 (x : Input) : BitVec 64 := (((v101c42 x) : BitVec 64).setWidth 32 : BitVec 32).setWidth 64 + (v101bac x)

def v101c58 (x : Input) : BitVec 64 := (v101c50 x) >>> 26

def v101c5c (x : Input) : BitVec 32 := ((v101c50 x) : BitVec 64).setWidth 32 &&& 67108863

def v101c66 (x : Input) : BitVec 64 := (((v101c58 x) : BitVec 64).setWidth 32 : BitVec 32).setWidth 64 + (v101be5 x)

def v101c6d (x : Input) : BitVec 64 := (v101c66 x) >>> 26

def v101c73 (x : Input) : BitVec 64 := (((v101c6d x) : BitVec 64).setWidth 32 : BitVec 32).setWidth 64 + (v101c1a x)

def v101c79 (x : Input) : BitVec 64 := (v101c73 x) >>> 26

def v101c7f (x : Input) : BitVec 64 := (((v101c79 x) : BitVec 64).setWidth 32 : BitVec 32).setWidth 64 + (v101c3c x)

def v101c85 (x : Input) : BitVec 64 := (v101c7f x) >>> 26

def v101c89 (x : Input) : BitVec 32 := ((v101c85 x) : BitVec 64).setWidth 32 + (((v101c85 x) : BitVec 64).setWidth 32 <<< 2)

def v101c8c (x : Input) : BitVec 32 := (v101c89 x) + (v101c46 x)

def v101c91 (x : Input) : BitVec 32 := (v101c8c x) >>> 26

def v101c94 (x : Input) : BitVec 32 := (v101c91 x) + (v101c5c x)

def v101c97 (x : Input) : BitVec 32 := (v101c8c x) &&& 67108863

def v101ca5 (x : Input) : BitVec 32 := ((v101c66 x) : BitVec 64).setWidth 32 &&& 67108863

def v101cb0 (x : Input) : BitVec 32 := ((v101c73 x) : BitVec 64).setWidth 32 &&& 67108863

def v101cba (x : Input) : BitVec 32 := ((v101c7f x) : BitVec 64).setWidth 32 &&& 67108863

inductive Label | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8

def program : Program (fun _ => _root_.Empty) Label (fun _ => 0) 0 := ⟨fun
  | .s0 => .terminate (.br ⟨.s1, #v[]⟩)
  | .s1 => .terminate (.br ⟨.s2, #v[]⟩)
  | .s2 => .terminate (.br ⟨.s3, #v[]⟩)
  | .s3 => .terminate (.br ⟨.s4, #v[]⟩)
  | .s4 => .terminate (.br ⟨.s5, #v[]⟩)
  | .s5 => .terminate (.br ⟨.s6, #v[]⟩)
  | .s6 => .terminate (.br ⟨.s7, #v[]⟩)
  | .s7 => .terminate (.br ⟨.s8, #v[]⟩)
  | .s8 => .terminate (.ret #v[])⟩

@[refine_layout] def shared (fr : Activation) : List Atom :=
  [.readable fr.rsi 16,
   .writable fr.rdi 56,
   .fact (fr.rsp.toNat ≤ 0x101ab0 ∨ 0x101e40 + 88 ≤ fr.rsp.toNat),
   .fact (fr.rdi.toNat + 56 ≤ 0x101ab0 ∨ 0x101e40 ≤ fr.rdi.toNat),
   .fact (fr.rdi.toNat + 56 ≤ fr.rsp.toNat - 88 ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat),
   .fact (fr.rsi.toNat + 16 ≤ fr.rsp.toNat - 88 ∨ fr.rsp.toNat + 8 ≤ fr.rsi.toNat),
   .fact (fr.rsi.toNat + 16 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 56 ≤ fr.rsi.toNat)]

@[refine_layout] def core (x : Input) : LayoutCore program Empty.semantics lifted Unit where
  start
    | .s0 => .l101e30
    | .s1 => .l101ab0
    | .s2 => .l101af1
    | .s3 => .l101b40
    | .s4 => .l101b85
    | .s5 => .l101bcd
    | .s6 => .l101c13
    | .s7 => .l101c63
    | .s8 => .l101ca5
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms := fun l _ fr _ => shared fr ++ match l with
    | .s0 =>
        [.mem (fr.rdi + 16) 32 x.r[0],
         .mem (fr.rdi + 20) 32 x.r[1],
         .mem (fr.rdi + 24) 32 x.r[2],
         .mem (fr.rdi + 28) 32 x.r[3],
         .mem (fr.rdi + 32) 32 x.r[4],
         .mem (fr.rdi + 36) 32 x.acc[0],
         .mem (fr.rdi + 40) 32 x.acc[1],
         .mem (fr.rdi + 44) 32 x.acc[2],
         .mem (fr.rdi + 48) 32 x.acc[3],
         .mem (fr.rdi + 52) 32 x.acc[4],
         .mem fr.rsi 32 (x.block.extractLsb' 0 32),
         .mem (fr.rsi + 3) 32 (x.block.extractLsb' 24 32),
         .mem (fr.rsi + 6) 32 (x.block.extractLsb' 48 32),
         .mem (fr.rsi + 9) 32 (x.block.extractLsb' 72 32),
         .mem (fr.rsi + 12) 32 (x.block.extractLsb' 96 32)]
    | .s1 =>
        [.mem (fr.rdi + 16) 32 x.r[0],
         .mem (fr.rdi + 20) 32 x.r[1],
         .mem (fr.rdi + 24) 32 x.r[2],
         .mem (fr.rdi + 28) 32 x.r[3],
         .mem (fr.rdi + 32) 32 x.r[4],
         .mem (fr.rdi + 36) 32 x.acc[0],
         .mem (fr.rdi + 40) 32 x.acc[1],
         .mem (fr.rdi + 44) 32 x.acc[2],
         .mem (fr.rdi + 48) 32 x.acc[3],
         .mem (fr.rdi + 52) 32 x.acc[4],
         .mem fr.rsi 32 (x.block.extractLsb' 0 32),
         .mem (fr.rsi + 3) 32 (x.block.extractLsb' 24 32),
         .mem (fr.rsi + 6) 32 (x.block.extractLsb' 48 32),
         .mem (fr.rsi + 9) 32 (x.block.extractLsb' 72 32),
         .mem (fr.rsi + 12) 32 (x.block.extractLsb' 96 32),
         .gpr 2 (0)]
    | .s2 =>
        [.mem (fr.rdi + 16) 32 x.r[0],
         .mem (fr.rdi + 20) 32 x.r[1],
         .mem (fr.rdi + 24) 32 x.r[2],
         .mem (fr.rdi + 28) 32 x.r[3],
         .mem (fr.rdi + 32) 32 x.r[4],
         .mem (fr.rdi + 36) 32 x.acc[0],
         .mem (fr.rdi + 40) 32 x.acc[1],
         .mem (fr.rdi + 44) 32 x.acc[2],
         .mem (fr.rdi + 48) 32 x.acc[3],
         .mem (fr.rdi + 52) 32 x.acc[4],
         .mem fr.rsi 32 (x.block.extractLsb' 0 32),
         .mem (fr.rsi + 3) 32 (x.block.extractLsb' 24 32),
         .mem (fr.rsi + 6) 32 (x.block.extractLsb' 48 32),
         .mem (fr.rsi + 9) 32 (x.block.extractLsb' 72 32),
         .mem (fr.rsi + 12) 32 (x.block.extractLsb' 96 32),
         .mem (fr.rsp - 72) 64 ((x.r[2] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 64) 64 ((x.r[3] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 56) 64 ((x.r[4] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 80) 64 (((v101ae9 x) : BitVec 32).setWidth 64),
         .gpr 2 ((x.r[4] : BitVec 32).setWidth 64),
         .gpr 7 ((16777216 : BitVec 32).setWidth 64),
         .gpr 8 ((x.r[0] : BitVec 32).setWidth 64),
         .gpr 0 (((v101ae9 x) : BitVec 32).setWidth 64),
         .gpr 1 ((x.r[3] : BitVec 32).setWidth 64)]
    | .s3 =>
        [.mem (fr.rdi + 16) 32 x.r[0],
         .mem (fr.rdi + 20) 32 x.r[1],
         .mem (fr.rdi + 24) 32 x.r[2],
         .mem (fr.rdi + 28) 32 x.r[3],
         .mem (fr.rdi + 32) 32 x.r[4],
         .mem (fr.rdi + 36) 32 x.acc[0],
         .mem (fr.rdi + 40) 32 x.acc[1],
         .mem (fr.rdi + 44) 32 x.acc[2],
         .mem (fr.rdi + 48) 32 x.acc[3],
         .mem (fr.rdi + 52) 32 x.acc[4],
         .mem fr.rsi 32 (x.block.extractLsb' 0 32),
         .mem (fr.rsi + 3) 32 (x.block.extractLsb' 24 32),
         .mem (fr.rsi + 6) 32 (x.block.extractLsb' 48 32),
         .mem (fr.rsi + 9) 32 (x.block.extractLsb' 72 32),
         .mem (fr.rsi + 12) 32 (x.block.extractLsb' 96 32),
         .mem (fr.rsp - 72) 64 ((x.r[2] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 64) 64 ((x.r[3] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 56) 64 ((x.r[4] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 80) 64 (((v101ae9 x) : BitVec 32).setWidth 64),
         .mem (fr.rsp - 88) 64 (((v101af1 x) : BitVec 32).setWidth 64),
         .gpr 2 (((v101b19 x) : BitVec 32).setWidth 64),
         .gpr 7 (((v101b3c x) : BitVec 32).setWidth 64),
         .gpr 8 ((x.r[0] : BitVec 32).setWidth 64),
         .gpr 0 (((v101ae9 x) : BitVec 32).setWidth 64),
         .gpr 1 (((v101b32 x) : BitVec 32).setWidth 64),
         .gpr 9 (((v101af1 x) : BitVec 32).setWidth 64),
         .gpr 3 (((v101af9 x) : BitVec 32).setWidth 64),
         .gpr 15 (((v101b05 x) : BitVec 32).setWidth 64),
         .gpr 12 (((v101b28 x) : BitVec 32).setWidth 64),
         .gpr 6 (((v101b39 x) : BitVec 32).setWidth 64)]
    | .s4 =>
        [.mem (fr.rdi + 16) 32 x.r[0],
         .mem (fr.rdi + 20) 32 x.r[1],
         .mem (fr.rdi + 24) 32 x.r[2],
         .mem (fr.rdi + 28) 32 x.r[3],
         .mem (fr.rdi + 32) 32 x.r[4],
         .mem (fr.rdi + 36) 32 x.acc[0],
         .mem (fr.rdi + 40) 32 x.acc[1],
         .mem (fr.rdi + 44) 32 x.acc[2],
         .mem (fr.rdi + 48) 32 x.acc[3],
         .mem (fr.rdi + 52) 32 x.acc[4],
         .mem fr.rsi 32 (x.block.extractLsb' 0 32),
         .mem (fr.rsi + 3) 32 (x.block.extractLsb' 24 32),
         .mem (fr.rsi + 6) 32 (x.block.extractLsb' 48 32),
         .mem (fr.rsi + 9) 32 (x.block.extractLsb' 72 32),
         .mem (fr.rsi + 12) 32 (x.block.extractLsb' 96 32),
         .mem (fr.rsp - 72) 64 ((x.r[2] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 64) 64 ((x.r[3] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 56) 64 ((x.r[4] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 80) 64 (((v101ae9 x) : BitVec 32).setWidth 64),
         .mem (fr.rsp - 88) 64 (((v101af1 x) : BitVec 32).setWidth 64),
         .gpr 2 (((v101b19 x) : BitVec 32).setWidth 64),
         .gpr 7 (((v101b40 x) : BitVec 32).setWidth 64),
         .gpr 8 ((x.r[0] : BitVec 32).setWidth 64),
         .gpr 1 (((v101b32 x) : BitVec 32).setWidth 64),
         .gpr 3 (((v101af9 x) : BitVec 32).setWidth 64),
         .gpr 15 (((v101b05 x) : BitVec 32).setWidth 64),
         .gpr 12 (((v101b28 x) : BitVec 32).setWidth 64),
         .gpr 5 ((x.r[1] : BitVec 32).setWidth 64),
         .gpr 13 ((v101b7a x)),
         .gpr 11 ((v101b74 x)),
         .gpr 14 ((v101b81 x))]
    | .s5 =>
        [.mem (fr.rdi + 16) 32 x.r[0],
         .mem (fr.rdi + 20) 32 x.r[1],
         .mem (fr.rdi + 24) 32 x.r[2],
         .mem (fr.rdi + 28) 32 x.r[3],
         .mem (fr.rdi + 32) 32 x.r[4],
         .mem (fr.rdi + 36) 32 x.acc[0],
         .mem (fr.rdi + 40) 32 x.acc[1],
         .mem (fr.rdi + 44) 32 x.acc[2],
         .mem (fr.rdi + 48) 32 x.acc[3],
         .mem (fr.rdi + 52) 32 x.acc[4],
         .mem fr.rsi 32 (x.block.extractLsb' 0 32),
         .mem (fr.rsi + 3) 32 (x.block.extractLsb' 24 32),
         .mem (fr.rsi + 6) 32 (x.block.extractLsb' 48 32),
         .mem (fr.rsi + 9) 32 (x.block.extractLsb' 72 32),
         .mem (fr.rsi + 12) 32 (x.block.extractLsb' 96 32),
         .mem (fr.rsp - 72) 64 ((x.r[2] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 64) 64 ((x.r[3] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 56) 64 ((x.r[4] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 80) 64 ((v101bac x)),
         .mem (fr.rsp - 88) 64 (((v101af1 x) : BitVec 32).setWidth 64),
         .gpr 2 (((v101b19 x) : BitVec 32).setWidth 64),
         .gpr 7 (((v101b40 x) : BitVec 32).setWidth 64),
         .gpr 8 (((v101af1 x) : BitVec 32).setWidth 64),
         .gpr 0 (((v101b28 x) : BitVec 32).setWidth 64),
         .gpr 1 (((v101b32 x) : BitVec 32).setWidth 64),
         .gpr 9 ((x.r[0] : BitVec 32).setWidth 64),
         .gpr 3 (((v101af9 x) : BitVec 32).setWidth 64),
         .gpr 15 (((v101b05 x) : BitVec 32).setWidth 64),
         .gpr 12 (((v101b28 x) : BitVec 32).setWidth 64),
         .gpr 6 ((x.r[2] : BitVec 32).setWidth 64),
         .gpr 5 ((x.r[1] : BitVec 32).setWidth 64),
         .gpr 11 ((v101b74 x)),
         .gpr 14 ((v101bc7 x))]
    | .s6 =>
        [.mem (fr.rdi + 16) 32 x.r[0],
         .mem (fr.rdi + 20) 32 x.r[1],
         .mem (fr.rdi + 24) 32 x.r[2],
         .mem (fr.rdi + 28) 32 x.r[3],
         .mem (fr.rdi + 32) 32 x.r[4],
         .mem (fr.rdi + 36) 32 x.acc[0],
         .mem (fr.rdi + 40) 32 x.acc[1],
         .mem (fr.rdi + 44) 32 x.acc[2],
         .mem (fr.rdi + 48) 32 x.acc[3],
         .mem (fr.rdi + 52) 32 x.acc[4],
         .mem fr.rsi 32 (x.block.extractLsb' 0 32),
         .mem (fr.rsi + 3) 32 (x.block.extractLsb' 24 32),
         .mem (fr.rsi + 6) 32 (x.block.extractLsb' 48 32),
         .mem (fr.rsi + 9) 32 (x.block.extractLsb' 72 32),
         .mem (fr.rsi + 12) 32 (x.block.extractLsb' 96 32),
         .mem (fr.rsp - 72) 64 ((x.r[2] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 64) 64 ((x.r[3] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 56) 64 ((x.r[4] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 80) 64 ((v101bac x)),
         .mem (fr.rsp - 88) 64 ((v101be5 x)),
         .gpr 2 (((v101b19 x) : BitVec 32).setWidth 64),
         .gpr 7 (((v101b40 x) : BitVec 32).setWidth 64),
         .gpr 8 ((x.r[3] : BitVec 32).setWidth 64),
         .gpr 1 (((v101b32 x) : BitVec 32).setWidth 64),
         .gpr 9 ((x.r[0] : BitVec 32).setWidth 64),
         .gpr 3 (((v101af9 x) : BitVec 32).setWidth 64),
         .gpr 15 (((v101b05 x) : BitVec 32).setWidth 64),
         .gpr 12 (((v101b28 x) : BitVec 32).setWidth 64),
         .gpr 6 ((x.r[2] : BitVec 32).setWidth 64),
         .gpr 5 ((x.r[1] : BitVec 32).setWidth 64),
         .gpr 13 ((v101c10 x)),
         .gpr 11 ((v101b74 x)),
         .gpr 14 ((v101bff x))]
    | .s7 =>
        [.mem (fr.rdi + 16) 32 x.r[0],
         .mem (fr.rdi + 20) 32 x.r[1],
         .mem (fr.rdi + 24) 32 x.r[2],
         .mem (fr.rdi + 28) 32 x.r[3],
         .mem (fr.rdi + 32) 32 x.r[4],
         .mem (fr.rdi + 36) 32 x.acc[0],
         .mem (fr.rdi + 40) 32 x.acc[1],
         .mem (fr.rdi + 44) 32 x.acc[2],
         .mem (fr.rdi + 48) 32 x.acc[3],
         .mem (fr.rdi + 52) 32 x.acc[4],
         .mem fr.rsi 32 (x.block.extractLsb' 0 32),
         .mem (fr.rsi + 3) 32 (x.block.extractLsb' 24 32),
         .mem (fr.rsi + 6) 32 (x.block.extractLsb' 48 32),
         .mem (fr.rsi + 9) 32 (x.block.extractLsb' 72 32),
         .mem (fr.rsi + 12) 32 (x.block.extractLsb' 96 32),
         .mem (fr.rsp - 72) 64 ((x.r[2] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 64) 64 ((x.r[3] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 56) 64 ((x.r[4] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 80) 64 ((v101bac x)),
         .mem (fr.rsp - 88) 64 ((v101be5 x)),
         .gpr 7 ((v101c3c x)),
         .gpr 8 (((v101c5c x) : BitVec 32).setWidth 64),
         .gpr 0 ((v101c58 x)),
         .gpr 3 ((v101c1a x)),
         .gpr 11 (((v101c46 x) : BitVec 32).setWidth 64)]
    | .s8 =>
        [.mem (fr.rdi + 16) 32 x.r[0],
         .mem (fr.rdi + 20) 32 x.r[1],
         .mem (fr.rdi + 24) 32 x.r[2],
         .mem (fr.rdi + 28) 32 x.r[3],
         .mem (fr.rdi + 32) 32 x.r[4],
         .mem (fr.rdi + 36) 32 (v101c97 x),
         .mem (fr.rdi + 40) 32 (v101c94 x),
         .mem (fr.rdi + 44) 32 x.acc[2],
         .mem (fr.rdi + 48) 32 x.acc[3],
         .mem (fr.rdi + 52) 32 x.acc[4],
         .mem fr.rsi 32 (x.block.extractLsb' 0 32),
         .mem (fr.rsi + 3) 32 (x.block.extractLsb' 24 32),
         .mem (fr.rsi + 6) 32 (x.block.extractLsb' 48 32),
         .mem (fr.rsi + 9) 32 (x.block.extractLsb' 72 32),
         .mem (fr.rsi + 12) 32 (x.block.extractLsb' 96 32),
         .mem (fr.rsp - 72) 64 ((x.r[2] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 64) 64 ((x.r[3] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 56) 64 ((x.r[4] : BitVec 32).setWidth 64),
         .mem (fr.rsp - 80) 64 ((v101bac x)),
         .mem (fr.rsp - 88) 64 ((v101be5 x)),
         .gpr 2 ((v101c73 x)),
         .gpr 7 ((v101c3c x)),
         .gpr 0 ((v101c7f x)),
         .gpr 1 (((v101c97 x) : BitVec 32).setWidth 64),
         .gpr 9 ((v101c66 x)),
         .gpr 6 (((v101c94 x) : BitVec 32).setWidth 64)]
  Result := Unit
  output := fun _ => ⟨#v[], none, ()⟩
  done := fun _ fr _ =>
    [.mem (fr.rdi + 36) 32 (v101c97 x),
     .mem (fr.rdi + 40) 32 (v101c94 x),
     .mem (fr.rdi + 44) 32 (v101ca5 x),
     .mem (fr.rdi + 48) 32 (v101cb0 x),
     .mem (fr.rdi + 52) 32 (v101cba x)]
  footprint := fun _ fr => [⟨fr.rdi.toNat + 36, 20⟩]

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Mul
