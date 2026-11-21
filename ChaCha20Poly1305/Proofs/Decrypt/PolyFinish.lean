import ChaCha20Poly1305.Proofs.Decrypt.ActiveFrames
import ChaCha20Poly1305.Proofs.Decrypt.Empty
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn101ce0.Frame

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Finish
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

structure Input where
  s : Vector (BitVec 32) 4
  acc : Vector (BitVec 32) 5

def v101cf4 (x : Input) : BitVec 32 := x.acc[1] >>> 26

def v101cf7 (x : Input) : BitVec 32 := (v101cf4 x) + x.acc[2]

def v101cfa (x : Input) : BitVec 32 := x.acc[1] &&& 67108863

def v101d03 (x : Input) : BitVec 32 := (v101cf7 x) >>> 26

def v101d06 (x : Input) : BitVec 32 := (v101cf7 x) &&& 67108863

def v101d0c (x : Input) : BitVec 32 := (v101d03 x) + x.acc[3]

def v101d12 (x : Input) : BitVec 32 := (v101d0c x) >>> 26

def v101d16 (x : Input) : BitVec 32 := (v101d0c x) &&& 67108863

def v101d1c (x : Input) : BitVec 32 := (v101d12 x) + x.acc[4]

def v101d23 (x : Input) : BitVec 32 := (v101d1c x) >>> 26

def v101d2a (x : Input) : BitVec 32 := (v101d1c x) &&& 67108863

def v101d30 (x : Input) : BitVec 32 := (v101d23 x) + ((v101d23 x) <<< 2)

def v101d34 (x : Input) : BitVec 32 := (v101d30 x) + x.acc[0]

def v101d3b (x : Input) : BitVec 32 := (v101d34 x) >>> 26

def v101d3f (x : Input) : BitVec 32 := (v101d3b x) + (v101cfa x)

def v101d42 (x : Input) : BitVec 32 := (v101d34 x) &&& 67108863

def v101d49 (x : Input) : BitVec 32 := (v101d42 x) + 5

def v101d50 (x : Input) : BitVec 32 := (v101d49 x) >>> 26

def v101d54 (x : Input) : BitVec 32 := (v101d50 x) + (v101d3f x)

def v101d5a (x : Input) : BitVec 32 := (v101d54 x) >>> 26

def v101d5d (x : Input) : BitVec 32 := (v101d5a x) + (v101d06 x)

def v101d62 (x : Input) : BitVec 32 := (v101d5d x) >>> 26

def v101d66 (x : Input) : BitVec 32 := (v101d62 x) + (v101d16 x)

def v101d6c (x : Input) : BitVec 32 := (v101d66 x) >>> 26

def v101d70 (x : Input) : BitVec 32 := (v101d6c x) + (v101d2a x)

def v101d74 (x : Input) : BitVec 32 := (v101d70 x) + 4227858432

def v101d7b (x : Input) : BitVec 32 := (v101d6c x) + (v101d2a x)

def v101d81 (x : Input) : BitVec 32 := ((v101d74 x)).sshiftRight 31

def v101d84 (x : Input) : BitVec 32 := (v101d74 x) >>> 31

def v101d88 (x : Input) : BitVec 32 := (v101d84 x) - 1

def v101d8e (x : Input) : BitVec 32 := (v101d88 x) &&& 67108863

def v101d95 (x : Input) : BitVec 32 := (v101d49 x) &&& (v101d8e x)

def v101d98 (x : Input) : BitVec 32 := (v101d54 x) &&& (v101d8e x)

def v101d9b (x : Input) : BitVec 32 := (v101d5d x) &&& (v101d8e x)

def v101d9e (x : Input) : BitVec 32 := (v101d8e x) &&& (v101d66 x)

def v101da1 (x : Input) : BitVec 32 := (v101d88 x) &&& (v101d7b x)

def v101da4 (x : Input) : BitVec 32 := (v101d42 x) &&& (v101d81 x)

def v101da7 (x : Input) : BitVec 32 := (v101da4 x) ||| (v101d95 x)

def v101daa (x : Input) : BitVec 32 := (v101d3f x) &&& (v101d81 x)

def v101dad (x : Input) : BitVec 32 := (v101daa x) ||| (v101d98 x)

def v101db0 (x : Input) : BitVec 32 := (v101d06 x) &&& (v101d81 x)

def v101db2 (x : Input) : BitVec 32 := (v101db0 x) ||| (v101d9b x)

def v101db4 (x : Input) : BitVec 32 := (v101d16 x) &&& (v101d81 x)

def v101db6 (x : Input) : BitVec 32 := (v101db4 x) ||| (v101d9e x)

def v101db9 (x : Input) : BitVec 32 := (v101d81 x) &&& (v101d1c x)

def v101dbc (x : Input) : BitVec 32 := (v101db9 x) ||| (v101da1 x)

def v101dc2 (x : Input) : BitVec 32 := (v101dad x) <<< 26

def v101dc6 (x : Input) : BitVec 32 := (v101dc2 x) ||| (v101da7 x)

def v101dc9 (x : Input) : BitVec 32 := (v101dad x) >>> 6

def v101dd0 (x : Input) : BitVec 32 := (v101db2 x) <<< 20

def v101dd4 (x : Input) : BitVec 32 := (v101dd0 x) ||| (v101dc9 x)

def v101dd7 (x : Input) : BitVec 32 := (v101db2 x) >>> 12

def v101ddd (x : Input) : BitVec 32 := (v101db6 x) <<< 14

def v101de1 (x : Input) : BitVec 32 := (v101ddd x) ||| (v101dd7 x)

def v101de4 (x : Input) : BitVec 32 := (v101db6 x) >>> 18

def v101de7 (x : Input) : BitVec 32 := (v101dbc x) <<< 8

def v101dea (x : Input) : BitVec 32 := (v101de7 x) ||| (v101de4 x)

def v101dec (x : Input) : BitVec 32 := (v101dc6 x) + x.s[0]

def v101df5 (x : Input) : BitVec 64 := ((x.s[1] : BitVec 32).setWidth 64) + (((v101dd4 x) : BitVec 32).setWidth 64) + (if (v101dc6 x) + x.s[0] < (v101dc6 x) then 1 else 0)

def v101dfb (x : Input) : BitVec 64 := ((x.s[2] : BitVec 32).setWidth 64) + (((v101de1 x) : BitVec 32).setWidth 64)

def v101dfe (x : Input) : BitVec 64 := (v101df5 x) >>> 32

def v101e02 (x : Input) : BitVec 64 := (v101dfe x) + (v101dfb x)

def v101e05 (x : Input) : BitVec 32 := (v101dea x) + x.s[3]

def v101e0a (x : Input) : BitVec 64 := (v101e02 x) >>> 32

def v101e0e (x : Input) : BitVec 32 := (((v101e0a x) : BitVec 64).setWidth 32) + (v101e05 x)

inductive Label | s0 | s1 | s2 | s3 | s4 | s5

def program : Program (fun _ => _root_.Empty) Label (fun _ => 0) 0 := ⟨fun
  | .s0 => .terminate (.br ⟨.s1, #v[]⟩)
  | .s1 => .terminate (.br ⟨.s2, #v[]⟩)
  | .s2 => .terminate (.br ⟨.s3, #v[]⟩)
  | .s3 => .terminate (.br ⟨.s4, #v[]⟩)
  | .s4 => .terminate (.br ⟨.s5, #v[]⟩)
  | .s5 => .terminate (.ret #v[])⟩

@[refine_layout] def shared (fr : Activation) : List Atom :=
  [.readable fr.rsi 56,
   .writable fr.rdi 16,
   .fact (fr.rsp.toNat ≤ 0x101ce0 ∨ 0x101e28 + 48 ≤ fr.rsp.toNat),
   .fact (fr.rdi.toNat + 16 ≤ 0x101ce0 ∨ 0x101e28 ≤ fr.rdi.toNat),
   .fact (fr.rdi.toNat + 16 ≤ fr.rsp.toNat - 48 ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat),
   .fact (fr.rsi.toNat + 56 ≤ fr.rsp.toNat - 48 ∨ fr.rsp.toNat + 8 ≤ fr.rsi.toNat),
   .fact (fr.rsi.toNat + 56 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 16 ≤ fr.rsi.toNat)]

@[refine_layout] def core (x : Input) : LayoutCore program Empty.semantics lifted Unit where
  start
    | .s0 => .l101ce0
    | .s1 => .l101d20
    | .s2 => .l101d69
    | .s3 => .l101db0
    | .s4 => .l101dec
    | .s5 => .l101e24
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms := fun l _ fr _ => shared fr ++ match l with
    | .s0 =>
        [.mem fr.rsi 32 x.s[0],
         .mem (fr.rsi + 4) 32 x.s[1],
         .mem (fr.rsi + 8) 32 x.s[2],
         .mem (fr.rsi + 12) 32 x.s[3],
         .mem (fr.rsi + 36) 32 x.acc[0],
         .mem (fr.rsi + 40) 32 x.acc[1],
         .mem (fr.rsi + 44) 32 x.acc[2],
         .mem (fr.rsi + 48) 32 x.acc[3],
         .mem (fr.rsi + 52) 32 x.acc[4]]
    | .s1 =>
        [.mem fr.rsi 32 x.s[0],
         .mem (fr.rsi + 4) 32 x.s[1],
         .mem (fr.rsi + 8) 32 x.s[2],
         .mem (fr.rsi + 12) 32 x.s[3],
         .mem (fr.rsi + 36) 32 x.acc[0],
         .mem (fr.rsi + 40) 32 x.acc[1],
         .mem (fr.rsi + 44) 32 x.acc[2],
         .mem (fr.rsi + 48) 32 x.acc[3],
         .mem (fr.rsi + 52) 32 x.acc[4],
         .gpr 11 ((((v101cfa x) : BitVec 32).setWidth 64)),
         .gpr 1 ((((v101d06 x) : BitVec 32).setWidth 64)),
         .gpr 2 ((((v101d16 x) : BitVec 32).setWidth 64)),
         .gpr 8 ((((v101d1c x) : BitVec 32).setWidth 64))]
    | .s2 =>
        [.mem fr.rsi 32 x.s[0],
         .mem (fr.rsi + 4) 32 x.s[1],
         .mem (fr.rsi + 8) 32 x.s[2],
         .mem (fr.rsi + 12) 32 x.s[3],
         .mem (fr.rsi + 36) 32 x.acc[0],
         .mem (fr.rsi + 40) 32 x.acc[1],
         .mem (fr.rsi + 44) 32 x.acc[2],
         .mem (fr.rsi + 48) 32 x.acc[3],
         .mem (fr.rsi + 52) 32 x.acc[4],
         .gpr 11 ((((v101d54 x) : BitVec 32).setWidth 64)),
         .gpr 1 ((((v101d06 x) : BitVec 32).setWidth 64)),
         .gpr 2 ((((v101d16 x) : BitVec 32).setWidth 64)),
         .gpr 8 ((((v101d1c x) : BitVec 32).setWidth 64)),
         .gpr 9 ((((v101d3f x) : BitVec 32).setWidth 64)),
         .gpr 7 ((((v101d2a x) : BitVec 32).setWidth 64)),
         .gpr 10 ((((v101d42 x) : BitVec 32).setWidth 64)),
         .gpr 5 ((((v101d49 x) : BitVec 32).setWidth 64)),
         .gpr 3 ((((v101d5d x) : BitVec 32).setWidth 64)),
         .gpr 15 ((((v101d66 x) : BitVec 32).setWidth 64))]
    | .s3 =>
        [.mem fr.rsi 32 x.s[0],
         .mem (fr.rsi + 4) 32 x.s[1],
         .mem (fr.rsi + 8) 32 x.s[2],
         .mem (fr.rsi + 12) 32 x.s[3],
         .mem (fr.rsi + 36) 32 x.acc[0],
         .mem (fr.rsi + 40) 32 x.acc[1],
         .mem (fr.rsi + 44) 32 x.acc[2],
         .mem (fr.rsi + 48) 32 x.acc[3],
         .mem (fr.rsi + 52) 32 x.acc[4],
         .gpr 1 ((((v101d06 x) : BitVec 32).setWidth 64)),
         .gpr 2 ((((v101d16 x) : BitVec 32).setWidth 64)),
         .gpr 8 ((((v101d1c x) : BitVec 32).setWidth 64)),
         .gpr 9 ((((v101dad x) : BitVec 32).setWidth 64)),
         .gpr 7 ((((v101d81 x) : BitVec 32).setWidth 64)),
         .gpr 10 ((((v101da7 x) : BitVec 32).setWidth 64)),
         .gpr 3 ((((v101d9b x) : BitVec 32).setWidth 64)),
         .gpr 14 ((((v101da1 x) : BitVec 32).setWidth 64)),
         .gpr 13 ((((v101d9e x) : BitVec 32).setWidth 64))]
    | .s4 =>
        [.mem fr.rsi 32 x.s[0],
         .mem (fr.rsi + 4) 32 x.s[1],
         .mem (fr.rsi + 8) 32 x.s[2],
         .mem (fr.rsi + 12) 32 x.s[3],
         .mem (fr.rsi + 36) 32 x.acc[0],
         .mem (fr.rsi + 40) 32 x.acc[1],
         .mem (fr.rsi + 44) 32 x.acc[2],
         .mem (fr.rsi + 48) 32 x.acc[3],
         .mem (fr.rsi + 52) 32 x.acc[4],
         .gpr 8 ((((v101dc6 x) : BitVec 32).setWidth 64)),
         .gpr 9 ((((v101de1 x) : BitVec 32).setWidth 64)),
         .gpr 7 ((((v101dea x) : BitVec 32).setWidth 64)),
         .gpr 10 ((((v101dd4 x) : BitVec 32).setWidth 64))]
    | .s5 =>
        [.mem fr.rdi 32 (v101dec x),
         .mem (fr.rdi + 4) 32 (((v101df5 x) : BitVec 64).setWidth 32),
         .mem (fr.rdi + 8) 32 (((v101e02 x) : BitVec 64).setWidth 32),
         .mem (fr.rdi + 12) 32 (v101e0e x),
         .mem fr.rsi 32 x.s[0],
         .mem (fr.rsi + 4) 32 x.s[1],
         .mem (fr.rsi + 8) 32 x.s[2],
         .mem (fr.rsi + 12) 32 x.s[3],
         .mem (fr.rsi + 36) 32 x.acc[0],
         .mem (fr.rsi + 40) 32 x.acc[1],
         .mem (fr.rsi + 44) 32 x.acc[2],
         .mem (fr.rsi + 48) 32 x.acc[3],
         .mem (fr.rsi + 52) 32 x.acc[4],
         .gpr 1 ((((v101e0e x) : BitVec 32).setWidth 64)),
         .gpr 2 ((((((v101e02 x) : BitVec 64).setWidth 32) : BitVec 32).setWidth 64)),
         .gpr 9 ((((v101de1 x) : BitVec 32).setWidth 64)),
         .gpr 7 ((((v101e05 x) : BitVec 32).setWidth 64))]
  Result := Unit
  output := fun _ => ⟨#v[], none, ()⟩
  done := fun _ fr _ =>
    [.mem fr.rdi 32 (v101dec x),
     .mem (fr.rdi + 4) 32 (((v101df5 x) : BitVec 64).setWidth 32),
     .mem (fr.rdi + 8) 32 (((v101e02 x) : BitVec 64).setWidth 32),
     .mem (fr.rdi + 12) 32 (v101e0e x)]
  footprint := fun _ fr => [⟨fr.rdi.toNat, 16⟩]

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Finish
