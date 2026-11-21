import ChaCha20Poly1305.Proofs.Decrypt.Stream
import ChaCha20Poly1305.Proofs.Decrypt.Refine

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Xor
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

inductive Kind | full | tail4 | tail1
inductive Label | start | next

def program : Program (fun _ => _root_.Empty) Label (fun _ => 0) 0 := ⟨fun
  | .start => .terminate (.br ⟨.next,#v[]⟩)
  | .next => .terminate (.ret #v[])⟩

structure Input where
  sp : BitVec 64
  keyBase : BitVec 64
  buf : BitVec 64
  off : BitVec 64
  limit : BitVec 64
  remaining : Nat
  regs : Values Value Reg.count
  keyBytes : Vector (BitVec 8) 4
  srcBytes : Vector (BitVec 8) 4

@[refine_layout] def bytes : Kind → Nat | .full | .tail4 => 4 | .tail1 => 1
def done (k : Kind) (x : Input) := x.off + BitVec.ofNat 64 (bytes k) = x.limit

@[refine_layout] def geoFull (x : Input) : List Atom :=
  [.writable x.sp 368,.writable (x.sp+x.off) 305, .fact ((x.sp+x.off).toNat+305 ≤ 0x100fd0 ∨ 0x101036 ≤ (x.sp+x.off).toNat), .fact (x.off.toNat ≤ 63),.fact (x.limit = 67),
   .fact (x.sp.toNat+368 ≤ 0x100fd0 ∨ 0x101036 ≤ x.sp.toNat)]

@[refine_layout] def geoTail (k : Kind) (x : Input) : List Atom :=
  [.readable (x.keyBase+64) x.remaining,.writable x.buf x.remaining,
   .fact ((x.keyBase+64).toNat+x.remaining ≤ x.buf.toNat ∨ x.buf.toNat+x.remaining ≤ (x.keyBase+64).toNat),
   .fact (x.buf.toNat+x.remaining ≤ 0x101420 ∨ 0x1014a4 ≤ x.buf.toNat),
   .fact (x.off.toNat+bytes k ≤ x.remaining),.fact (x.remaining ≤ 64)]

@[refine_layout] def begins : Kind → Lifted.Label | .full => .l100fd0 | .tail4 => .l101420 | .tail1 => .l101490
@[refine_layout] def ends : Kind → Lifted.Label | .full => .l101036 | .tail4 => .l101467 | .tail1 => .l1014a4

@[refine_layout] def dst (k : Kind) (x : Input) := match k with
  | .full => x.sp+x.off+173
  | _ => x.buf+x.off

@[refine_layout] def fullRegs (x : Input) : List Atom :=
  [.reg 0 x.regs[0],
    .reg 7 x.regs[7],
    .reg 8 x.regs[8],
    .reg 9 x.regs[9],
    .reg 10 x.regs[10],
    .reg 11 x.regs[11],
    .reg 12 x.regs[12],
    .reg 22 x.regs[22],
    .reg 39 x.regs[39],
    .reg 50 x.regs[50],
    .reg 51 x.regs[51]]

@[refine_layout] def fullPointers (l : Label) (exitLoop : Bool) (x : Input) : List Atom := match l,exitLoop with
  | .start,_ => [.gpr 4 x.sp,
    .gpr 1 x.off]
  | .next,false => [.gpr 4 x.sp,
    .gpr 1 (x.off+4)]
  | .next,true => [.gpr 4 x.sp]

@[refine_layout] def fullData (l : Label) (x : Input) : List Atom := match l with
  | .start => [.mem (x.sp+x.off+237) 8 x.keyBytes[0],
    .mem (x.sp+x.off+238) 8 x.keyBytes[1],
    .mem (x.sp+x.off+239) 8 x.keyBytes[2],
    .mem (x.sp+x.off+240) 8 x.keyBytes[3],
    .mem (x.sp+x.off+301) 8 x.srcBytes[0],
    .mem (x.sp+x.off+302) 8 x.srcBytes[1],
    .mem (x.sp+x.off+303) 8 x.srcBytes[2],
    .mem (x.sp+x.off+304) 8 x.srcBytes[3]]
  | .next => [.mem (dst .full x+0) 8 (x.keyBytes[0] ^^^ x.srcBytes[0]),
    .mem (dst .full x+1) 8 (x.keyBytes[1] ^^^ x.srcBytes[1]),
    .mem (dst .full x+2) 8 (x.keyBytes[2] ^^^ x.srcBytes[2]),
    .mem (dst .full x+3) 8 (x.keyBytes[3] ^^^ x.srcBytes[3])]

@[refine_layout] def tail4Regs (x : Input) : List Atom :=
  [.reg 0 x.regs[0],
    .reg 3 x.regs[3],
    .reg 4 x.regs[4],
    .reg 8 x.regs[8],
    .reg 11 x.regs[11],
    .reg 14 x.regs[14],
    .reg 15 x.regs[15],
    .reg 22 x.regs[22],
    .reg 39 x.regs[39],
    .reg 50 x.regs[50],
    .reg 51 x.regs[51]]

@[refine_layout] def tail4Pointers (l : Label) (exitLoop : Bool) (x : Input) : List Atom := match l,exitLoop with
  | .start,_ => [.gpr 1 (x.buf+3),
    .gpr 2 (x.buf+3),
    .gpr 6 x.off,
    .gpr 9 x.keyBase,
    .gpr 10 x.limit]
  | .next,false => [.gpr 1 (x.buf+3),
    .gpr 2 (x.buf+3),
    .gpr 6 (x.off+4),
    .gpr 9 x.keyBase,
    .gpr 10 x.limit]
  | .next,true => [.gpr 1 (x.buf+3),
    .gpr 2 (x.buf+3),
    .gpr 6 (x.off+4),
    .gpr 9 x.keyBase]

@[refine_layout] def tail4Data (l : Label) (x : Input) : List Atom := match l with
  | .start => [.mem (x.keyBase+64+x.off) 8 x.keyBytes[0],
    .mem (x.keyBase+64+x.off+1) 8 x.keyBytes[1],
    .mem (x.keyBase+64+x.off+2) 8 x.keyBytes[2],
    .mem (x.keyBase+64+x.off+3) 8 x.keyBytes[3],
    .mem (x.buf+x.off) 8 x.srcBytes[0],
    .mem (x.buf+x.off+1) 8 x.srcBytes[1],
    .mem (x.buf+x.off+2) 8 x.srcBytes[2],
    .mem (x.buf+x.off+3) 8 x.srcBytes[3]]
  | .next => [.mem (dst .tail4 x+0) 8 (x.keyBytes[0] ^^^ x.srcBytes[0]),
    .mem (dst .tail4 x+1) 8 (x.keyBytes[1] ^^^ x.srcBytes[1]),
    .mem (dst .tail4 x+2) 8 (x.keyBytes[2] ^^^ x.srcBytes[2]),
    .mem (dst .tail4 x+3) 8 (x.keyBytes[3] ^^^ x.srcBytes[3])]

@[refine_layout] def tail1Regs (x : Input) : List Atom :=
  [.reg 4 x.regs[4],
    .reg 7 x.regs[7],
    .reg 9 x.regs[9],
    .reg 14 x.regs[14],
    .reg 22 x.regs[22],
    .reg 39 x.regs[39],
    .reg 50 x.regs[50],
    .reg 51 x.regs[51]]

@[refine_layout] def tail1Pointers (l : Label) (exitLoop : Bool) (x : Input) : List Atom := match l,exitLoop with
  | .start,_ => [.gpr 0 x.limit,
    .gpr 1 (x.keyBase+64),
    .gpr 2 x.off,
    .gpr 3 x.buf,
    .gpr 11 x.buf]
  | .next,false => [.gpr 0 x.limit,
    .gpr 1 (x.keyBase+64),
    .gpr 2 (x.off+1),
    .gpr 3 x.buf,
    .gpr 11 x.buf]
  | .next,true => [.gpr 0 x.limit,
    .gpr 1 (x.keyBase+64),
    .gpr 2 (x.off+1)]

@[refine_layout] def tail1Data (l : Label) (x : Input) : List Atom := match l with
  | .start => [.mem (x.keyBase+64+x.off) 8 x.keyBytes[0],
    .mem (x.buf+x.off) 8 x.srcBytes[0]]
  | .next => [.mem (dst .tail1 x+0) 8 (x.keyBytes[0] ^^^ x.srcBytes[0])]

def layout (k : Kind) (x : Input) (exitLoop : Bool) : Layout program Empty.semantics lifted Ram where
  start | .start => begins k | .next => if exitLoop then ends k else begins k
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms l _ _ := match k with
    | .full => geoFull x ++ fullRegs x ++ fullPointers l exitLoop x ++ fullData l x
    | .tail4 => geoTail .tail4 x ++ tail4Regs x ++ tail4Pointers l exitLoop x ++ tail4Data l x
    | .tail1 => geoTail .tail1 x ++ tail1Regs x ++ tail1Pointers l exitLoop x ++ tail1Data l x
  Result := Unit
  output := fun _ => ⟨#v[],none,()⟩
  done := fun _ _ => []
  retAddr := fun _ => 0
  original := id
  regions := fun _ => [⟨(dst k x).toNat,bytes k⟩]
end ChaCha20Poly1305.Proofs.Decrypt.Stream.Xor
