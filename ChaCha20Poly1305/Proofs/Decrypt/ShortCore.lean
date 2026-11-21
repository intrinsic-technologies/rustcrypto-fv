import ChaCha20Poly1305.Proofs.Decrypt.Environment
import ChaCha20Poly1305.Proofs.Decrypt.Copy
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn101aa0.Frame

namespace ChaCha20Poly1305.Proofs.Decrypt.Short

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted

inductive Label | entry | shim | alloc | copy | finish

def program : Program (fun _ => _root_.Empty) Label (fun _ => 0) 0 := ⟨fun
  | .entry => .terminate (.call ⟨.shim, #v[]⟩ ⟨.alloc, #v[], rfl, none⟩)
  | .alloc => .terminate (.call ⟨.copy, #v[]⟩ ⟨.finish, #v[], rfl, none⟩)
  | _ => .terminate (.ret #v[])⟩

theorem executes : program.Exec Empty.semantics ⟨⟨.entry, #v[], ()⟩, []⟩ ⟨#v[], none, ()⟩ :=
  .next rfl (.next rfl (.next rfl (.next rfl (.done rfl))))

@[refine_layout] def shared (e : Env) (c : Activation) (fr : Activation) : List Atom :=
  [.fact (e.heap = fr.r8), .fact (e.src = fr.rcx), .fact (e.sp = fr.rsp),
    .fact (fr.low.toNat = fr.rsp.toNat - 1136),
    .fact (c.rbp = 1), .fact (c.r12 = fr.r8 + e.n), .fact (c.r13 = limit e),
    .readable fr.rcx e.n.toNat, .writable fr.r8 e.n.toNat, .writable 0x300000 16]

@[refine_layout] def core (e : Env) : LayoutCore program Empty.semantics lifted Activation where
  start
    | .entry => .l1014c0 | .alloc => .l10153a | .finish => .l10158b
    | .copy => .l102dc0 | .shim => .l101aa0
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms l c fr _ := match l with
    | .entry => shared e c fr ++
        [.readable fr.rdi 32, .readable (fr.rsp + 16) 16,
         .mem (fr.rsp + 16) 64 e.n, .mem (fr.rsp + 24) 64 e.cap,
         .fact (fr.rdi.toNat + 32 ≤ fr.rsp.toNat - 1008 ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat),
         .fact (fr.rdi.toNat + 32 ≤ 0x300000 ∨ 0x300010 ≤ fr.rdi.toNat)]
    | .alloc => shared e c fr ++
        [.gpr 14 e.n, .mem 0x300000 64 fr.r8, .mem 0x300008 64 c.r13]
    | .finish => shared e c fr ++
        [.gpr 14 e.n, .mem 0x300000 64 c.r12, .mem 0x300008 64 c.r13]
    | .shim => [.gpr 0 c.rbp, .mem 0x300000 64 c.r12, .mem 0x300008 64 c.r13]
    | .copy => [.gpr 7 c.rbp, .mem 0x300000 64 c.r12, .mem 0x300008 64 c.r13,
         .readable fr.rsi fr.rdx.toNat, .writable fr.rdi fr.rdx.toNat,
         .fact (fr.rsi = e.src), .fact (fr.rdi = e.heap), .fact (fr.rdx = e.n),
         .fact (fr.rsp = e.sp - 144), .fact (144 ≤ e.sp.toNat)]
  Result := Unit
  output := fun _ => ⟨#v[], none, ()⟩
  done := fun c _ _ => [.gpr 0 c.rbp, .mem 0x300000 64 c.r12, .mem 0x300008 64 c.r13]
  footprint := fun _ _ => [⟨e.heap.toNat, e.n.toNat⟩, ⟨0x300000, 16⟩]

@[refine_layout] def leafFrame (fr : Activation) : List Atom :=
  [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
   .gpr 12 fr.r12, .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15,
   .reg 39 ⟨32,fr.mxcsr⟩, .reg 50 ⟨16,fr.ftw⟩, .reg 51 ⟨16,fr.fcw⟩,
   .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2^32),
   .fact (fr.low.toNat ≤ fr.rsp.toNat)]

@[refine_layout] def frameAt (l : Lifted.Label) (fr : Activation) : List Atom :=
  match l with
  | .l102dc0 => leafFrame fr ++ [.gpr 7 fr.rdi, .gpr 6 fr.rsi, .gpr 2 fr.rdx]
  | .l101aa0 => leafFrame fr
  | _ => Decrypt.frameAt l fr

end ChaCha20Poly1305.Proofs.Decrypt.Short
