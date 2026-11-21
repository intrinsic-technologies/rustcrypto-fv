import ChaCha20Poly1305.Proofs.Decrypt.ShortCore
import ChaCha20Poly1305.Proofs.Decrypt.Compose

namespace ChaCha20Poly1305.Proofs.Decrypt.Prefix

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted

structure Inputs (e : Short.Env) where
  key : Vector (BitVec 64) 4
  ciphertext : BitVec (8*e.n.toNat)
  srcStack : e.src.toNat + e.n.toNat ≤ e.sp.toNat-1136 ∨ e.sp.toNat + 8 ≤ e.src.toNat
  srcAlloc : e.src.toNat + e.n.toNat ≤ 0x300000 ∨ 0x300010 ≤ e.src.toNat

@[refine_layout] def keyAtoms (k : BitVec 64) (ws : Vector (BitVec 64) 4) : List Atom :=
  [.mem k 64 ws[0],.mem (k+8) 64 ws[1],.mem (k+16) 64 ws[2],.mem (k+24) 64 ws[3]]

@[refine_layout] def core (e : Short.Env) (x : Inputs e) : LayoutCore Short.program Empty.semantics lifted Activation where
  start := (Short.core e).start
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms l c fr p := (Short.core e).atoms l c fr p ++
    match l with
    | .entry => keyAtoms fr.rdi x.key ++
        [.fact (c.rdx = 0), .fact (memLoad fr.original e.src (8*e.n.toNat) = x.ciphertext)]
    | .alloc => keyAtoms (fr.rsp - 80) x.key ++
        [.fact (c.rdx = 0), .fact (memLoad fr.original e.src (8*e.n.toNat) = x.ciphertext)]
    | .finish => keyAtoms (fr.rsp - 80) x.key ++
        [.gpr 5 e.heap,.mem (fr.rsp - 128) 64 e.n,.mem (fr.rsp - 120) 64 e.heap,
         .mem e.heap (8*e.n.toNat) x.ciphertext]
    | .shim => [.fact (c.rdx = 0)]
    | .copy => [.gpr 2 c.rdx,.mem e.src (8*e.n.toNat) x.ciphertext]
  Result := Unit
  output := fun _ => ⟨#v[],none,()⟩
  done := fun c fr p => (Short.core e).done c fr p ++
    [.mem e.heap (8*c.rdx.toNat) (x.ciphertext.setWidth (8*c.rdx.toNat))]
  footprint := (Short.core e).footprint

end ChaCha20Poly1305.Proofs.Decrypt.Prefix
