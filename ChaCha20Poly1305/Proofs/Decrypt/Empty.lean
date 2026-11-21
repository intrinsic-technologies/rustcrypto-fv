import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Decrypt
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Decrypt.Frame
import ChaCha20Poly1305.Proofs.Common.Refine.Tactic

namespace ChaCha20Poly1305.Proofs.Decrypt.Empty

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted

inductive Label | entry

def program : Program (fun _ => Empty) Label (fun _ => 0) 0 :=
  ⟨fun _ => .terminate (.ret #v[])⟩

def semantics : Dialect (fun _ => Empty) Unit Unit :=
  Dialect.ofPure (fun op => nomatch op) (fun _ => true)

@[refine_layout] def core : LayoutCore program semantics lifted Unit where
  start := fun _ => .l1014c0
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms := fun _ _ fr _ =>
    [.readable fr.rdi 32, .readable (fr.rsp + 16) 16, .mem (fr.rsp + 16) 64 0,
     .writable 0x300000 16,
     .fact (fr.rsp.toNat ≤ 0x100000 ∨ 0x102def + 0x3f0 ≤ fr.rsp.toNat),
     .fact (fr.rdi.toNat + 32 ≤ fr.rsp.toNat - 0x3f0 ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat),
     .fact (fr.rdi.toNat + 32 ≤ 0x300000 ∨ 0x300010 ≤ fr.rdi.toNat),
     .fact (fr.rsp.toNat + 8 ≤ 0x300000 ∨ 0x300010 ≤ fr.rsp.toNat - 0x3f0),
     .fact (fr.rsp.toNat + 32 ≤ 0x300000 ∨ 0x300010 ≤ fr.rsp.toNat + 16)]
  Result := Unit
  output := fun _ => ⟨#v[], none, ()⟩
  done := fun _ _ _ => [.gpr 0 1]
  footprint := fun _ _ => [⟨0x300000, 16⟩]

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option pp.maxSteps 2000

theorem blocks :
    ∀ l, (Layout.withFrame Decrypt.frameAt Decrypt.doneAt core).BlockSimulation fnCode l := by
  intro l
  cases l
  x86_refine [program]
  all_goals first | contradiction | simp_all only [BitVec.msb_zero, Bool.false_eq_true, not_false_eq_true] | skip

end ChaCha20Poly1305.Proofs.Decrypt.Empty
