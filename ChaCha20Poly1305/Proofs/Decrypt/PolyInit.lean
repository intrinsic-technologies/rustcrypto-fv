import ChaCha20Poly1305.Proofs.Decrypt.ActiveFrames
import ChaCha20Poly1305.Proofs.Decrypt.Copy
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn101e40.Frame
import ChaCha20Poly1305.Proofs.Decrypt.Poly1305

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Init

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted

def r (key : BitVec 256) := key &&& 0x0ffffffc0ffffffc0ffffffc0fffffff

def limb (key : BitVec 256) (i : Nat) : BitVec 32 :=
  ((r key).extractLsb' (26*i) 32) &&& 0x3ffffff

@[refine_layout] def core (key : BitVec 256) : LayoutCore Copy.program Empty.semantics lifted Unit where
  start := fun _ => .l101e40
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms := fun _ _ fr _ =>
    [.readable fr.rsi 32, .writable fr.rdi 56,
     .fact (fr.rdi.toNat + 56 ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 32 ≤ fr.rdi.toNat),
     .fact (fr.rdi.toNat + 56 ≤ 0x101e40 ∨ 0x101eb8 ≤ fr.rdi.toNat),
     .fact (fr.rdi.toNat + 56 ≤ fr.rsp.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat),
     .mem fr.rsi 32 (key.extractLsb' 0 32),
     .mem (fr.rsi + 3) 32 (key.extractLsb' 24 32),
     .mem (fr.rsi + 6) 32 (key.extractLsb' 48 32),
     .mem (fr.rsi + 9) 32 (key.extractLsb' 72 32),
     .mem (fr.rsi + 12) 32 (key.extractLsb' 96 32),
     .mem (fr.rsi + 16) 64 (key.extractLsb' 128 64),
     .mem (fr.rsi + 24) 64 (key.extractLsb' 192 64)]
  Result := Unit
  output := fun _ => ⟨#v[], none, ()⟩
  done := fun _ fr _ =>
    [.gpr 0 fr.rdi,
     .mem fr.rdi 64 (key.extractLsb' 128 64),
     .mem (fr.rdi + 8) 64 (key.extractLsb' 192 64),
     .mem (fr.rdi + 16) 32 (limb key 0),
     .mem (fr.rdi + 20) 32 (limb key 1),
     .mem (fr.rdi + 24) 32 (limb key 2),
     .mem (fr.rdi + 28) 32 (limb key 3),
     .mem (fr.rdi + 32) 32 (limb key 4),
     .mem (fr.rdi + 36) 32 0,
     .mem (fr.rdi + 40) 32 0,
     .mem (fr.rdi + 44) 32 0,
     .mem (fr.rdi + 48) 32 0,
     .mem (fr.rdi + 52) 32 0]
  footprint := fun _ fr => [⟨fr.rdi.toNat, 56⟩]

set_option maxRecDepth 10000
set_option maxHeartbeats 600000

private theorem bitExt32 {x y : BitVec 32} (h : ∀ j : Fin 32, x.getLsbD j = y.getLsbD j) : x = y :=
  BitVec.eq_of_getLsbD_eq (fun k hk => h ⟨k,hk⟩)

theorem blocks (key : BitVec 256) :
    ∀ l, (Layout.withFrame Fn101e40.active Fn101e40.doneAt (core key)).BlockSimulation fnCode l := by
  intro l
  cases l
  x86_refine [Copy.program]
  all_goals
    apply bitExt32
    intro j
    unfold limb r
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight]
    obtain ⟨j, hj⟩ := j
    dsimp only
    iterate 32
      cases j
      case zero => simp +decide
      rename_i j
    omega

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Init
