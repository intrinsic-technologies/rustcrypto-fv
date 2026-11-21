import ChaCha20Poly1305.Proofs.Decrypt.TailGroups
import ChaCha20Poly1305.Proofs.Decrypt.ControlOneStart
import ChaCha20Poly1305.Proofs.Decrypt.ControlFinishTail

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 500000
set_option maxRecDepth 6000

theorem residual (x : Input) (fr : Activation) (a : lifted.Location) (s : Scope x fr a.store)
    (hl : a.label = (if rem4 x = 0 then .l1014a4 else .l10146c))
    (input : Atom.All fnCode a.arguments a.store (tailRegs x fr ++ [.gpr 6 (groups x)])) :
    Ahead lifted fnCode (fun b => b.label = .l1014a4 ∧
      Atom.All fnCode b.arguments b.store (Full.registers fr ++ [.gpr 9 fr.rdi,.gpr 14 (Tail.rem64 x.n)]) ∧
      Xor.Effect (tailPtr x+groups x) (fr.rdi+groups x+64) (tailPtr x+groups x) (rem4 x).toNat a.store b.store) a := by
  by_cases zero : rem4 x = 0
  · refine ⟨a,.refl _,by rw [ite_eq_left zero] at hl; exact hl,?_,?_⟩
    · unpack_atoms input []
      join_atoms []
    · rw [zero]; exact Xor.Effect.zero
  · obtain ⟨b,ab,bl,out,f⟩ := Micro.run (oneStartValid x fr) (by rw [ite_eq_right zero] at hl; exact hl) input
    have q := remFourNat x
    have p : 0 < (rem4 x).toNat := by
      apply Nat.pos_of_ne_zero; intro h; exact zero (BitVec.eq_of_toNat_eq h)
    let n := (rem4 x).toNat-1
    have tot : 1*(n+1) = (rem4 x).toNat := by dsimp [n]; omega
    obtain ⟨c,bc,cl,sv,_,ef⟩ := tailXor b (fr.rdi+groups x) (tailPtr x+groups x) (rem4 x) (rem4 x).toNat n
      .tail1 (by intro h; cases h) (s.after f).residualGeo tot (Nat.le_refl _) bl (by
        unpack_atoms out []
        join_atoms [Xor.regsAt,tailInput]
        all_goals assumption)
    refine ⟨c,jumpTrans ab bc,cl,?_,afterEmpty f ef (.refl _ _)⟩
    unpack_atoms out []
    unpack_atoms sv [Xor.saved,tailInput]
    join_atoms []
    all_goals assumption

theorem tailBytes (x : Input) (fr : Activation) (a : lifted.Location) (s : Scope x fr a.store)
    (nonzero : 0 < (Tail.rem64 x.n).toNat)
    (hl : a.label = (if (Tail.rem64 x.n).toNat < 4 then .l1013bf else .l1013e3))
    (input : Atom.All fnCode a.arguments a.store (Full.registers fr ++ tailState x fr)) :
    Ahead lifted fnCode (fun b => b.label = .l1014a4 ∧
      Atom.All fnCode b.arguments b.store (Full.registers fr ++ [.gpr 9 fr.rdi,.gpr 14 (Tail.rem64 x.n)]) ∧
      Xor.Effect (tailPtr x) (fr.rdi+64) (tailPtr x) (Tail.rem64 x.n).toNat a.store b.store) a := by
  obtain ⟨b,ab,bl,atoms,f⟩ := tailGroups x fr a s nonzero hl input
  obtain ⟨c,bc,cl,regs,g⟩ := residual x fr b (s.after f.frame) bl atoms
  refine ⟨c,jumpTrans ab bc,cl,regs,?_⟩
  have total : (groups x).toNat+(rem4 x).toNat = (Tail.rem64 x.n).toNat := by
    rw [groupsNat,remFourNat,remNat]; omega
  have dst : Xor.ptr (tailPtr x) (groups x).toNat = tailPtr x+groups x := by simp [Xor.ptr]
  have key : Xor.ptr (fr.rdi+64) (groups x).toNat = fr.rdi+groups x+64 := by simp [Xor.ptr]; ac_rfl
  rw [← dst,← key] at g
  rw [← total]
  exact Xor.Effect.join s.tailGeo.shape (Nat.le_of_eq total) f g

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
