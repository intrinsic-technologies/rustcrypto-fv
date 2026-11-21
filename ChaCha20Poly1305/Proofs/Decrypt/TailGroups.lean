import ChaCha20Poly1305.Proofs.Decrypt.TailGeometry
import ChaCha20Poly1305.Proofs.Decrypt.ControlSmallStart
import ChaCha20Poly1305.Proofs.Decrypt.ControlFourStart
import ChaCha20Poly1305.Proofs.Decrypt.ControlFourEnd

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 500000
set_option maxRecDepth 6000
set_option pp.maxSteps 180

theorem tailGroups (x : Input) (fr : Activation) (a : lifted.Location) (s : Scope x fr a.store)
    (nonzero : 0 < (Tail.rem64 x.n).toNat)
    (hl : a.label = (if (Tail.rem64 x.n).toNat < 4 then .l1013bf else .l1013e3))
    (input : Atom.All fnCode a.arguments a.store (Full.registers fr ++ tailState x fr)) :
    Ahead lifted fnCode (fun b => b.label = (if rem4 x = 0 then .l1014a4 else .l10146c) ∧
      Atom.All fnCode b.arguments b.store (tailRegs x fr ++ [.gpr 6 (groups x)]) ∧
      Xor.Effect (tailPtr x) (fr.rdi+64) (tailPtr x) (groups x).toNat a.store b.store) a := by
  have r := remNat x
  have g := groupsNat x
  have q := remFourNat x
  by_cases small : (Tail.rem64 x.n).toNat < 4
  · obtain ⟨b,ab,bl,post,f⟩ := Micro.run (smallStartValid x fr) (by change a.label = Lifted.Label.l1013bf; rwa [ite_eq_left small] at hl) input
    have z : groups x = 0 := BitVec.eq_of_toNat_eq (by change _ = 0; omega)
    have nz : rem4 x ≠ 0 := by intro h; rw [h] at q; change 0 = _ at q; omega
    refine ⟨b,ab,by rw [ite_eq_right nz]; exact bl,by rw [z]; exact post,?_⟩
    rw [z]
    exact ⟨noWrite f,by change ∀ k, k<0 → _; omega⟩
  · obtain ⟨b,ab,bl,post,f⟩ := Micro.run (fourStartValid x fr) (by change a.label = Lifted.Label.l1013e3; rwa [ite_eq_right small] at hl) input
    change Atom.All _ _ _ (tailRegs x fr ++ _) at post
    let n := (groups x).toNat/4-1
    have tot : 4*(n+1) = (groups x).toNat := by dsimp [n]; omega
    have t := s.tailGeo
    have z := tailInput b fr.rdi (tailPtr x) (groups x) (Tail.rem64 x.n).toNat
    obtain ⟨c,bc,cl,saved,regs,eff⟩ := tailXor b fr.rdi (tailPtr x) (groups x) (Tail.rem64 x.n).toNat n
      .tail4 (by intro h; cases h) (s.after f).tailGeo tot (by omega) bl (by
        unpack_atoms post []
        join_atoms [Xor.regsAt,tailInput]
        all_goals assumption)
    let last := decide (rem4 x ≠ 0)
    have after : Atom.All fnCode c.arguments c.store (tailRegs x fr ++ [.gpr 6 (groups x)]) := by
      have off : Xor.ptr 0 (4*n) + 4 = groups x := by
        apply BitVec.eq_of_toNat_eq
        have := (groups x).isLt
        have bound : 4*n+4 = (groups x).toNat := by omega
        simp only [Xor.ptr,BitVec.zero_add,BitVec.toNat_add,BitVec.toNat_ofNat,BitVec.ofNat_eq_ofNat]
        omega
      unpack_atoms post []
      unpack_atoms saved [Xor.saved,tailInput]
      unpack_atoms regs [Xor.regsAt,Xor.shift,tailInput,Xor.bytes]
      join_atoms [off]
      all_goals first | assumption | grind
    have iff : rem4 x ≠ 0 ↔ last=true := by simp [last]
    obtain ⟨d,cd,dl,dout,df⟩ := Micro.run (fourEndValid x fr last iff) cl after
    refine ⟨d,jumpTrans ab (jumpTrans bc cd),?_,dout,afterEmpty f eff df⟩
    change d.label = (if last then _ else _) at dl
    by_cases rz : rem4 x = 0
    · rw [ite_eq_left rz]; rw [ite_eq_right (show ¬ last = true by simp only [last,rz]; decide)] at dl; exact dl
    · rw [ite_eq_right rz]; rw [ite_eq_left (iff.mp rz)] at dl; exact dl

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
