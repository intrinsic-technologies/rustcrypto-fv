import ChaCha20Poly1305.Proofs.Decrypt.StreamControl
import ChaCha20Poly1305.Proofs.Decrypt.XorLoop
import ChaCha20Poly1305.Proofs.Decrypt.JoinTactic

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
set_option maxHeartbeats 400000

theorem fullXor (x : Input) (j : BitVec 64) (fr : Activation) (a : lifted.Location)
    (hl : a.label = .l100fd0) (stack : Writable fnCode a.store fr.rsp 368)
    (sep : fr.rsp.toNat+368 ≤ 0x100fd0 ∨ 0x101036 ≤ fr.rsp.toNat)
    (input : Atom.All fnCode a.arguments a.store (fixedRegs x j fr ++ [.gpr 1 3])) :
    Ahead lifted fnCode (fun b => b.label = .l101036 ∧ Atom.All fnCode b.arguments b.store (fixedRegs x j fr) ∧
      Xor.Effect (fr.rsp+304) (fr.rsp+240) (fr.rsp+176) 64 a.store b.store) a := by
  let z : Xor.Input := ⟨fr.rsp,0,0,3,67,0,a.arguments,Vector.replicate 4 0,Vector.replicate 4 0⟩
  have low := stack.readable.low
  have ptrs : Xor.src .full z = fr.rsp+304 ∧ Xor.key .full z = fr.rsp+240 ∧ Xor.dst .full z = fr.rsp+176 := by
    simp [Xor.src,Xor.key,Xor.dst,z,BitVec.add_assoc]
  have geo (t : Nat) (ht : t ≤ 15) :
      Atom.All fnCode a.arguments a.store (Xor.attrs .full (Xor.shift z (4*t))) := by
    have bound := Xor.ptrNat (a := (3 : BitVec 64)) (i := 4*t) (by change 3+4*t < 2^64; omega)
    let off := Xor.ptr (3:BitVec 64) (4*t)
    have offNat : off.toNat = 3+4*t := bound
    have so : (fr.rsp + off).toNat = fr.rsp.toNat+off.toNat := by bv_omega
    change _ ∧ Writable _ _ (fr.rsp+off) 305 ∧ _ ∧ _ ∧ _ ∧ _ ∧ True
    exact ⟨stack,stack.sub (by omega) (by omega),by change (fr.rsp+off).toNat+305 ≤ 0x100fd0 ∨ 0x101036 ≤ (fr.rsp+off).toNat; omega,
      by change off.toNat ≤ 63; omega,rfl,sep,trivial⟩
  have ready : Xor.ReadyAt .full z .start false a := by
    refine ⟨hl,by simpa only [Nat.mul_zero,Xor.shift_zero] using geo 0 (by decide),?_,?_⟩
    · repeat' constructor
    · unpack_atoms input []
      join_atoms [Xor.regsAt,z]
  have shape : Xor.Shape (Xor.src .full z) (Xor.key .full z) (Xor.dst .full z) (Xor.bytes .full*(15+1)) := by
    rw [ptrs.1,ptrs.2.1,ptrs.2.2]
    constructor <;> simp only [Xor.bytes,Nat.reduceAdd,Nat.reduceMul] <;> bv_omega
  obtain ⟨b,steps,done,eff⟩ := Xor.loop .full z 15 rfl shape geo ready
  rw [ptrs.1, ptrs.2.1, ptrs.2.2] at eff
  refine ⟨b,steps,done.label,?_,eff⟩
  have h := done.saved
  have p := done.regs
  unpack_atoms input []
  unpack_atoms h [Xor.saved,Xor.shift,z]
  unpack_atoms p [Xor.regsAt,Xor.shift,z]
  join_atoms []
  all_goals assumption

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
