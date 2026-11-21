import ChaCha20Poly1305.Proofs.Decrypt.TailControl
import ChaCha20Poly1305.Proofs.Decrypt.FullXorRun
import ChaCha20Poly1305.Proofs.Decrypt.BlockMath

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
set_option maxHeartbeats 500000
set_option maxRecDepth 6000

def tailInput (a : lifted.Location) (base buf limit : BitVec 64) (remain : Nat) : Xor.Input :=
  ⟨0,base,buf,0,limit,remain,a.arguments,Vector.replicate 4 0,Vector.replicate 4 0⟩

structure TailGeo (key buf : BitVec 64) (n : Nat) (m : Ram) : Prop where
  keys : Readable m (key+64) n
  buffer : Writable fnCode m buf n
  apart : (key+64).toNat+n ≤ buf.toNat ∨ buf.toNat+n ≤ (key+64).toNat
  code : buf.toNat+n ≤ 0x101420 ∨ 0x1014a4 ≤ buf.toNat
  small : n ≤ 64

theorem tailXor (a : lifted.Location) (base buf limit : BitVec 64) (remain n : Nat)
    (k : Xor.Kind) (tail : k ≠ .full)
    (geo : TailGeo base buf remain a.store)
    (reach : Xor.bytes k*(n+1) = limit.toNat) (fits : limit.toNat ≤ remain)
    (hl : a.label = Xor.begins k)
    (pre : Atom.All fnCode a.arguments a.store
      (Xor.regsAt k .start false (tailInput a base buf limit remain))) :
    let x := tailInput a base buf limit remain
    Ahead lifted fnCode (fun b => b.label = Xor.ends k ∧
      Atom.All fnCode b.arguments b.store (Xor.saved k x) ∧ Atom.All fnCode b.arguments b.store
        (Xor.regsAt k .next true (Xor.shift x (Xor.bytes k*n))) ∧
      Xor.Effect buf (base+64) buf limit.toNat a.store b.store) a := by
  let x := tailInput a base buf limit remain
  change Ahead _ _ (fun b => _ ∧ Atom.All _ _ _ (Xor.saved k x) ∧ _ ∧ _) a
  have p : Xor.src k x = buf ∧ Xor.key k x = base+64 ∧ Xor.dst k x = buf := by
    cases k <;> simp_all [Xor.src,Xor.key,Xor.dst,x,tailInput]
  obtain ⟨keys,buffer,sep,code,small⟩ := geo
  have kLow := keys.low
  have bLow := buffer.readable.low
  have shape : Xor.Shape (Xor.src k x) (Xor.key k x) (Xor.dst k x) (Xor.bytes k*(n+1)) := by
    rw [p.1,p.2.1,p.2.2,reach]
    exact ⟨by omega,by omega,by omega,by omega,.inl rfl⟩
  have access (t : Nat) (ht : t ≤ n) :
      Atom.All fnCode a.arguments a.store (Xor.attrs k (Xor.shift x (Xor.bytes k*t))) := by
    have bound : Xor.bytes k*t+Xor.bytes k ≤ limit.toNat := by
      rw [← reach,← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ (by omega)
    have off : (Xor.shift x (Xor.bytes k*t)).off.toNat = Xor.bytes k*t := by
      exact (Xor.ptrNat (a := (0:BitVec 64)) (i := Xor.bytes k*t) (by change 0+Xor.bytes k*t < 2^64; omega)).trans (Nat.zero_add _)
    have bound' : (Xor.shift x (Xor.bytes k*t)).off.toNat + Xor.bytes k ≤ remain := by rw [off]; omega
    cases k <;> try contradiction
    all_goals exact ⟨keys,buffer,sep,code,bound',small,trivial⟩
  have start : Xor.ReadyAt k x .start false a := by
    refine ⟨hl,by simpa only [Nat.mul_zero,Xor.shift_zero] using access 0 (by omega),?_,pre⟩
    cases k <;> try contradiction
    all_goals repeat' constructor
  obtain ⟨b,s,ready,ef⟩ := Xor.loop k x n (by change 0+Xor.bytes k*(n+1)=limit.toNat; omega) shape access start
  rw [p.1,p.2.1,p.2.2,reach] at ef
  have saved : Xor.saved k (Xor.shift x (Xor.bytes k*n)) = Xor.saved k x := by cases k <;> rfl
  refine ⟨b,s,?_,saved ▸ ready.saved,ready.regs,ef⟩
  cases k <;> exact ready.label

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
