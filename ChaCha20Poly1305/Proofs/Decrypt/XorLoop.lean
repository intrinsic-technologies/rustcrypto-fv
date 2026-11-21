import ChaCha20Poly1305.Proofs.Decrypt.XorEffect
import ChaCha20Poly1305.Proofs.Decrypt.RoundFrame

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Xor
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

def shift (x : Input) (i : Nat) := {x with off := ptr x.off i}

theorem shift_zero (x : Input) : shift x 0 = x := by simp [shift,ptr]

theorem shift_add (x : Input) (i j : Nat) : shift (shift x i) j = shift x (i+j) := by
  simp only [shift,ptr_assoc]

theorem key_shift (k : Kind) (x : Input) (i : Nat) : key k (shift x i) = ptr (key k x) i := by
  cases k <;> simp [key,shift,ptr] <;> ac_rfl
theorem src_shift (k : Kind) (x : Input) (i : Nat) : src k (shift x i) = ptr (src k x) i := by
  cases k <;> simp [src,shift,ptr] <;> ac_rfl
theorem dst_shift (k : Kind) (x : Input) (i : Nat) : dst k (shift x i) = ptr (dst k x) i := by
  cases k <;> simp [dst,shift,ptr] <;> ac_rfl

theorem Shape.tail {s k d : BitVec 64} {p q : Nat} (sh : Shape s k d (p+q)) :
    Shape (ptr s p) (ptr k p) (ptr d p) q := by
  obtain ⟨hs,hk,hd,hka,hsa⟩ := sh
  constructor <;> simp only [ptrNat (a := s) (i := p) (by omega),ptrNat (a := d) (i := p) (by omega),
    ptrNat (a := k) (i := p) (by omega)]
  all_goals first | omega | (rcases hsa with h | h <;> first | (left; rw [h]) | omega)

private theorem attrs_later {k : Kind} {x : Input} {m m' : Ram} {regions : List MemoryRegion} {rs rs'}
    (hf : RamWriteFrame m m' regions) (h : Atom.All fnCode rs m (attrs k x)) :
    Atom.All fnCode rs' m' (attrs k x) := by
  apply ChaChaRound.keepFrame _ hf h
  intro t hat
  cases k <;> simp only [attrs,geoFull,geoTail,List.mem_cons,List.not_mem_nil,or_false] at hat
  all_goals rcases hat with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

private theorem cont (k : Kind) (x : Input) {a : lifted.Location} (h : ReadyAt k x .next false a)
    (ha : Atom.All fnCode a.arguments a.store (attrs k (shift x (bytes k)))) :
    ReadyAt k (shift x (bytes k)) .start false a := by
  cases k <;> exact ⟨h.label,ha,h.saved,h.regs⟩

private theorem stop (k : Kind) (x : Input) {a : lifted.Location} (h : ReadyAt k x .start false a) :
    ReadyAt k x .start true a := by
  cases k <;> exact ⟨h.label,h.attrs,h.saved,h.regs⟩

private theorem bytesPos (k : Kind) : 0 < bytes k := by cases k <;> decide

theorem loop {a : lifted.Location} (k : Kind) (x : Input) (n : Nat)
    (reach : x.off.toNat + bytes k * (n+1) = x.limit.toNat)
    (shape : Shape (src k x) (key k x) (dst k x) (bytes k*(n+1)))
    (access : ∀ t, t ≤ n → Atom.All fnCode a.arguments a.store (attrs k (shift x (bytes k*t))))
    (start : ReadyAt k x .start false a) :
    Ahead lifted fnCode (fun b => ReadyAt k (shift x (bytes k*n)) .next true b ∧
      Effect (src k x) (key k x) (dst k x) (bytes k*(n+1)) a.store b.store) a := by
  have pos := bytesPos k
  induction n generalizing a x
  all_goals
    have lb := x.limit.isLt
    have boundStep : x.off.toNat+bytes k < 2^64 := by
      rw [Nat.mul_succ] at reach; omega
    have offNat : (x.off + BitVec.ofNat 64 (bytes k)).toNat = x.off.toNat + bytes k := ptrNat boundStep
  case zero =>
    have eq : done k x := BitVec.eq_of_toNat_eq (offNat.trans (by simpa only [Nat.zero_add,Nat.mul_one] using reach))
    obtain ⟨b,j,v,e,f⟩ := iteration k x true (by simp [eq]) (stop _ _ start)
    simp only [Nat.zero_add,Nat.mul_zero,shift_zero,Nat.mul_one]
    exact ⟨b,j,v,⟨f,e⟩⟩
  case succ n ih =>
    have tot : bytes k*((n+1)+1) = bytes k + bytes k*(n+1) := by rw [Nat.mul_succ,Nat.add_comm]
    have notDone : ¬ done k x := by
      intro eq
      have eq' := (congrArg BitVec.toNat eq).symm.trans offNat
      rw [tot] at reach
      have hp : 0 < bytes k*(n+1) := Nat.mul_pos pos (by omega)
      omega
    obtain ⟨b,prev,atNext,v,f⟩ := iteration k x false (by simp [notDone]) start
    let y := shift x (bytes k)
    have ac (t : Nat) (ht : t ≤ n) : Atom.All fnCode b.arguments b.store (attrs k (shift y (bytes k*t))) := by
      dsimp only [y]
      rw [shift_add,show bytes k+bytes k*t = bytes k*(t+1) by rw [Nat.mul_succ,Nat.add_comm]]
      exact attrs_later f (access _ (by omega))
    have r : y.off.toNat+bytes k*(n+1) = y.limit.toNat := by
      change (ptr x.off (bytes k)).toNat + _ = x.limit.toNat
      rw [ptrNat boundStep,Nat.add_assoc,← tot]; exact reach
    have sh : Shape (src k y) (key k y) (dst k y) (bytes k*(n+1)) := by
      simp only [y,src_shift,key_shift,dst_shift]
      exact Shape.tail (tot ▸ shape)
    have st : ReadyAt k y .start false b := cont _ _ atNext (by simpa only [Nat.mul_zero,shift_zero] using ac 0 (by omega))
    obtain ⟨c,post,final,ef⟩ := ih (x := y) (a := b) r sh ac st
    refine ⟨c,jumpTrans prev post,?_,?_⟩
    · simpa only [y,shift_add,Nat.mul_succ,Nat.add_comm (bytes k) (bytes k*n)] using final
    · rw [tot]
      simp only [y,src_shift,key_shift,dst_shift] at ef
      exact Effect.join (tot ▸ shape) (Nat.le_refl _) ⟨f,v⟩ ef

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Xor
