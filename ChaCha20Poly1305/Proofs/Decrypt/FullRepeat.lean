import ChaCha20Poly1305.Proofs.Decrypt.StreamScope
import ChaCha20Poly1305.Proofs.Decrypt.FullOne

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 600000
set_option maxRecDepth 6000
set_option pp.maxSteps 150

private theorem nextLive (x : Input) (fr : Activation) (i : Nat) {m rs}
    (h : Atom.All fnCode rs m (nextRegs (atBlock x i) (BitVec.ofNat 64 i) fr)) :
    Atom.All fnCode rs m (live x (i+1) fr) := by
  unpack_atoms h [atBlock,Vector.getElem_set,UInt32.toBitVec_add,UInt32.toBitVec_ofNat']
  all_goals simp +decide only [ite_true,ite_false,UInt32.toBitVec_add,UInt32.toBitVec_ofNat'] at *
  join_atoms [BitVec.ofNat_add]
  all_goals first | assumption | (congr 1 <;> bv_omega)

def streamByte (x : Input) (i : Nat) : BitVec 8 :=
  ((ChaChaRound.stream (atBlock x (i/64)).w)[i%64]'(Nat.mod_lt _ (by decide))).toBitVec

structure PrefixResult (x : Input) (fr : Activation) (m : Ram) (i : Nat) (b : lifted.Location) : Prop where
  label : b.label = (if i = x.n.toNat/64 then .l1010b3 else .l100c70)
  regs : Atom.All fnCode b.arguments b.store (live x i fr)
  frame : RamWriteFrame m b.store (prefixFrame x fr i)
  data : ∀ k, k<64*i → Xor.readAt b.store x.buf k = streamByte x k ^^^ Xor.readAt m x.buf k

theorem fullPrefix (x : Input) (fr : Activation) (a : lifted.Location) (scope : Scope x fr a.store)
    (pos : 0 < x.n.toNat/64) (hl : a.label = .l100c70)
    (start : Atom.All fnCode a.arguments a.store (live x 0 fr))
    (pins : Atom.All fnCode a.arguments a.store (pointers x fr ++ fixedSlots x fr))
    (i : Nat) (bound : i ≤ x.n.toNat/64) :
    Ahead lifted fnCode (PrefixResult x fr a.store i) a := by
  induction i with
  | zero =>
    exact ⟨a,.refl _,⟨by rw [ite_eq_right (Nat.ne_of_lt pos)]; exact hl,start,.refl _ _,by omega⟩⟩
  | succ i ih =>
    have hi : i < x.n.toNat/64 := by omega
    obtain ⟨b,ab,old⟩ := ih (by omega)
    have sc := scope.after old.frame
    let y := atBlock x i
    let j := BitVec.ofNat 64 i
    let last := decide (i+1=x.n.toNat/64)
    have jl : (j+1).toNat = i+1 := by have := x.len; dsimp [j]; bv_omega
    have dh : j+1 = y.n >>> 6 ↔ last=true := by
      change j+1 = x.n >>> 6 ↔ decide (i+1=_) = true
      rw [decide_eq_true_eq, ← BitVec.toNat_inj]
      exact ⟨fun h => jl.symm.trans (h.trans (blocksNat x)),fun h => jl.trans (h.trans (blocksNat x).symm)⟩
    have p := (Atom.all_append _ _).1 (pinsKept (rs' := b.arguments) scope (by omega) old.frame pins)
    obtain ⟨c,bc,l,r,f,v⟩ := fullOne y j fr b last dh (sc.block hi)
      (by simpa [Nat.ne_of_lt hi] using old.label) (setupAt sc old.regs p.2) p.1
    have addr : (blockPtr y j).toNat = x.buf.toNat+i*64 :=
      blockAddress x i (by omega) scope.buf.readable.low
    have f' : RamWriteFrame a.store c.store (prefixFrame x fr (i+1)) := by
      apply (RamWriteFrame.refl a.store _).trans old.frame _ |>.trans f
      · intro z hz
        rcases List.mem_cons.mp hz with rfl|hz
        · exact ⟨_,.head _,by dsimp; omega,by dsimp; omega⟩
        · exact ⟨_,.tail _ hz,Nat.le_refl _,Nat.le_refl _⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl|hz
        · exact ⟨_,.head _,Nat.le_refl _,by dsimp; omega⟩
        · exact ⟨_,.tail _ hz,Nat.le_refl _,Nat.le_refl _⟩
    refine ⟨c,jumpTrans ab bc,⟨by simpa [last] using l,nextLive x fr i r,f',?_⟩⟩
    intro k hk
    let dest := Xor.ptr x.buf k
    have dlo := scope.buf.readable.low
    have sk := scope.stackBuf
    have dp : dest.toNat = x.buf.toNat+k := Xor.ptrNat (by omega)
    by_cases prev : k < 64*i
    · rw [← old.data _ prev]
      apply f.memLoad_eq
      change Outside _ dest 1
      simp [Outside,blockScratch,dp,addr]
      omega
    · let t := k-64*i
      have ht : t<64 := by dsimp [t]; omega
      have idx : i*64+t=k := by dsimp [t]; omega
      have wj : j <<< 6 = BitVec.ofNat 64 (i*64) := by
        apply BitVec.eq_of_toNat_eq
        rw [blockIndex x i (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      have rd (m : Ram) : Xor.readAt m (blockPtr y j) t = Xor.readAt m x.buf k := by
        simp only [Xor.readAt,blockPtr,y,atBlock,wj,BitVec.add_assoc,← BitVec.ofNat_add,idx]
      have hb : Xor.readAt b.store x.buf k = Xor.readAt a.store x.buf k := by
        apply old.frame.memLoad_eq
        change Outside _ dest 1
        simp [Outside,prefixFrame,blockScratch,dp]
        omega
      have ev := v t ht
      rw [rd,rd,hb] at ev
      simpa only [streamByte,show k/64=i by omega,show k%64=t by dsimp [t]; omega,y] using ev

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
