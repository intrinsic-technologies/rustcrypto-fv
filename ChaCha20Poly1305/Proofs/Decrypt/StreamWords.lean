import ChaCha20Poly1305.Proofs.Decrypt.StreamControl
import ChaCha20Poly1305.Proofs.Decrypt.XorRun
import ChaCha20Poly1305.Proofs.Common.Refine.Lemma.Region

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Standards.RFC.ChaCha20Poly1305

def sums (w : Vector UInt32 16) : Vector (BitVec 32) 16 :=
  Vector.ofFn fun i => (ChaChaRound.rounds 10 w)[i].toBitVec + w[i].toBitVec

theorem sumByte (w : Vector UInt32 16) {i : Nat} (hi : i<64) :
    storedByte (sums w)[i/4] (i%4) = (ChaChaRound.stream w)[i] := by
  simp only [ChaChaRound.stream,serialize,sums,Vector.getElem_ofFn]
  have h : i%4 < 4 := Nat.mod_lt _ (by decide)
  generalize i%4 = k at *
  rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem sumRead {w : Vector UInt32 16} {a : BitVec 64} {m : Ram} (words : WordsAt m a 32 (sums w))
    (i : Nat) (hi : i<64) : Xor.readAt m a i = (ChaChaRound.stream w)[i].toBitVec := by
  have v := words (i/4) (by omega)
  rw [← sumByte w hi,← v,storedByte_memLoad _ _ _ (by change i%4 < 4; omega),Xor.readAt,memLoad_8]
  congr 2
  simp only [wordAddr,BitVec.add_assoc,← BitVec.ofNat_add,Nat.reduceDiv,Nat.div_add_mod]

def chunkWords (m : Ram) (a : BitVec 64) : Vector (BitVec 64) 8 :=
  Vector.ofFn fun i => memLoad m (wordAddr a 64 i) 64

theorem qwordsInitial (m : Ram) (a : BitVec 64) (rs) :
    Atom.All fnCode rs m (qwords a (chunkWords m a)) := by
  simp +decide [qwords,chunkWords,wordAddr,Atom.All,Atom.Holds]

theorem qwordsRead {m m' : Ram} {src dst : BitVec 64} {rs}
    (h : Atom.All fnCode rs m' (qwords dst (chunkWords m src)))
    (i : Nat) (hi : i<64) : Xor.readAt m' dst i = Xor.readAt m src i := by
  have hv (k : Nat) (hk : k < 8) : memLoad m' (wordAddr dst 64 k) 64 = memLoad m (wordAddr src 64 k) 64 := by
    simp only [qwords,chunkWords,Atom.All,Atom.Holds,Vector.getElem_ofFn,wordAddr] at h
    iterate 8
      cases k
      case zero => simp +decide [wordAddr] at h ⊢; first | assumption | grind
      rename_i k
    omega
  have eq := memByte_of_memLoad_eq (hv (i/8) (by omega)) (i%8) (by change i%8 < 8; omega)
  simp only [wordAddr,Nat.reduceDiv,BitVec.add_assoc,← BitVec.ofNat_add,Nat.div_add_mod] at eq
  simpa only [Xor.readAt,memLoad_8] using congrArg UInt8.toBitVec eq

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
