import Standards.RFC.ChaCha20Poly1305

namespace ChaCha20Poly1305.Proofs.Core

open Standards.RFC.ChaCha20Poly1305

def zeros32 : ByteArray := ⟨Array.replicate 32 0⟩

theorem keygen (key : Vector UInt8 32) (nonce : Vector UInt8 12) :
    chacha20Encrypt key 0 nonce zeros32 = ⟨(poly1305KeyGen key nonce).toArray⟩ := by
  have hs : zeros32.size = 32 := rfl
  apply ByteArray.ext
  simp only [chacha20Encrypt, chachaEncrypt, hs, poly1305KeyGen, chacha20Block, Id.run]
  simp
  simp only [pure]
  apply Array.ext
  · simp [hs]
  · intro i h1 h2
    rw [Array.getElem_ofFn, Array.getElem_ofFn]
    have hi : i < 32 := by simpa using h2
    have hz : (zeros32.extract 0 32)[i]'(by simp [hs]; omega) = 0 := by
      rw [ByteArray.getElem_extract]
      simp [zeros32, ByteArray.getElem_eq_getElem_data]
    simp only [hz, UInt8.zero_xor]
    exact getElem!_pos (chachaBlock key (counterNonceWords 1 0 nonce)) i (by omega)

end ChaCha20Poly1305.Proofs.Core
