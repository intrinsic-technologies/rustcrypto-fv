import ChaCha20Poly1305.Proofs.Decrypt.Environment
import Init.Data.ByteArray.Lemmas
import Init.Data.Array.Extract

namespace ChaCha20Poly1305.Proofs.Decrypt

open X86 X86.Machine Prelude ChaCha20Poly1305.Spec.Program

private theorem prefixPush {bs : ByteArray} {n : Nat} (h : n < bs.size) :
    (bs.extract 0 n).push bs[n] = bs.extract 0 (n+1) := by
  apply ByteArray.ext
  simp only [ByteArray.data_push, ByteArray.data_extract]
  rw [Array.extract_succ_right (by omega) (show n < bs.data.size from h)]
  rfl

theorem readRegion_of_bytes {t : RamState} {r : MemoryRegion} {bs : ByteArray}
    (h : r.HasBytes t.external bs) : readRegion t r = .ok bs := by
  obtain ⟨hs,hb⟩ := h
  let step (acc : ByteArray) (i : Nat) : Except Fault ByteArray :=
    match t.external[BitVec.ofNat 64 (r.start+i)]? with
    | some b => .ok (acc.push b)
    | none => .error (.unmappedMemory (BitVec.ofNat 64 (r.start+i)))
  have aux (n : Nat) (hn : n ≤ bs.size) :
      (List.range n).foldlM step ByteArray.empty = .ok (bs.extract 0 n) := by
    induction n with
    | zero => simp [ByteArray.extract_same]; rfl
    | succ n ih =>
      rw [List.range_succ, List.foldlM_append, ih (by omega)]
      simp only [List.foldlM_cons, List.foldlM_nil]
      dsimp [step, Bind.bind, Except.bind]
      rw [hb ⟨n, by omega⟩]
      exact congrArg Except.ok (prefixPush (by omega))
  change (List.range r.size).foldlM step ByteArray.empty = .ok bs
  change bs.size = r.size at hs
  rw [← hs,aux _ (Nat.le_refl _),ByteArray.extract_zero_size]

theorem output_region {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hc : ValidCall decrypt s [key,nonce,aad,msg]) :
    outputRegion decrypt s = registerRegion s .r9 (msg.size - 16) := by
  have h := Short.message_length hc
  simp [outputRegion,hasRoom,bufferBytes,decrypt,Routine.inPlace] at ⊢
  exact congrArg (fun n => registerRegion s .r9 (n-16)) h

end ChaCha20Poly1305.Proofs.Decrypt
