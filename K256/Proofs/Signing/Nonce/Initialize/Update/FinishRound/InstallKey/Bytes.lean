import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.InstallKey.Memory
import K256.Proofs.Common.WordCopy
import K256.Proofs.Signing.UpdateV.Finalize.Memory

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2

private theorem copiedWords {m : Ram} {src dst call : BitVec 64} (ret : BitVec 64)
    (srcBound : src.toNat + 32 < 2^64) (dstBound : dst.toNat + 32 < 2^64)
    (callBound : call.toNat + 8 < 2^64)
    (separate : src.toNat + 32 ≤ dst.toNat ∨ dst.toNat + 32 ≤ src.toNat)
    (callApart : call.toNat + 8 ≤ dst.toNat ∨ dst.toNat + 32 ≤ call.toNat) :
    ∀ i < 4, memLoad (memStore (keyCopy m src dst) call ret) (wordAddr dst 64 i) 64 =
      memLoad m (wordAddr src 64 i) 64 := by
  have sa (k : BitVec 64) (h : k.toNat ≤ 24) : (src + k).toNat = src.toNat + k.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have da (k : BitVec 64) (h : k.toNat ≤ 24) : (dst + k).toNat = dst.toNat + k.toNat :=
    Nat.mod_eq_of_lt (by omega)
  intro i hi
  obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
  all_goals
    simp only [keyCopy, wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    simp (disch := first | decide | (apply RangeApart.of_toNat <;>
      simp (disch := decide) only [sa, da, BitVec.reduceToNat, Nat.reduceDiv] <;> omega))
      only [memLoad_memStore_same, memLoad_memStore_of_rangeApart]


theorem keyCallBytes {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (live : Live (keyAt second input) fr a m state)
    (digest : (⟨(digestPtr fr second).toNat, 32⟩ : MemoryRegion).HasBytes m (nextKey second input state)) :
    RamWriteFrame m (keyCallMemory m fr second input) (keyWrites fr) ∧
      StateAt (keyCallMemory m fr second input) fr.rdi ⟨nextKey second input state, state.value⟩ := by
  let src := digestPtr fr second
  let dst := fr.rdi
  let call := sp fr - 8
  have dep := env.depth
  have lim := env.limit
  have dataLim := env.dataLow
  have lo := env.low
  have apart := env.apart
  have lowNat : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [lo, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from dep)]
    rfl
  have stackNat : (sp fr).toNat = fr.rsp.toNat - 712 := by
    rw [sp, BitVec.toNat_sub_of_le (show (712 : BitVec 64) ≤ fr.rsp by exact Nat.le_trans (by decide) dep)]
    rfl
  have callNat : call.toNat = (sp fr).toNat - 8 := by
    apply BitVec.toNat_sub_of_le
    change 8 ≤ (sp fr).toNat
    omega
  have srcRange : fr.low.toNat ≤ src.toNat ∧ src.toNat + 32 ≤ fr.rsp.toNat := by
    cases second <;> simp only [src, digestPtr, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_add,
      BitVec.reduceToNat] <;> omega
  have dstLim : dst.toNat + 64 < 2^32 := dataLim
  have frame : RamWriteFrame m (keyCallMemory m fr second input) (keyWrites fr) := by
    have off (k : BitVec 64) (fit : k.toNat ≤ 24) : (fr.rdi + k).toNat = fr.rdi.toNat + k.toNat :=
      Nat.mod_eq_of_lt (by omega)
    unfold keyCallMemory keyCopy
    apply RamWriteFrame.memStore
    · repeat' apply RamWriteFrame.memStore
      · exact RamWriteFrame.refl _ _
      all_goals
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
        simp (disch := decide) only [InRegion, Nat.reduceDiv, off, BitVec.reduceToNat]
        omega
    · exact ⟨_, .head _, Nat.le_refl _, Nat.le_refl _, by change call.toNat + 8 ≤ 2^64; omega⟩
  refine ⟨frame, ?_, ?_⟩
  · have size : (nextKey second input state).size = 32 := digest.1
    have rd := (env.writable.readable.of_frame live.writes).of_frame frame
    have words := copiedWords (m := m) (src := src) (dst := dst) (call := call) (valueReturn second input)
      (by omega) (by omega) (by omega) (by dsimp only [dst]; omega) (by dsimp only [dst]; omega)
    rw [← size]
    apply Common.hasBytes_of_word_copy (n := 4) digest size (rd.sub (Nat.le_refl _) (by omega))
    simpa only [keyCallMemory, src, dst, call, BitVec.ofNat_toNat, BitVec.setWidth_eq] using words
  · have pos : (fr.rdi + 32).toNat = fr.rdi.toNat + 32 := Nat.mod_eq_of_lt (by change fr.rdi.toNat + 32 < 2^64; omega)
    change (⟨fr.rdi.toNat + 32,32⟩ : MemoryRegion).HasBytes _ state.value
    rw [← pos]
    apply UpdateV.Finalize.bytesAfter frame _ (by simpa only [pos] using live.bytes.value)
    refine ⟨by rw [pos]; omega, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | h
    · change (fr.rdi + 32).toNat + 32 ≤ call.toNat ∨ call.toNat + 8 ≤ (fr.rdi + 32).toNat
      rw [pos]
      omega
    · obtain rfl := List.mem_singleton.mp h
      exact Or.inr (Nat.le_of_eq pos.symm)

end K256.Proofs.Signing.Nonce.Initialize.Update
