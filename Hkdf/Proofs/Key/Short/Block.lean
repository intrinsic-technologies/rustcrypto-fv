import Hkdf.Proofs.Key.Memory

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Short

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.HMAC

theorem copied_block [Bindings] {initial u t : RamState}
    {boundary : ReturnBoundary} {key : ByteArray}
    (ctx : Context initial boundary key) (state : State initial boundary u)
    (fits : key.size ≤ 64)
    (output : u.regValue .rdi = blockAddress initial)
    (input : u.regValue .rsi = initial.regValue .rsi)
    (rsp : stackPtr u = stackPtr initial - 384)
    (zeros : (⟨(blockAddress initial).toNat, 64⟩ : MemoryRegion).HasBytes
      u.external ⟨Array.replicate 64 0⟩)
    (result : CalleeResult u t boundary key.size 0)
    (copied : ∀ i < key.size,
      t.external[u.regValue .rdi + BitVec.ofNat 64 i]? =
        u.external[u.regValue .rsi + BitVec.ofNat 64 i]?) :
    (⟨(blockAddress initial).toNat, 64⟩ : MemoryRegion).HasBytes t.external (keyBlock key) := by
  have bounds := stack_bounds ctx.toCalleePre
  change 720 ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2^32 at bounds
  have blockNat : (blockAddress initial).toNat = (stackPtr initial).toNat - 376 :=
    stack_sub_toNat ctx.toCalleePre (by decide)
  have rspNat : (stackPtr u).toNat = (stackPtr initial).toNat - 384 := by
    rw [rsp]
    exact stack_sub_toNat ctx.toCalleePre (by decide)
  have source : (registerRegion initial .rsi key.size).HasBytes u.external key := by
    apply Hkdf.Proofs.Common.CallFrame.frame_hasBytes state.frame ?_ (by
      have bound : (initial.regValue .rsi).toNat + key.size < 2^32 := ctx.inputBounded
      change (initial.regValue .rsi).toNat + key.size ≤ 2^64
      omega) ctx.bytes
    intro region member
    have cases : region = registerRegion initial .rdi 64 ∨
        region = Stack.region initial stackBytes := by simpa [writeRegions] using member
    rcases cases with rfl | rfl
    · exact ctx.separation ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
    · exact ctx.separation ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)
  have normalized : keyBlock key = key ++ ⟨Array.replicate (64 - key.size) 0⟩ := by
    simp only [keyBlock, show ¬64 < key.size by omega, ↓reduceIte]
  refine ⟨keyBlock_size key, ?_⟩
  intro index
  obtain ⟨i, hIndex⟩ := index
  have hi : i < 64 := by simpa only [keyBlock_size] using hIndex
  have address : BitVec.ofNat 64 ((blockAddress initial).toNat + i) =
      blockAddress initial + BitVec.ofNat 64 i := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have addressNat : (blockAddress initial + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - 376 + i := by
    rw [BitVec.toNat_add, blockNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [address]
  simp only [normalized, ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  change t.external[blockAddress initial + BitVec.ofNat 64 i]? =
    some ((key.data ++ Array.replicate (64 - key.size) 0)[i]'(by
      simp only [Array.size_append, Array.size_replicate]
      change i < key.size + (64 - key.size)
      omega))
  by_cases inside : i < key.size
  · rw [Array.getElem_append_left inside]
    have byte := copied i inside
    rw [output, input] at byte
    have inputByte := source.2 ⟨i, inside⟩
    exact byte.trans (by simpa only [registerRegion, BitVec.ofNat_add,
      BitVec.ofNat_toNat, BitVec.setWidth_eq, ByteArray.getElem_eq_getElem_data] using inputByte)
  · have outside : key.data.size ≤ i := by change key.size ≤ i; omega
    rw [Array.getElem_append_right outside, Array.getElem_replicate]
    rw [result.frame _ (by
      intro region member contains
      have cases : region = registerRegion u .rdi key.size ∨ region = Stack.region u 0 := by
        simpa using member
      rcases cases with rfl | rfl
      · change (u.regValue .rdi).toNat ≤ _ ∧
          _ < (u.regValue .rdi).toNat + key.size at contains
        rw [output, blockNat, addressNat] at contains
        omega
      · have high : (blockAddress initial + BitVec.ofNat 64 i).toNat <
            (stackPtr u).toNat + 8 := by
          simpa only [Hkdf.Proofs.Common.Machine.stack_region_end] using contains.2
        rw [addressNat, rspNat] at high
        omega)]
    have byte := zeros.2 ⟨i, by simpa only [ByteArray.size, Array.size_replicate]⟩
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      ByteArray.getElem_eq_getElem_data, Array.getElem_replicate] using byte

end Hkdf.Proofs.Key.Short
