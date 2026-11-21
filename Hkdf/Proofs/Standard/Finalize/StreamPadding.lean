import Hkdf.Proofs.Standard.Finalize.Hmac
import Hkdf.Proofs.Common.StreamPadding.Run

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.StreamPadding

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.StreamPadding (Variant base writes)
open Hkdf.Proofs.Common.StreamPadding.Execution
open Hkdf.Proofs.Common.SHA256

theorem preserved [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (rsp : stackPtr s = stackPtr initial - 408)
    (frame : MemoryWriteFrame s t (writes .hmac (stackPtr s)))
    (offset size : Nat) (low : 168 ≤ offset) (high : offset + size ≤ 416) :
    (Component.mem (stackPtr s + BitVec.ofNat 64 offset) size).Agrees s t := by
  have localRSP : stackPtr s = base .hmac initial := rsp
  have bounds := local_bounds .hmac pre localRSP
  have address (n : Nat) (hn : n ≤ 416) :
      (stackPtr s + BitVec.ofNat 64 n).toNat = (stackPtr s).toNat + n := by
    rw [localRSP, local_toNat .hmac pre n hn, base_toNat .hmac pre]
  have below : (stackPtr s - 344).toNat = (stackPtr s).toNat - 344 := by
    change (stackPtr s - BitVec.ofNat 64 344).toNat = _
    rw [localRSP, below_toNat .hmac pre 344 (by decide), base_toNat .hmac pre]
    simp only [Variant.frame]
    omega
  apply frame_agrees_of_disjoint frame
  · rw [address offset (by omega)]
    simp only [Variant.frame] at bounds
    omega
  · intro region member a contains written
    have cases : region = ⟨(stackPtr s - 344).toNat, 344⟩ ∨
        region = ⟨(stackPtr s + 72).toNat, 64⟩ ∨
        region = ⟨(stackPtr s + 136).toNat, 32⟩ ∨
        region = ⟨(stackPtr s + 8).toNat, 64⟩ := by
      simpa only [writes, Variant.tail, Variant.hash, Variant.scratch,
        Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false,
        BitVec.ofNat_eq_ofNat] using member
    change (stackPtr s + BitVec.ofNat 64 offset).toNat ≤ a ∧
      a < (stackPtr s + BitVec.ofNat 64 offset).toNat + size at contains
    rw [address offset (by omega)] at contains
    rcases cases with rfl | rfl | rfl | rfl
    · change (stackPtr s - 344).toNat ≤ a ∧ a < (stackPtr s - 344).toNat + 344 at written
      rw [below] at written
      omega
    · change (stackPtr s + BitVec.ofNat 64 72).toNat ≤ a ∧
        a < (stackPtr s + BitVec.ofNat 64 72).toNat + 64 at written
      rw [address 72 (by decide)] at written
      omega
    · change (stackPtr s + BitVec.ofNat 64 136).toNat ≤ a ∧
        a < (stackPtr s + BitVec.ofNat 64 136).toNat + 32 at written
      rw [address 136 (by decide)] at written
      omega
    · change (stackPtr s + BitVec.ofNat 64 8).toNat ≤ a ∧
        a < (stackPtr s + BitVec.ofNat 64 8).toNat + 64 at written
      rw [address 8 (by decide)] at written
      omega

theorem run [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {key message : ByteArray}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (hmac : HmacAt initial (initial.regValue .rsi) key message)
    (size : 64 + message.size < 2^61) :
    ∃ t, Running initial boundary
        #v[registerRegion initial .rdi 176, Stack.region initial 1264] t ∧
      t.RIP = 0x10df0d ∧ stackPtr t = stackPtr initial - 408 ∧
      t.regValue .rbx = initial.regValue .rdi ∧
      HashStateAt t (stackPtr initial - 272)
        (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash
          (bytePadding (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message))) ∧
      HashStateAt t (stackPtr initial - 232)
        (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash
          (HMAC.xorPad (HMAC.keyBlock key) 0x5c)) ∧
      loadBytes t.external (stackPtr initial - 200) 8 = .ok 1 ∧
      (∀ i < 48, t.external[stackPtr initial - 40 + BitVec.ofNat 64 i]? =
        (Hmac.savedMemory initial)[stackPtr initial - 40 + BitVec.ofNat 64 i]?) ∧
      t.regValue .rbp = initial.regValue .rbp ∧
      t.MXCSR = initial.MXCSR ∧ t.FP87_Control = initial.FP87_Control := by
  obtain ⟨s, running, rip, rsp, rbx, copied, saved, rbp, mxcsr, fcw⟩ :=
    Hmac.copy_input pre hmac
  have stream : StreamAt s (stackPtr s + 72)
      (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message) := by
    rw [rsp, show stackPtr initial - 408 + 72 = stackPtr initial - 336 by bv_omega]
    exact copied.inner
  obtain ⟨t, result⟩ := Common.StreamPadding.run .hmac pre running rsp rip stream
    (by simpa only [ByteArray.size_append, HMAC.xorPad_keyBlock_size] using size)
  have localAddress (offset : Nat) (bound : offset ≤ 408) :
      stackPtr s + BitVec.ofNat 64 offset =
        stackPtr initial - BitVec.ofNat 64 (408 - offset) := by
    rw [rsp]
    exact local_address .hmac pre offset bound
  have outerBytes := preserved pre rsp result.frame 176 40 (by decide) (by decide)
  have outerHash : HashStateAt t (stackPtr initial - 232)
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash
        (HMAC.xorPad (HMAC.keyBlock key) 0x5c)) := by
    apply Hkdf.Proofs.Common.hashState_of_bytes copied.outerHash
    intro i hi
    have same := outerBytes i (by omega)
    rw [localAddress 176 (by decide)] at same
    have source : stackPtr initial - 336 + 104 = stackPtr initial - 232 := by bv_omega
    rw [source]
    simpa only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] using same
  have outerCount : loadBytes t.external (stackPtr initial - 200) 8 = .ok 1 := by
    have same : (Component.mem (stackPtr initial - 200) 8).Agrees s t := by
      simpa only [localAddress 208 (by decide), Nat.reduceSub, BitVec.ofNat_eq_ofNat] using
        preserved pre rsp result.frame 208 8 (by decide) (by decide)
    rw [agrees_loadBytes same]
    have source : stackPtr initial - 336 + 136 = stackPtr initial - 200 := by bv_omega
    simpa only [source] using copied.outerBlocks
  have sameSaved : (Component.mem (stackPtr initial - 40) 48).Agrees s t := by
    simpa only [localAddress 368 (by decide), Nat.reduceSub, BitVec.ofNat_eq_ofNat] using
      preserved pre rsp result.frame 368 48 (by decide) (by decide)
  refine ⟨t, result.running, result.rip, result.rsp.trans rsp, result.rbx.trans rbx,
    ?_, outerHash, outerCount, ?_, result.rbp.trans rbp, result.mxcsr.trans mxcsr,
    result.fcw.trans fcw⟩
  · simpa only [show BitVec.ofNat 64 Variant.hmac.hash = (136 : BitVec 64) from rfl,
      rsp, show stackPtr initial - 408 + 136 = stackPtr initial - 272 by bv_omega]
      using result.hashWords
  · intro i hi
    exact (sameSaved i hi).trans (saved i hi)

end Hkdf.Proofs.Standard.Finalize.StreamPadding
