import Hkdf.Proofs.NewExpand.Extract.Update.Bulk.Compress
import Hkdf.Proofs.NewExpand.Extract.Update.Bulk.Prepare
import Hkdf.Proofs.NewExpand.Extract.Update.Message

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Update

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.SHA256
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem fullBlockLength (v : BitVec 64) (bound : v.toNat < 2^32) :
    v &&& 0x7fffffffffffffc0 = BitVec.ofNat 64 (64 * (v.toNat / 64)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have div := Nat.and_div_two_pow (a := v.toNat) (b := 0x7fffffffffffffc0) (n := 6)
  change (v.toNat &&& 0x7fffffffffffffc0) / 64 = (v.toNat / 64) &&& (2^57 - 1) at div
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)] at div
  have rem := Nat.and_mod_two_pow (a := v.toNat) (b := 0x7fffffffffffffc0) (n := 6)
  change (v.toNat &&& 0x7fffffffffffffc0) % 64 = (v.toNat % 64) &&& 0 at rem
  rw [Nat.and_zero] at rem
  change v.toNat &&& 0x7fffffffffffffc0 = (64 * (v.toNat / 64)) % 2^64
  omega

theorem bulk [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray}
    (pre : ExtractPre initial boundary salt ikm) (frame : Frame initial s boundary)
    (rip : s.RIP = 0x10fc84) (ptr : s.regValue .r15 = initial.regValue .rcx)
    (len : s.regValue .r14 = initial.regValue .r8) (hash : s.regValue .rax = base initial + 184)
    (hmac : HmacAt s (base initial + 120) (salt.getD (RFC5869.defaultSalt .sha256)) ByteArray.empty) :
    ∃ t, Frame initial t boundary ∧ t.RIP = 0x10fcb2 ∧
      t.regValue .r12 = initial.regValue .rcx + BitVec.ofNat 64 (64 * (ikm.size / 64)) ∧
      t.regValue .r14 = BitVec.ofNat 64 (ikm.size % 64) ∧
      HashFields t (base initial + 120) (salt.getD (RFC5869.defaultSalt .sha256)) ikm := by
  have slot : stackPtr s + 216 = stackPtr initial - BitVec.ofNat 64 240 := by
    rw [frame.rsp, base]
    bv_omega
  have writable : MemWritable s (stackPtr s + 216) 8 := by
    rw [slot]
    exact stack_writable8 pre.call.stack pre.call.stackAvoid frame.allocated (by decide) (by decide)
  have apart : RangeApart (stackPtr s + 216) 8 0x10fc9f 14 := by
    rw [slot]
    exact stack_codeApart pre.call.stack (stackAvoid pre _ (by simp)) (offset := 240)
      (codeOffset := 0xfc9f) (by decide) (by decide) (by decide)
  obtain ⟨u, run, ready, atCall, dest, source, blocks, residual, tailPtr, stored, agrees⟩ :=
    prepareBulk (supportedMachine_readyToStep frame.machine) frame.loaded rip pre.call.outerBoundary
      writable apart
  have unchanged (off : BitVec 64) (size : Nat) (away : OffsetsApart 216 8 off size)
      (small : 8 + size < 2^64) : (Component.mem (base initial + off) size).Agrees s u := by
    intro i hi
    apply agrees.byte
    intro comp member covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j, hj, eq⟩ := covered
    rw [frame.rsp] at eq
    exact OffsetsApart.ne away (base initial) hj hi small eq.symm
  have running := frame.toRunning.of_agrees run ready agrees (by
    intro comp member a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    rw [slot] at covered
    exact ⟨_, by simp, stackRegion_contains_sub pre.call.stack.2.2.1
      (offset := 240) (by decide) (by decide) covered⟩) (stackAvoid pre) (by simp)
  have saved := unchanged 408 56 (by unfold OffsetsApart; decide +kernel) (by decide)
  rw [show base initial + 408 = stackPtr initial - 48 from by unfold base; bv_omega] at saved
  have frameU : Frame initial u boundary :=
    ⟨running, frame.toSaved.of_agrees saved (agrees.mxcsr (by simp)) (agrees.fcw (by simp)),
      (agrees.read (n := 64) (r := 4) (by simp)).trans frame.rsp,
      (agrees_memLoad (unchanged 80 8 (by unfold OffsetsApart; decide +kernel) (by decide))).trans
        frame.outputPtr⟩
  have sizeEq : (s.regValue .r14).toNat = ikm.size := len ▸ pre.ikmLength
  have count : u.regValue .rdx = BitVec.ofNat 64 (ikm.size / 64) := by
    rw [blocks, ← sizeEq]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.reducePow, BitVec.toNat_ofNat]
    have := (s.regValue .r14).isLt
    omega
  have inputBound := pre.ikmBytes.1
  change (initial.regValue .rcx).toNat + ikm.size < 2^32 at inputBound
  have full := fullBlockLength (s.regValue .r14) (by omega)
  have tailLen : u.regValue .r14 = BitVec.ofNat 64 (ikm.size % 64) := by
    rw [residual, ← sizeEq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    change (s.regValue .r14).toNat &&& (2^6 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
    omega
  let key := salt.getD (RFC5869.defaultSalt .sha256)
  let inner := compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (HMAC.xorPad (HMAC.keyBlock key) 0x36)
  have innerAt : HashStateAt s (base initial + 184) inner := by
    simpa only [inner, key, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, ByteArray.append_empty] using hmac.inner.hashWords
  have words := hashState_of_bytes innerAt
    (unchanged 184 32 (by unfold OffsetsApart; decide +kernel) (by decide))
  obtain ⟨t, frameT, ripT, abi, finalWords, same⟩ :=
    compress pre frameU atCall (dest.trans hash) (source.trans ptr) count words
  have subrange (offset size : Nat) (within : offset + size ≤ 48) :
      (Component.mem (base initial + 216 + BitVec.ofNat 64 offset) size).Agrees u t := by
    intro i hi
    simpa only [BitVec.add_assoc, BitVec.ofNat_add] using same (offset + i) (by omega)
  have innerBlocks : loadBytes s.external (base initial + 216) 8 = .ok 1 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, ByteArray.append_empty, HMAC.xorPad_keyBlock_size,
      Nat.reduceDiv, BitVec.ofNat_eq_ofNat] using hmac.inner.blocks
  have kept := stack_readable pre.call.stack running.allocated (offset := 240) (len := 8)
    (by decide) (by decide)
  rw [← slot, frame.rsp] at kept
  rw [frame.rsp] at stored
  have counter := Bytes.of_memLoad (n := 64) kept.mem
  rw [stored, Memory.memLoad_of_loadBytes64 innerBlocks, count] at counter
  have counterU := counter.loadBytes64
  have counterT := (agrees_loadBytes (subrange 0 8 (by decide))).trans (by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using counterU)
  have outerAt : HashStateAt s (base initial + 224) (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash
      (HMAC.xorPad (HMAC.keyBlock key) 0x5c)) := by
    simpa only [key, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hmac.outerHash
  have outerWords := hashState_of_bytes outerAt
    (unchanged 224 32 (by unfold OffsetsApart; decide +kernel) (by decide))
  have outerCount := (agrees_loadBytes
    (unchanged 256 8 (by unfold OffsetsApart; decide +kernel) (by decide))).trans (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hmac.outerBlocks)
  refine ⟨t, frameT, ripT, ?_, (abi.1 .r14 (by simp)).trans tailLen, ?_⟩
  · rw [abi.1 .r12 (by simp), tailPtr, ptr, full, sizeEq]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using finalWords
    · simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.add_zero,
        BitVec.ofNat_add] using counterT
    · have outerSame : (Component.mem (base initial + 224) 32).Agrees u t := by
        simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
          subrange 8 32 (by decide)
      simpa only [key, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using
        hashState_of_bytes outerWords outerSame
    · have last := agrees_loadBytes (subrange 40 8 (by decide))
      simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
        last.trans (by simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using outerCount)

end Hkdf.Proofs.NewExpand.Extract.Update
