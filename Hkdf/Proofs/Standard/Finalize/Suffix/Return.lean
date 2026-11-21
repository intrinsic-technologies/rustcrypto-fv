import Hkdf.Proofs.Standard.Finalize.Suffix.Return.Payload
import Hkdf.Proofs.Standard.Finalize.Suffix.Return.Copy
import Hkdf.Proofs.Standard.Finalize.Suffix.Return.Epilogue
import Hkdf.Proofs.Standard.Finalize.Suffix.Rekeyed

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Return

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256

private theorem hmacAt_of_rekeyed_copy {s t : RamState} {src dest : BitVec 64} {key : ByteArray}
    (packed : RekeyedAt s src key)
    (copied : ∀ i < 80, t.external[dest + 64 + BitVec.ofNat 64 i]? =
      s.external[src + BitVec.ofNat 64 i]?)
    (tailLength : t.external[dest + 63]? = some 0) :
    HmacAt t dest key ByteArray.empty := by
  have field (offset i : Nat) (within : offset + i < 80) :
      t.external[dest + 64 + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[src + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using copied (offset + i) within
  have counter (offset : Nat) (within : offset + 8 ≤ 80)
      (word : loadBytes s.external (src + BitVec.ofNat 64 offset) 8 = .ok 1) :
      loadBytes t.external (dest + 64 + BitVec.ofNat 64 offset) 8 = .ok 1 := by
    apply Bytes.loadBytes64
    intro i hi
    exact (field offset i (by omega)).trans (Memory.bytes_of_loadBytes64 word i hi)
  refine ⟨?_, ?_, ?_⟩
  · rw [ByteArray.append_empty]
    have size := HMAC.xorPad_keyBlock_size key 0x36
    apply (StreamAt.single_block_iff size).2
    refine ⟨?_, tailLength, ?_⟩
    · rw [← compressBlocks_single _ _ size]
      exact hashState_of_bytes packed.innerHash (fun i hi ↦ copied i (by omega))
    · simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
        counter 32 (by decide) packed.innerBlocks
  · apply hashState_of_bytes packed.outerHash
    intro i hi
    have h := field 40 i (by omega)
    change t.external[dest + 64 + 40 + BitVec.ofNat 64 i]? = _ at h
    rw [show dest + 64 + 40 = dest + 104 by bv_omega] at h
    exact h
  · simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
      counter 72 (by decide) packed.outerBlocks

theorem run [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {digest : ByteArray} (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10e240)
    (digestBytes : (MemoryRegion.mk (stackPtr initial - 192).toNat 32).HasBytes s.external digest)
    (packed : RekeyedAt s (stackPtr initial - 120) digest) :
    ∃ t, CalleeResult initial t boundary 176 1264 ∧
      (registerRegion initial .rdi 32).HasBytes t.external digest ∧
      HmacAt t (initial.regValue .rdi + 32) digest ByteArray.empty := by
  have code := programText_slice (programLoaded_codeIn state.running.loaded)
    0xe240 Stores.bytes (by decide +kernel) (by decide +kernel)
  have outside : ∀ ip : Nat, 0x10e240 ≤ ip → ip ≤ 0x10e273 →
      (BitVec.ofNat 64 ip) ≠ boundary.rip := by
    intro ip low high
    apply boundary_ne_program pre.outerBoundary
    have inside := inProgram_of_textOffset (ip - 0x100000) (by omega)
    have addr : Extracted.textAddress + BitVec.ofNat 64 (ip - 0x100000) =
        BitVec.ofNat 64 ip := by
      calc
        _ = BitVec.ofNat 64 (0x100000 + (ip - 0x100000)) :=
          (BitVec.ofNat_add (n := 64) 0x100000 (ip - 0x100000)).symm
        _ = BitVec.ofNat 64 ip := congrArg (BitVec.ofNat 64) (by omega)
    exact addr ▸ inside
  obtain ⟨fuel, u, execution, ready, _, effect⟩ := Stores.run boundary outside s
    (supportedMachine_readyToStep state.running.machine) code (stores_pre pre state rip)
  have stateU := stores_state pre state execution ready effect
  have bytesU := stores_bytes pre state effect digestBytes
  have stackU := stores_stack pre state effect (depth := 120) (length := 80)
    (by decide) (by decide)
  have tailU := stores_tailLength pre state effect
  obtain ⟨v, stateV, ripV, preserved, copied⟩ := copy pre stateU effect.rip
  obtain ⟨t, result, memory⟩ := epilogue pre stateV ripV
  refine ⟨t, result, ⟨bytesU.1, ?_⟩, hmacAt_of_rekeyed_copy packed ?_ ?_⟩
  · intro i
    have bound : i.val < 32 := by have h := bytesU.1; change digest.size = 32 at h; omega
    have same := preserved i.val (by omega)
    have original := bytesU.2 i
    simpa only [memory, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using same.trans (by
        simpa only [registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
          BitVec.setWidth_eq] using original)
  · intro i hi
    rw [memory, show initial.regValue .rdi + 32 + 64 = initial.regValue .rdi + 96 by bv_omega]
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
      (copied i hi).trans (stackU i hi)
  · rw [memory, show initial.regValue .rdi + 32 + 63 = initial.regValue .rdi + 95 by bv_omega]
    exact (preserved 95 (by decide)).trans tailU

end Hkdf.Proofs.Standard.Finalize.Suffix.Return
