import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Invariants
import Sha2.Proofs.Common.SHA512.Compression.InputWords
import Sha2.Proofs.Common.SHA512.Mathematics.CompressionState
import Sha2.Proofs.Wrapper.Call
import Sha2.Proofs.FIPS180.SHA512

set_option autoImplicit false
namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions Sha2.Proofs.NIST Prelude X86 X86.Machine X86.UserProcess X86Proofs
theorem input_words_of_bytes {s : RamState} {block : ByteArray}
    (bytes : (registerRegion s .rsi 128).HasBytes s.external block)
    (i : Nat) (bound : i < 16) :
    bswap64 ((contextOfRam s).inputWords (8*i)) = word (Encoding.octetsToBits block) i :=
  input_memLoad_word bytes i bound

open Sha2.Spec.Program Sha2.Proofs.Program

theorem round_constant_bytes : ∀ i : Fin 80, ∀ j : Fin 8,
    Extracted.rodataBytes.toList[8 * i.val + j.val]'(by
      rw [chunked_toList_length]
      change 8 * i.val + j.val < 680
      omega) = storedByte (SHA512.roundConstants[i.val]!).toBitVec j.val := by
  simp only [Prelude.Bytes.Chunked.toList, Prelude.Bytes.Chunked.toListFrom,
    List.getElem_map, List.getElem_range', Nat.zero_add]
  decide +kernel

theorem constants_of_loaded {s : RamState} (loaded : ProgramLoaded s)
    (i : Nat) (bound : i < 80) :
    (contextOfRam s).constants (8 * i) = (SHA512.roundConstants[i]!).toBitVec := by
  have stored : Bytes s.external (0x200000 + BitVec.ofNat 64 (8 * i)) 8
      (storedByte (SHA512.roundConstants[i]!).toBitVec) := by
    intro j hj
    have byte := Sha2.Proofs.Wrapper.rodata_loaded loaded (offset := 8 * i + j) (by omega)
    rw [round_constant_bytes ⟨i, bound⟩ ⟨j, hj⟩] at byte
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.rodataAddress, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using byte
  exact stored.memLoad (by decide) (by decide)

theorem constants_eq_K_of_loaded {s : RamState} (loaded : ProgramLoaded s)
    (i : Nat) (bound : i < 80) :
    (contextOfRam s).constants (8 * i) = Standards.NIST.SHA2.SHA512.K[i] := by
  rw [Sha2.Proofs.FIPS180.SHA512Bridge.K_getElem i bound]
  exact constants_of_loaded loaded i bound


theorem compress_of_invariant57 {hash : Array UInt64} {block : Array Bool} {values : Values}
    (final : invariant57 (BitVecState.ofState (SHA512.State.ofArray hash)) block values) :
    hashState values = BitVecState.ofState (SHA512.State.ofArray (SHA512.compress hash block)) := by
  let h := BitVecState.ofState (SHA512.State.ofArray hash)
  change invariant57 h block values at final
  rw [compress_bitVecState, rounds_words]
  change hashState values =
    ⟨h.a + a h block 80, h.b + a h block 79, h.c + a h block 78, h.d + a h block 77,
      h.e + e h block 80, h.f + e h block 79, h.g + e h block 78, h.h + e h block 77⟩
  rcases final with ⟨h0, h1, h3, h8, h9, h10, h11, h13⟩
  simp only [hashState, h0, h1, h3, h8, h9, h10, h11, h13]

theorem hashState_correct
    (run_correct : ∀ (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values),
      (∀ i, i < 16 → bswap64 (context.inputWords (8 * i)) = word block i) →
      (∀ i, i < 80 → context.constants (8 * i) = (SHA512.roundConstants[i]!).toBitVec) →
      invariant00 h block s → invariant57 h block (run context Program.operations s))
    {initial : RamState} {hash : Array UInt64} {block : ByteArray}
    (loaded : ProgramLoaded initial) (registers : RegistersAt initial hash)
    (bytes : (registerRegion initial .rsi 128).HasBytes initial.external block) :
    hashState (run (contextOfRam initial) Program.operations (ofRam initial)) =
      BitVecState.ofState (SHA512.State.ofArray (SHA512.compress hash (Encoding.octetsToBits block))) := by
  apply compress_of_invariant57
  exact run_correct _ _ _ _ (input_words_of_bytes bytes) (constants_of_loaded loaded)
    (invariant00_of_hashState _ (hashState_ofRam registers))

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
