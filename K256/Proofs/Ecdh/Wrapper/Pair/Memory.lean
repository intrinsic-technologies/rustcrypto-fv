import K256.Proofs.Ecdh.Wrapper.State
import K256.Proofs.Ecdh.CallSite
import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Negate.Machine
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Ecdh.Wrapper.Pair

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR
  Generate.Generator.Multiply Generate.Generator.Multiply.Prepare.Bases.Negate

private theorem copiedScalar (m : Ram) (sp : BitVec 64) (w : Vector (BitVec 64) 4) :
    let pushed := memStore (storeFour m (sp + 464) w) (sp - 8) (0x1018b0 : BitVec 64)
    WordsAt (memCopy pushed (sp + 192) (sp + 344) 152) (sp + 312) 64 w := by
  dsimp only
  intro i hi
  have dst : wordAddr (sp + 312) 64 i = (sp + 192) + BitVec.ofNat 64 (120 + 8 * i) := by
    simp only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, ← BitVec.add_assoc]
    congr 1
    bv_omega
  rw [dst, Sec1.Parser.Result.memLoad_memCopy _ _ _ (by decide) (by change 120 + 8 * i + 8 ≤ 152; omega)]
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases casesI with rfl | rfl | rfl | rfl <;>
    simp only [storeFour, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd] <;> segment_words [] <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem recordMemory {s : RamState} {secret key : ByteArray} {m : Ram} {d : Nat} {peer : Projective}
    (call : ValidCall ecdhDiffieHellman s [secret, key]) (memory : Scalar.Memory s m)
    (source : peer.Stored m (localSp s + 344)) :
    let sp := localSp s
    let staged := storeFour m (sp + 464) (scalarWords d)
    let pushed := memStore staged (sp - 8) (0x1018b0 : BitVec 64)
    let result := memCopy pushed (sp + 192) (sp + 344) 152
    StoreOk Extracted.programImage staged (sp - 8) 8 0x1018ad 3 ∧
      Scalar.Memory s pushed ∧ Scalar.Memory s result ∧ memLoad result (sp - 8) 64 = 0x1018b0 ∧
      ScalarAt s result 312 d ∧ peer.Stored result (sp + 192) := by
  dsimp only
  let sp := localSp s
  let staged := storeFour m (sp + 464) (scalarWords d)
  let pushed := memStore staged (sp - 8) (0x1018b0 : BitVec 64)
  let result := memCopy pushed (sp + 192) (sp + 344) 152
  obtain ⟨room, low, top⟩ := Scalar.stack_geometry call
  have offset (k : Nat) (h : k ≤ 512) : (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
    change (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k
    have small : sp.toNat + k < 2 ^ 64 := by dsimp only [sp]; omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt small]
  have o192 := offset 192 (by decide)
  have o344 := offset 344 (by decide)
  have o464 := offset 464 (by decide)
  have slot : sp - 8 = s.regValue .rsp - 6160 := by unfold sp localSp; bv_omega
  have oSlot : (sp - 8).toNat = (stackPtr s).toNat - 6160 := by rw [slot]; exact Common.stackOffset (off := 6160) call.stackAvailable (by decide)
  have writes : RamWriteFrame m staged [⟨(sp + 464).toNat, 32⟩] := by
    have inside (k : Nat) (hk : 464 ≤ k) (hl : k ≤ 488) :
        InRegions [⟨(sp + 464).toNat, 32⟩] (sp + BitVec.ofNat 64 k) 8 := by
      refine ⟨_, List.mem_singleton_self _, ?_, ?_, ?_⟩
      all_goals try dsimp only
      all_goals rw [offset k (by omega)]
      all_goals change (sp + 464).toNat = sp.toNat + 464 at o464
      all_goals dsimp only [sp] at * <;> omega
    simp only [staged, storeFour, BitVec.add_assoc, BitVec.reduceAdd]
    have start := RamWriteFrame.refl m [MemoryRegion.mk (sp + 464).toNat 32]
    let w := scalarWords d
    have fr0 := start.memStore (a := sp + 464) w[0] (inside 464 (by decide) (by decide))
    have fr1 := fr0.memStore (a := sp + 472) w[1] (inside 472 (by decide) (by decide))
    have fr2 := fr1.memStore (a := sp + 480) w[2] (inside 480 (by decide) (by decide))
    have fr3 := fr2.memStore (a := sp + 488) w[3] (inside 488 (by decide) (by decide))
    exact fr3
  have bounds (k size : Nat) (hk : k ≤ 512) (hs : size ≤ 152) :
      ∀ r ∈ [MemoryRegion.mk (sp + BitVec.ofNat 64 k).toNat size],
        (stackPtr s).toNat - 10088 ≤ r.start ∧ r.start + r.size ≤ (stackPtr s).toNat - 48 := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    simp only [offset k hk, sp]
    omega
  have stage := memory.advance call writes (bounds 464 32 (by decide) (by decide))
  obtain ⟨push, after, pushFrame, tag, apart⟩ := callSite call stage 6160 (by decide) (by decide)
    0x10185f bytes_l10185f 78 3 (fun x hx => Common.fnCode_subset_programImage x (code_l10185f x hx))
    (by decide) 0x1018b0
  change sp - 8 = s.regValue .rsp - BitVec.ofNat 64 6160 at slot
  rw [← slot] at push after pushFrame tag apart
  have frame : RamWriteFrame pushed result [⟨(sp + 192).toNat, 152⟩] := by
    apply Sec1.Wrapper.Copy.memCopy_frame (RamWriteFrame.refl _ _)
    exact ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _, by
      change (sp + 192).toNat = sp.toNat + 192 at o192
      dsimp only [sp] at *; omega⟩
  have peerStaged := source.of_frame writes (by
    refine ⟨?_, fun r hr => ?_⟩
    · change (sp + 344).toNat + 120 ≤ 2 ^ 64
      change (sp + 344).toNat = sp.toNat + 344 at o344
      dsimp only [sp] at *; omega
    · obtain rfl := List.mem_singleton.mp hr
      left
      change (sp + 344).toNat + 120 ≤ (sp + 464).toNat
      rw [show (sp + 344).toNat = _ from o344, show (sp + 464).toNat = _ from o464]
      omega)
  have peerPushed : peer.Stored pushed (sp + 344) :=
    peerStaged.of_frame pushFrame (by
      have eq : sp + 344 = s.regValue .rsp - 5808 := by unfold sp localSp; bv_omega
      rw [eq]
      exact apart 5808 120 (by decide) (by decide))
  refine ⟨push, after, after.advance call frame (bounds 192 152 (by decide) (by decide)), ?_, ?_, ?_⟩
  · refine (frame.memLoad_eq ?_).trans tag
    refine ⟨by change (sp - 8).toNat + 8 ≤ 2 ^ 64; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    left
    change (sp - 8).toNat + 8 ≤ (sp + 192).toNat
    change (sp + 192).toNat = sp.toNat + 192 at o192
    dsimp only [sp] at *; omega
  · exact copiedScalar m sp (scalarWords d)
  · change peer.Stored result (sp + 192)
    have srcAt : peer.Stored pushed ((sp + 344) + BitVec.ofNat 64 0) := by
      rw [BitVec.add_zero]
      exact peerPushed
    simpa only [BitVec.add_zero] using
      (Projective.Stored.memCopy (off := 0) (len := 152) (dst := sp + 192) (src := sp + 344)
        srcAt (by decide) (by decide))

end K256.Proofs.Ecdh.Wrapper.Pair
