import K256.Proofs.Ecdh.Wrapper.Tables.Initialize

namespace K256.Proofs.Ecdh.Wrapper.Tables

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

def writes (sp : BitVec 64) : List MemoryRegion :=
  [⟨sp.toNat - 8, 8⟩, ⟨sp.toNat + 344, 5760⟩]

theorem tableOffset {sp : BitVec 64} (low : sp.toNat + 6104 < 2^64)
    {k : Nat} (hk : k ≤ 6104) : (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

private theorem inside {sp : BitVec 64} {k n : Nat} (low : sp.toNat + 6104 < 2^64)
    (lo : 344 ≤ k) (hi : k + n ≤ 6104) : InRegions (writes sp) (sp + BitVec.ofNat 64 k) n := by
  refine ⟨_, List.Mem.tail _ (.head _), ?_⟩
  change sp.toNat + 344 ≤ _ ∧ _ ≤ sp.toNat + 344 + 5760 ∧ _ ≤ 2^64
  rw [tableOffset (by omega : sp.toNat + 6104 < 2^64) (by omega : k ≤ 6104)]
  omega

theorem identityFrame {sp : BitVec 64} {m : Ram} (low : sp.toNat + 6104 < 2^64)
    (i : Nat) (count : i ≤ 16) : RamWriteFrame m (identityCopies m sp i) (writes sp) := by
  induction i with
  | zero => exact .refl _ _
  | succ i ih =>
    exact Sec1.Wrapper.Copy.memCopy_frame (ih (by omega)) (inside low (by omega) (by omega))

def callMemory (m : Ram) (sp ret : BitVec 64) (dst src n : Nat) : Ram :=
  memCopy (memStore m (sp - 8) ret) (sp + BitVec.ofNat 64 dst) (sp + BitVec.ofNat 64 src) n

theorem callMemoryFrame {m n : Ram} {sp : BitVec 64} (low : sp.toNat + 6104 < 2^64)
    (room : 8 ≤ sp.toNat) (frame : RamWriteFrame m n (writes sp))
    (ret : BitVec 64) {dst src len : Nat} (lo : 344 ≤ dst) (hi : dst + len ≤ 6104) :
    RamWriteFrame m (callMemory n sp ret dst src len) (writes sp) := by
  apply Sec1.Wrapper.Copy.memCopy_frame _ (inside low lo hi)
  apply frame.memStore
  refine ⟨_, List.Mem.head _, ?_⟩
  have h : (sp - 8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr room)
  change sp.toNat - 8 ≤ _ ∧ _ ≤ sp.toNat - 8 + 8 ∧ _ ≤ 2^64
  rw [h]
  omega

theorem tableMemory {s : RamState} {secret key : ByteArray} {m n : Ram}
    (call : ValidCall ecdhDiffieHellman s [secret, key]) (mem : Scalar.Memory s m)
    (frame : RamWriteFrame m n (writes (localSp s))) : Scalar.Memory s n := by
  obtain ⟨depth, _, sp⟩ := Scalar.stack_geometry call
  apply mem.advance call frame
  intro r hr
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> dsimp only <;> omega

theorem outside {s : RamState} {secret key : ByteArray} (call : ValidCall ecdhDiffieHellman s [secret, key])
    {k n : Nat} (hi : k+n ≤ 344) : Outside (writes (localSp s)) (localSp s + BitVec.ofNat 64 k) n := by
  obtain ⟨depth, low, sp⟩ := Scalar.stack_geometry call
  rw [Outside, tableOffset (by omega) (by omega)]
  refine ⟨by omega, fun r hr => ?_⟩
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> dsimp only <;> omega

end K256.Proofs.Ecdh.Wrapper.Tables
