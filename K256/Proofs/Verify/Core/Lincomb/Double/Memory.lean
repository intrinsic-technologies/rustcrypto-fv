import K256.Proofs.Verify.Core.Lincomb.Double.Setup

namespace K256.Proofs.Verify.Core.Lincomb.Double

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Common.Tactic Common.Field
open Generate.Generator.Multiply (Projective)

abbrev firstMemory (a : Registers) (m : Ram) (sp src dst : BitVec 64) : Ram :=
  let q := localStack sp
  let pre := memStore (savedStack a m sp) (q + 0x1a0) dst
  memStore (copyPoint pre q src) (q - 8) (0x110d0e : BitVec 64)

private theorem firstCopyFrame {a : Registers} {m : Ram} {sp src dst : BitVec 64}
    (e : RoutineEntry a m sp 0x298) :
    let q := localStack sp
    let pre := memStore (savedStack a m sp) (q + 0x1a0) dst
    RamWriteFrame pre (copyPoint pre q src) [⟨(q + 0x128).toNat,120⟩] := by
  intro q pre
  have room := e.room
  have bound := e.stack.readable.low
  have base : (sp - 0x298).toNat = sp.toNat - 0x298 := BitVec.toNat_sub_of_le (by exact room)
  change (sp - 0x298).toNat + 0x298 ≤ 2^32 at bound
  rw [base] at bound
  have addr := stackOffset (q := q) (k := 0x128) rfl room (by omega) (by decide)
  apply Sec1.Wrapper.Copy.memCopy_frame (RamWriteFrame.refl _ _)
  refine ⟨_, .head _, Nat.le_refl _, Nat.le_refl _, ?_⟩
  change (q + BitVec.ofNat 64 0x128).toNat + 120 ≤ 2^64
  rw [addr]
  omega

set_option maxHeartbeats 800000 in
theorem firstMemoryFacts {a : Registers} {m : Ram} {sp src dst : BitVec 64} {p : Projective}
    (e : RoutineEntry a m sp 0x298) (source : Outside [scratch sp 0x298] src 120)
    (point : p.Stored m src) :
    let q := localStack sp
    let n := firstMemory a m sp src dst
    p.Stored n (q + 0x128) ∧ memLoad n (q + 0x1a0) 64 = dst ∧
      memLoad n (q - 8) 64 = 0x110d0e ∧
      ∀ i : Fin 6, let r := (#v[5,15,14,13,12,3] : Vector (Fin Reg.count) 6)[i]
        (⟨64, memLoad n (sp - BitVec.ofNat 64 (8*(i.val+1))) 64⟩ : Value) = a[r] := by
  intro q n
  let pre := memStore (savedStack a m sp) (q + 0x1a0) dst
  let copied := copyPoint pre q src
  have room := e.room
  have high := e.stack.readable.low
  have base : (sp - 0x298).toNat = sp.toNat - 0x298 := BitVec.toNat_sub_of_le (by exact room)
  change (sp - 0x298).toNat + 0x298 ≤ 2^32 at high
  rw [base] at high
  have ptr (k : Nat) (hk : k ≤ 0x228) :
      (q + BitVec.ofNat 64 k).toNat = sp.toNat - 0x228 + k :=
    stackOffset rfl room (by omega) hk
  have frame : RamWriteFrame m pre [scratch sp 0x298] := by
    apply (savedFrame (a := a) (m := m) room (by omega)).memStore
    refine ⟨_, .head _, ?_⟩
    change sp.toNat - 0x298 ≤ (q + BitVec.ofNat 64 0x1a0).toNat ∧
      (q + BitVec.ofNat 64 0x1a0).toNat + 8 ≤ sp.toNat - 0x298 + 0x298 ∧
      (q + BitVec.ofNat 64 0x1a0).toNat + 8 ≤ 2^64
    rw [ptr 0x1a0 (by decide)]
    omega
  have storedPre := point.of_frame frame source
  have old : p.Stored pre (src + BitVec.ofNat 64 0) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using storedPre
  have moved : p.Stored copied (q + 0x128) := by
    have copy := old.memCopy (dst := q + 0x128) (off := 0) (len := 120) (by decide) (by decide)
    change p.Stored copied ((q + 0x128) + 0#64) at copy
    rw [BitVec.add_zero] at copy
    exact copy
  have frameCopy : RamWriteFrame pre copied [⟨(q + 0x128).toNat,120⟩] := firstCopyFrame e
  have callNat : (q - 8).toNat = sp.toNat - 0x230 := by
    change (sp - 0x228 - 8).toNat = _
    rw [show sp - 0x228 - 8 = sp - 0x230 by bv_omega]
    exact BitVec.toNat_sub_of_le (by exact show 0x230 ≤ sp.toNat by omega)
  have push : RamWriteFrame copied n [⟨(q - 8).toNat,8⟩] := by
    exact (RamWriteFrame.refl _ _).memStore _ ⟨_, .head _, Nat.le_refl _, Nat.le_refl _, by rw [callNat]; omega⟩
  have copyNat : (q + 0x128).toNat = sp.toNat - 0x228 + 0x128 := ptr 0x128 (by decide)
  have destNat : (q + 0x1a0).toNat = sp.toNat - 0x228 + 0x1a0 := ptr 0x1a0 (by decide)
  refine ⟨moved.of_frame push ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [copyNat]; omega, ?_⟩
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    change (q + 0x128).toNat + 120 ≤ (q - 8).toNat ∨ (q - 8).toNat + 8 ≤ (q + 0x128).toNat
    rw [callNat, copyNat]
    omega
  · rw [push.memLoad_eq, frameCopy.memLoad_eq]
    · exact memLoad_memStore_same _ _ _ rfl (by decide)
    · refine ⟨by rw [destNat]; omega, ?_⟩
      intro r hr
      rcases List.mem_singleton.mp hr with rfl
      change (q + 0x1a0).toNat + 8 ≤ (q + 0x128).toNat ∨ (q + 0x128).toNat + 120 ≤ (q + 0x1a0).toNat
      rw [copyNat, destNat]
      omega
    · refine ⟨by rw [destNat]; omega, ?_⟩
      intro r hr
      rcases List.mem_singleton.mp hr with rfl
      change (q + 0x1a0).toNat + 8 ≤ (q - 8).toNat ∨ (q - 8).toNat + 8 ≤ (q + 0x1a0).toNat
      rw [callNat, destNat]
      omega
  · exact memLoad_memStore_same _ _ _ rfl (by decide)
  · intro i
    let addr := sp - BitVec.ofNat 64 (8*(i.val+1))
    have addrNat : addr.toNat = sp.toNat - 8*(i.val+1) := by
      have hi := i.isLt
      have k : (BitVec.ofNat 64 (8*(i.val+1))).toNat = 8*(i.val+1) := Nat.mod_eq_of_lt (by omega)
      dsimp only [addr]
      rw [BitVec.toNat_sub_of_le (by change (BitVec.ofNat 64 (8*(i.val+1))).toNat ≤ sp.toNat; rw [k]; omega), k]
    change (⟨64,memLoad n addr 64⟩ : Value) = a[(#v[5,15,14,13,12,3] : Vector (Fin Reg.count) 6)[i]]
    rw [push.memLoad_eq, frameCopy.memLoad_eq]
    · have w : RangeApart (q + 0x1a0) 8 addr 8 := by
        refine RangeApart.of_offsets (x := sp) (c := 0 - 0x88)
          (d := 0 - BitVec.ofNat 64 (8*(i.val+1))) (by dsimp only [q,localStack]; bv_omega)
          (addr_sub _ _) ?_
        rcases i with ⟨j,hj⟩
        rcases (by omega : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5) with rfl|rfl|rfl|rfl|rfl|rfl
        all_goals dsimp only [Fin.val_mk]; decide
      change (⟨64,memLoad (memStore (savedStack a m sp) (q+0x1a0) dst) addr 64⟩ : Value) = _
      rw [memLoad_memStore_of_rangeApart _ _ _ _ _ w]
      have width (r : Fin Reg.count) (member : r.val ∈ [3,5,12,13,14,15]) :
          (⟨64,a[r].get 64⟩ : Value) = a[r] := by
        cases hv : a[r] with
        | mk n bits =>
          have h := e.saved r member
          rw [hv] at h
          change n = 64 at h
          subst n
          rfl
      rcases i with ⟨j,hj⟩
      rcases (by omega : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5) with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals
        dsimp only [addr,savedStack]
        segment_words [Nat.reduceAdd,Nat.reduceMul,BitVec.ofNat_eq_ofNat]
        first | exact width 5 (by decide) | exact width 15 (by decide) | exact width 14 (by decide)
              | exact width 13 (by decide) | exact width 12 (by decide) | exact width 3 (by decide)
    · refine ⟨by rw [addrNat]; omega, ?_⟩
      intro r hr
      rcases List.mem_singleton.mp hr with rfl
      change addr.toNat + 8 ≤ (q + 0x128).toNat ∨ (q + 0x128).toNat + 120 ≤ addr.toNat
      rw [addrNat, copyNat]
      have := i.isLt
      omega
    · refine ⟨by rw [addrNat]; omega, ?_⟩
      intro r hr
      rcases List.mem_singleton.mp hr with rfl
      change addr.toNat + 8 ≤ (q - 8).toNat ∨ (q - 8).toNat + 8 ≤ addr.toNat
      rw [addrNat, callNat]
      have := i.isLt
      omega

end K256.Proofs.Verify.Core.Lincomb.Double
