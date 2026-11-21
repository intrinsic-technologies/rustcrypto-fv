import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode.State

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)
open Encode

theorem Encode.writtenWord {fr : Activation} {a : Verify.Core.Registers} {m : Ram} {x k : Nat}
    (hk : k < 4) (depth : 208 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 208)
    (dstAfter : fr.rsp.toNat + 8 ≤ fr.rdx.toNat)
    (dstWrite : Writable Extracted.programImage fr.original fr.rdx 32)
    (loop : Loop fr x k a m) :
    let v := bswapSpec ((scalarWords x)[k])
    let staged := memStore m (fr.rsp - 56) v
    let pushed := memStore staged (fr.rsp - 80) (0x10014b : BitVec 64)
    let dest := wordAddr fr.rdx 64 (3-k)
    let result := memCopy pushed dest (fr.rsp - 56) 8
    Atom.All Extracted.programImage a result (Fn100000.frameAt .l100110 fr) ∧
      RamWriteFrame fr.original result [fr.region, ⟨fr.rdx.toNat,32⟩] ∧
      ∀ i (_hi : i < k+1) (bound : i < 4),
        memLoad result (wordAddr fr.rdx 64 (3-i)) 64 = bswapSpec ((scalarWords x)[i]) := by
  intro v staged pushed dest result
  have atoms := loop.atoms
  rw [show label k = .l100110 from ite_eq_left hk] at atoms
  simp only [Fn100000.frameAt, Fn100000.frameAtG0, Atom.All, Atom.Holds] at atoms ⊢
  obtain ⟨sp, df, r13, r14, mx, ft, fc, s3, s12, s13, s14, s15, s5, retRead, retVal,
    retLow, area, room, align, gotRead, gotVal, gotBound, _⟩ := atoms
  have stackNat (off : BitVec 64) (h : off.toNat ≤ 208) :
      (fr.rsp - off).toNat = fr.rsp.toNat - off.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have floorNat : (fr.rsp - 208).toNat = fr.rsp.toNat - 208 := stackNat 208 (by decide)
  have stageNat : (fr.rsp - 56).toNat = fr.rsp.toNat - 56 := stackNat 56 (by decide)
  have pushNat : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := stackNat 80 (by decide)
  have dstTop := dstWrite.readable.low
  have wordNat (i : Nat) (hi : i < 4) :
      (wordAddr fr.rdx 64 (3-i)).toNat = fr.rdx.toNat + 8*(3-i) := by
    exact toNat_add_ofNat _ _ (by omega)
  have destNat : dest.toNat = fr.rdx.toNat + 8*(3-k) := wordNat k hk
  have stackWrite {b : BitVec 64} (lo : fr.rsp.toNat - 208 ≤ b.toNat)
      (hi : b.toNat + 8 ≤ fr.rsp.toNat) : Writable Extracted.programImage m b 8 :=
    area.sub (by rw [floorNat]; exact lo) (by rw [floorNat]; omega)
  have stageWrite := stackWrite (b := fr.rsp - 56) (by omega) (by omega)
  have pushWrite := stackWrite (b := fr.rsp - 80) (by omega) (by omega)
  have copyWrite := dstWrite.sub (a := dest) (n := 8) (by omega) (by omega)
  have readable {b : BitVec 64} {n : Nat} (r : Readable m b n) : Readable result b n :=
    ((r.memStore _ v).memStore _ (0x10014b : BitVec 64)).memStore _ (memLoad pushed (fr.rsp - 56) 64)
  have preserve (b : BitVec 64) (stageApart : RangeApart (fr.rsp - 56) 8 b 8)
      (pushApart : RangeApart (fr.rsp - 80) 8 b 8) (copyApart : RangeApart dest 8 b 8) :
      memLoad result b 64 = memLoad m b 64 := by
    calc
      memLoad result b 64 = memLoad pushed b 64 :=
        memLoad_memStore_of_rangeApart _ _ _ _ _ copyApart
      _ = memLoad staged b 64 := memLoad_memStore_of_rangeApart _ _ _ _ _ pushApart
      _ = memLoad m b 64 := memLoad_memStore_of_rangeApart _ _ _ _ _ stageApart
  have keepSlot (off : BitVec 64) (h : off.toNat ≤ 48) :
      memLoad result (fr.rsp - off) 64 = memLoad m (fr.rsp - off) 64 := by
    have addr := stackNat off (by omega)
    apply preserve <;> apply RangeApart.of_toNat <;> omega
  have keepRet : memLoad result fr.rsp 64 = memLoad m fr.rsp 64 := by
    apply preserve <;> apply RangeApart.of_toNat <;> omega
  have rod : rodataSection ∈ Extracted.programSections :=
    List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have gotApart {b : BitVec 64} {ram : Ram} (w : Writable Extracted.programImage ram b 8) :
      RangeApart b 8 0x203dd0 8 := by
    intro i hi j hj eqAddr
    have addr := toNat_add_ofNat 0x203dd0 j (by simp only [BitVec.reduceToNat]; omega)
    obtain ⟨byte, member⟩ := Fn100000.callSlots_span rod (0x203dd0 + BitVec.ofNat 64 j)
      (by change 0x203dd0 ≤ _; rw [addr]; simp only [BitVec.reduceToNat]; omega)
      (by change _ < 0x203e28; rw [addr]; simp only [BitVec.reduceToNat]; omega)
    exact w.notCode _ member i hi eqAddr.symm
  have keepGot := preserve 0x203dd0 (gotApart stageWrite) (gotApart pushWrite) (gotApart copyWrite)
  have onStack {b : BitVec 64} (lo : fr.rsp.toNat - 208 ≤ b.toNat)
      (hi : b.toNat + 8 ≤ fr.rsp.toNat) :
      InRegions [fr.region, ⟨fr.rdx.toNat,32⟩] b 8 := by
    refine ⟨fr.region, List.mem_cons_self .., ?_⟩
    have lowNat : fr.low.toNat = fr.rsp.toNat - 208 := (congrArg BitVec.toNat low).trans floorNat
    simp only [InRegion, Activation.region, lowNat]
    omega
  have inDest : InRegions [fr.region, ⟨fr.rdx.toNat,32⟩] dest 8 := by
    refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
    simp only [InRegion, destNat]
    omega
  refine ⟨⟨sp, df, r13, r14, mx, ft, fc,
    (keepSlot 48 (by decide)).trans s3, (keepSlot 40 (by decide)).trans s12,
    (keepSlot 32 (by decide)).trans s13, (keepSlot 24 (by decide)).trans s14,
    (keepSlot 16 (by decide)).trans s15, (keepSlot 8 (by decide)).trans s5,
    readable retRead, keepRet.trans retVal, retLow, ⟨readable area.readable, area.tables, area.notCode⟩,
    room, align, readable gotRead, keepGot.trans gotVal, gotBound, trivial⟩, ?_, ?_⟩
  · exact ((loop.writes.memStore v (onStack (by omega) (by omega))).memStore
      (0x10014b : BitVec 64) (onStack (by omega) (by omega))).memStore
        (memLoad pushed (fr.rsp - 56) 64) inDest
  · intro i hi bound
    by_cases same : i = k
    · subst i
      calc
        memLoad result dest 64 = memLoad pushed (fr.rsp - 56) 64 :=
          memLoad_memStore_same _ _ _ (by decide) (by decide)
        _ = memLoad staged (fr.rsp - 56) 64 :=
          memLoad_memStore_of_rangeApart _ _ _ _ _ (by apply RangeApart.of_toNat <;> omega)
        _ = v := memLoad_memStore_same _ _ _ (by decide) (by decide)
    · have addr := wordNat i bound
      refine (preserve _ ?_ ?_ ?_).trans (loop.words i (by omega) bound)
      all_goals apply RangeApart.of_toNat <;> omega

end K256.Proofs.Signing.Nonce.Initialize
