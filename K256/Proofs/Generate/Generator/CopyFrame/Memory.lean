import K256.Proofs.Generate.Generator.Child
import K256.Proofs.Generate.Generator.Calls
import K256.Proofs.Generate.Generator.Copy
import K256.Proofs.Generate.Generator.Affine.Repr
import K256.Proofs.Generate.Generator.Sample.Memory
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.CopyFrame

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR Standards.SECG.ECC
  Standards.SECG.DomainParameters

abbrev atDepth (s : RamState) (depth : Nat) := s.regValue .rsp - BitVec.ofNat 64 depth

abbrev scalarWords (d : Nat) : ScalarWords :=
  Vector.ofFn fun i : Fin 4 => BitVec.ofNat 64 (d / 2^(64*i.val))

abbrev stackWrites (s : RamState) (m : Ram) :=
  RamWriteFrame s.external m [Stack.region s signingKeyGenerateFromRng.minStackBytes]

def childRegions (s : RamState) (window dst size : Nat) : List MemoryRegion :=
  [⟨(atDepth s (688 + window)).toNat, (atDepth s 688).toNat - (atDepth s (688 + window)).toNat⟩,
    ⟨(atDepth s dst).toNat, size⟩]

abbrev mulInput (s : RamState) (m : Ram) (d : Nat) :=
  multiplyMemory m (atDepth s 680) (scalarWords d)

abbrev affineInput (s : RamState) (m : Ram) :=
  memStore m (atDepth s 688) (0x1060c7 : BitVec 64)

private theorem addAtDepth (s : RamState) {depth off : Nat} (h : off ≤ depth)
    (hl : off < 2 ^ 64) :
    atDepth s depth + BitVec.ofNat 64 off = atDepth s (depth - off) := by
  rw [atDepth, atDepth, ← BitVec.ofNat_sub_ofNat_of_le depth off hl h]
  bv_omega

private theorem stackStore {s : RamState} {random : ByteArray}
    (call : ValidCall signingKeyGenerateFromRng s [random]) {m : Ram} (writes : stackWrites s m)
    {off : Nat} {v : BitVec 64} (h : off ≤ 10584) :
    stackWrites s (memStore m (atDepth s off) v) :=
  writes.memStore v ⟨_, List.mem_singleton_self _, stackRange call h (by omega)⟩

private theorem mulInput_stores (s : RamState) (m : Ram) (d : Nat) :
    mulInput s m d = memStore (memStore (memStore (memStore (memStore m
      (atDepth s 656) (scalarWords d)[3]) (atDepth s 664) (scalarWords d)[2])
      (atDepth s 672) (scalarWords d)[1]) (atDepth s 680) (scalarWords d)[0])
      (atDepth s 688) (0x1060b7 : BitVec 64) := by
  have h24 : atDepth s 680 + 24 = atDepth s 656 :=
    addAtDepth s (depth := 680) (off := 24) (by decide) (by decide)
  have h16 : atDepth s 680 + 16 = atDepth s 664 :=
    addAtDepth s (depth := 680) (off := 16) (by decide) (by decide)
  have h8 : atDepth s 680 + 8 = atDepth s 672 :=
    addAtDepth s (depth := 680) (off := 8) (by decide) (by decide)
  have hpush : atDepth s 680 - 8 = atDepth s 688 := by
    unfold atDepth
    rw [BitVec.sub_sub]
    rfl
  simp only [multiplyMemory, h24, h16, h8, hpush]

private theorem childRegionsWithin {s : RamState} {random : ByteArray}
    (call : ValidCall signingKeyGenerateFromRng s [random]) {window dst size : Nat}
    (hw : 688 + window ≤ 10584) (hd : dst ≤ 10584) (hs : size ≤ dst + 8) :
    RegionsWithin (childRegions s window dst size)
      [Stack.region s signingKeyGenerateFromRng.minStackBytes] := by
  intro r hr
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [childRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have inside := stackRange (off := 688 + window) (len := window) call hw (by omega)
    have room : 10584 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
    have lo : (atDepth s (688 + window)).toNat = (stackPtr s).toNat - (688 + window) :=
      stackOffset call hw
    have hi : (atDepth s 688).toNat = (stackPtr s).toNat - 688 := stackOffset call (by decide)
    have len : (atDepth s 688).toNat - (atDepth s (688 + window)).toNat = window := by
      rw [lo, hi]
      omega
    refine ⟨inside.1, ?_⟩
    change (atDepth s (688 + window)).toNat + _ ≤ _
    rw [len]
    exact inside.2.1
  · have inside := stackRange call hd hs
    exact ⟨inside.1, inside.2.1⟩

private theorem childLoadOutside {s : RamState} {random : ByteArray}
    (call : ValidCall signingKeyGenerateFromRng s [random]) {window dst size off len : Nat}
    (hw : 688 + window ≤ 10584) (hd : dst ≤ 10584) (hoff : off ≤ 680)
    (hlen : len ≤ off + 8) (hsep : dst + len ≤ off ∨ off + size ≤ dst) :
    Outside (childRegions s window dst size) (atDepth s off) len := by
  refine ⟨(stackRange call (by omega) hlen).2.2, ?_⟩
  intro r hr
  simp only [childRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  have room : 10584 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
  have ha : (atDepth s off).toNat = (stackPtr s).toNat - off := stackOffset call (by omega)
  rcases hr with rfl | rfl
  · right
    change (atDepth s (688 + window)).toNat +
      ((atDepth s 688).toNat - (atDepth s (688 + window)).toNat) ≤ (atDepth s off).toNat
    rw [ha, show (atDepth s 688).toNat = (stackPtr s).toNat - 688 from stackOffset call (by decide),
      show (atDepth s (688 + window)).toNat = (stackPtr s).toNat - (688 + window) from stackOffset call hw]
    omega
  · change (atDepth s off).toNat + len ≤ (atDepth s dst).toNat ∨
      (atDepth s dst).toNat + size ≤ (atDepth s off).toNat
    rw [ha, show (atDepth s dst).toNat = (stackPtr s).toNat - dst from stackOffset call hd]
    omega

private theorem depthApart {s : RamState} {random : ByteArray}
    (call : ValidCall signingKeyGenerateFromRng s [random]) {deep shallow : Nat}
    (hdeep : deep ≤ 10584) (hsep : shallow + 8 ≤ deep) :
    RangeApart (atDepth s deep) 8 (atDepth s shallow) 8 := by
  have room : 10584 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
  have start : (atDepth s deep).toNat = (stackPtr s).toNat - deep := stackOffset call hdeep
  have stop : (atDepth s shallow).toNat = (stackPtr s).toNat - shallow := stackOffset call (by omega)
  apply RangeApart.of_toNat (stackRange call hdeep (by omega)).2.2
    (stackRange call (by omega) (by omega)).2.2
  change (atDepth s deep).toNat + 8 ≤ (atDepth s shallow).toNat ∨
    (atDepth s shallow).toNat + 8 ≤ (atDepth s deep).toNat
  rw [start, stop]
  omega

private theorem sampleOuter_load {s : RamState} {random : ByteArray}
    (call : ValidCall signingKeyGenerateFromRng s [random]) {m : Ram}
    (frame : RamWriteFrame (activation s).original m (Sample.regions (activation s))) {off : Nat}
    (ho : off ≤ 16) :
    memLoad m (atDepth s off) 64 = memLoad (entryMemory s) (atDepth s off) 64 := by
  apply frame.memLoad_eq
  refine ⟨(stackRange call (by omega) (by omega)).2.2, ?_⟩
  intro r hr
  simp only [Sample.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
  have room : 10584 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
  have ha : (atDepth s off).toNat = (stackPtr s).toNat - off := stackOffset call (by omega)
  rcases hr with rfl | rfl
  · right
    change (atDepth s 10584).toNat + ((atDepth s 288).toNat - (atDepth s 10584).toNat) ≤ _
    rw [ha, show (atDepth s 10584).toNat = (stackPtr s).toNat - 10584 from stackOffset call (by decide),
      show (atDepth s 288).toNat = (stackPtr s).toNat - 288 from stackOffset call (by decide)]
    omega
  · right
    change (atDepth s 208).toNat + 16 ≤ _
    rw [ha, show (atDepth s 208).toNat = (stackPtr s).toNat - 208 from stackOffset call (by decide)]
    omega

theorem mulInput_memory {s : RamState} {random : ByteArray} (call : ValidCall signingKeyGenerateFromRng s [random])
    {m : Ram} (writes : stackWrites s m) (d : Nat) :
    stackWrites s (mulInput s m d) ∧ WordsAt (mulInput s m d) (atDepth s 680) 64 (scalarWords d) ∧
    memLoad (mulInput s m d) (atDepth s 688) 64 = 0x1060b7 := by
  constructor
  · rw [mulInput_stores]
    repeat' apply stackStore call _ (by decide)
    exact writes
  · constructor
    · intro i hi
      have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases h with rfl | rfl | rfl | rfl
      all_goals
        rw [show wordAddr (atDepth s 680) 64 _ = atDepth s _ from
          addAtDepth s (by decide) (by decide), mulInput_stores]
        simp (disch := store_disch) only [atDepth, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, store_norm]
    · rw [mulInput_stores]
      simp (disch := store_disch) only [store_norm]

theorem affineInput_memory {s : RamState} {random : ByteArray} (call : ValidCall signingKeyGenerateFromRng s [random])
    {m n : Ram} (writes : stackWrites s m)
    (frame : RamWriteFrame m n (childRegions s 9768 456 120))
    {point : Curve.Point} (proj : Affine.ProjectiveAt n (atDepth s 456) point) :
    stackWrites s n ∧ stackWrites s (affineInput s n) ∧
    Affine.ProjectiveAt (affineInput s n) (atDepth s 456) point ∧
    memLoad (affineInput s n) (atDepth s 688) 64 = 0x1060c7 := by
  have frame' := writes.trans frame (childRegionsWithin call (by decide) (by decide) (by decide))
  refine ⟨frame', stackStore call frame' (by decide), ?_, ?_⟩
  · obtain ⟨x, y, z, xl, yl, zl, xw, yw, zw, xr, yr, zr, pt⟩ := proj
    have yAddr : atDepth s 456 + 40 = atDepth s 416 :=
      addAtDepth s (depth := 456) (off := 40) (by decide) (by decide)
    have zAddr : atDepth s 456 + 80 = atDepth s 376 :=
      addAtDepth s (depth := 456) (off := 80) (by decide) (by decide)
    refine ⟨x, y, z, xl, yl, zl, ?_, ?_, ?_, xr, yr, zr, pt⟩
    all_goals
      apply WordsAt.write_apart (by assumption)
      first | rw [yAddr] | rw [zAddr] | skip
      simp only [atDepth]
      store_disch
  · simp (disch := store_disch) only [affineInput, store_norm]

theorem copyReady {s : RamState} {random : ByteArray} {a b : Sample.Registers} {m n o : Ram} {d : Nat}
    {point : Curve.Point} (call : ValidCall signingKeyGenerateFromRng s [random])
    (sample : Sample.Accepted (activation s) d a m)
    (mulFrame : RamWriteFrame (mulInput s m d) n (childRegions s 9768 456 120))
    (affFrame : RamWriteFrame (affineInput s n) o (childRegions s 976 544 88))
    (scalar : K256.Spec.Secp256k1.randomSecret random = some d)
    (publicKey : Keys.publicKey Secp256k1.domain (Encoding.natToOctets 32 d) = some point)
    (aff : Sec1.Parser.PublicKeyAt o (atDepth s 544) point)
    (rsp : b[4] = ⟨64, atDepth s 680⟩) (df : b[22] = ⟨1, 0⟩) :
    CopyReady s random b o d point := by
  have sampleFrame : stackWrites s m := Sample.stackFrame call (sampleEntry call) sample.writes
  obtain ⟨mulStack, mulWords, _⟩ := mulInput_memory call sampleFrame d
  have afterMul : stackWrites s n :=
    mulStack.trans mulFrame (childRegionsWithin call (by decide) (by decide) (by decide))
  have afterAff : stackWrites s o :=
    (stackStore call afterMul (by decide : 688 ≤ 10584)).trans affFrame
      (childRegionsWithin call (by decide) (by decide) (by decide))
  have preserved (off : Nat) (hoff : off ≤ 680) (sep : off ≤ 336 ∨ 552 ≤ off) :
      memLoad o (atDepth s off) 64 = memLoad (mulInput s m d) (atDepth s off) 64 := by
    rw [affFrame.memLoad_eq (childLoadOutside call (by decide) (by decide) hoff (by omega) (by omega))]
    rw [affineInput, memLoad_memStore_of_rangeApart _ _ _ _ _ (depthApart call (by decide) (by omega))]
    exact mulFrame.memLoad_eq (childLoadOutside call (by decide) (by decide) hoff (by omega) (by omega))
  have afterSample (off : Nat) (hoff : off ≤ 336 ∨ 552 ≤ off) (hprep : off ≤ 648) :
      memLoad o (atDepth s off) 64 = memLoad m (atDepth s off) 64 := by
    rw [preserved off (by omega) hoff, mulInput_stores]
    simp (disch := apply depthApart call <;> omega) only [memLoad_memStore_of_rangeApart]
  have limbs : WordsAt o (atDepth s 680) 64 (scalarWords d) := by
    intro i hi
    have addr : wordAddr (atDepth s 680) 64 i = atDepth s (680 - 8 * i) :=
      addAtDepth s (by omega) (by omega)
    rw [addr, preserved (680 - 8 * i) (by omega) (Or.inr (by omega)), ← addr]
    exact mulWords i hi
  have atoms := sample.atoms
  change Atom.All Extracted.programImage a m (Fn105f30.frameAtG0 .l10607d (activation s)) at atoms
  simp only [Fn105f30.frameAtG0, Atom.All, Atom.Holds] at atoms
  obtain ⟨_, _, _, _, _, _, keySlot, dstSlot, r12Slot, r13Slot, r14Slot, r15Slot, rbpSlot, _,
    resumeSlot, _⟩ := atoms
  simp only [activation, Activation.ofEntry, BitVec.sub_sub,
    BitVec.reduceAdd] at keySlot dstSlot r12Slot r13Slot r14Slot r15Slot rbpSlot
  have fromSample (off : Nat) (sep : off ≤ 336 ∨ 552 ≤ off) (prep : off ≤ 648) (v : BitVec 64)
      (h : memLoad m (atDepth s off) 64 = v) : memLoad o (atDepth s off) 64 = v :=
    (afterSample off sep prep).trans h
  have fromEntry (off : Nat) (ho : off ≤ 16) (v : BitVec 64)
      (h : memLoad (entryMemory s) (atDepth s off) 64 = v) :
      memLoad o (atDepth s off) 64 = v :=
    (afterSample off (Or.inl (by omega)) (by omega)).trans ((sampleOuter_load call sample.writes ho).trans h)
  obtain ⟨_, _, _, savedRbx, savedR14, ret⟩ := entryMemory_load s
  refine ⟨scalar, publicKey, limbs, aff, rsp, df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, afterAff⟩
  · exact fromSample 648 (by decide) (by decide) _ keySlot
  · exact fromSample 336 (by decide) (by decide) _ dstSlot
  · exact fromSample 328 (by decide) (by decide) _ r12Slot
  · exact fromSample 320 (by decide) (by decide) _ r13Slot
  · exact fromSample 312 (by decide) (by decide) _ r14Slot
  · exact fromSample 304 (by decide) (by decide) _ r15Slot
  · exact fromSample 296 (by decide) (by decide) _ rbpSlot
  · exact fromSample 288 (by decide) (by decide) _ resumeSlot
  · exact fromEntry 16 (by decide) _ savedRbx
  · exact fromEntry 8 (by decide) _ savedR14
  · have h0 : atDepth s 0 = s.regValue .rsp := BitVec.sub_zero _
    exact h0 ▸ fromEntry 0 (by decide) _ (h0.symm ▸ ret)

end K256.Proofs.Generate.Generator.CopyFrame
