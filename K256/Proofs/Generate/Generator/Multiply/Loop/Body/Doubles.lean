import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Transport

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

private def doublesSetupMemory (m : Ram) (sp count pointer : BitVec 64) :=
  memStore (memStore m (sp + 0x250) count) (sp + 0xf0) pointer

private theorem doublesSetupBlock {a : Registers} {m : Ram} {sp count pointer : BitVec 64}
    (rsp : a[4].get 64 = sp)
    (stack : Writable Extracted.programImage m sp 0x258)
    (cx : a[1] = ⟨64,count⟩) (dx : a[2] = ⟨64,pointer⟩)
    (widths : ParseSignature.ArgumentWidths a) (saved : SavedWidths a) :
    ∃ b, Reaches .l11d7ef a m .l11d810 b (doublesSetupMemory m sp count pointer) ∧
      ParseSignature.ArgumentWidths b ∧ SavedWidths b ∧
      b[1].get 64 = 4 ∧ b[5].get 64 = 0x1000003d10 ∧ b[12] = a[12] ∧
      ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i] := by
  refine ⟨?b, ?reach, ?widths, ?saved, ?cx, ?rbp, ?r12, ?keep⟩
  case reach =>
    have run : program.runBlock (dialect Extracted.programImage) ⟨.l11d7ef,a,m⟩ =
        .jump ⟨.l11d810,?b,doublesSetupMemory m sp count pointer⟩ := by
      arithmetic_segment using code_l11d7ef [rsp,cx,dx,doublesSetupMemory]
    apply Semantics.Reaches.single
    change program.step _ _ = _
    simp only [Program.step, run, Transfer.next]
  case widths =>
    rintro ⟨i,hi⟩ hm
    have w := widths ⟨i,hi⟩ hm
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact w
  case saved =>
    rintro ⟨i,hi⟩ hm
    have w := saved ⟨i,hi⟩ hm
    simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact w
  case keep =>
    rintro ⟨i,hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> rfl
  all_goals rfl

private def doublesSetupWrites (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp + 0x250).toNat, 8⟩, ⟨(sp + 0xf0).toNat, 8⟩]

private theorem doublesSetupFrame {m : Ram} {sp count pointer : BitVec 64}
    (low : sp.toNat + 0x258 ≤ 2^32) :
    RamWriteFrame m (doublesSetupMemory m sp count pointer) (doublesSetupWrites sp) := by
  unfold doublesSetupMemory doublesSetupWrites
  slot_state region

private theorem doublesSetupAccOutside {sp : BitVec 64} (low : sp.toNat + 0x258 ≤ 2^32) :
    Outside (doublesSetupWrites sp) (sp + 0x128) 120 := by
  have addr (off : BitVec 64) (h : off.toNat ≤ 0x258) :
      (sp + off).toNat = sp.toNat + off.toNat := BitVec.toNat_add_of_lt (by omega)
  simp only [Outside, doublesSetupWrites, List.mem_cons, List.not_mem_nil, or_false,
    addr _ (by decide : (0x128 : BitVec 64).toNat ≤ 0x258),
    addr _ (by decide : (0x250 : BitVec 64).toNat ≤ 0x258),
    addr _ (by decide : (0xf0 : BitVec 64).toNat ≤ 0x258), BitVec.reduceToNat]
  refine ⟨by omega, ?_⟩
  rintro _ (rfl | rfl) <;> dsimp only <;> omega

theorem windowDoubles (doubles : type_of% @fourDoubles)
    {fr : Activation} {initial a : Registers} {m : Ram} {d k : Nat} {p : Projective}
    (entry : CoreEntry fr initial d) (bound : k < 32) (s : WindowHead fr a m d (k+1))
    (acc : p.Stored m (fr.rsp - 0xb90)) :
    ∃ b n, Reaches .l11d7ef a m .l11f5e5 b n ∧ RoundState fr d k .l11f5e5 b n ∧
      p.double.double.double.double.Stored n (fr.rsp - 0xb90) := by
  let sp := fr.rsp - 0xcb8
  let count := BitVec.ofNat 64 (k+1)
  let pointer := fr.r9 + BitVec.ofNat 64 (32+(k+1))
  let m' := doublesSetupMemory m sp count pointer
  have nonzero : count ≠ 0 := by
    intro h
    have eq := congrArg BitVec.toNat h
    change (BitVec.ofNat 64 (k+1)).toNat = 0 at eq
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show k+1 < 2^64 by omega)] at eq
    omega
  have atoms : Atom.All Extracted.programImage a m (Fn11c880.frameAt .l11d7ef fr) := by
    simpa only [windowLabel, ← show count = BitVec.ofNat 64 (k+1) from rfl, ite_eq_right nonzero] using s.atoms
  have rsp : a[4].get 64 = sp := congrArg (Value.get 64) atoms.1
  have full : Writable Extracted.programImage m (fr.rsp - 0xed8) 0xed8 :=
    atoms.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have stack : Writable Extracted.programImage m sp 0x258 := by
    change Writable Extracted.programImage m (fr.rsp - 0xcb8) 0x258
    slot_state region
  obtain ⟨b, path, widths, saved, rounds, mask, temp, keep⟩ :=
    doublesSetupBlock rsp stack s.count s.pointer s.widths s.saved
  have frame : RamWriteFrame m m' (doublesSetupWrites sp) := doublesSetupFrame stack.readable.low
  have stored : p.Stored m' (fr.rsp - 0xb90) := by
    apply acc.of_frame frame
    rw [show fr.rsp - 0xb90 = sp + 0x128 by dsimp only [sp]; bv_omega]
    exact doublesSetupAccOutside stack.readable.low
  have savedCount : memLoad m' (fr.rsp - 0xa68) 64 = BitVec.ofNat 64 k + 1 := by
    have apart : RangeApart (sp + 0xf0) 8 (sp + 0x250) 8 :=
      RangeApart.of_offsets rfl rfl (by decide)
    rw [show fr.rsp - 0xa68 = sp + 0x250 by dsimp only [sp]; bv_omega]
    dsimp only [m', doublesSetupMemory]
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ apart, memLoad_memStore_same _ _ _ rfl (by decide)]
    rw [show count = BitVec.ofNat 64 (k+1) from rfl, BitVec.ofNat_add]
    rfl
  have savedPointer : memLoad m' (fr.rsp - 0xbc8) 64 = (fr.r9 + BitVec.ofNat 64 (32+k)) + 1 := by
    rw [show fr.rsp - 0xbc8 = sp + 0xf0 by dsimp only [sp]; bv_omega]
    dsimp only [m', doublesSetupMemory]
    rw [memLoad_memStore_same _ _ _ rfl (by decide)]
    simp only [pointer, ← Nat.add_assoc, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  have prefixFrame : RamWriteFrame m m' (windowWrites sp) := by
    refine (RamWriteFrame.refl _ _).trans frame ?_
    dsimp only [sp, doublesSetupWrites]
    round_within using entry
  let start : RoundState fr d k .l11d810 b m' :=
    ⟨windowAtomsAfterWrites entry (l := .l11d7ef) (t := .l11d810) rfl rfl atoms prefixFrame keep,
      widths, saved, s.memory.afterWrites entry prefixFrame, savedCount, savedPointer⟩
  obtain ⟨c, n, rest, doneAtoms, doneWidths, doneSaved, doubled, doneFrame⟩ :=
    doubles start.atoms start.widths start.saved rounds mask (by rw [temp, s.temp])
      (start.memory.locals (0x1c8, 0xfffffffffff8) (by simp)) stored
  have roundFrame : RamWriteFrame m' n (roundWrites sp) := by
    refine (RamWriteFrame.refl _ _).trans doneFrame ?_
    dsimp only [sp]
    round_within using entry
  exact ⟨c, n, path.trans rest, start.afterFrame entry roundFrame doneAtoms doneWidths doneSaved,
    doubled⟩

end K256.Proofs.Generate.Generator.Multiply
