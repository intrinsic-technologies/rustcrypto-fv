import K256.Proofs.Verify.Hash.Compression.Interface
import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Verify.Hash.Compression

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

variable {entry : CFG.Values Value Reg.count} {original : Ram} {sp dst src : BitVec 64}
    {initial : Array UInt32} {input : ByteArray}

private theorem setupCode : ∀ x ∈ codeRange 0x1218e9 bytes_l1218e9, x ∈ Extracted.programImage := by
  intro x hx
  have code := code_l1218e9 x hx
  apply List.mem_flatMap.mpr
  refine ⟨textSection, by simp [Extracted.programSections, textSection], ?_⟩
  simpa only [fnCode, sections, ImageSections.toCodeMap, List.flatMap_cons,
    List.flatMap_nil, List.append_nil] using code

private theorem stackAddress (sp : BitVec 64) (depth : 336 ≤ sp.toNat) {d : Nat}
    (hd : d ≤ 336) : (sp - BitVec.ofNat 64 d).toNat = sp.toNat - d := by
  have h : (BitVec.ofNat 64 d).toNat = d := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h]; omega), h]

private theorem stackRange {sp : BitVec 64} (depth : 336 ≤ sp.toNat) {d : Nat}
    (hl : 8 ≤ d) (hu : d ≤ 336) :
    InRegions [⟨sp.toNat - 336, 336⟩] (sp - BitVec.ofNat 64 d) 8 := by
  have hs := sp.isLt
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [InRegion, stackAddress sp depth hu]
  omega

private theorem stackStore {m : Ram} (depth : 336 ≤ sp.toNat)
    (area : Writable Extracted.programImage m (sp - 336) 336)
    (d off len : Nat) (hl : 8 ≤ d) (hu : d ≤ 336) (fits : off + len ≤ bytes_l1218e9.length) :
    StoreOk Extracted.programImage m (sp - BitVec.ofNat 64 d) 8
      (0x1218e9 + BitVec.ofNat 64 off) len := by
  have addr := stackAddress sp depth hu
  have base := stackAddress sp depth (d := 336) (by decide)
  change (sp - 336).toNat = _ at base
  exact ParseSignature.storeOk_of_codeRange (area.sub (by omega) (by omega)) setupCode fits

private theorem hashOutside (call : Call entry original sp dst src initial input)
    {off : Nat} (hoff : off + 4 ≤ 32) :
    Outside [⟨sp.toNat - 336, 336⟩] (dst + BitVec.ofNat 64 off) 4 := by
  have lo := call.hashWritable.readable.low
  have depth := call.depth
  have sep := call.hashStack
  have addr : (dst + BitVec.ofNat 64 off).toNat = dst.toNat + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨by rw [addr]; omega, ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  simp only [addr]
  omega

private theorem hashLoad (call : Call entry original sp dst src initial input)
    {m : Ram} (wf : RamWriteFrame original m [⟨sp.toNat - 336, 336⟩])
    (off : Nat) (hoff : off + 4 ≤ 32) :
    LoadOk m (dst + BitVec.ofNat 64 off) 4 :=
  LoadOk.of_offsets (call.hashWritable.readable.of_frame wf) rfl (addr_self dst)
    (by change (BitVec.ofNat 64 off - 0#64).toNat + 4 ≤ 32
        rw [BitVec.sub_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact hoff)

private theorem hashWord (call : Call entry original sp dst src initial input)
    {m : Ram} (wf : RamWriteFrame original m [⟨sp.toNat - 336, 336⟩])
    (i : Nat) (hi : i < 8) :
    ((memLoad m (wordAddr dst 32 i) 32).setWidth 64).setWidth 32 = initial[i]!.toBitVec := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, wf.memLoad_eq (hashOutside call (off := 4 * i) (by omega))]
  simpa only [Vector.getElem_ofFn] using call.state.2 i hi

set_option maxHeartbeats 600000 in
theorem setup (call : Call entry original sp dst src initial input) (pos : 0 < input.size / 64) :
    ∃ args mem, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l1218e0, entry, original⟩, []⟩ ⟨⟨.l121930, args, mem⟩, []⟩ ∧
      LoopState entry original sp dst src (input.size / 64) 0 initial args mem := by
  let count := input.size / 64
  have lo := call.inputReadable.low
  have nonzero : entry[2].get 64 ≠ 0 := by
    rw [call.rdx]
    intro h
    have h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
    change input.size / 64 = 0 at h'
    omega
  have branch : ∃ next : CFG.Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l1218e0, entry, original⟩ =
        .jump ⟨.l1218e9, next, original⟩ ∧
      next[4].get 64 = sp ∧ next[7].get 64 = dst ∧ next[6].get 64 = src ∧
      next[2].get 64 = BitVec.ofNat 64 count ∧
      (∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
        next[i] = entry[i]) := by
    refine ⟨?_, ?step, ?post⟩
    case step =>
      cfg_eval [testFlags, BitVec.and_self, beq_iff_eq, nonzero]
      rfl
    case post =>
      refine ⟨call.rsp, call.rdi, call.rsi, call.rdx, ?_⟩
      rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h | h | h | h <;> subst i <;> rfl
  obtain ⟨next, branch, rsp, rdi, rsi, rdx, same⟩ := branch
  have saved (i : Fin Reg.count) (hi : i.val ∈ [3, 5, 12, 13, 14, 15]) :
      next[i].get 64 = entry[i].get 64 :=
    congrArg (Value.get 64) (same i (List.mem_append_left [22, 39, 50, 51] hi))
  let limit := src + BitVec.ofNat 64 (64 * count)
  let m1 := memStore original (sp - 8) (entry[5].get 64)
  let m2 := memStore m1 (sp - 16) (entry[15].get 64)
  let m3 := memStore m2 (sp - 24) (entry[14].get 64)
  let m4 := memStore m3 (sp - 32) (entry[13].get 64)
  let m5 := memStore m4 (sp - 40) (entry[12].get 64)
  let m6 := memStore m5 (sp - 48) (entry[3].get 64)
  let m7 := memStore m6 (sp - 136) limit
  let m8 := memStore m7 (sp - 144) dst
  let region : MemoryRegion := ⟨sp.toNat - 336, 336⟩
  have f0 := RamWriteFrame.refl original [region]
  have f1 : RamWriteFrame original m1 [region] := f0.memStore _ (stackRange call.depth (d := 8) (by decide) (by decide))
  have f2 : RamWriteFrame original m2 [region] := f1.memStore _ (stackRange call.depth (d := 16) (by decide) (by decide))
  have f3 : RamWriteFrame original m3 [region] := f2.memStore _ (stackRange call.depth (d := 24) (by decide) (by decide))
  have f4 : RamWriteFrame original m4 [region] := f3.memStore _ (stackRange call.depth (d := 32) (by decide) (by decide))
  have f5 : RamWriteFrame original m5 [region] := f4.memStore _ (stackRange call.depth (d := 40) (by decide) (by decide))
  have f6 : RamWriteFrame original m6 [region] := f5.memStore _ (stackRange call.depth (d := 48) (by decide) (by decide))
  have f7 : RamWriteFrame original m7 [region] := f6.memStore _ (stackRange call.depth (d := 136) (by decide) (by decide))
  have f8 : RamWriteFrame original m8 [region] := f7.memStore _ (stackRange call.depth (d := 144) (by decide) (by decide))
  have guard {m : Ram} (f : RamWriteFrame original m [region])
      (d off len : Nat) (hl : 8 ≤ d) (hu : d ≤ 336) (fits : off + len ≤ bytes_l1218e9.length) :=
    stackStore call.depth (call.stackWritable.of_frame f) d off len hl hu fits
  have g1 : StoreOk Extracted.programImage original (sp - 8) 8 0x1218e9 1 :=
    guard f0 8 0 1 (by decide) (by decide) (by decide)
  have g2 : StoreOk Extracted.programImage m1 (sp - 16) 8 0x1218ea 2 :=
    guard f1 16 1 2 (by decide) (by decide) (by decide)
  have g3 : StoreOk Extracted.programImage m2 (sp - 24) 8 0x1218ec 2 :=
    guard f2 24 3 2 (by decide) (by decide) (by decide)
  have g4 : StoreOk Extracted.programImage m3 (sp - 32) 8 0x1218ee 2 :=
    guard f3 32 5 2 (by decide) (by decide) (by decide)
  have g5 : StoreOk Extracted.programImage m4 (sp - 40) 8 0x1218f0 2 :=
    guard f4 40 7 2 (by decide) (by decide) (by decide)
  have g6 : StoreOk Extracted.programImage m5 (sp - 48) 8 0x1218f2 1 :=
    guard f5 48 9 1 (by decide) (by decide) (by decide)
  have g7 : StoreOk Extracted.programImage m6 (sp - 136) 8 0x121904 8 :=
    guard f6 136 27 8 (by decide) (by decide) (by decide)
  have g8 : StoreOk Extracted.programImage m7 (sp - 144) 8 0x121924 8 :=
    guard f7 144 59 8 (by decide) (by decide) (by decide)
  have l0 : LoadOk m7 dst 4 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hashLoad call f7 0 (by decide)
  have l1 : LoadOk m7 (dst + 4) 4 := hashLoad call f7 4 (by decide)
  have l2 : LoadOk m7 (dst + 8) 4 := hashLoad call f7 8 (by decide)
  have l3 : LoadOk m7 (dst + 12) 4 := hashLoad call f7 12 (by decide)
  have l4 : LoadOk m7 (dst + 16) 4 := hashLoad call f7 16 (by decide)
  have l5 : LoadOk m7 (dst + 20) 4 := hashLoad call f7 20 (by decide)
  have l6 : LoadOk m7 (dst + 24) 4 := hashLoad call f7 24 (by decide)
  have l7 : LoadOk m8 (dst + 28) 4 := hashLoad call f8 28 (by decide)
  have shift : BitVec.ofNat 64 count <<< (6 : Nat) = BitVec.ofNat 64 (64 * count) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 count * BitVec.ofNat 64 64 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  have shifted : BitVec.ofNat 64 count <<< (6 : Nat) + src = limit := by
    rw [shift, BitVec.add_comm]
  have rsp192 : (sp - 336) + 192 = sp - 144 := by bv_omega
  have rsp200 : (sp - 336) + 200 = sp - 136 := by bv_omega
  have run : ∃ args,
      program.runBlock (dialect Extracted.programImage) ⟨.l1218e9, next, original⟩ =
        .jump ⟨.l121930, args, m8⟩ ∧
      LoopState entry original sp dst src count 0 initial args m8 := by
    refine ⟨?_, ?step, ?post⟩
    case step =>
      have s1 : next[5].get 64 = entry[5].get 64 := saved 5 (by decide)
      have s2 : next[15].get 64 = entry[15].get 64 := saved 15 (by decide)
      have s3 : next[14].get 64 = entry[14].get 64 := saved 14 (by decide)
      have s4 : next[13].get 64 = entry[13].get 64 := saved 13 (by decide)
      have s5 : next[12].get 64 = entry[12].get 64 := saved 12 (by decide)
      have s6 : next[3].get 64 = entry[3].get 64 := saved 3 (by decide)
      cfg_eval [rsp, rdi, rsi, rdx, s1, s2, s3, s4, s5, s6, shifted]
      rw [ite_eq_left g1, ite_eq_left g2, ite_eq_left g3, ite_eq_left g4, ite_eq_left g5, ite_eq_left g6, ite_eq_left g7,
        ite_eq_left l0, ite_eq_left l1, ite_eq_left l2, ite_eq_left l3, ite_eq_left l4, ite_eq_left l5, ite_eq_left l6,
        ite_eq_left g8, ite_eq_left l7]
    case post =>
      refine ⟨rfl, ?_, call.state.1, ?_, f8, ?_, ?_, ?_, ?_⟩
      · change next[6].get 64 = src + 0#64
        rw [BitVec.add_zero, rsi]
      · rintro ⟨i, hi⟩
        have index : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
        rcases index with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · have word := hashWord call f7 0 (by decide)
          change ((memLoad m7 (dst + 0#64) 32).setWidth 64).setWidth 32 = _ at word
          rw [BitVec.add_zero] at word
          exact word
        · exact hashWord call f7 1 (by decide)
        · exact hashWord call f7 2 (by decide)
        · exact hashWord call f7 3 (by decide)
        · exact hashWord call f7 4 (by decide)
        · exact hashWord call f7 5 (by decide)
        · exact hashWord call f7 6 (by decide)
        · exact hashWord call f8 7 (by decide)
      · rw [rsp192]
        exact memLoad_memStore_same _ _ _ (by decide) (by decide)
      · rw [rsp200]
        change memLoad (memStore m7 (sp - 144) dst) (sp - 136) 64 = limit
        rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          apply RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _)
          decide)]
        exact memLoad_memStore_same _ _ _ (by decide) (by decide)
      · have slots :
            memLoad m8 (sp - 48) 64 = entry[3].get 64 ∧
            memLoad m8 (sp - 8) 64 = entry[5].get 64 ∧
            memLoad m8 (sp - 40) 64 = entry[12].get 64 ∧
            memLoad m8 (sp - 32) 64 = entry[13].get 64 ∧
            memLoad m8 (sp - 24) 64 = entry[14].get 64 ∧
            memLoad m8 (sp - 16) 64 = entry[15].get 64 := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals
            simp (disch := first | decide | (apply RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _); decide))
              only [m8, m7, m6, m5, m4, m3, m2, m1, memLoad_memStore_same, memLoad_memStore_of_rangeApart]
        obtain ⟨slot3, slot5, slot12, slot13, slot14, slot15⟩ := slots
        rintro ⟨i, hi⟩
        have index : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
        rcases index with rfl | rfl | rfl | rfl | rfl | rfl
        · exact slot3
        · exact slot5
        · exact slot12
        · exact slot13
        · exact slot14
        · exact slot15
      · rintro ⟨i, hi⟩ h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl
        · exact same 22 (by decide)
        · exact same 39 (by decide)
        · exact same 50 (by decide)
        · exact same 51 (by decide)
  obtain ⟨args, jump, ready⟩ := run
  exact ⟨args, m8, .step (congrArg (Transfer.next _ []) branch)
    (.step (congrArg (Transfer.next _ []) jump) (.refl _)), ready⟩

end K256.Proofs.Verify.Hash.Compression
