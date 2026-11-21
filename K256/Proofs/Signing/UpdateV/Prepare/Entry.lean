import K256.Proofs.Signing.UpdateV.State
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.SignatureRun
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Signing.UpdateV

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2 K256.Proofs.Verify.Hash

private def padSetup (fr : Activation) : Ram :=
  let m := memStore fr.original (fr.rsp - 8) fr.rbp
  let m := memStore m (fr.rsp - 16) fr.r15
  let m := memStore m (fr.rsp - 24) fr.r14
  let m := memStore m (fr.rsp - 32) fr.r13
  let m := memStore m (fr.rsp - 40) fr.r12
  let m := memStore m (fr.rsp - 48) fr.rbx
  let m := memStore m (fr.rsp - 160) (0 : BitVec 64)
  let m := memStore m (fr.rsp - 168) (0 : BitVec 64)
  let m := memStore m (fr.rsp - 176) (0 : BitVec 64)
  memStore m (fr.rsp - 184) (0 : BitVec 64)

private def padMemory (fr : Activation) : Ram :=
  let m := memStore (padSetup fr) (fr.rsp - 480) (memLoad (padSetup fr) fr.rdi 64)
  let m := memStore m (fr.rsp - 472) (memLoad (padSetup fr) (fr.rdi + 8) 64)
  let m := memStore m (fr.rsp - 464) (memLoad (padSetup fr) (fr.rdi + 16) 64)
  let m := memStore m (fr.rsp - 456) (memLoad (padSetup fr) (fr.rdi + 24) 64)
  let m := memStore m (fr.rsp - 448) (0 : BitVec 64)
  let m := memStore m (fr.rsp - 440) (0 : BitVec 64)
  let m := memStore m (fr.rsp - 432) (0 : BitVec 64)
  memStore m (fr.rsp - 424) (0 : BitVec 64)

private theorem stackApart (sp d e : BitVec 64)
    (h : 8 ≤ (d - e).toNat ∧ 8 ≤ (e - d).toNat) :
    RangeApart (sp - d) 8 (sp - e) 8 := by
  apply RangeApart.of_diff
  rwa [show sp - e - (sp - d) = d - e by bv_omega,
    show sp - d - (sp - e) = e - d by bv_omega]

private theorem storeGuard {m : Ram} {sp pc d : BitVec 64} {len : Nat}
    (area : Writable Extracted.programImage m (sp - 1200) 1200)
    (bound : ((0 - d) - (0 - 1200)).toNat + 8 ≤ 1200)
    (text : (pc - 0x104970).toNat + len ≤ bytes_l104970.length) :
    StoreOk Extracted.programImage m (sp - d) 8 pc len := by
  have write := area.of_offsets (addr_sub sp d) (addr_sub _ _) bound
  have h := ParseSignature.storeOk_of_codeRange write
    (fun x hx => Common.fnCode_subset_programImage x (code_l104970 x hx)) text
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, show (0x104970 : BitVec 64) + (pc - 0x104970) = pc by bv_omega] at h

private def padWords (fr : Activation) : Vector (BitVec 64) 8 :=
  Vector.ofFn fun i => if i.val < 4 then
    memLoad (padSetup fr) (fr.rdi + BitVec.ofNat 64 (8 * i.val)) 64 else 0

private theorem padMemoryWords (fr : Activation) :
    WordsAt (padMemory fr) (fr.rsp - 480) 64 (padWords fr) := by
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := first | exact stackApart _ _ _ (by decide) | decide) only
      [wordAddr, padWords, Vector.getElem_ofFn, padMemory, Nat.reduceDiv, Nat.reduceMul,
        Nat.reduceLT, BitVec.add_zero, Lift.reduceAddOffset,
        ↓reduceIte, memLoad_memStore_same, memLoad_memStore_of_rangeApart] <;> rfl

private theorem padMemoryBytes {fr : Activation} {key : ByteArray}
    (keyAt : (⟨fr.rdi.toNat, 32⟩ : MemoryRegion).HasBytes fr.original key)
    (source : ∀ d : Nat, d + 8 ≤ 32 →
      memLoad (padSetup fr) (fr.rdi + BitVec.ofNat 64 d) 64 =
        memLoad fr.original (fr.rdi + BitVec.ofNat 64 d) 64)
    (readable : Readable (padMemory fr) (fr.rsp - 480) 64) :
    (⟨(fr.rsp - 480).toNat, 64⟩ : MemoryRegion).HasBytes (padMemory fr) (keyPad key 0) := by
  have size := keyPad_size key 0
  have h := (padMemoryWords fr).hasBytes readable size (by
    intro i hi hw
    have keySize : key.size = 32 := keyAt.1
    simp only [Nat.reduceDiv] at hw
    rw [keyPad_getElem key 0 i (by omega), UInt8.xor_zero, padWords, Vector.getElem_ofFn]
    by_cases h : i < 32
    · have keyBound : i < key.size := by omega
      rw [ite_eq_left (show i / 8 < 4 by omega), Array.getElem?_eq_getElem keyBound, Option.getD_some]
      change key[i] = storedByte
        (memLoad (padSetup fr) (fr.rdi + BitVec.ofNat 64 (8 * (i / 8))) 64) (i % 8)
      rw [source _ (by omega), storedByte_memLoad _ _ _ (Nat.mod_lt _ (by decide))]
      have address :
          fr.rdi + BitVec.ofNat 64 (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) =
            BitVec.ofNat 64 (fr.rdi.toNat + i) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod, BitVec.ofNat_add,
          BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [address]
      exact (congrArg (fun b => b.getD 0) (keyAt.2 ⟨i, keyBound⟩)).symm
    · rw [ite_eq_right (show ¬ i / 8 < 4 by omega),
        Array.getElem?_eq_none (show key.size ≤ i by omega), storedByte_eq_extract]
      change (0 : UInt8) = UInt8.ofBitVec ((0#64).extractLsb' (8 * (i % 8)) 8)
      rw [BitVec.extractLsb'_zero]
      rfl)
  simpa only [size] using h

set_option maxRecDepth 4096 in
private theorem padEntryRun {fr : Activation} {a : Values Value Reg.count}
    (area : Writable Extracted.programImage fr.original (fr.rsp - 1200) 1200)
    (read0 : LoadOk (padSetup fr) fr.rdi 8)
    (read8 : LoadOk (padSetup fr) (fr.rdi + 8) 8)
    (read16 : LoadOk (padSetup fr) (fr.rdi + 16) 8)
    (read24 : LoadOk (padSetup fr) (fr.rdi + 24) 8)
    (getSp : a[4].get 64 = fr.rsp) (getBp : a[5].get 64 = fr.rbp)
    (getBx : a[3].get 64 = fr.rbx) (getDi : a[7].get 64 = fr.rdi)
    (get12 : a[12].get 64 = fr.r12) (get13 : a[13].get 64 = fr.r13)
    (get14 : a[14].get 64 = fr.r14) (get15 : a[15].get 64 = fr.r15) :
    ∃ b, program.runBlock (dialect Extracted.programImage)
      ⟨.l104970, a, fr.original⟩ = .jump ⟨.l104a00, b, padMemory fr⟩ ∧
      b[0] = ⟨64, 3⟩ ∧ b[4] = ⟨64, fr.rsp - 488⟩ ∧ b[3] = ⟨64, fr.rdi⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,7,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i]) := by
  refine ⟨?_, ?run, ?regs⟩
  case run =>
    unfold padSetup at read0 read8 read16 read24
    cfg_eval [getSp, getBp, getBx, getDi, get12, get13, get14, get15]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first
      | with_reducible exact read0
      | with_reducible exact read8
      | with_reducible exact read16
      | with_reducible exact read24
      | exact storeGuard (by
          repeat' (with_reducible first
            | apply Writable.memStore
            | exact area)) (by decide) (by decide +kernel))
    unfold padMemory padSetup
    rfl
  case regs =>
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 260000 in
theorem padEntry {fr : Activation} {a : Values Value Reg.count} {key : ByteArray}
    (entry : Atom.All Extracted.programImage a fr.original (Fn104970.frameAt .l104970 fr))
    (low : fr.low = fr.rsp - 1200) (depth : 1200 ≤ fr.rsp.toNat)
    (limit : fr.rsp.toNat + 8 < 2^32)
    (dataLow : fr.rdi.toNat + 64 < 2^32)
    (apart : fr.rdi.toNat + 64 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (writable : Writable Extracted.programImage fr.original fr.rdi 64)
    (k : (⟨fr.rdi.toNat, 32⟩ : MemoryRegion).HasBytes fr.original key) :
    ∃ b t, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l104970, a, fr.original⟩, []⟩ ⟨⟨.l104a00, b, t⟩, []⟩ ∧
      Atom.All Extracted.programImage b t (Fn104970.frameAt .l104a00 fr) ∧
      RamWriteFrame fr.original t [fr.region] ∧
      b[0] = ⟨64, 3⟩ ∧ (⟨(fr.rsp - 488 + 8).toNat, 64⟩ : MemoryRegion).HasBytes t (keyPad key 0) := by
  simp only [Fn104970.frameAt, Fn104970.frameAtG5, Atom.All, Atom.Holds] at entry
  obtain ⟨sp, df, _, _, bx, bp, _, di, r8, r9, r12, r13, r14, r15, mx, ft, fc,
    retR, retM, retL, area, space, align, memcpyR, memcpyM, memsetR, memsetM, got⟩ := entry
  have addr (d : Nat) (hd : d ≤ 1200) :
      (fr.rsp - BitVec.ofNat 64 d).toNat = fr.rsp.toNat - d := by
    have h : (BitVec.ofNat 64 d).toNat = d := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h]; omega)), h]
  have lowNat : fr.low.toNat = fr.rsp.toNat - 1200 := by rw [low]; exact addr 1200 (by decide)
  have inside (d : Nat) (hd : 8 ≤ d) (hd' : d ≤ 1200) :
      InRegions [fr.region] (fr.rsp - BitVec.ofNat 64 d) 8 := by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change fr.low.toNat ≤ _ ∧ _ + 8 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ∧ _ + 8 ≤ 2^64
    rw [addr d hd', lowNat]
    omega
  have outside {p : BitVec 64} (hl : p.toNat + 8 ≤ 2^64)
      (sep : p.toNat + 8 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ p.toNat) :
      Outside [fr.region] p 8 := by
    refine ⟨hl, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change p.toNat + 8 ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ p.toNat
    omega
  have setupFrame : RamWriteFrame fr.original (padSetup fr) [fr.region] := by
    have step1 := (RamWriteFrame.refl fr.original [fr.region]).memStore fr.rbp (inside 8 (by decide) (by decide))
    have step2 := step1.memStore fr.r15 (inside 16 (by decide) (by decide))
    have step3 := step2.memStore fr.r14 (inside 24 (by decide) (by decide))
    have step4 := step3.memStore fr.r13 (inside 32 (by decide) (by decide))
    have step5 := step4.memStore fr.r12 (inside 40 (by decide) (by decide))
    have step6 := step5.memStore fr.rbx (inside 48 (by decide) (by decide))
    have step7 := step6.memStore (0 : BitVec 64) (inside 160 (by decide) (by decide))
    have step8 := step7.memStore (0 : BitVec 64) (inside 168 (by decide) (by decide))
    have step9 := step8.memStore (0 : BitVec 64) (inside 176 (by decide) (by decide))
    exact step9.memStore (0 : BitVec 64) (inside 184 (by decide) (by decide))
  have frame : RamWriteFrame fr.original (padMemory fr) [fr.region] := by
    have step1 := setupFrame.memStore (memLoad (padSetup fr) fr.rdi 64) (inside 480 (by decide) (by decide))
    have step2 := step1.memStore (memLoad (padSetup fr) (fr.rdi + 8) 64) (inside 472 (by decide) (by decide))
    have step3 := step2.memStore (memLoad (padSetup fr) (fr.rdi + 16) 64) (inside 464 (by decide) (by decide))
    have step4 := step3.memStore (memLoad (padSetup fr) (fr.rdi + 24) 64) (inside 456 (by decide) (by decide))
    have step5 := step4.memStore (0 : BitVec 64) (inside 448 (by decide) (by decide))
    have step6 := step5.memStore (0 : BitVec 64) (inside 440 (by decide) (by decide))
    have step7 := step6.memStore (0 : BitVec 64) (inside 432 (by decide) (by decide))
    exact step7.memStore (0 : BitVec 64) (inside 424 (by decide) (by decide))
  have srcAddr (d : Nat) (hd : d ≤ 64) :
      (fr.rdi + BitVec.ofNat 64 d).toNat = fr.rdi.toNat + d := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have srcLoad (d : Nat) (hd : d + 8 ≤ 32) :
      memLoad (padSetup fr) (fr.rdi + BitVec.ofNat 64 d) 64 =
        memLoad fr.original (fr.rdi + BitVec.ofNat 64 d) 64 := by
    apply setupFrame.memLoad_eq
    apply outside <;> rw [srcAddr d (by omega)] <;> omega
  have source := writable.readable.of_frame setupFrame
  have read (d : Nat) (hd : d + 8 ≤ 64) :
      LoadOk (padSetup fr) (fr.rdi + BitVec.ofNat 64 d) 8 := by
    apply LoadOk.of_region source <;> rw [srcAddr d (by omega)] <;> omega
  have read0 : LoadOk (padSetup fr) fr.rdi 8 :=
    LoadOk.of_region source (Nat.le_refl _) (by omega)
  have read8 := read 8 (by decide)
  have read16 := read 16 (by decide)
  have read24 := read 24 (by decide)
  have getSp : a[4].get 64 = fr.rsp := congrArg (Value.get 64) sp
  have getBp : a[5].get 64 = fr.rbp := congrArg (Value.get 64) bp
  have getBx : a[3].get 64 = fr.rbx := congrArg (Value.get 64) bx
  have getDi : a[7].get 64 = fr.rdi := congrArg (Value.get 64) di
  have get12 : a[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
  have get13 : a[13].get 64 = fr.r13 := congrArg (Value.get 64) r13
  have get14 : a[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have get15 : a[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
  obtain ⟨b, jump, regs⟩ :=
    padEntryRun area read0 read8 read16 read24 getSp getBp getBx getDi get12 get13 get14 get15
  have kept (i : Fin Reg.count) (hi : i.val ∈ [5,7,8,9,12,13,14,15,22,39,50,51]) :
      b[i] = a[i] := regs.2.2.2 i hi
  refine ⟨b, padMemory fr, .single (congrArg (Transfer.next _ []) jump), ?atoms, frame, regs.1, ?pad⟩
  case atoms =>
    have preserved {p : BitVec 64} (h : Outside [fr.region] p 8) :
        memLoad (padMemory fr) p 64 = memLoad fr.original p 64 := frame.memLoad_eq h
    have gotApart := got.1
    have outsideMemcpy : Outside [fr.region] (0x203dd0 : BitVec 64) 8 :=
      outside (by decide) (by
        change 0x203dd8 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ 0x203dd0
        omega)
    have outsideMemset : Outside [fr.region] (0x203e10 : BitVec 64) 8 :=
      outside (by decide) (by
        change 0x203e18 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ 0x203e10
        omega)
    obtain ⟨saved48, saved40, saved32, saved24, saved16, saved8⟩ :
        memLoad (padMemory fr) (fr.rsp - 48) 64 = fr.rbx ∧
        memLoad (padMemory fr) (fr.rsp - 40) 64 = fr.r12 ∧
        memLoad (padMemory fr) (fr.rsp - 32) 64 = fr.r13 ∧
        memLoad (padMemory fr) (fr.rsp - 24) 64 = fr.r14 ∧
        memLoad (padMemory fr) (fr.rsp - 16) 64 = fr.r15 ∧
        memLoad (padMemory fr) (fr.rsp - 8) 64 = fr.rbp := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals
        simp (disch := first | exact stackApart _ _ _ (by decide) | decide) only
          [padMemory, padSetup, memLoad_memStore_same, memLoad_memStore_of_rangeApart]
    simp only [Fn104970.frameAt, Fn104970.frameAtG5, Atom.All, Atom.Holds]
    exact ⟨regs.2.1, (kept 22 (by decide)).trans df, regs.2.2.1,
      (kept 5 (by decide)).trans bp, (kept 7 (by decide)).trans di, (kept 8 (by decide)).trans r8,
      (kept 9 (by decide)).trans r9, (kept 12 (by decide)).trans r12, (kept 13 (by decide)).trans r13,
      (kept 14 (by decide)).trans r14, (kept 15 (by decide)).trans r15,
      (kept 39 (by decide)).trans mx, (kept 50 (by decide)).trans ft, (kept 51 (by decide)).trans fc,
      saved48, saved40, saved32, saved24, saved16, saved8, retR.of_frame frame,
      (preserved (outside (by omega) (Or.inr (Nat.le_refl _)))).trans retM,
      retL, area.of_frame frame, space, align, memcpyR.of_frame frame,
      (preserved outsideMemcpy).trans memcpyM, memsetR.of_frame frame,
      (preserved outsideMemset).trans memsetM, got⟩
  case pad =>
    rw [show fr.rsp - 488 + 8 = fr.rsp - 480 by bv_omega]
    exact padMemoryBytes k srcLoad
      ((area.of_frame frame).readable.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))

end K256.Proofs.Signing.UpdateV
