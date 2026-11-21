import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.State
import K256.Proofs.Signing.Nonce.Initialize.Update.Memory
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.SignatureRun
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Prepare

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

private def writeWords (m : Ram) (stores : List (BitVec 64 × BitVec 64)) : Ram :=
  stores.foldl (fun n (p, w) => memStore n p w) m

private theorem writeWords_frame {m n : Ram} {regions : List MemoryRegion}
    (frame : RamWriteFrame m n regions) {stores : List (BitVec 64 × BitVec 64)}
    (inside : ∀ p ∈ stores.map Prod.fst, InRegions regions p 8) :
    RamWriteFrame m (writeWords n stores) regions := by
  induction stores generalizing n with
  | nil => exact frame
  | cons store stores ih =>
    exact ih (frame.memStore store.2 (inside _ (List.mem_cons_self)))
      (fun p hp => inside p (List.mem_cons_of_mem _ hp))

private def saveRegs (fr : Activation) (m : Ram) : Ram :=
  writeWords m [(fr.rsp - 8, fr.rbp), (fr.rsp - 16, fr.r15), (fr.rsp - 24, fr.r14),
    (fr.rsp - 32, fr.r13), (fr.rsp - 40, fr.r12), (fr.rsp - 48, fr.rbx)]

private def clearContext (fr : Activation) (m : Ram) : Ram :=
  writeWords m [(fr.rsp - 160, 0), (fr.rsp - 168, 0), (fr.rsp - 176, 0), (fr.rsp - 184, 0)]

private def writePad (m : Ram) (src dst : BitVec 64) : Ram :=
  writeWords m [(dst, memLoad m src 64), (dst + 8, memLoad m (src + 8) 64),
    (dst + 16, memLoad m (src + 16) 64), (dst + 24, memLoad m (src + 24) 64),
    (dst + 32, 0), (dst + 40, 0), (dst + 48, 0), (dst + 56, 0)]

private def beforePad (fr : Activation) (m : Ram) (second : Bool) : Ram :=
  clearContext fr (if second then m else saveRegs fr m)

private def afterPad (fr : Activation) (m : Ram) (second : Bool) : Ram :=
  writePad (beforePad fr m second) fr.rdi (pad fr second)

private theorem stackStore {m : Ram} {rsp d pc base : BitVec 64} {len : Nat} {codeBytes : List UInt8}
    (area : Writable Extracted.programImage m (rsp - 1920) 1920)
    (text : ∀ x ∈ codeRange base codeBytes, x ∈ fnCode)
    (bound : ((0 - d) - (0 - 1920)).toNat + 8 ≤ 1920)
    (within : (pc - base).toNat + len ≤ codeBytes.length) :
    StoreOk Extracted.programImage m (rsp - d) 8 pc len := by
  have write := area.of_offsets (addr_sub rsp d) (addr_sub _ _) bound
  have h := ParseSignature.storeOk_of_codeRange write
    (fun x hx => Common.fnCode_subset_programImage x (text x hx)) within
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, show base + (pc - base) = pc by bv_omega] at h

private theorem stackApart (rsp d e : BitVec 64)
    (h : 8 ≤ (d - e).toNat ∧ 8 ≤ (e - d).toNat) :
    RangeApart (rsp - d) 8 (rsp - e) 8 := by
  apply RangeApart.of_diff
  rwa [show rsp - e - (rsp - d) = d - e by bv_omega,
    show rsp - d - (rsp - e) = e - d by bv_omega]

private theorem padWords (m : Ram) (src dst : BitVec 64) :
    WordsAt (writePad m src dst) dst 64
      (Vector.ofFn fun i : Fin 8 =>
        if i.val < 4 then memLoad m (src + BitVec.ofNat 64 (8 * i.val)) 64 else 0) := by
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch :=
      first
      | apply RangeApart.of_offsets rfl rfl; decide
      | apply RangeApart.of_offsets (addr_self _) rfl; decide
      | apply RangeApart.of_offsets rfl (addr_self _); decide
      | decide) only [wordAddr, Vector.getElem_ofFn, writePad, writeWords, List.foldl, Nat.reduceDiv,
        Nat.reduceMul, Nat.reduceLT, BitVec.ofNat_eq_ofNat, BitVec.add_zero, ↓reduceIte, memLoad_memStore_same,
        memLoad_memStore_of_rangeApart] <;> rfl

private theorem padBytes {m : Ram} {src dst : BitVec 64} {key : ByteArray}
    (keyAt : (⟨src.toNat, 32⟩ : MemoryRegion).HasBytes m key)
    (readable : Readable (writePad m src dst) dst 64) :
    (⟨dst.toNat, 64⟩ : MemoryRegion).HasBytes (writePad m src dst) (UpdateV.keyPad key 0) := by
  have size := UpdateV.keyPad_size key 0
  have h := (padWords m src dst).hasBytes readable size (by
    intro i hi hw
    have keySize : key.size = 32 := keyAt.1
    rw [UpdateV.keyPad_getElem key 0 i (by omega), UInt8.xor_zero, Vector.getElem_ofFn]
    by_cases h : i < 32
    · have keyBound : i < key.size := by omega
      rw [ite_eq_left (show i / 8 < 4 by omega), Array.getElem?_eq_getElem keyBound, Option.getD_some]
      change key[i] = storedByte (memLoad m (src + BitVec.ofNat 64 (8 * (i / 8))) 64) (i % 8)
      rw [storedByte_memLoad _ _ _ (Nat.mod_lt _ (by decide))]
      have address :
          src + BitVec.ofNat 64 (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) =
            BitVec.ofNat 64 (src.toNat + i) := by
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
private theorem runEntry {fr : Activation} {a : Verify.Core.Registers} {m : Ram} (second : Bool)
    (area : Writable Extracted.programImage m (fr.rsp - 1920) 1920)
    (source : Readable (beforePad fr m second) fr.rdi 32)
    (atoms : Atom.All Extracted.programImage a m (Fn103f30.frameAt (start second) fr)) :
    ∃ b : Verify.Core.Registers, program.runBlock (dialect Extracted.programImage) ⟨start second, a, m⟩ =
      .jump ⟨head second false, b, afterPad fr m second⟩ ∧
      b[0] = ⟨64, 3⟩ ∧ b[4] = ⟨64, sp fr⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,7,8,9,12,13,22,39,50,51] → b[i] = a[i]) ∧
      (second = false → b[5] = ⟨64, fr.rdi⟩ ∧ b[14] = ⟨64, fr.rsi⟩ ∧ b[15] = ⟨64, fr.rdx⟩) ∧
      (second = true → b[5] = a[5] ∧ b[14] = a[14] ∧ b[15] = a[15]) := by
  have read0 : LoadOk (beforePad fr m second) fr.rdi 8 :=
    LoadOk.of_offsets source (addr_self _) (addr_self _) (by decide)
  have read8 : LoadOk (beforePad fr m second) (fr.rdi + 8) 8 :=
    LoadOk.of_offsets source rfl (addr_self _) (by decide)
  have read16 : LoadOk (beforePad fr m second) (fr.rdi + 16) 8 :=
    LoadOk.of_offsets source rfl (addr_self _) (by decide)
  have read24 : LoadOk (beforePad fr m second) (fr.rdi + 24) 8 :=
    LoadOk.of_offsets source rfl (addr_self _) (by decide)
  cases second
  · simp only [start, Fn103f30.frameAt, Fn103f30.frameAtG4, Atom.All, Atom.Holds, Bool.false_eq_true,
      ↓reduceIte] at atoms
    obtain ⟨spEq, _, _, dx, bx, bp, si, di, _, _, r12, r13, r14, r15, _⟩ := atoms
    have getSp : a[4].get 64 = fr.rsp := congrArg (Value.get 64) spEq
    have getBp : a[5].get 64 = fr.rbp := congrArg (Value.get 64) bp
    have getBx : a[3].get 64 = fr.rbx := congrArg (Value.get 64) bx
    have getDi : a[7].get 64 = fr.rdi := congrArg (Value.get 64) di
    have getSi : a[6].get 64 = fr.rsi := congrArg (Value.get 64) si
    have getDx : a[2].get 64 = fr.rdx := congrArg (Value.get 64) dx
    have get12 : a[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
    have get13 : a[13].get 64 = fr.r13 := congrArg (Value.get 64) r13
    have get14 : a[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
    have get15 : a[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
    refine ⟨?_, ?run, ?regs⟩
    case run =>
      change program.runBlock _ ⟨.l103f30, a, m⟩ = _
      simp only [beforePad, clearContext, saveRegs, writeWords, List.foldl, Bool.false_eq_true,
        ↓reduceIte] at read0 read8 read16 read24
      cfg_eval [getSp, getBp, getBx, getDi, getSi, getDx, get12, get13, get14, get15]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first
        | with_reducible exact read0
        | with_reducible exact read8
        | with_reducible exact read16
        | with_reducible exact read24
        | exact stackStore (by
            repeat' (with_reducible first
              | apply Writable.memStore
              | exact area)) code_l103f30 (by decide) (by decide +kernel))
      simp only [afterPad, beforePad, clearContext, saveRegs, writePad, writeWords, List.foldl,
        pad, sp, Bool.false_eq_true, ↓reduceIte, Lift.reduceAddOffset] <;> rfl
    case regs =>
      refine ⟨rfl, rfl, ?_, fun _ => ⟨rfl, rfl, rfl⟩, fun bad => by cases bad⟩
      intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [start, Fn103f30.frameAt, Fn103f30.frameAtG4, Atom.All, Atom.Holds, ↓reduceIte] at atoms
    obtain ⟨spEq, _, bx, _⟩ := atoms
    have getSp : a[4].get 64 = fr.rsp - 712 := congrArg (Value.get 64) spEq
    have getBx : a[3].get 64 = fr.rdi := congrArg (Value.get 64) bx
    refine ⟨?_, ?run, ?regs⟩
    case run =>
      change program.runBlock _ ⟨.l10438b, a, m⟩ = _
      simp only [beforePad, clearContext, writeWords, List.foldl, ↓reduceIte] at read0 read8 read16 read24
      cfg_eval [getSp, getBx]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first
        | with_reducible exact read0
        | with_reducible exact read8
        | with_reducible exact read16
        | with_reducible exact read24
        | exact stackStore (by
            repeat' (with_reducible first
              | apply Writable.memStore
              | exact area)) code_l10438b (by decide) (by decide +kernel))
      simp only [afterPad, beforePad, clearContext, writePad, writeWords, List.foldl, pad, sp,
        ↓reduceIte, Lift.reduceAddOffset] <;> rfl
    case regs =>
      refine ⟨rfl, spEq, ?_, (fun bad => by cases bad), fun _ => ⟨rfl, rfl, rfl⟩⟩
      intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem padAddress (fr : Activation) (second : Bool) :
    pad fr second = fr.rsp - (if second then 664 else 552) := by
  cases second <;> simp only [pad, sp, Bool.false_eq_true, ↓reduceIte, Lift.reduceAddOffset]

private theorem padFrames (fr : Activation) (m : Ram) (second : Bool)
    (inside : ∀ d : BitVec 64, 8 ≤ d.toNat → d.toNat ≤ 1920 →
      InRegions [fr.region] (fr.rsp - d) 8) :
    RamWriteFrame m (beforePad fr m second) [fr.region] ∧
    RamWriteFrame m (afterPad fr m second) [fr.region] := by
  have saved : RamWriteFrame m (if second then m else saveRegs fr m) [fr.region] := by
    cases second
    · change RamWriteFrame m (saveRegs fr m) _
      unfold saveRegs
      apply writeWords_frame (RamWriteFrame.refl m _)
      intro p hp
      simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact inside _ (by decide) (by decide)
    · exact RamWriteFrame.refl m _
  have prepared : RamWriteFrame m (beforePad fr m second) [fr.region] := by
    unfold beforePad clearContext
    apply writeWords_frame saved
    intro p hp
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> exact inside _ (by decide) (by decide)
  refine ⟨prepared, ?_⟩
  unfold afterPad writePad
  apply writeWords_frame prepared
  intro p hp
  simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases second <;>
    simp only [padAddress, Bool.false_eq_true, ↓reduceIte, Lift.reduceAddOffset] <;>
    exact inside _ (by decide) (by decide)

set_option maxRecDepth 4096 in
theorem enter {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (live : Live (start second) fr a m state) (slots : second = true → Slots fr m) :
    ∃ b n, Verify.Core.Reaches (start second) a m (head second false) b n ∧
      Live (head second false) fr b n state ∧ (second = true → Slots fr n) ∧
      b[0] = ⟨64, 3⟩ ∧
      (⟨(pad fr second).toNat, 64⟩ : MemoryRegion).HasBytes n (UpdateV.keyPad state.key 0) := by
  have depth := env.depth
  have limit := env.limit
  have base : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from depth)]
    rfl
  have inside (d : BitVec 64) (lo : 8 ≤ d.toNat) (hi : d.toNat ≤ 1920) :
      InRegions [fr.region] (fr.rsp - d) 8 := by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change fr.low.toNat ≤ _ ∧ _ + 8 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ∧ _ + 8 ≤ 2^64
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega)), base]
    omega
  obtain ⟨preFrame, frame⟩ := padFrames fr m second inside
  have extendsRegion : RegionsWithin [fr.region] [fr.region, ⟨fr.rdi.toNat,64⟩] := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  have writes := live.writes.trans frame extendsRegion
  have source : Readable (beforePad fr m second) fr.rdi 32 :=
    (env.writable.readable.of_frame (live.writes.trans preFrame extendsRegion)).sub
      (Nat.le_refl _) (by omega)
  obtain ⟨b, run, index, rsp, keep, firstRegs, secondRegs⟩ :=
    runEntry second (env.stack.of_frame live.writes) source live.atoms
  have readablePad : Readable (afterPad fr m second) (pad fr second) 64 := by
    cases second <;> rw [padAddress] <;>
      exact (env.stack.readable.of_frame writes).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have bytes : (⟨(pad fr second).toNat, 64⟩ : MemoryRegion).HasBytes
      (afterPad fr m second) (UpdateV.keyPad state.key 0) :=
    padBytes (env.stateAfter live.bytes preFrame).key readablePad
  have outside {p : BitVec 64} (bound : p.toNat + 8 ≤ 2^64)
      (sep : p.toNat + 8 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ p.toNat) :
      Outside [fr.region] p 8 := by
    refine ⟨bound, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change p.toNat + 8 ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ p.toNat
    omega
  have retMem := frame.memLoad_eq (k := 64) (outside (p := fr.rsp) (by omega) (Or.inr (Nat.le_refl _)))
  have gotMem (got : 0x204598 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0) :
      memLoad (afterPad fr m second) 0x203dd0 64 = memLoad m 0x203dd0 64 ∧
      memLoad (afterPad fr m second) 0x203e10 64 = memLoad m 0x203e10 64 := by
    constructor
    · apply frame.memLoad_eq
      exact outside (by decide) (by change 0x203dd8 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ 0x203dd0; omega)
    · apply frame.memLoad_eq
      exact outside (by decide) (by change 0x203e18 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ 0x203e10; omega)
  have widths : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → b[i].width = 64 := by
    intro ⟨i, valid⟩ hi
    have w := live.savedWidths ⟨i, valid⟩ hi
    simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (congrArg Value.width (keep 3 (by decide))).trans w
    · cases second
      · exact congrArg Value.width (firstRegs rfl).1
      · exact (congrArg Value.width (secondRegs rfl).1).trans w
    · exact (congrArg Value.width (keep 12 (by decide))).trans w
    · exact (congrArg Value.width (keep 13 (by decide))).trans w
    · cases second
      · exact congrArg Value.width (firstRegs rfl).2.1
      · exact (congrArg Value.width (secondRegs rfl).2.1).trans w
    · cases second
      · exact congrArg Value.width (firstRegs rfl).2.2
      · exact (congrArg Value.width (secondRegs rfl).2.2).trans w
  refine ⟨b, afterPad fr m second, .single (congrArg (Transfer.next _ []) run),
    ⟨?atoms, writes, env.stateAfter live.bytes frame, ?impossible, widths⟩, ?slots, index, bytes⟩
  case impossible =>
    cases second <;> intro impossible <;> cases impossible
  case atoms =>
    have atoms := live.atoms
    cases second
    · simp only [start, head, Fn103f30.frameAt, Fn103f30.frameAtG4, Atom.All, Atom.Holds,
        Bool.false_eq_true, ↓reduceIte] at atoms ⊢
      obtain ⟨_, df, _, _, bx, _, _, di, r8, r9, r12, r13, _, _, mx, ft, fc,
        retR, retM, retL, area, space, align, memcpyR, memcpyM, memsetR, memsetM, got⟩ := atoms
      obtain ⟨rbp, r14, r15⟩ := firstRegs rfl
      obtain ⟨s48, s40, s32, s24, s16, s8⟩ :
          memLoad (afterPad fr m false) (fr.rsp - 48) 64 = fr.rbx ∧
          memLoad (afterPad fr m false) (fr.rsp - 40) 64 = fr.r12 ∧
          memLoad (afterPad fr m false) (fr.rsp - 32) 64 = fr.r13 ∧
          memLoad (afterPad fr m false) (fr.rsp - 24) 64 = fr.r14 ∧
          memLoad (afterPad fr m false) (fr.rsp - 16) 64 = fr.r15 ∧
          memLoad (afterPad fr m false) (fr.rsp - 8) 64 = fr.rbp := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals
          simp (disch := first | exact stackApart _ _ _ (by decide) | decide) only
            [afterPad, beforePad, padAddress, clearContext, saveRegs, writePad, writeWords, List.foldl,
              Bool.false_eq_true, ↓reduceIte, Lift.reduceAddOffset,
              memLoad_memStore_same, memLoad_memStore_of_rangeApart]
      obtain ⟨memcpy, memset⟩ := gotMem got.1
      exact ⟨rsp, (keep 22 (by decide)).trans df, (keep 3 (by decide)).trans bx, rbp,
        (keep 7 (by decide)).trans di, (keep 8 (by decide)).trans r8, (keep 9 (by decide)).trans r9,
        (keep 12 (by decide)).trans r12, (keep 13 (by decide)).trans r13, r14, r15,
        (keep 39 (by decide)).trans mx, (keep 50 (by decide)).trans ft, (keep 51 (by decide)).trans fc,
        s48, s40, s32, s24, s16, s8, retR.of_frame frame, retMem.trans retM,
        retL, area.of_frame frame, space, align, memcpyR.of_frame frame,
        memcpy.trans memcpyM, memsetR.of_frame frame, memset.trans memsetM, got⟩
    · simp only [start, head, Fn103f30.frameAt, Fn103f30.frameAtG4, Atom.All, Atom.Holds,
        ↓reduceIte] at atoms ⊢
      obtain ⟨_, df, bx, r14, mx, ft, fc, _, s48, s40, s32, s24, s16, s8, retR, retM,
        retL, area, space, align, memcpyR, memcpyM, memsetR, memsetM, got⟩ := atoms
      have saved (d : BitVec 64) (which : d = 48 ∨ d = 40 ∨ d = 32 ∨ d = 24 ∨ d = 16 ∨ d = 8) :
          memLoad (afterPad fr m true) (fr.rsp - d) 64 = memLoad m (fr.rsp - d) 64 := by
        rcases which with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals
          simp (disch := first | exact stackApart _ _ _ (by decide) | decide) only
            [afterPad, beforePad, padAddress, clearContext, writePad, writeWords, List.foldl,
              ↓reduceIte, Lift.reduceAddOffset, memLoad_memStore_of_rangeApart]
      obtain ⟨memcpy, memset⟩ := gotMem got.1
      exact ⟨rsp, (keep 22 (by decide)).trans df, (keep 3 (by decide)).trans bx,
        (secondRegs rfl).2.1.trans r14, (keep 39 (by decide)).trans mx,
        (keep 50 (by decide)).trans ft, (keep 51 (by decide)).trans fc,
        (saved 48 (by decide)).trans s48, (saved 40 (by decide)).trans s40,
        (saved 32 (by decide)).trans s32, (saved 24 (by decide)).trans s24,
        (saved 16 (by decide)).trans s16, (saved 8 (by decide)).trans s8,
        retR.of_frame frame, retMem.trans retM, retL, area.of_frame frame, space, align,
        memcpyR.of_frame frame, memcpy.trans memcpyM, memsetR.of_frame frame, memset.trans memsetM, got⟩
  case slots =>
    intro h
    subst second
    obtain ⟨stop, value, stateSlot⟩ := slots rfl
    simp only [sp, Lift.reduceAddOffset] at stop value stateSlot
    constructor
    all_goals
      simp (disch := first | exact stackApart _ _ _ (by decide) | decide) only
        [afterPad, beforePad, padAddress, clearContext, writePad, writeWords, List.foldl, sp,
          ↓reduceIte, Lift.reduceAddOffset, memLoad_memStore_of_rangeApart]
      first
      | exact stop
      | exact value
      | exact stateSlot

end K256.Proofs.Signing.Nonce.Initialize.Update.Prepare
