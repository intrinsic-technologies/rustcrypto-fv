import AesGcm.Proofs.Machine.CTR.Outer.Invariant
import AesGcm.Proofs.Machine.CTR.Entry
import AesGcm.Proofs.Machine.CTR.KeySetup
import AesGcm.Proofs.Machine.CTR.CountSplit
import AesGcm.Proofs.Machine.CTR.BatchBegin
import AesGcm.Proofs.Machine.Runtime.Root.Memory
import AesGcm.Proofs.Machine.Runtime.StackGeometry

namespace AesGcm.Proofs.Machine.CTR

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.KeySchedule

private theorem prefix_jump {code : CodeMap} {loc next : LIR.lifted.Location}
    (h : LIR.program.runBlock (dialect code) loc = .jump next) :
    (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ := by
  apply Semantics.Reaches.single
  change Transfer.next (dialect code) [] (LIR.program.runBlock (dialect code) loc) = _
  rw [h]
  rfl

private theorem batch_prefix_branch (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (loc : LIR.lifted.Location)
    (sp destination : BitVec 64) (batches : Nat)
    (hlabel : loc.label = if batches = 0 then (if use256 then .l109509 else .l10805f)
      else (if use256 then .l1085da else .l10714a))
    (ht : GPRsTyped loc.arguments)
    (h4 : loc.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp⟩)
    (h2 : loc.arguments[2]'(by change 2 < 53; decide) = ⟨64, destination⟩)
    (hw : Writable code loc.store (sp + 216) 16) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      (next.label = if batches = 0 then (if use256 then .l109509 else .l10805f)
        else (if use256 then .l108e98 else .l107a08)) ∧
      GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [2,4,9,22,39,50,51] → next.arguments[r] = loc.arguments[r]) ∧
      RamWriteFrame loc.store next.store [span (sp + 216) 16] ∧
      (batches ≠ 0 → memLoad next.store (sp + 216) 64 = destination ∧
        memLoad next.store (sp + 224) 64 = 0) := by
  by_cases hz : batches = 0
  · exact ⟨loc, .refl _, by simpa only [hz, ↓reduceIte] using hlabel, ht,
      fun _ _ => rfl, .refl _ _, fun h => (h hz).elim⟩
  · obtain ⟨next, hj, hl, hm, hk, ht', hf⟩ :=
      batch_begin use256 code hcode loc.arguments loc.store sp destination ht
        (by rw [h4]; rfl) (by rw [h2]; rfl) hw
    have hs : (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ := by
      apply prefix_jump
      change LIR.program.runBlock (dialect code) ⟨loc.label, loc.arguments, loc.store⟩ = _
      rw [hlabel, ite_eq_right hz]
      exact hj
    refine ⟨next, hs, by simpa only [hz, ↓reduceIte] using hl, ht', ?_, hf, ?_⟩
    · intro r hr
      apply hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      omega
    · intro _
      rw [hm]
      constructor <;> runtime_finish []

private theorem entryMemory_saved (args : Values Value Reg.count) (mem : Ram) :
    let rsp := args[4].get 64
    let m := entryMemory args mem
    memLoad m (rsp - 48) 64 = args[3].get 64 ∧
    memLoad m (rsp - 40) 64 = args[12].get 64 ∧
    memLoad m (rsp - 32) 64 = args[13].get 64 ∧
    memLoad m (rsp - 24) 64 = args[14].get 64 ∧
    memLoad m (rsp - 16) 64 = args[15].get 64 ∧
    memLoad m (rsp - 8) 64 = args[5].get 64 := by
  have away (m : Ram) (a b v : BitVec 64)
      (h : 8 ≤ (b - a).toNat ∧ 8 ≤ (a - b).toNat) :=
    memLoad_memStore_apart m (args[4].get 64) a b v 64 h (by decide) (by decide)
  simp (disch := decide) only [entryMemory, BitVec.sub_eq_add_neg, away, memLoad_memStore_same,
    and_self]

set_option maxHeartbeats 3000000 in
theorem crypt_prefix (use256 : Bool) (code : CodeMap) (fr : Activation)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count)
    (hTypes : GPRsTyped args)
    (hArgs : args[4] = ⟨64, fr.rsp⟩ ∧ args[1] = ⟨64, fr.rcx⟩ ∧ args[2] = ⟨64, fr.rdx⟩ ∧
      args[3] = ⟨64, fr.rbx⟩ ∧ args[5] = ⟨64, fr.rbp⟩ ∧ args[6] = ⟨64, fr.rsi⟩ ∧
      args[7] = ⟨64, fr.rdi⟩ ∧ args[8] = ⟨64, fr.r8⟩ ∧ args[9] = ⟨64, fr.r9⟩ ∧
      args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧ args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩)
    (key : Vector UInt8 ((AES16.variant use256).keyBytes)) (input : ByteArray)
    (blockCount : Nat) (hsize : input.size = 16 * blockCount)
    (schedule counter source destination : BitVec 64)
    (hPre : Readable fr.original fr.rdi 8 ∧ memLoad fr.original fr.rdi 64 = schedule ∧
      AES16.ScheduleIn (AES16.variant use256) key schedule fr.original ∧
      Readable fr.original schedule (16 * ((AES16.variant use256).Nr + 1)) ∧
      Readable fr.original fr.rsi 32 ∧ memLoad fr.original fr.rsi 64 = counter ∧
      memLoad fr.original (fr.rsi + 8) 64 = source ∧ memLoad fr.original (fr.rsi + 16) 64 = destination ∧
      (memLoad fr.original (fr.rsi + 24) 64).toNat = blockCount ∧ Writable code fr.original counter 20 ∧
      Readable fr.original source input.size ∧ (span source input.size).HasBytes fr.original input ∧
      Writable code fr.original destination input.size ∧
      (source = destination ∨ (span source input.size).Disjoint (span destination input.size)))
    (hSlots : ∀ slot ∈ ([0x201208, 0x201210, 0x201230] : List (BitVec 64)),
      (span destination input.size).Disjoint (span slot 8) ∧ (span counter 20).Disjoint (span slot 8))
    (hSaved : Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧ fr.ret.toNat < 2^32)
    (hWindow : Writable code fr.original (fr.rsp - (if use256 then 0xa80 else 0x870))
      (if use256 then 0xa80 else 0x870))
    (hLow : fr.low.toNat + (if use256 then 0xa80 else 0x870) ≤ fr.rsp.toNat)
    (hAlign : fr.rsp.toNat % 16 = 8)
    (hSlot0Readable : Readable fr.original 0x201208 8)
    (hSlot0Value : memLoad fr.original 0x201208 64 = 0x103f00)
    (hSlot1Readable : Readable fr.original 0x201210 8)
    (hSlot1Value : memLoad fr.original 0x201210 64 = 0x103880)
    (hSlot2Readable : Readable fr.original 0x201230 8)
    (hSlot2Value : memLoad fr.original 0x201230 64 = 0x101230)
    (hSlotsApart : (if use256 then 0x201cb8 else 0x201aa8) ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208)
    (hCallStack : ∀ region ∈ [span fr.rdi 8, span fr.rsi 32,
      span schedule (16 * ((AES16.variant use256).Nr + 1)), span counter 20,
      span source input.size, span destination input.size], (callStack fr).Disjoint region)
    (hDestinationRegions : ∀ region ∈ [span fr.rdi 8, span fr.rsi 32,
      span schedule (16 * ((AES16.variant use256).Nr + 1)), span counter 20],
      (span destination input.size).Disjoint region)
    (hCounterRegions : ∀ region ∈ [span fr.rdi 8, span fr.rsi 32,
      span schedule (16 * ((AES16.variant use256).Nr + 1)), span source input.size,
      span destination input.size], (span counter 20).Disjoint region)
    (hFp : args[22] = ⟨1, 0⟩ ∧ args[39] = ⟨32, fr.mxcsr⟩ ∧
      args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l1084e0 else .l107050, args, fr.original⟩, []⟩ ⟨next, []⟩ ∧
      ((next.label = (if use256 then .l108e98 else .l107a08) ∧ OuterInvariant use256 code fr key input (blockCount / 4) 0 schedule counter source destination next) ∨
       (blockCount / 4 = 0 ∧ OuterExit use256 code fr key input blockCount schedule counter source destination next)) := by
  rcases hPre with ⟨hRdi, hRdiWord, hSchedule, hScheduleR, hDesc, hCounter, hSource,
    hDestination, hCount, hCounterW, hSourceR, hSourceB, hDestW, hAlias⟩
  rcases hSaved with ⟨hRetR, hRet, hRetLow⟩
  rcases hArgs with ⟨h4, _, _, h3, h5, h6, h7, _, _, h12, h13, h14, h15⟩
  rcases hFp with ⟨h22, h39, h50, h51⟩
  let sp := outerStackPointer fr use256
  let w : Nat := if use256 then 0xa80 else 0x870
  let depth : Nat := if use256 then 0x908 else 0x708
  let bottom := fr.rsp - BitVec.ofNat 64 w
  have wbound : w ≤ 2688 := by cases use256 <;> decide
  have dpos : 1800 ≤ depth := by cases use256 <;> decide
  have room : depth + 296 ≤ w := by cases use256 <;> decide
  have hroom : fr.low.toNat + w ≤ fr.rsp.toNat := hLow
  have rspLow := hRetR.low
  have rsp48 : (fr.rsp - 48).toNat = fr.rsp.toNat - 48 := by bv_omega
  have spNat : sp.toNat = fr.rsp.toNat - depth := by
    have hs : sp = fr.rsp - BitVec.ofNat 64 depth := by cases use256 <;> rfl
    rw [hs, BitVec.toNat_sub_of_le (by change depth % 2^64 ≤ fr.rsp.toNat; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have bottomNat : bottom.toNat = fr.rsp.toNat - w := by
    dsimp only [bottom]
    rw [BitVec.toNat_sub_of_le (by change w % 2^64 ≤ fr.rsp.toNat; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hWindow' : Writable code fr.original bottom w := by
    cases use256 <;> exact hWindow
  have stackWrite {p : BitVec 64} {n : Nat}
      (hl : fr.rsp.toNat - w ≤ p.toNat) (hh : p.toNat + n ≤ fr.rsp.toNat) :
      Writable code fr.original p n :=
    hWindow'.sub (by rw [bottomNat]; omega) (by rw [bottomNat]; omega)
  have spAdd (n : Nat) (hn : n ≤ 2688) :
      (sp + BitVec.ofNat 64 n).toNat = sp.toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have spSub (n : Nat) (hn : n ≤ 296) :
      (sp - BitVec.ofNat 64 n).toNat = sp.toNat - n := by
    rw [BitVec.toNat_sub_of_le (by change n % 2^64 ≤ sp.toNat; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ext {p : BitVec 64} {n : Nat} (hn : 0 < n) (hr : Readable fr.original p n)
      (hreg : (callStack fr).Disjoint (span p n)) :=
    outside_activationRegion hr hn (by omega) hreg
  have bounds {p : BitVec 64} {n : Nat} (ho : Outside [fr.region] p n) :
      p.toNat + n ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ p.toNat := by
    have hb := ho.2 fr.region (by simp)
    simp only [Activation.region] at hb
    omega
  have outRdi := ext (by decide) hRdi (hCallStack _ (by simp))
  have outDesc := ext (by decide) hDesc (hCallStack _ (by simp))
  have schedPos : 0 < 16 * ((AES16.variant use256).Nr + 1) := by omega
  have outSched := ext schedPos hScheduleR (hCallStack _ (by simp))
  have outCounter := ext (by decide) hCounterW.readable (hCallStack _ (by simp))
  have args4 : args[4].get 64 = fr.rsp := by rw [h4]; rfl
  have args7 : args[7].get 64 = fr.rdi := by rw [h7]; rfl
  obtain ⟨entry, ej, el, em, ew, e3, ek, et, ef⟩ :=
    entry_widening use256 code hcode args fr.original schedule hTypes
      (by rw [args4]; exact stackWrite (by omega) (by omega))
      (by rw [args7]; exact hRdi) (by rw [args7]; exact hRdiWord)
      (by rw [args4, args7]; have := bounds outRdi; omega)
  rw [args4] at ef ew
  have eWin : RamWriteFrame fr.original entry.store [span bottom w] := by
    apply (RamWriteFrame.refl _ _).trans ef
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨span bottom w, by simp, by simp only [span, bottomNat, rsp48]; omega,
      by simp only [span, bottomNat, rsp48]; omega⟩
  have winRoot : RegionsWithin [span bottom w] [fr.region] := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨fr.region, by simp, by simp only [span, Activation.region, bottomNat]; omega,
      by simp only [span, Activation.region, bottomNat]; omega⟩
  have efFull := (RamWriteFrame.refl _ _).trans eWin winRoot
  have wdiff : (if use256 then 0x201cb8 else 0x201aa8) = 0x201238 + w := by
    cases use256 <;> decide
  have outSlot (slot : BitVec 64) (ha : 0x201208 ≤ slot.toNat)
      (hb : slot.toNat + 8 ≤ 0x201238) : Outside [span bottom w] slot 8 := by
    refine ⟨by omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    simp only [span, bottomNat]
    omega
  have out0 := outSlot 0x201208 (by decide) (by decide)
  have out1 := outSlot 0x201210 (by decide) (by decide)
  have out2 := outSlot 0x201230 (by decide) (by decide)
  let off : Nat := if use256 then 1304 else 1048
  have wideNat : (sp + wideningOffset use256).toNat = sp.toNat + off := by
    have ho : wideningOffset use256 = BitVec.ofNat 64 off := by cases use256 <;> rfl
    rw [ho, spAdd _ (by cases use256 <;> decide)]
  have wideEnd : off + 8 * keyWords use256 + 48 = depth := by cases use256 <;> decide
  have offMin : 344 ≤ off := by cases use256 <;> decide
  have dim : 8 * ((AES16.variant use256).Nr + 1) = keyWords use256 := by
    cases use256 <;> rfl
  let keys := (narrowScheduleWords (AES16.variant use256) key).cast dim
  have readLen : 16 * ((AES16.variant use256).Nr + 1) = 2 * keyWords use256 := by omega
  have hKeys : WordsAt entry.store schedule 16 keys := by
    have hs := narrowScheduleWords_in (AES16.scheduleIn_of_frame hSchedule efFull outSched)
    intro i hi
    exact hs i (by omega)
  have wideWrite : Writable code fr.original (sp + wideningOffset use256) (8 * keyWords use256) :=
    stackWrite (by omega) (by omega)
  have wideSep : RangeApart (sp + wideningOffset use256) (8 * keyWords use256)
      schedule (2 * keyWords use256) := by
    apply RangeApart.of_toNat
    · exact Nat.le_trans wideWrite.readable.low (by decide)
    · have := outSched.1; omega
    · have := bounds outSched; omega
  have wa344 : (sp + 344).toNat = sp.toNat + 344 := spAdd 344 (by decide)
  have ws8 : (sp - 8).toNat = sp.toNat - 8 := spSub 8 (by decide)
  have e39 := (ek 39 (by decide)).trans h39
  have e50 := (ek 50 (by decide)).trans h50
  have e51 := (ek 51 (by decide)).trans h51
  have hdMod : depth % 16 = 8 := by cases use256 <;> decide
  obtain ⟨setup, sr, sl, sRead, sWords, s4, st, sf, sk, sSchedule⟩ :=
    key_setup_reaches use256 code hcode entry.arguments entry.store sp schedule keys et
      ((ek 22 (by decide)).trans h22) (e39.trans (congrArg (fun x => Value.mk 32 (Value.get 32 x)) e39.symm))
      (e50.trans (congrArg (fun x => Value.mk 16 (Value.get 16 x)) e50.symm))
      (e51.trans (congrArg (fun x => Value.mk 16 (Value.get 16 x)) e51.symm))
      (by omega)
      (by rw [← readLen]; exact hScheduleR.of_frame ef)
      (wideWrite.of_frame ef) wideSep hKeys
      ((stackWrite (p := sp + 344) (by omega) (by omega)).of_frame ef)
      ((stackWrite (p := sp - 8) (by omega) (by omega)).of_frame ef)
      (hSlot0Readable.of_frame ef) ((eWin.memLoad_eq out0).trans hSlot0Value)
      (by omega)
  have startReach := prefix_jump ej
  have setupReach : (LIR.program.sem (dialect code)).Reaches ⟨entry, []⟩ ⟨setup, []⟩ := by
    change (LIR.program.sem (dialect code)).Reaches
      ⟨⟨entry.label, entry.arguments, entry.store⟩, []⟩ _
    rw [el, ← ew]
    exact sr
  let locals : MemoryRegion := ⟨bottom.toNat, fr.rsp.toNat - 48 - bottom.toNat⟩
  have localSub {rs : List MemoryRegion}
      (h : ∀ r ∈ rs, bottom.toNat ≤ r.start ∧ r.start + r.size ≤ fr.rsp.toNat - 48) :
      RegionsWithin rs [locals] := by
    intro r hr
    obtain ⟨h1,h2⟩ := h r hr
    exact ⟨locals, by simp, h1, by dsimp only [locals]; omega⟩
  have sLocal : RamWriteFrame entry.store setup.store [locals] := by
    apply (RamWriteFrame.refl _ _).trans sf
    apply localSub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [span] <;> omega
  have localWin : RegionsWithin [locals] [span bottom w] := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨span bottom w, by simp, Nat.le_refl _, by dsimp only [locals, span]; omega⟩
  have sWin := eWin.trans sLocal localWin
  have sRoot := (RamWriteFrame.refl _ _).trans sWin winRoot
  let count := memLoad fr.original (fr.rsi + 24) 64
  have countNat : count.toNat = blockCount := hCount
  have descWord (n : Nat) (hn : n + 8 ≤ 32) :
      memLoad setup.store (fr.rsi + BitVec.ofNat 64 n) 64 =
        memLoad fr.original (fr.rsi + BitVec.ofNat 64 n) 64 :=
    sRoot.memLoad_eq (outside_subregion outDesc (by omega) hn)
  have wa232 : (sp + 232).toNat = sp.toNat + 232 := spAdd 232 (by decide)
  have arg6 : args[6].get 64 = fr.rsi := by rw [h6]; rfl
  have setup3 := ((sk 3 (by decide)).trans e3).trans (congrArg (Value.mk 64) arg6)
  have desc0 : memLoad setup.store fr.rsi 64 = memLoad fr.original fr.rsi 64 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using descWord 0 (by decide)
  obtain ⟨splitLoc, cj, cl, cm, _, c2, c9, ck, ct, cf⟩ :=
    count_split use256 code hcode setup.arguments setup.store sp fr.rsi counter source
      destination count st (by rw [s4]; rfl)
      (congrArg (Value.get 64) setup3) (by omega)
      ((stackWrite (p := sp + 232) (by omega) (by omega)).of_frame sRoot)
      (hDesc.of_frame sRoot) (by have := bounds outDesc; omega)
      (desc0.trans hCounter)
      ((descWord 8 (by decide)).trans hSource) ((descWord 16 (by decide)).trans hDestination)
      (descWord 24 (by decide))
  have splitReach : (LIR.program.sem (dialect code)).Reaches ⟨setup, []⟩ ⟨splitLoc, []⟩ := by
    apply prefix_jump
    change LIR.program.runBlock (dialect code) ⟨setup.label, setup.arguments, setup.store⟩ = _
    rw [sl]
    exact cj
  have batchNat : (count >>> 2).toNat = blockCount / 4 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, countNat]
  have hz : count >>> 2 = 0 ↔ blockCount / 4 = 0 := by
    rw [← batchNat, ← BitVec.toNat_inj]
    rfl
  simp only [hz] at cl
  have wa216 : (sp + 216).toNat = sp.toNat + 216 := spAdd 216 (by decide)
  obtain ⟨next, br, bl, bt, bk, bf, bSlots⟩ := batch_prefix_branch use256 code hcode
    splitLoc sp destination (blockCount / 4) cl ct ((ck 4 (by decide)).trans s4) c2
    (((stackWrite (p := sp + 216) (by omega) (by omega)).of_frame sRoot).of_frame cf)
  have subC : RegionsWithin [span (sp + 232) 104] [locals] := by
    apply localSub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨by change _ ≤ (sp + 232).toNat; omega, by change (sp + 232).toNat + 104 ≤ _; omega⟩
  have subB : RegionsWithin [span (sp + 216) 16] [locals] := by
    apply localSub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨by change _ ≤ (sp + 216).toNat; omega, by change (sp + 216).toNat + 16 ≤ _; omega⟩
  have nLocal := (sLocal.trans cf subC).trans bf subB
  have nWin := eWin.trans nLocal localWin
  have nRoot := (RamWriteFrame.refl _ _).trans nWin winRoot
  have nRead := hScheduleR.of_frame nRoot
  have nSchedule := AES16.scheduleIn_of_frame hSchedule nRoot outSched
  have nCounter := nRoot.memLoad_eq (k := 32) (outside_subregion outCounter (offset := 16)
    (by decide) (by decide))
  have nSource : (span source input.size).HasBytes next.store input := by
    apply hasBytes_of_frame nRoot hSourceB (Nat.le_trans hSourceR.low (by decide))
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact span_disjoint_activationRegion (hCallStack _ (by simp))
  have savedWord (k : Nat) (hk : k ≤ 48) :
      memLoad next.store (fr.rsp - BitVec.ofNat 64 k) 64 =
        memLoad entry.store (fr.rsp - BitVec.ofNat 64 k) 64 := by
    apply nLocal.memLoad_eq
    have ha := stack_sub_toNat fr (window := 48) (by omega) hk
    refine ⟨by rw [ha]; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    simp only [locals, ha]
    omega
  obtain ⟨p3,p12,p13,p14,p15,p5⟩ := entryMemory_saved args fr.original
  change memLoad (entryMemory args fr.original) (args[4].get 64 - 48) 64 = args[3].get 64 at p3
  rw [← em, args4, h3] at p3
  change memLoad (entryMemory args fr.original) (args[4].get 64 - 40) 64 = args[12].get 64 at p12
  rw [← em, args4, h12] at p12
  change memLoad (entryMemory args fr.original) (args[4].get 64 - 32) 64 = args[13].get 64 at p13
  rw [← em, args4, h13] at p13
  change memLoad (entryMemory args fr.original) (args[4].get 64 - 24) 64 = args[14].get 64 at p14
  rw [← em, args4, h14] at p14
  change memLoad (entryMemory args fr.original) (args[4].get 64 - 16) 64 = args[15].get 64 at p15
  rw [← em, args4, h15] at p15
  change memLoad (entryMemory args fr.original) (args[4].get 64 - 8) 64 = args[5].get 64 at p5
  rw [← em, args4, h5] at p5
  have returnOutside : Outside [span bottom w] fr.rsp 8 := by
    refine ⟨by omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    simp only [span, bottomNat]
    omega
  have nReturn := (nWin.memLoad_eq returnOutside).trans hRet
  have fp (r : Fin 53) (hr : r.val ∈ [22,39,50,51]) : next.arguments[r] = args[r] := by
    exact (bk r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)).trans
      ((ck r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)).trans
      ((sk r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)).trans
      (ek r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega))))
  have n4 := (bk 4 (by decide)).trans ((ck 4 (by decide)).trans s4)
  have n0 := (nWin.memLoad_eq out0).trans hSlot0Value
  have n1 := (nWin.memLoad_eq out1).trans hSlot1Value
  have n2 := (nWin.memLoad_eq out2).trans hSlot2Value
  have frameSlots : (if use256 then 0x201cb8 else 0x201aa8) ≤ fr.rsp.toNat ∨
      fr.rsp.toNat ≤ 0x201210 := by omega
  have frameLayout : cryptFrameAt use256 next.label fr =
      cryptFrameAt use256 (if use256 then .l108e98 else .l107a08) fr := by
    rw [bl]
    split <;> cases use256 <;> rfl
  have nFrame : Atom.All code next.arguments next.store (cryptFrameAt use256 next.label fr) := by
    rw [frameLayout]
    have view : next.arguments[4]'(by change 4 < 53; decide) =
        ⟨64, fr.rsp - (if use256 then 0x908 else 0x708)⟩ := n4
    have stack := hWindow.of_frame nRoot
    have h22' := (fp 22 (by decide)).trans h22
    have h39' := (fp 39 (by decide)).trans h39
    have h50' := (fp 50 (by decide)).trans h50
    have h51' := (fp 51 (by decide)).trans h51
    have r3 := (savedWord 48 (by decide)).trans p3
    have r12 := (savedWord 40 (by decide)).trans p12
    have r13 := (savedWord 32 (by decide)).trans p13
    have r14 := (savedWord 24 (by decide)).trans p14
    have r15 := (savedWord 16 (by decide)).trans p15
    have r5 := (savedWord 8 (by decide)).trans p5
    cases use256 <;>
      exact ⟨view, h22', h39', h50', h51', r3, r12, r13, r14, r15, r5,
        hRetR.of_frame nRoot, nReturn, hRetLow, stack, hLow, hAlign,
        hSlot1Readable.of_frame nRoot, n1, hSlot2Readable.of_frame nRoot, n2, frameSlots, trivial⟩
  have outsideAbove {p : BitVec 64} {n : Nat} (hp : sp.toNat + 336 ≤ p.toNat)
      (hl : p.toNat + n ≤ 2^64) :
      Outside [span (sp + 232) 104] p n ∧ Outside [span (sp + 216) 16] p n := by
    constructor <;> refine ⟨hl, ?_⟩ <;> intro r hr <;>
      obtain rfl := List.mem_singleton.mp hr <;> right <;> simp only [span] <;> omega
  have wsize : 8 * keyWords use256 ≤ 960 := by cases use256 <;> decide
  obtain ⟨owc,owb⟩ := outsideAbove (p := sp + 344) (n := 64 / 8 * keyWords use256)
    (by omega) (by change (sp + 344).toNat + 8 * keyWords use256 ≤ _; omega)
  have wideWords := (sWords.of_frame cf (by decide) owc).of_frame bf (by decide) owb
  have wa336 : (sp + 336).toNat = sp.toNat + 336 := spAdd 336 (by decide)
  obtain ⟨osc,osb⟩ := outsideAbove (p := sp + 336) (n := 8) (by omega) (by omega)
  have nPtr := (bf.memLoad_eq osb).trans ((cf.memLoad_eq osc).trans sSchedule)
  have slotLoad (k : Nat) (hk : 232 ≤ k ∧ k ≤ 328) :
      memLoad next.store (sp + BitVec.ofNat 64 k) 64 =
      memLoad (countMemory setup.store sp source counter count) (sp + BitVec.ofNat 64 k) 64 := by
    rw [← cm]
    apply bf.memLoad_eq
    have ha := spAdd k (by omega)
    refine ⟨by rw [ha]; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    simp only [span, ha]
    omega
  obtain ⟨w232,w240,w248,w320,w328⟩ := countMemory_slots setup.store sp source counter count
  rw [countNat] at w232 w328
  have countBV : count = BitVec.ofNat 64 blockCount := by rw [← countNat]; simp
  have wa72 : (sp + 72).toNat = sp.toNat + 72 := spAdd 72 (by decide)
  have ws296 : (sp - 296).toNat = sp.toNat - 296 := spSub 296 (by decide)
  have stack296 := stackWrite (p := sp - 296) (n := 528) (by omega) (by omega)
  have stack72 := stackWrite (p := sp + 72) (n := 264) (by omega) (by omega)
  have innerSlots : (if use256 then 0x2013b0 else 0x2013a0) ≤ sp.toNat ∨
      sp.toNat + 232 ≤ 0x201208 := by
    have hdiff : (if use256 then 0x2013b0 else 0x2013a0) + depth ≤
        (if use256 then 0x201cb8 else 0x201aa8) := by cases use256 <;> decide
    omega
  have nw : WordsAt next.store (sp + 344) 64
      ((narrowScheduleWords (AES16.variant use256) key).map Fixslice16.widenWord) := by
    intro i hi
    exact wideWords i (by omega)
  have state : OuterState use256 code fr key input blockCount schedule counter source destination next := by
    refine ⟨nFrame, ?_, ?_, bt, nSchedule, nRead⟩
    · exact ⟨(bk 2 (by decide)).trans c2, n4, (bk 9 (by decide)).trans c9,
        (slotLoad 232 (by decide)).trans w232, (slotLoad 240 (by decide)).trans w240,
        (slotLoad 248 (by decide)).trans w248, (slotLoad 320 (by decide)).trans (w320.trans countBV),
        (slotLoad 328 (by decide)).trans w328, nPtr, n0, n1, n2,
        hSlot0Readable.of_frame nRoot, hSlot1Readable.of_frame nRoot, hSlot2Readable.of_frame nRoot,
        stack296.readable.of_frame nRoot, stack296.of_frame nRoot, stack72.of_frame nRoot,
        (sRead.of_frame cf).of_frame bf, nw, hSourceR.of_frame nRoot, hDestW.of_frame nRoot,
        hCounterW.readable.of_frame nRoot, hCounterW.of_frame nRoot, nRead, innerSlots, hCallStack,
        hDestinationRegions, hCounterRegions, hAlias, hSlots, hSlotsApart, trivial⟩
    · apply (RamWriteFrame.refl _ _).trans nRoot
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨fr.region, by simp, Nat.le_refl _, Nat.le_refl _⟩
  have emptyBytes (out : ByteArray) : (span destination 0).HasBytes next.store (out.extract 0 0) := by
    rw [ByteArray.extract_same]
    exact ⟨rfl, fun i => Fin.elim0 i⟩
  refine ⟨next, startReach.trans (setupReach.trans (splitReach.trans br)), ?_⟩
  by_cases hz : blockCount / 4 = 0
  · right
    have rem : input.size % 64 = input.size := Nat.mod_eq_of_lt (by omega)
    refine ⟨hz, state, by simpa only [hz, ↓reduceIte] using bl, ?_, ?_, ?_⟩
    · simpa only [hz, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using nCounter
    · simpa only [rem, Nat.sub_self, BitVec.ofNat_eq_ofNat, BitVec.add_zero, ByteArray.extract_zero_size]
        using nSource
    · simpa only [rem, Nat.sub_self] using emptyBytes _
  · left
    have hl := bl
    simp only [hz, ↓reduceIte] at hl
    have hc : input.size / 16 = blockCount := by omega
    refine ⟨hl, ?_, hl, by omega, (bSlots hz).1, (bSlots hz).2, ?_, ?_, ?_⟩
    · simpa only [hc] using state
    · simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using nCounter
    · simpa only [Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
        ByteArray.extract_zero_size] using nSource
    · exact emptyBytes _

end AesGcm.Proofs.Machine.CTR
