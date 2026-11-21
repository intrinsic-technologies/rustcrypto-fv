import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.Copy.Bounds
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Copy
import K256.Proofs.Verify.LIR.Fn103f30

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Prepare

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private theorem copyStackWritable {fr : Activation} {input : Input} {m : Ram}
    (env : Environment fr input) {regions : List MemoryRegion}
    (frame : RamWriteFrame fr.original m regions) {addr : BitVec 64} {size : Nat}
    (lo : (sp fr - 8).toNat ≤ addr.toNat) (hi : addr.toNat + size ≤ fr.rsp.toNat) :
    Writable Extracted.programImage m addr size := by
  apply Absorb.stackWritable env frame _ hi
  have depth := env.depth
  have base := copyBase env
  have slot := copySlot env
  have bottom : (fr.rsp - 1920).toNat = fr.rsp.toNat - 1920 :=
    BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from depth)
  rw [env.low, bottom]
  omega

private theorem stackWritableAt {fr : Activation} {input : Input} {m : Ram}
    (env : Environment fr input) {regions : List MemoryRegion}
    (frame : RamWriteFrame fr.original m regions) (i n : Nat) (fits : i + n ≤ 712) :
    Writable Extracted.programImage m (sp fr + BitVec.ofNat 64 i) n := by
  have base := copyBase env
  have depth := env.depth
  apply copyStackWritable env frame <;> rw [copyAddr env i (by omega)]
  · rw [copySlot env]; omega
  · omega

private theorem slotWritable {fr : Activation} {input : Input} {m : Ram}
    (env : Environment fr input) {regions : List MemoryRegion}
    (frame : RamWriteFrame fr.original m regions) :
    Writable Extracted.programImage m (sp fr - 8) 8 := by
  have depth := env.depth
  have base := copyBase env
  apply copyStackWritable env frame (Nat.le_refl _)
  rw [copySlot env]
  omega

set_option maxRecDepth 2000 in
private theorem enterCopy {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (live : Live (exitLabel second true) fr a m state) :
    ∃ ca : Verify.Core.Registers,
      program.runBlock (dialect Extracted.programImage) ⟨exitLabel second true, a, m⟩ =
        .call ⟨.l12a820, ca, pushed fr second m⟩
          (Verify.Hash.Update.returnFrame (appendAt second) (copyReturn second)) ∧
      ca[7].get 64 = context fr second ∧ ca[6].get 64 = sp fr + 496 ∧
      ca[2].get 64 = 168 ∧ ca[4].get 64 = sp fr - 8 ∧ ca[22].get 1 = 0 ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → ca[i] = a[i]) := by
  let base : BitVec 64 := if second then 0x1044de else 0x1040ba
  let bytes := if second then bytes_l1044de else bytes_l1040ba
  let padBase : Nat := if second then 48 else 160
  let storeOffset (first next : Nat) := if second then next else first
  let pads := padWords fr second m
  have code : ∀ x ∈ codeRange base bytes, x ∈ Extracted.programImage := by
    cases second
    · exact fun x hx => Common.fnCode_subset_programImage x (code_l1040ba x hx)
    · exact fun x hx => Common.fnCode_subset_programImage x (code_l1044de x hx)
  have frame (k : Nat) (hk : k ≤ 8) := padsFrame env m second k hk
  have writable (k offset n : Nat) (hk : k ≤ 8) (fits : offset + n ≤ 712) :
      Writable Extracted.programImage (pads k) (sp fr + BitVec.ofNat 64 offset) n :=
    (stackWritableAt env live.writes offset n fits).of_frame (frame k hk)
  have loadAt (k offset : Nat) (hk : k ≤ 8) (fits : offset + 8 ≤ 712) :
      LoadOk (pads k) (sp fr + BitVec.ofNat 64 offset) 8 :=
    let r := (writable k offset 8 hk fits).readable
    ⟨r.low, r.present⟩
  have loadValue (k offset : Nat) (hk : k ≤ 8) (fits : offset + 8 ≤ 496) :
      memLoad (pads k) (sp fr + BitVec.ofNat 64 offset) 64 =
        memLoad m (sp fr + BitVec.ofNat 64 offset) 64 := by
    apply (frame k hk).memLoad_eq
    have addr := copyAddr env offset (by omega)
    have base := copyBase env
    have limit := env.limit
    refine ⟨by change _ + 8 ≤ 2^64; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact .inl (by change _ + 8 ≤ (sp fr).toNat + 496; omega)
  have storeAt (k offset off : Nat) (hk : k ≤ 8) (fits : offset + 8 ≤ 712)
      (within : off + 8 ≤ bytes.length) :
      StoreOk Extracted.programImage (pads k) (sp fr + BitVec.ofNat 64 offset) 8
        (base + BitVec.ofNat 64 off) 8 :=
    ParseSignature.storeOk_of_codeRange (writable k offset 8 hk fits) code within
  have storePad (k read : Nat) (hk : read ≤ 8) (fits : padBase + 8 * (7-k) + 8 ≤ 496) :
      memStore (pads k) (sp fr + BitVec.ofNat 64 (496 + 8 * (7-k)))
        (memLoad (pads read) (sp fr + BitVec.ofNat 64 (padBase + 8 * (7-k))) 64) = pads (k+1) := by
    rw [loadValue read _ hk fits]
    rfl
  have rep : RepMovsOk Extracted.programImage m 0 (sp fr + 328) (sp fr + 560) 13 8 (base + 21) 3 :=
    Generate.Generator.Multiply.Prepare.copyGuard
      (stackWritableAt env live.writes 328 104 (by decide)).readable
      (ParseSignature.storeOk_of_codeRange (off := 21)
        (stackWritableAt env live.writes 560 104 (by decide)) code (by cases second <;> decide +kernel))
      (.inl (by
        change (sp fr + 328).toNat + 104 ≤ (sp fr + 560).toNat
        rw [show (sp fr + 328).toNat = _ from copyAddr env 328 (by decide),
          show (sp fr + 560).toNat = _ from copyAddr env 560 (by decide)]
        omega))
  have push : StoreOk Extracted.programImage (pads 8) (sp fr - 8) 8
      (base + BitVec.ofNat 64 (if second then 149 else 173)) 6 := by
    apply ParseSignature.storeOk_of_codeRange ((slotWritable env live.writes).of_frame (frame 8 (by decide))) code
    cases second <;> decide +kernel
  obtain ⟨rsp, df, got, target, apart⟩ :
      a[4] = ⟨64, sp fr⟩ ∧ a[22] = ⟨1, 0⟩ ∧ Readable m 0x203dd0 8 ∧
      memLoad m 0x203dd0 64 = 0x12a820 ∧ (0x204598 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0) := by
    have entry := live.atoms
    cases second <;>
      simp only [exitLabel, Fn103f30.frameAt, Fn103f30.frameAtG5] at entry
    all_goals
      obtain ⟨rsp, df, rest⟩ := entry
      obtain ⟨read, target, _, _, apart, _⟩ :
          Readable m 0x203dd0 8 ∧ memLoad m 0x203dd0 64 = 0x12a820 ∧
          Readable m 0x203e10 8 ∧ memLoad m 0x203e10 64 = 0x12a700 ∧
          (0x204598 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0) ∧ True := by
        repeat' first | exact rest | obtain ⟨_, rest⟩ := rest
      exact ⟨rsp, df, read, target, apart⟩
  have gotLoad : LoadOk (pads 8) 0x203dd0 8 :=
    let r := got.of_frame (frame 8 (by decide))
    ⟨r.low, r.present⟩
  have gotTarget : memLoad (pads 8) 0x203dd0 64 = 0x12a820 := by
    refine ((frame 8 (by decide)).memLoad_eq ?_).trans target
    refine ⟨by decide, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    have base := copyBase env
    have depth := env.depth
    change 0x203dd0 + 8 ≤ (sp fr).toNat + 496 ∨ (sp fr).toNat + 496 + 168 ≤ 0x203dd0
    rcases apart with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  have rspBits : a[4].get 64 = sp fr := congrArg (Value.get 64) rsp
  have dfBits : a[22].get 1 = 0 := congrArg (Value.get 1) df
  cases second
  all_goals
    have step0 := storePad 0 0 (by decide) (by decide)
    have step1 := storePad 1 1 (by decide) (by decide)
    have step2 := storePad 2 2 (by decide) (by decide)
    have step3 := storePad 3 3 (by decide) (by decide)
    have step4 := storePad 4 4 (by decide) (by decide)
    have step5 := storePad 5 5 (by decide) (by decide)
    have step6 := storePad 6 6 (by decide) (by decide)
    have step7 := storePad 7 6 (by decide) (by decide)
    simp only [padBase, Bool.false_eq_true, ite_false, ite_true, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceAdd, ← BitVec.ofNat_eq_ofNat] at step0 step1 step2 step3 step4 step5 step6 step7
    refine Exists.intro ?_ ?_
    rotate_left
    constructor
    · first
      | change program.runBlock _ ⟨.l1040ba, _, _⟩ = _
      | change program.runBlock _ ⟨.l1044de, _, _⟩ = _
      cfg_eval [rspBits, dfBits, Nat.reduceMul, or_true, false_or]
      refine Eq.trans (ite_eq_left rep) ?_
      rw [show memCopy m (sp fr + 560) (sp fr + 328) 104 = pads 0 from rfl]
      refine Eq.trans (ite_eq_left (loadAt 0 (padBase + 56) (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (storeAt 0 552 (storeOffset 32 29)
        (by decide) (by decide) (by decide +kernel))) ?_
      rw [step0]
      refine Eq.trans (ite_eq_left (loadAt 1 (padBase + 48) (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (storeAt 1 544 (storeOffset 48 42)
        (by decide) (by decide) (by decide +kernel))) ?_
      rw [step1]
      refine Eq.trans (ite_eq_left (loadAt 2 (padBase + 40) (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (storeAt 2 536 (storeOffset 64 55)
        (by decide) (by decide) (by decide +kernel))) ?_
      rw [step2]
      refine Eq.trans (ite_eq_left (loadAt 3 (padBase + 32) (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (storeAt 3 528 (storeOffset 80 68)
        (by decide) (by decide) (by decide +kernel))) ?_
      rw [step3]
      refine Eq.trans (ite_eq_left (loadAt 4 (padBase + 24) (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (storeAt 4 520 (storeOffset 96 81)
        (by decide) (by decide) (by decide +kernel))) ?_
      rw [step4]
      refine Eq.trans (ite_eq_left (loadAt 5 (padBase + 16) (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (storeAt 5 512 (storeOffset 112 94)
        (by decide) (by decide) (by decide +kernel))) ?_
      rw [step5]
      refine Eq.trans (ite_eq_left (loadAt 6 padBase (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (loadAt 6 (padBase + 8) (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (storeAt 6 504 (storeOffset 136 112)
        (by decide) (by decide) (by decide +kernel))) ?_
      rw [step6]
      refine Eq.trans (ite_eq_left (storeAt 7 496 (storeOffset 144 120)
        (by decide) (by decide) (by decide +kernel))) ?_
      rw [step7]
      simp only [gotLoad, gotTarget]
      refine Eq.trans (ite_eq_left ⟨trivial, push, trivial⟩) ?_
      rfl
    · refine ⟨rfl, rfl, rfl, rfl, dfBits, ?_⟩
      rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl

theorem copyExecute {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (live : Live (exitLabel second true) fr a m state) :
    ∃ b, Verify.Core.Reaches (exitLabel second true) a m (appendAt second) b (copied fr second m) ∧
      b[4] = ⟨64, sp fr⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  obtain ⟨ca, call, dst, src, size, rsp, df, kept⟩ := enterCopy second env live
  let slot := sp fr - 8
  have padFrame := padsFrame env m second 8 (by decide)
  have writeContext : Writable Extracted.programImage m (context fr second) 168 := by
    cases second
    · exact stackWritableAt env live.writes 160 168 (by decide)
    · exact stackWritableAt env live.writes 328 168 (by decide)
  have write := (writeContext.of_frame padFrame).memStore slot (copyReturn second)
  have read := ((stackWritableAt env live.writes 496 168 (by decide)).readable.of_frame padFrame).memStore
    slot (copyReturn second)
  have retRead := ((slotWritable env live.writes).readable.of_frame padFrame).memStore slot (copyReturn second)
  have dstBounds : (context fr second).toNat = (sp fr).toNat + (if second then 328 else 160) := by
    cases second
    · exact copyAddr env 160 (by decide)
    · exact copyAddr env 328 (by decide)
  have srcBounds : (sp fr + 496).toNat = (sp fr).toNat + 496 := copyAddr env 496 (by decide)
  have apart : (context fr second).toNat + 168 ≤ (sp fr + 496).toNat := by
    rw [dstBounds, srcBounds]
    cases second
    · change (sp fr).toNat + 160 + 168 ≤ (sp fr).toNat + 496
      omega
    · change (sp fr).toNat + 328 + 168 ≤ (sp fr).toNat + 496
      omega
  have retApart : RangeApart (context fr second) 168 slot 8 := by
    cases second <;> apply RangeApart.of_offsets rfl (addr_sub _ _) <;> decide
  have ret : memLoad (pushed fr second m) slot 64 = copyReturn second :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have retLow : (memLoad (pushed fr second m) slot 64).toNat < 2^32 := by
    rw [ret]
    cases second <;> decide
  obtain ⟨out, run, store, tag, _, back, saved⟩ :=
    Verify.Hash.Update.memcpy dst src size rsp df read write (.inr apart) retApart retRead retLow
  change out.store = copied fr second m at store
  have reached := Verify.Core.Lincomb.reachesCall call run
    (tag.trans (congrArg (fun bits => some (⟨64, bits⟩ : Value)) ret))
  refine ⟨out.values, store ▸ reached, ?_, ?_⟩
  · rw [back, BitVec.sub_add_cancel]
  · intro i hi
    apply (saved i ?_).trans (kept i hi)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega

end K256.Proofs.Signing.Nonce.Initialize.Update.Prepare
