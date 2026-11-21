import K256.Proofs.Verify.Core.Lincomb.Loop.State
import K256.Proofs.Verify.Core.Lincomb.Recode.Stack
import K256.Proofs.Generate.Generator.Affine.Memory
import K256.Proofs.Sec1.Serialize.Assemble.Memory

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private theorem prefixJump {source target finish : Label} {a b c : Registers} {m n p : Ram}
    (step : program.runBlock (dialect Extracted.programImage) ⟨source, a, m⟩ =
      .jump ⟨target, b, n⟩) (rest : Reaches target b n finish c p) :
    Reaches source a m finish c p :=
  .step (by
    change (program.runBlock _ _).next _ [] = _
    rw [step]
    rfl) rest

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem freshPrefix {a : Registers} {m : Ram} {sp dst iterator dataPtr : BitVec 64}
    (entry : RoutineEntry a m sp 0x478)
    (di : a[7].get 64 = dst) (si : a[6].get 64 = iterator)
    (first : memLoad m iterator 64 = dataPtr)
    (last : memLoad m (iterator + 8) 64 = dataPtr + 0x1340)
    (unset : memLoad m (iterator + 16) 64 = 0 ∧ memLoad m (iterator + 64) 64 = 0)
    (iterRead : Readable m iterator 112)
    (iterApart : Outside [scratch sp 0x478, ⟨dst.toNat, 120⟩] iterator 112) :
    ∃ b n, Reaches .l1100a0 a m .l110156 b n ∧ SavedFrame a m sp dst b n ∧
      b[13] = ⟨64, 0⟩ ∧ b[14] = ⟨64, dataPtr⟩ ∧ b[5] = ⟨64, dataPtr + 0x1340⟩ ∧
      b[15] = ⟨64, iterator⟩ ∧ b[3].width = 64 ∧ b[12].width = 64 ∧
      memLoad n (baseSp sp) 64 = 0 ∧ memLoad n (baseSp sp + 0x60) 64 = dataPtr + 0x1340 ∧
      memLoad n (baseSp sp + 0x98) 64 = 0 := by
  let pushed := memStore (memStore (memStore (memStore (memStore (memStore
    m (sp - 8) (a[5].get 64)) (sp - 16) (a[15].get 64)) (sp - 24) (a[14].get 64))
    (sp - 32) (a[13].get 64)) (sp - 40) (a[12].get 64)) (sp - 48) (a[3].get 64)
  let prologue := memStore pushed (sp - 0x108) dst
  let stash := memStore prologue (sp - 0x1c0) dst
  let cleared := memStore stash (sp - 0x1d8) (0 : BitVec 64)
  let measured := memStore cleared (sp - 0x178) (dataPtr + 0x1340)
  let finalMem := memStore (memStore (memStore (memStore (memStore (memStore
    measured (sp - 0x140) (0 : BitVec 64)) (sp - 0x138) (a[11].get 64))
    (sp - 0x130) (0 : BitVec 64)) (sp - 0x128) (a[3].get 64))
    (sp - 0x120) (a[9].get 64)) (sp - 0x118) (a[10].get 64)
  have room := entry.room
  have within (off : BitVec 64) (lo : 8 ≤ off.toNat) (hi : off.toNat ≤ 0x478) :
      InRegions [scratch sp 0x478] (sp - off) 8 :=
    ⟨_, .head _, Recode.inScratch room hi lo⟩
  have stack (off : BitVec 64) (lo : 8 ≤ off.toNat) (hi : off.toNat ≤ 0x478) :
      Writable Extracted.programImage m (sp - off) 8 :=
    Recode.stackSlot entry hi lo
  have pushedFrame : RamWriteFrame m pushed [scratch sp 0x478] := by
    dsimp only [pushed]
    repeat' apply RamWriteFrame.memStore _ _ (within _ (by decide) (by decide))
    exact .refl _ _
  have prologueFrame := pushedFrame.memStore dst (within 0x108 (by decide) (by decide))
  have stashFrame := prologueFrame.memStore dst (within 0x1c0 (by decide) (by decide))
  have clearedFrame := stashFrame.memStore (0 : BitVec 64) (within 0x1d8 (by decide) (by decide))
  have measuredFrame := clearedFrame.memStore (dataPtr + 0x1340) (within 0x178 (by decide) (by decide))
  have finalFrame : RamWriteFrame m finalMem [scratch sp 0x478] := by
    dsimp only [finalMem]
    iterate 6 apply RamWriteFrame.memStore _ _ (within _ (by decide) (by decide))
    exact measuredFrame
  have backRead : LoadOk measured (sp - 0x1d8) 8 :=
    let read := ((stack 0x1d8 (by decide) (by decide)).of_frame measuredFrame).readable
    ⟨read.low, read.present⟩
  have backWord : memLoad measured (sp - 0x1d8) 64 = 0 := by
    simp (disch := store_disch) only [measured, cleared,
      memLoad_memStore_same, memLoad_memStore_of_rangeApart]
  have iterFacts {n : Ram} (frame : RamWriteFrame m n [scratch sp 0x478])
      (off : BitVec 64) (fits : off.toNat + 8 ≤ 112) :
      LoadOk n (iterator + off) 8 ∧ memLoad n (iterator + off) 64 = memLoad m (iterator + off) 64 := by
    have low := iterRead.low
    have pos : (iterator + off).toNat = iterator.toNat + off.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have separate : Outside [scratch sp 0x478] iterator 112 :=
      ⟨iterApart.1, fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact iterApart.2 _ (.head _)⟩
    exact ⟨LoadOk.of_region (iterRead.of_frame frame) (by omega) (by omega),
      frame.memLoad_eq (Generate.Generator.Affine.outside_subregion separate (by omega) (by omega))⟩
  have frontInfo := iterFacts (n := prologue) prologueFrame 16 (by decide)
  have endInfo := iterFacts (n := stash) stashFrame 8 (by decide)
  have backInfo := iterFacts (n := stash) stashFrame 64 (by decide)
  have firstInfo := iterFacts (n := cleared) clearedFrame 0 (by decide)
  rw [show iterator + (0 : BitVec 64) = iterator from BitVec.add_zero _] at firstInfo
  have rsp : a[4].get 64 = sp := congrArg (Value.get 64) entry.rsp
  have savedBase : baseSp sp + 0xd0 = sp - 0x108 := by unfold baseSp; bv_omega
  have endBase : baseSp sp + 0x60 = sp - 0x178 := by unfold baseSp; bv_omega
  have backBase : baseSp sp + 0x98 = sp - 0x140 := by unfold baseSp; bv_omega
  have zeroAndByte (x : BitVec 8) : (0 : BitVec 8) &&& x = 0 := BitVec.zero_and (x := x)
  have cmpTest : (testFlags (0 : BitVec 64)).ZF.getD false = true := rfl
  have code (pc : BitVec 64) (bytes : List UInt8)
      (included : ∀ x ∈ codeRange pc bytes, x ∈ fnCode) :
      ∀ x ∈ codeRange pc bytes, x ∈ Extracted.programImage :=
    fun x hx => Common.fnCode_subset_programImage x (included x hx)
  refine ⟨?_, finalMem, ?route, ?frame, ?front, ?next, ?tableEnd, ?iter, ?rbx, ?r12,
    ?back, ?endWord, ?unsetWord⟩
  case route =>
    refine prefixJump (target := .l1100db) (b := ?_) (n := prologue) ?edge ?_
    case edge =>
      cfg_eval [rsp, di, si]
      repeat'
        (refine Eq.trans (ite_eq_left ?_) ?_
         apply Sec1.Serialize.Assemble.storeOk_inBlock (included := code _ _ code_l1100a0)
         · repeat' (with_reducible apply Writable.memStore)
           exact stack _ (by decide) (by decide)
         · decide)
      rw [ite_eq_left frontInfo.1, frontInfo.2.trans unset.1]
      rfl
    refine prefixJump (target := .l110107) (b := ?_) (n := cleared) ?edge ?_
    case edge =>
      cfg_eval [di]
      refine Eq.trans (ite_eq_left ?_) ?_
      · exact Recode.storeGuard (off := 0) (len := 5)
          ((stack 0x1c0 (by decide) (by decide)).of_frame prologueFrame) code_l1100db (by decide)
      rw [ite_eq_left endInfo.1, ite_eq_left backInfo.1, endInfo.2.trans last, backInfo.2.trans unset.2]
      refine Eq.trans (ite_eq_left ?_) ?_
      · exact Recode.storeGuard (off := 13) (len := 4)
          ((stack 0x1d8 (by decide) (by decide)).of_frame stashFrame) code_l1100db (by decide)
      rfl
    refine prefixJump (target := .l110156) (b := ?_) (n := finalMem) ?edge ?_
    case edge =>
      cfg_eval [cmpTest, setWidth_mergeGPR8]
      rw [ite_eq_left firstInfo.1, firstInfo.2.trans first]
      refine Eq.trans (ite_eq_left ?_) ?_
      · exact Recode.storeGuard (off := 10) (len := 5)
          ((stack 0x178 (by decide) (by decide)).of_frame clearedFrame) code_l110107 (by decide)
      rw [ite_eq_left backRead, backWord]
      repeat'
        (refine Eq.trans (ite_eq_left ?_) ?_
         apply Sec1.Serialize.Assemble.storeOk_inBlock (included := code _ _ code_l110107)
         · repeat' (with_reducible apply Writable.memStore)
           exact stack _ (by decide) (by decide)
         · decide)
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, zeroAndByte, testFlags_ZF,
        beq_self_eq_true]
      rfl
    exact .refl _
  case frame =>
    refine ⟨rfl, ?destWord, ?savedRbx, ?savedR12, ?savedR13, ?savedR14, ?savedR15, ?savedRbp,
      ?control, finalFrame⟩
    case control =>
      rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    all_goals
      simp (disch := store_disch) only [savedBase, finalMem, measured, cleared, stash, prologue,
        pushed, memLoad_memStore_same, memLoad_memStore_of_rangeApart]
  case front => rfl
  case next => rfl
  case tableEnd => rfl
  case iter => rfl
  case rbx => exact entry.saved 3 (by decide)
  case r12 => rfl
  all_goals
    simp (disch := store_disch) only [endBase, backBase, baseSp, finalMem, measured, cleared,
      memLoad_memStore_same, memLoad_memStore_of_rangeApart]

end K256.Proofs.Verify.Core.Lincomb.Loop
