import K256.Proofs.Verify.Core.Lincomb.Recode.Stack

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def staged (a : Registers) (m : Ram) (sp dst : BitVec 64) : Ram :=
  let m₁ := memStore m (sp-8) (a[5].get 64)
  let m₂ := memStore m₁ (sp-16) (a[15].get 64)
  let m₃ := memStore m₂ (sp-24) (a[14].get 64)
  let m₄ := memStore m₃ (sp-32) (a[13].get 64)
  let m₅ := memStore m₄ (sp-40) (a[12].get 64)
  let m₆ := memStore m₅ (sp-48) (a[3].get 64)
  let m₇ := memStore m₆ (sp-120) dst
  memStore m₇ (sp-144) (0x1107ea : BitVec 64)

theorem stagedSaved (a : Registers) (m : Ram) (sp dst : BitVec 64) :
    SavedAt a sp (staged a m sp dst) := by
  intro ⟨i, hi⟩
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := store_disch) only [staged,
      Nat.reduceAdd, Nat.reduceMul, memLoad_memStore_of_rangeApart]
    first | rfl | exact memLoad_memStore_same _ _ _ (by decide) (by decide)

theorem stagedDest (a : Registers) (m : Ram) (sp dst : BitVec 64) :
    memLoad (staged a m sp dst) (sp-120) 64 = dst := by
  simp (disch := store_disch) only [staged, memLoad_memStore_same, memLoad_memStore_of_rangeApart]

theorem stagedReturn (a : Registers) (m : Ram) (sp dst : BitVec 64) :
    memLoad (staged a m sp dst) (sp-144) 64 = 0x1107ea :=
  memLoad_memStore_same _ _ _ (by decide) (by decide)

theorem stageFrame {a : Registers} {m : Ram} {sp dst : BitVec 64}
    (entry : RoutineEntry a m sp 0x110) :
    RamWriteFrame m (staged a m sp dst) [scratch sp 0x110] := by
  have within (off : BitVec 64) (h₁ : off.toNat ≤ 0x110) (h₂ : 8 ≤ off.toNat) :
      InRegions [scratch sp 0x110] (sp-off) 8 :=
    ⟨_, List.mem_singleton_self _, inScratch entry.room h₁ h₂⟩
  unfold staged
  repeat' apply RamWriteFrame.memStore _ _ (within _ (by decide) (by decide))
  exact .refl _ _

structure InitArgs (a b : Registers) (sp src : BitVec 64) : Prop where
  rsp : b[4] = ⟨64, sp-144⟩
  dst : b[7].get 64 = sp-88
  srcEq : b[6].get 64 = src
  length : b[2].get 64 = 16
  capacity : b[15].get 64 = 257
  bits : b[13].get 64 = 128
  width : b[12] = ⟨64, 5⟩
  windowMod : b[3].get 64 = 32
  df : b[22] = a[22]
  mxcsr : b[39] = a[39]
  ftw : b[50] = a[50]
  fcw : b[51] = a[51]
  savedWidth : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → b[i].width = 64

set_option maxHeartbeats 900000 in
theorem callInitialize {a : Registers} {m : Ram} {sp dst src : BitVec 64}
    (entry : RoutineEntry a m sp 0x110) (di : a[7].get 64 = dst)
    (si : a[6].get 64 = 257) (dx : a[2].get 64 = src) (cx : a[1].get 64 = 16)
    (r8 : a[8].get 64 = 128) (r9 : a[9].get 64 = 5) :
    ∃ b, program.runBlock machine ⟨.l1107b0, a, m⟩ =
      .call ⟨.l1241e0, b, staged a m sp dst⟩ (returnTo .l1107ea 0x1107ea) ∧
      InitArgs a b sp src := by
  have rsp : a[4].get 64 = sp := congrArg (Value.get 64) entry.rsp
  have store0 : StoreOk Extracted.programImage m (sp-8) 8 0x1107b0 1 :=
    storeGuard (off := 0) (stackSlot entry (off := 8) (by decide) (by decide : 8 ≤ (8 : BitVec 64).toNat))
      code_l1107b0 (by decide)
  let m1 := memStore m (sp-8) (a[5].get 64)
  have store1 : StoreOk Extracted.programImage m1 (sp-16) 8 0x1107b1 2 :=
    storeGuard (off := 1) ((stackSlot entry (off := 16) (by decide) (by decide : 8 ≤ (16 : BitVec 64).toNat)).memStore (sp-8) (a[5].get 64))
      code_l1107b0 (by decide)
  let m2 := memStore m1 (sp-16) (a[15].get 64)
  have store2 : StoreOk Extracted.programImage m2 (sp-24) 8 0x1107b3 2 :=
    storeGuard (off := 3) (((stackSlot entry (off := 24) (by decide) (by decide : 8 ≤ (24 : BitVec 64).toNat)).memStore (sp-8) (a[5].get 64)).memStore (sp-16) (a[15].get 64))
      code_l1107b0 (by decide)
  let m3 := memStore m2 (sp-24) (a[14].get 64)
  have store3 : StoreOk Extracted.programImage m3 (sp-32) 8 0x1107b5 2 :=
    storeGuard (off := 5) ((((stackSlot entry (off := 32) (by decide) (by decide : 8 ≤ (32 : BitVec 64).toNat)).memStore (sp-8) (a[5].get 64)).memStore (sp-16) (a[15].get 64)).memStore (sp-24) (a[14].get 64))
      code_l1107b0 (by decide)
  let m4 := memStore m3 (sp-32) (a[13].get 64)
  have store4 : StoreOk Extracted.programImage m4 (sp-40) 8 0x1107b7 2 :=
    storeGuard (off := 7) (((((stackSlot entry (off := 40) (by decide) (by decide : 8 ≤ (40 : BitVec 64).toNat)).memStore (sp-8) (a[5].get 64)).memStore (sp-16) (a[15].get 64)).memStore (sp-24) (a[14].get 64)).memStore (sp-32) (a[13].get 64))
      code_l1107b0 (by decide)
  let m5 := memStore m4 (sp-40) (a[12].get 64)
  have store5 : StoreOk Extracted.programImage m5 (sp-48) 8 0x1107b9 1 :=
    storeGuard (off := 9) ((((((stackSlot entry (off := 48) (by decide) (by decide : 8 ≤ (48 : BitVec 64).toNat)).memStore (sp-8) (a[5].get 64)).memStore (sp-16) (a[15].get 64)).memStore (sp-24) (a[14].get 64)).memStore (sp-32) (a[13].get 64)).memStore (sp-40) (a[12].get 64))
      code_l1107b0 (by decide)
  let m6 := memStore m5 (sp-48) (a[3].get 64)
  have store6 : StoreOk Extracted.programImage m6 (sp-120) 8 0x1107ca 5 :=
    storeGuard (off := 26) (((((((stackSlot entry (off := 120) (by decide) (by decide : 8 ≤ (120 : BitVec 64).toNat)).memStore (sp-8) (a[5].get 64)).memStore (sp-16) (a[15].get 64)).memStore (sp-24) (a[14].get 64)).memStore (sp-32) (a[13].get 64)).memStore (sp-40) (a[12].get 64)).memStore (sp-48) (a[3].get 64))
      code_l1107b0 (by decide)
  let m7 := memStore m6 (sp-120) (dst)
  have store7 : StoreOk Extracted.programImage m7 (sp-144) 8 0x1107e5 5 :=
    storeGuard (off := 53) ((((((((stackSlot entry (off := 144) (by decide) (by decide : 8 ≤ (144 : BitVec 64).toNat)).memStore (sp-8) (a[5].get 64)).memStore (sp-16) (a[15].get 64)).memStore (sp-24) (a[14].get 64)).memStore (sp-32) (a[13].get 64)).memStore (sp-40) (a[12].get 64)).memStore (sp-48) (a[3].get 64)).memStore (sp-120) (dst))
      code_l1107b0 (by decide)
  refine ⟨?_, ?step, ?post⟩
  case step =>
    dsimp only [m1, m2, m3, m4, m5, m6, m7] at store1 store2 store3 store4 store5 store6 store7
    cfg_eval [rsp, di, si, dx, cx, r8, r9, store0, store1, store2, store3, store4, store5, store6, store7]
    repeat' first
      | rw [ite_eq_left store2] | rw [ite_eq_left store3] | rw [ite_eq_left store4]
      | rw [ite_eq_left store5] | rw [ite_eq_left store6] | rw [ite_eq_left store7]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, bound⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | exact entry.saved 5 (by decide) | exact entry.saved 14 (by decide)

end K256.Proofs.Verify.Core.Lincomb.Recode
