import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.Verify.Core.Lincomb.Prepare.State

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

abbrev digitTemp (sp : BitVec 64) := frameSp sp + 0x38
abbrev digitCallSp (sp : BitVec 64) := frameSp sp - 8

abbrev digitSaved : List Nat := [3,12,13,14,22,39,50,51]

structure SerializeArgs (a b : Registers) (sp src : BitVec 64) : Prop where
  rsp : b[4] = ⟨64, digitCallSp sp⟩
  si : b[6] = ⟨64, src⟩
  di : b[7] = ⟨64, digitTemp sp⟩
  bp : b[5] = a[5]
  temp : b[15] = ⟨64, digitTemp sp⟩
  keep : ∀ i : Fin Reg.count, i.val ∈ digitSaved → b[i] = a[i]

structure RecodeArgs (a b : Registers) (sp digits dst : BitVec 64) : Prop where
  rsp : b[4] = ⟨64, digitCallSp sp⟩
  bp : b[5] = ⟨64, digits⟩
  di : b[7].get 64 = dst
  si : b[6].get 64 = 257
  dx : b[2].get 64 = digitTemp sp
  cx : b[1].get 64 = 16
  r8 : b[8].get 64 = 128
  r9 : b[9].get 64 = 5
  temp : b[15] = a[15]
  keep : ∀ i : Fin Reg.count, i.val ∈ digitSaved → b[i] = a[i]

set_option maxRecDepth 1600 in
theorem serializeFirstBlock {a : Registers} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = frameSp sp)
    (push : StoreOk Extracted.programImage m (digitCallSp sp) 8 0x10f4bf 5) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l10f4af,a,m⟩ =
      .call ⟨.l10a2f0,b,memStore m (digitCallSp sp) (0x10f4c4 : BitVec 64)⟩
        (callResume .l10f4c4 0x10f4c4) ∧ SerializeArgs a b sp (frameSp sp + 0xe0) := by
  refine ⟨?_, ?run, ?args⟩
  case run => cfg_eval [rsp, push]; rfl
  case args =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, hi⟩ h
    simp only [digitSaved, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

set_option maxRecDepth 1600 in
theorem recodeFirstBlock {a : Registers} {m : Ram} {sp digits : BitVec 64}
    (rsp : a[4].get 64 = frameSp sp) (temp : a[15].get 64 = digitTemp sp)
    (ptr : memLoad m (frameSp sp + 0xd8) 64 = digits)
    (read : LoadOk m (frameSp sp + 0xd8) 8)
    (push : StoreOk Extracted.programImage m (digitCallSp sp) 8 0x10f4e9 5) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l10f4c4,a,m⟩ =
      .call ⟨.l1107b0,b,memStore m (digitCallSp sp) (0x10f4ee : BitVec 64)⟩
        (callResume .l10f4ee 0x10f4ee) ∧ RecodeArgs a b sp digits (digits + 8) := by
  refine ⟨?_, ?run, ?args⟩
  case run => cfg_eval [rsp, temp, ptr, read, push]; rfl
  case args =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, hi⟩ h
    simp only [digitSaved, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

set_option maxRecDepth 1600 in
theorem serializeSecondBlock {a : Registers} {m : Ram} {sp digits value : BitVec 64}
    (rsp : a[4].get 64 = frameSp sp) (bp : a[5].get 64 = digits)
    (ax : a[0].get 64 = value)
    (store : StoreOk Extracted.programImage m digits 8 0x10f4ee 4)
    (push : StoreOk Extracted.programImage (memStore m digits value) (digitCallSp sp) 8 0x10f502 5) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l10f4ee,a,m⟩ =
      .call ⟨.l10a2f0,b,memStore (memStore m digits value) (digitCallSp sp) (0x10f507 : BitVec 64)⟩
        (callResume .l10f507 0x10f507) ∧ SerializeArgs a b sp (frameSp sp + 0xb0) := by
  refine ⟨?_, ?run, ?args⟩
  case run => cfg_eval [rsp, bp, ax, store, push]; rfl
  case args =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, hi⟩ h
    simp only [digitSaved, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

set_option maxRecDepth 1600 in
theorem recodeSecondBlock {a : Registers} {m : Ram} {sp digits : BitVec 64}
    (rsp : a[4].get 64 = frameSp sp) (temp : a[15].get 64 = digitTemp sp)
    (bp : a[5] = ⟨64, digits⟩)
    (push : StoreOk Extracted.programImage m (digitCallSp sp) 8 0x10f527 5) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l10f507,a,m⟩ =
      .call ⟨.l1107b0,b,memStore m (digitCallSp sp) (0x10f52c : BitVec 64)⟩
        (callResume .l10f52c 0x10f52c) ∧ RecodeArgs a b sp digits (digits + 0x118) := by
  have bpGet : a[5].get 64 = digits := congrArg (Value.get 64) bp
  refine ⟨?_, ?run, ?args⟩
  case run => cfg_eval [rsp, temp, bpGet, push]; rfl
  case args =>
    refine ⟨rfl, bp, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, hi⟩ h
    simp only [digitSaved, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Verify.Core.Lincomb.Prepare
