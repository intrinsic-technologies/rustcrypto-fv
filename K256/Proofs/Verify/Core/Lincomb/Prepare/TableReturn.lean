import K256.Proofs.Verify.Core.Lincomb.Prepare.State
import K256.Proofs.Verify.Core.Lincomb.Recode.Stack
import K256.Proofs.Generate.Generator.Multiply.Prepare.Copy
import K256.Proofs.Sec1.Wrapper.Copy.Execution
import K256.Proofs.Common.Lift.Generated.Values.Register2

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem tableReturn {initial a : Registers} {original m : Ram} {sp tables acc : BitVec 64}
    (entry : RoutineEntry initial original sp 0x558)
    (saved : SavedFrame initial sp tables a m)
    (accPtr : a[14].get 64 = acc)
    (read : Readable m acc 120)
    (write : Writable Extracted.programImage m (tables + 0x708) 120)
    (separate : acc.toNat + 120 ≤ (tables + 0x708).toNat ∨ (tables + 0x708).toNat + 120 ≤ acc.toNat)
    (ret : memLoad m sp 64 = memLoad original sp 64)
    (stack : Readable m (sp - 48) 56)
    (apart : Outside [⟨(tables + 0x708).toNat, 120⟩] (sp - 48) 56) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10f9e3, a, m⟩, []⟩ out ∧
      out.store = memCopy m (tables + 0x708) acc 120 ∧ out.tag = some ⟨64, memLoad original sp 64⟩ ∧
      out.values[4] = ⟨64, sp + 8⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = initial[i] := by
  let n := memCopy m (tables + 0x708) acc 120
  have room := entry.room
  have low := entry.returnSlot.low
  have nsp : (sp - 48).toNat = sp.toNat - 48 := by bv_omega
  have frame : RamWriteFrame m n [⟨(tables + 0x708).toNat, 120⟩] :=
    Sec1.Wrapper.Copy.memCopy_frame (.refl ..) ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _,
      by have := write.readable.low; change (tables + 0x708).toNat + 120 ≤ 2^64; omega⟩
  have memory (off : BitVec 64) (small : off.toNat ≤ 48) :
      memLoad n (sp - off) 64 = memLoad m (sp - off) 64 := by
    apply frame.memLoad_eq
    apply Generate.Generator.Affine.outside_subregion apart
    all_goals
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega : off.toNat ≤ sp.toNat))]
      omega
  have loads (off : BitVec 64) (small : off.toNat ≤ 48) : LoadOk n (sp - off) 8 := by
    apply LoadOk.of_region (stack.of_frame frame)
    all_goals
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega : off.toNat ≤ sp.toNat))]
      omega
  have last : memLoad n sp 64 = memLoad original sp 64 :=
    (by simpa only [show ∀ w : BitVec 64, w - 0 = w from BitVec.sub_zero] using memory 0 (by decide) : memLoad n sp 64 = memLoad m sp 64).trans ret
  have retOk : LoadOk n sp 8 := by simpa only [show ∀ w : BitVec 64, w - 0 = w from BitVec.sub_zero] using loads 0 (by decide)
  have inc := fun x hx => Common.fnCode_subset_programImage x (code_l10f9e3 x hx)
  have copy := Generate.Generator.Multiply.Prepare.copyGuard (count := 15) (size := 8) read
    (ParseSignature.storeOk_of_codeRange (off := 18) (len := 3) write inc (by decide)) separate
  have rsp := congrArg (Value.get 64) saved.rsp
  have table := congrArg (Value.get 64) saved.tableBase
  have df := congrArg (Value.get 1) ((saved.control 22 (by decide)).trans entry.df)
  have bx := (memory 48 (by decide)).trans saved.rbx
  have r12 := (memory 40 (by decide)).trans saved.r12
  have r13 := (memory 32 (by decide)).trans saved.r13
  have r14 := (memory 24 (by decide)).trans saved.r14
  have r15 := (memory 16 (by decide)).trans saved.r15
  have bp := (memory 8 (by decide)).trans saved.rbp
  change a[4].get 64 = sp - 0x2b8 at rsp
  change a[3].get 64 = tables at table
  change a[22].get 1 = 0 at df
  have returned := entry.returnLow
  refine ⟨?out, .done ?run, ?store, ?tag, ?rsp, ?saved⟩
  case run =>
    unfold Program.step
    cfg_eval [rsp,table,df,accPtr,Lift.reduceSubOffset,Lift.reduceAddOffset,
      BitVec.reduceAdd,BitVec.reduceSub]
    refine Eq.trans (congrArg _ (ite_eq_left (Or.inr copy))) ?_
    simp only [show memCopy m (tables + 0x708) acc 120 = n from rfl, bx,r12,r13,r14,r15,bp,last,
      retOk, returned, and_self, loads 48 (by decide), loads 40 (by decide),
      loads 32 (by decide), loads 24 (by decide), loads 16 (by decide), loads 8 (by decide), ite_true]
    rfl
  case store => rfl
  case tag => rfl
  case rsp => rfl
  case saved =>
    rintro ⟨i, hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact Recode.saveValue entry (i := 3) (by decide)
    · exact Recode.saveValue entry (i := 5) (by decide)
    · exact Recode.saveValue entry (i := 12) (by decide)
    · exact Recode.saveValue entry (i := 13) (by decide)
    · exact Recode.saveValue entry (i := 14) (by decide)
    · exact Recode.saveValue entry (i := 15) (by decide)
    · exact saved.control 22 (by decide)
    · exact saved.control 39 (by decide)
    · exact saved.control 50 (by decide)
    · exact saved.control 51 (by decide)

end K256.Proofs.Verify.Core.Lincomb.Prepare
