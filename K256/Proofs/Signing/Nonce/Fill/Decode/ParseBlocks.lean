import K256.Proofs.Signing.Nonce.Fill.State
import K256.Proofs.Verify.LIR.Fn100a40
import K256.Proofs.Verify.Core.Affine.Call
import K256.Proofs.Verify.Choice
import K256.Proofs.Verify.Core.Scalars.Digest.Fill.Call
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
open Verify.Core (Registers Reaches)

theorem orderScanLength {a : Registers} {m : Ram} {base : BitVec 64}
    (rsp : a[4].get 64 = base) (area : Readable m (base+48) 8)
    (size : memLoad m (base+48) 64 = 32) :
    ∃ b, Reaches .l100bf0 a m .l100bf8 b m ∧ b[6] = ⟨64,32⟩ ∧ b[13] = ⟨64,32⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,4,5,8,9,12,14,15,22,39,50,51] → b[i] = a[i] := by
  refine ⟨?_,.single ?next,?post⟩
  case next =>
    change (program.runBlock (dialect Extracted.programImage) _).next _ [] = _
    cfg_eval [rsp,size]
    have step : LoadOk m (base+48) 8 := LoadOk.of_region area (Nat.le_refl _) (Nat.le_refl _)
    simp only [step, ite_true, CFG.Transfer.next]
    rfl
  case post =>
    refine ⟨rfl,rfl,?_⟩
    rintro ⟨i, _⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

def parserSetupWrites (base : BitVec 64) : List MemoryRegion :=
  [⟨(base-8).toNat,8⟩, ⟨(base+60).toNat,4⟩, ⟨(base+104).toNat,32⟩]

theorem enterParser {a : Registers} {m : Ram} {base src : BitVec 64}
    (rsp : a[4].get 64 = base) (rspLow : 8 ≤ base.toNat)
    (bits : a[8] = ⟨64,256⟩)
    (area : Writable Extracted.programImage m (base-8) 144)
    (srcSlot : memLoad m (base+40) 64 = src) :
    ∃ (b : Registers) (n : Ram), program.runBlock (dialect Extracted.programImage) ⟨.l100bf8,a,m⟩ =
      .call ⟨.l127d70,b,n⟩ (Verify.resumeAt .l100c38 0x100c38) ∧
      RamWriteFrame m n (parserSetupWrites base) ∧ memLoad n (base-8) 64 = 0x100c38 ∧
      b[4] = ⟨64,base-8⟩ ∧ b[1] = ⟨64,4⟩ ∧ b[2] = ⟨64,base+104⟩ ∧ b[7] = ⟨64,src⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,6,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  have lim := area.readable.low
  have lower : (base - 8).toNat = base.toNat - 8 := BitVec.toNat_sub_of_le (by
    change 8 ≤ base.toNat
    exact rspLow)
  have b8 : a[8].get 64 = 256 := congrArg (Value.get 64) bits
  refine ⟨?_, ?_, ?step, ?post⟩
  case step =>
    cfg_eval [rsp,b8]
    segment_words [srcSlot]
    have code : ∀ x ∈ codeRange 0x100bf8 bytes_l100bf8, x ∈ Extracted.programImage :=
      fun x hx => Verify.Core.Affine.coreText x (code_l100bf8 x hx)
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code)
    rfl
  case post =>
    refine ⟨?_,?_,rfl,rfl,rfl,rfl,?_⟩
    · unfold parserSetupWrites
      slot_state region
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · rintro ⟨i,_⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        first | rfl | exact bits.symm

theorem parseStatus {a : Registers} {m : Ram} (status : a[0].get 8 = 255) :
    ∃ b, Reaches .l100c38 a m .l100c40 b m ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) := by
  have low : (a[0].get 64).setWidth 8 = 255 := by
    simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)] using status
  refine ⟨?_, .single ?step, ?kept⟩
  case step =>
    change (program.runBlock (dialect Extracted.programImage) _).next _ [] = _
    cfg_eval [low, cmpSpec_ZF]
    rfl
  case kept =>
    rintro ⟨i, _⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Signing.Nonce.Fill
