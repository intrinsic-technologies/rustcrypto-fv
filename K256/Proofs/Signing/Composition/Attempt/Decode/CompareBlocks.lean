import K256.Proofs.Signing.Composition.Attempt.Decode.SelectBlocks
import K256.Proofs.Signing.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Composition.Attempt.Decode

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Signing.LIR
open Verify.Core (Registers)

def compareMemory (m : Ram) (base : BitVec 64) : Ram :=
  memStore (zeroFour m (base+256)) (base-8) (0x10599c : BitVec 64)

def compareArgs (a : Registers) (base : BitVec 64) : Registers :=
  ((a.set 4 ⟨64,base-8⟩).set 6 ⟨64,base+256⟩).set 7 ⟨64,base+192⟩

set_option maxHeartbeats 1000000 in
theorem compareBlock {a : Registers} {m : Ram} {base : BitVec 64}
    (rsp : a[4].get 64 = base) (rbp : a[5].get 64 = base+192) (r13 : a[13].get 64 = base+256)
    (win : Writable Extracted.programImage m (base-8) 296) :
    program.runBlock (dialect Extracted.programImage) ⟨.l105961,a,m⟩ =
      .call ⟨.l10a280,compareArgs a base,compareMemory m base⟩ (resume .l10599c 0x10599c) := by
  cfg_eval [rsp,rbp,r13]
  repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l105961)
  unfold compareArgs compareMemory zeroFour
  simp only [reduceAddOffset]
  congr 2
  apply (show ∀ {u v : Vector Value Reg.count},
    (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from fun h => Vector.ext fun i hi => h ⟨i,hi⟩)
  intro i
  finite_cases i <;> simp only [Vector.getElem_set] <;> rfl

theorem invertChoiceBlock {a : Registers} {m : Ram} {base : BitVec 64}
    (rsp : a[4].get 64 = base) (bit : (a[0].get 64).setWidth 8 = 0)
    (win : Writable Extracted.programImage m (base-8) 8) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10599c,a,m⟩ =
      .call ⟨.l127d50,b,memStore m (base-8) (0x1059a8 : BitVec 64)⟩ (resume .l1059a8 0x1059a8) ∧
      b[4] = ⟨64,base-8⟩ ∧ b[7] = ⟨64,1⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,6,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i]) := by
  refine ⟨?b,?path,?sp,?di,?keep⟩
  case path =>
    cfg_eval [rsp]
    refine Eq.trans (ite_eq_left ?_) ?_
    · slot_guard using code_l10599c
    · rfl
  case sp => rfl
  case di =>
    change Value.mk 64 _ = ⟨64,1⟩
    congr 1
    rw [setWidth_mergeGPR8,setWidth_mergeGPR8,bit]
    rfl
  case keep =>
    intro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl


end K256.Proofs.Signing.Composition.Attempt.Decode
