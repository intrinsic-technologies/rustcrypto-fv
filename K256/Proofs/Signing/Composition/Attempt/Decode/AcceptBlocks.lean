import K256.Proofs.Signing.Composition.Attempt.Decode.CallFrame
import K256.Proofs.Signing.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Composition.Attempt.Decode

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Signing.LIR
open Verify.Core (Registers)

def copySelected (m : Ram) (base : BitVec 64) : Ram :=
  let m0 := memStore m (base+128) (memLoad m (base+192) 64)
  let m1 := memStore m0 (base+136) (memLoad m (base+200) 64)
  let m2 := memStore m1 (base+144) (memLoad m (base+208) 64)
  memStore m2 (base+152) (memLoad m (base+216) 64)

set_option maxHeartbeats 950000 in
theorem acceptCallBlock {a : Registers} {m : Ram} {base : BitVec 64}
    (rsp : a[4].get 64 = base) (nonzero : (a[0].get 64).setWidth 8 = 1)
    (inRange : (a[14].get 64).setWidth 8 = 1)
    (win : Writable Extracted.programImage m (base-8) 232) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l1059a8,a,m⟩ =
      .call ⟨.l127d50,b,memStore (copySelected m base) (base-8) (0x1059f3 : BitVec 64)⟩
        (resume .l1059f3 0x1059f3) ∧ b[4] = ⟨64,base-8⟩ ∧ b[7] = ⟨64,1⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,6,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i]) ∧
      b[1].width = 64 ∧ b[2].width = 64 := by
  refine ⟨?b,?path,?sp,?di,?keep,?c1,?c2⟩
  case path =>
    cfg_eval [rsp]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1059a8)
    simp (disch := store_disch) only [memLoad_memStore_of_rangeApart]
    rfl
  case sp => rfl
  case di =>
    change Value.mk 64 _ = ⟨64,1⟩
    congr 1
    rw [setWidth_mergeGPR8,nonzero,inRange]
    rfl
  case keep =>
    intro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  case c1 => rfl
  case c2 => rfl

theorem acceptBranch {a : Registers} {m : Ram} (bit : a[0] = ⟨64,1⟩) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l1059f3,a,m⟩ =
      .jump ⟨.l1059fb,b,m⟩ ∧
    (∀ i : Fin Reg.count, i.val ∈ [1,2,3,4,5,6,7,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i]) := by
  refine ⟨a.set 19 (Value.ofBool true),?path,?keep⟩
  case path =>
    have zf : (cmpSpec ((a[0].get 64).setWidth 8) 1).ZF = true := by
      rw [bit]
      decide
    cfg_eval
    simp only [zf,Bool.not_true,Bool.false_eq_true,↓reduceIte]
    congr 2
    apply (show ∀ {u v : Vector Value Reg.count},
      (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from fun h => Vector.ext fun i hi => h ⟨i,hi⟩)
    intro i
    finite_cases i <;> simp only [Vector.getElem_set] <;> rfl
  case keep =>
    intro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    change (a.set 19 (Value.ofBool true))[i] = a[i]
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp (config := {decide := true}) only [Vector.getElem_set,↓reduceIte]

theorem copySelectedFrame {s : RamState} {secret msg : ByteArray} {m : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) :
    RamWriteFrame m (copySelected m (sp s)) (workRegions s) :=
  ((((RamWriteFrame.refl m _).memStore _ (localSlot call (off:=128) (by decide))).memStore _
    (localSlot call (off:=136) (by decide))).memStore _ (localSlot call (off:=144) (by decide))).memStore _
    (localSlot call (off:=152) (by decide))

theorem copySelectedWords {m : Ram} {base : BitVec 64} {w : Vector (BitVec 64) 4}
    (values : WordsAt m (base+192) 64 w) :
    WordsAt (copySelected m base) (base+128) 64 w := by
  intro i hi
  obtain rfl|rfl|rfl|rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals
    simpa (disch := first | store_disch | decide) only [copySelected,wordAddr,Nat.reduceDiv,Nat.reduceMul,
      BitVec.add_zero,reduceAddOffset,memLoad_memStore_of_rangeApart,memLoad_memStore_same] using values _ hi

end K256.Proofs.Signing.Composition.Attempt.Decode
