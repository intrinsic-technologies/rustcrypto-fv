import K256.Proofs.Signing.Composition.Attempt.State
import K256.Proofs.Signing.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Composition.Attempt.Decode

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Signing.LIR
open Verify.Core (Registers)

def decoderMemory (m : Ram) (base : BitVec 64) : Ram :=
  let m3 := memStore m (base+480) (memLoad m (base+408) 64)
  let m2 := memStore m3 (base+472) (memLoad m (base+400) 64)
  let m1 := memStore m2 (base+464) (memLoad m (base+392) 64)
  let m0 := memStore m1 (base+456) (memLoad m (base+384) 64)
  memStore m0 (base-8) (0x10591b : BitVec 64)

def decoderArgs (a : Registers) (m : Ram) (base : BitVec 64) : Registers :=
  let args := (a.set 0 ⟨64,memLoad m (base+384) 64⟩).set 1 ⟨64,memLoad m (base+392) 64⟩
  let args := args.set 4 ⟨64,base-8⟩
  (args.set 6 ⟨64,base+456⟩).set 7 ⟨64,base+8⟩

set_option maxHeartbeats 900000 in
theorem decoderBlock {a : Registers} {m : Ram} {base : BitVec 64}
    (rsp : a[4].get 64 = base) (rbx : a[3].get 64 = base+456)
    (r12 : a[12].get 64 = base+8)
    (win : Writable Extracted.programImage m (base-8) 496) :
    program.runBlock (dialect Extracted.programImage) ⟨.l1058d0,a,m⟩ =
      .call ⟨.l109e60,decoderArgs a m base,decoderMemory m base⟩ (resume .l10591b 0x10591b) := by
  cfg_eval [rsp,rbx,r12]
  repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1058d0)
  simp (disch := store_disch) only [memLoad_memStore_of_rangeApart]
  unfold decoderArgs decoderMemory
  congr 2
  apply (show ∀ {u v : Vector Value Reg.count},
    (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
      fun h => Vector.ext fun i hi => h ⟨i,hi⟩)
  intro i
  finite_cases i <;> simp only [Vector.getElem_set] <;> rfl

theorem decoderWord (m : Ram) (base : BitVec 64) (i : Nat) (hi : i < 4) :
    Common.scalarWord (decoderMemory m base) (base+456) i = Common.scalarWord m (base+384) i := by
  obtain rfl|rfl|rfl|rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals
    simp (disch := first | store_disch | decide) only [Common.scalarWord,decoderMemory,
      Nat.reduceSub,Nat.reduceMul,reduceAddOffset,
      BitVec.add_zero,memLoad_memStore_of_rangeApart,memLoad_memStore_same]
  all_goals rfl

end K256.Proofs.Signing.Composition.Attempt.Decode
