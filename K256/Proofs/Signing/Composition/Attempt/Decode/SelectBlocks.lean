import K256.Proofs.Signing.Composition.Attempt.Decode.CallFrame
import K256.Proofs.Signing.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Composition.Attempt.Decode

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Signing.LIR
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

def zeroFour (m : Ram) (dest : BitVec 64) : Ram :=
  let m := memStore m (dest+24) (0 : BitVec 64)
  let m := memStore m (dest+16) (0 : BitVec 64)
  let m := memStore m (dest+8) (0 : BitVec 64)
  memStore m dest (0 : BitVec 64)

def selectMemory (m : Ram) (base : BitVec 64) : Ram :=
  memStore (zeroFour m (base+160)) (base-8) (0x105961 : BitVec 64)

def selectArgs (a : Registers) (m : Ram) (base : BitVec 64) : Registers :=
  let flag := (memLoad m (base+40) 32).setWidth 64
  let a := (((a.set 14 ⟨64,flag⟩).set 1 ⟨64,flag⟩).set 2 ⟨64,base+8⟩).set 4 ⟨64,base-8⟩
  (a.set 6 ⟨64,base+160⟩).set 7 ⟨64,base+192⟩

set_option maxHeartbeats 1000000 in
theorem selectBlock {a : Registers} {m : Ram} {base : BitVec 64}
    (rsp : a[4].get 64 = base) (rbp : a[5].get 64 = base+192)
    (r12 : a[12].get 64 = base+8) (r15 : a[15].get 64 = base+160)
    (win : Writable Extracted.programImage m (base-8) 232) :
    program.runBlock (dialect Extracted.programImage) ⟨.l10591b,a,m⟩ =
      .call ⟨.l10a220,selectArgs a m base,selectMemory m base⟩ (resume .l105961 0x105961) := by
  cfg_eval [rsp,rbp,r12,r15]
  repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10591b)
  simp (disch := store_disch) only [memLoad_memStore_of_rangeApart]
  unfold selectArgs selectMemory zeroFour
  simp only [reduceAddOffset]
  congr 2
  apply (show ∀ {u v : Vector Value Reg.count},
    (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from fun h => Vector.ext fun i hi => h ⟨i,hi⟩)
  intro i
  finite_cases i <;> simp only [Vector.getElem_set] <;> rfl

theorem zeroFourFrame {s : RamState} {secret msg : ByteArray} {m : Ram} {off : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (fits : off+32 ≤ 344) :
    RamWriteFrame m (zeroFour m (sp s+BitVec.ofNat 64 off)) (workRegions s) := by
  unfold zeroFour
  have localStore (i : Nat) (hi : i+8 ≤ 32) :
      InRegions (workRegions s) (sp s+BitVec.ofNat 64 off+BitVec.ofNat 64 i) 8 := by
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact localSlot call (by omega)
  exact ((((RamWriteFrame.refl m _).memStore _ (localStore 24 (by decide))).memStore _
    (localStore 16 (by decide))).memStore _ (localStore 8 (by decide))).memStore _ (localSlot call (by omega))

theorem zeroFourWords {m : Ram} {dest : BitVec 64} :
    WordsAt (zeroFour m dest) dest 64 (Vector.replicate 4 0) := by
  intro i hi
  obtain rfl|rfl|rfl|rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals
    simp (disch := first | store_disch | decide) only [zeroFour,wordAddr,Nat.reduceDiv,Nat.reduceMul,
      BitVec.add_zero,BitVec.ofNat_eq_ofNat,memLoad_memStore_of_rangeApart,memLoad_memStore_same,Vector.getElem_replicate]

end K256.Proofs.Signing.Composition.Attempt.Decode
