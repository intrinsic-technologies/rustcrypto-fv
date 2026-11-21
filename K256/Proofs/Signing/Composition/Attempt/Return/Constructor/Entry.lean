import K256.Proofs.Signing.Composition.Attempt.Return.Constructor.State
import K256.Proofs.Signing.Composition.Attempt.Memory
import K256.Proofs.Signing.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Composition.Attempt.Return.Constructor

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Signing.LIR
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

def entryMemory (m : Ram) (base : BitVec 64) : Ram :=
  let m3 := memStore m (base+184) (memLoad m (base+152) 64)
  let m2 := memStore m3 (base+176) (memLoad m (base+144) 64)
  let m1 := memStore m2 (base+168) (memLoad m (base+136) 64)
  let m0 := memStore m1 (base+160) (memLoad m (base+128) 64)
  memStore m0 (base-8) (0x105d35 : BitVec 64)

def entryArgs (a : Registers) (m : Ram) (base : BitVec 64) : Registers :=
  let args := (a.set 0 ⟨64,memLoad m (base+128) 64⟩).set 1 ⟨64,memLoad m (base+136) 64⟩
  let args := args.set 4 ⟨64,base-8⟩
  ((args.set 6 ⟨64,base+160⟩).set 7 ⟨64,base+8⟩).set 2 ⟨64,base+456⟩

set_option maxHeartbeats 900000 in
theorem entryBlock {a : Registers} {m : Ram} {base : BitVec 64}
    (rsp : a[4].get 64 = base) (r14 : a[14].get 64 = base+160) (r15 : a[15].get 64 = base+456)
    (r12 : a[12].get 64 = base+8)
    (win : Writable Extracted.programImage m (base-8) 200) :
    program.runBlock (dialect Extracted.programImage) ⟨.l105ce7,a,m⟩ =
      .call ⟨.l103450,entryArgs a m base,entryMemory m base⟩ (resume .l105d35 0x105d35) := by
  cfg_eval [rsp,r14,r15,r12]
  repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l105ce7)
  simp (disch := store_disch) only [memLoad_memStore_of_rangeApart]
  unfold entryArgs entryMemory
  congr 2
  apply (show ∀ {u v : Vector Value Reg.count},
    (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
      fun h => Vector.ext fun i hi => h ⟨i,hi⟩)
  intro i
  finite_cases i <;> simp only [Vector.getElem_set] <;> rfl

private theorem entryFrame {s : RamState} {secret msg : ByteArray} (m : Ram)
    (call : ValidCall signingKeyTrySign s [secret,msg]) :
    RamWriteFrame m (entryMemory m (sp s)) (workRegions s) := by
  obtain ⟨room,high,base⟩ := stackBounds call
  have low : (sp s-9904).toNat = (sp s).toNat-9904 := belowNat call (by decide)
  have slot : (sp s-8).toNat = (sp s).toNat-8 := belowNat call (by decide)
  have localSlot {i : Nat} (hi : i+8 ≤ 344) :
      InRegions (workRegions s) (sp s+BitVec.ofNat 64 i) 8 := by
    refine ⟨_,List.mem_cons_self,?_⟩
    change (sp s-9904).toNat ≤ _ ∧ _ + 8 ≤ (sp s-9904).toNat + 10248 ∧ _ + 8 ≤ 2^64
    rw [low,offsetNat call (by omega)]
    omega
  have push : InRegions (workRegions s) (sp s-8) 8 := by
    refine ⟨_,List.mem_cons_self,?_⟩
    change (sp s-9904).toNat ≤ _ ∧ _ + 8 ≤ (sp s-9904).toNat + 10248 ∧ _ + 8 ≤ 2^64
    rw [low,slot]
    omega
  exact (((((RamWriteFrame.refl m _).memStore _ (localSlot (i:=184) (by decide))).memStore _
    (localSlot (i:=176) (by decide))).memStore _ (localSlot (i:=168) (by decide))).memStore _
    (localSlot (i:=160) (by decide))).memStore _ push

private theorem entryWords {m : Ram} {base : BitVec 64} {r sigS : Nat}
    (first : WordsAt m (base+128) 64 (scalarWords r))
    (second : WordsAt m (base+456) 64 (scalarWords sigS)) :
    WordsAt (entryMemory m base) (base+160) 64 (scalarWords r) ∧
      WordsAt (entryMemory m base) (base+456) 64 (scalarWords sigS) := by
  constructor <;> intro i hi
  · refine Eq.trans ?_ (first i hi)
    obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    all_goals simp (disch := first | decide | store_disch) only [wordAddr, Nat.reduceDiv, Nat.reduceMul,
      reduceAddOffset,BitVec.add_zero,entryMemory,memLoad_memStore_same,memLoad_memStore_of_rangeApart]
  · refine Eq.trans ?_ (second i hi)
    obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    all_goals simp (disch := first | decide | store_disch) only [wordAddr, Nat.reduceDiv, Nat.reduceMul,
      reduceAddOffset,BitVec.add_zero,entryMemory,memLoad_memStore_of_rangeApart]

theorem enter {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {st : State} {r sigS : Nat} {a : Registers} {m : Ram}
    (words : SignatureScalars s d msg st r sigS a m) :
    ∃ b n, Reach (core .l105ce7 a m) (inside .l103450 b n) ∧
      Entry s d msg st r sigS b n := by
  obtain ⟨first,second⟩ := entryWords words.rWords words.sWords
  have write := entryFrame m call
  let b := entryArgs a m (sp s)
  let n := entryMemory m (sp s)
  have win : Writable Extracted.programImage m (sp s-8) 200 := by
    rw [addr_sub]
    exact stackWindow call words.toMemory (by decide)
  have run := entryBlock (m := m) (a := a) (base := sp s)
    (by rw [words.rsp]; rfl) (by rw [words.temp]; rfl)
    (by rw [words.r15]; rfl) (by rw [words.r12]; rfl) win
  refine ⟨b,n,.step (b := inside .l103450 b n) ?_ (.refl _),words.toLoopMemory.preserve_work call write,
    ?regs,?_,?_,?_,?_,?_,memLoad_memStore_same _ _ _ (by decide) (by decide),first,second⟩
  case regs =>
    constructor
    case widths =>
      intro ⟨i,hi⟩ member
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp only [b,entryArgs,Fin.getElem_fin,Vector.getElem_set]
      all_goals first | rfl | exact words.widths 8 (by decide) | exact words.widths 9 (by decide)
    all_goals simp only [b,entryArgs,Vector.getElem_set]
    all_goals first | rfl | exact words.df | exact words.rbx | exact words.rbp | exact words.r12
                    | exact words.r13 | exact words.r14 | exact words.r15 | exact words.fp
  · exact congrArg (Transfer.next (dialect Extracted.programImage) [resume .l102795 0x102795]) run
  all_goals simp only [b,entryArgs,Vector.getElem_set]
  all_goals first | rfl | exact words.temp

end K256.Proofs.Signing.Composition.Attempt.Return.Constructor
