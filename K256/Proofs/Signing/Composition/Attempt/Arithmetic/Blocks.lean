import K256.Proofs.Signing.Composition.Attempt.State
import K256.Proofs.Common.Tactic
import K256.Proofs.Signing.LIR.Generated.Values

namespace K256.Proofs.Signing.Composition.Attempt.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Verify.Core (Registers)
open Signing.LIR

abbrev SavedRegs (b a : Registers) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]

local macro "saved_regs" : tactic => `(tactic|
  (intro ⟨i, _⟩ hi
   simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
   rcases hi with h|h|h|h|h|h|h|h|h|h <;> subst i <;> first | rfl | (simp (disch := decide) only [Fin.getElem_fin,Vector.getElem_set_ne,Vector.getElem_set_self]; rfl)))

local macro "run_call" code:term : tactic => `(tactic|
  (repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using $code)
   rfl))

def fillWrites (p : BitVec 64) : List MemoryRegion :=
  [⟨(p-8).toNat,48⟩, ⟨(p+192).toNat,32⟩, ⟨(p+456).toNat,4⟩]

set_option maxHeartbeats 1000000 in
theorem setupFill {a : Registers} {m : Ram} {p : BitVec 64}
    (rsp : a[4].get 64 = p) (src : a[14].get 64 = p+160) (dst : a[5].get 64 = p+192)
    (window : Writable Extracted.programImage m (p-8) 468) :
    ∃ (b : Registers) (n : Ram), program.runBlock (dialect Extracted.programImage) ⟨.l105b88,a,m⟩ =
        .call ⟨.l127d70,b,n⟩ (resume .l105bf2 0x105bf2) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[7] = ⟨64,p+160⟩ ∧ b[6] = ⟨64,32⟩ ∧
      b[2] = ⟨64,p+192⟩ ∧ b[1] = ⟨64,4⟩ ∧ b[8] = ⟨64,256⟩ ∧ b[9] = a[9] ∧
      SavedRegs b a ∧ RamWriteFrame m n (fillWrites p) ∧ memLoad n (p-8) 64 = 0x105bf2 := by
  let n := memStore m (p+8) (1 : BitVec 8)
  let n := memStore n (p+8) (0 : BitVec 8)
  let n := memStore n (p+8) (0 : BitVec 8)
  let n := memStore n (p+8) (0 : BitVec 8)
  let n := memStore n (p+456) (256 : BitVec 32)
  let n := memStore n (p+216) (0 : BitVec 64)
  let n := memStore n (p+208) (0 : BitVec 64)
  let n := memStore n (p+200) (0 : BitVec 64)
  let n := memStore n (p+192) (0 : BitVec 64)
  let n := memStore n (p-8) (0x105bf2 : BitVec 64)
  refine ⟨?b,n,?run,?post⟩
  case run =>
    cfg_eval [rsp,src,dst]
    run_call code_l105b88
  case post =>
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,?kept,?frame,?tag⟩
    case kept => saved_regs
    case frame =>
      have low := window.readable.low
      have pLow : 8 ≤ p.toNat := by
        simp only [BitVec.toNat_sub,BitVec.reduceToNat,Nat.reducePow] at low
        have := p.isLt
        omega
      have base : (p-8).toNat = p.toNat-8 := BitVec.toNat_sub_of_le pLow
      rw [base] at low
      have slot (off len : Nat) (which : off+len ≤ 40 ∨ (192 ≤ off ∧ off+len ≤ 224) ∨
          (456 ≤ off ∧ off+len ≤ 460)) :
          InRegions (fillWrites p) (p+BitVec.ofNat 64 off) len := by
        have atNat (d : Nat) (h : d ≤ 460) : (p+BitVec.ofNat 64 d).toNat = p.toNat+d := by
          rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a := d) (by omega),
            Nat.mod_eq_of_lt (by omega)]
        have offNat := atNat off (by omega)
        rcases which with h|⟨h₁,h₂⟩|⟨h₁,h₂⟩
        · exact ⟨_,List.mem_cons_self,by simp only [InRegion,base,offNat]; omega⟩
        · exact ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,by
            change (p+192).toNat ≤ (p+BitVec.ofNat 64 off).toNat ∧
              (p+BitVec.ofNat 64 off).toNat + len ≤ (p+192).toNat + 32 ∧
              (p+BitVec.ofNat 64 off).toNat + len ≤ 2^64
            have addr : (p+192).toNat = p.toNat+192 := atNat 192 (by decide)
            rw [offNat,addr]
            omega⟩
        · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),by
            change (p+456).toNat ≤ (p+BitVec.ofNat 64 off).toNat ∧
              (p+BitVec.ofNat 64 off).toNat + len ≤ (p+456).toNat + 4 ∧
              (p+BitVec.ofNat 64 off).toNat + len ≤ 2^64
            have addr : (p+456).toNat = p.toNat+456 := atNat 456 (by decide)
            rw [offNat,addr]
            omega⟩
      dsimp only [n]
      apply RamWriteFrame.memStore _ _ (⟨_,List.mem_cons_self,by simp only [InRegion,base]; omega⟩)
      iterate 9
        apply RamWriteFrame.memStore _ _ (slot _ _ (by decide))
      exact .refl _ _
    case tag => exact memLoad_memStore_same _ _ _ (by decide) (by decide)

theorem afterFill {a : Registers} {m : Ram} (status : a[0].get 8 = 255) :
    ∃ b, Reach (core .l105bf2 a m) (core .l105bfa b m) ∧
      SavedRegs b a ∧ b[4] = a[4] ∧ b[2] = a[2] ∧ b[8] = a[8] ∧ b[9] = a[9] := by
  have low : (a[0].get 64).setWidth 8 = 255 := by
    simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)] using status
  refine ⟨?b,.single ?step,?post⟩
  case step =>
    change (program.runBlock (dialect Extracted.programImage) ⟨.l105bf2,a,m⟩).next _ _ = _
    cfg_eval [low]
    rfl
  case post => exact ⟨by saved_regs,rfl,rfl,rfl,rfl⟩

private def copyWords (m : Ram) (src dst : BitVec 64) : Ram :=
  let n := memStore m (dst + 24) (memLoad m (src + 24) 64)
  let n := memStore n (dst + 16) (memLoad m (src + 16) 64)
  let n := memStore n (dst + 8) (memLoad m (src + 8) 64)
  memStore n dst (memLoad m src 64)

local macro "copy_simp" : tactic => `(tactic|
  (simp (disch := store_disch) only [copyWords, BitVec.add_assoc, BitVec.reduceAdd,
    memLoad_memStore_same, memLoad_memStore_of_rangeApart]))

set_option maxHeartbeats 1000000 in
theorem setupReduce {a : Registers} {m : Ram} {p : BitVec 64} {x : Nat}
    (rsp : a[4].get 64 = p) (r12 : a[12].get 64 = p+8)
    (window : Writable Extracted.programImage m (p-8) 232)
    (src : WordsAt m (p+192) 64 (Generate.Generator.Multiply.scalarWords x)) :
    ∃ (b : Registers) (n : Ram), program.runBlock (dialect Extracted.programImage) ⟨.l105bfa,a,m⟩ =
        .call ⟨.l109f80,b,n⟩ (resume .l105c3e 0x105c3e) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[7] = ⟨64,p+128⟩ ∧ b[6] = ⟨64,p+8⟩ ∧
      b[1].width = 64 ∧ b[2] = a[2] ∧ b[8] = a[8] ∧ b[9] = a[9] ∧ SavedRegs b a ∧
      RamWriteFrame m n [⟨(p-8).toNat,48⟩] ∧ memLoad n (p-8) 64 = 0x105c3e ∧
      WordsAt n (p+8) 64 (Generate.Generator.Multiply.scalarWords x) := by
  let n := memStore (copyWords m (p+192) (p+8)) (p-8) (0x105c3e : BitVec 64)
  refine ⟨?b,n,?run,?post⟩
  case run =>
    cfg_eval [rsp,r12]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l105bfa)
    dsimp only [n,copyWords]
    copy_simp <;> rfl
  case post =>
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,?kept,?frame,?tag,?words⟩
    case kept => saved_regs
    case frame =>
      have low := window.readable.low
      dsimp only [n,copyWords]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      slot_state region
    case tag => exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    case words =>
      intro i hi
      rw [← src i hi]
      obtain rfl|rfl|rfl|rfl := show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by omega
      all_goals
        dsimp only [n]
        simp only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero]
        copy_simp


def productSetupWrites (p : BitVec 64) : List MemoryRegion :=
  [⟨(p-8).toNat,48⟩, ⟨(p+160).toNat,32⟩]

set_option maxHeartbeats 1500000 in
theorem setupProduct {a : Registers} {m : Ram} {p key : BitVec 64} {r kinv : Nat}
    (rsp : a[4].get 64 = p) (r12 : a[12].get 64 = p+8) (rbp : a[5].get 64 = p+192)
    (ptr : memLoad m (p+344) 64 = key)
    (window : Writable Extracted.programImage m (p-8) 464)
    (rwds : WordsAt m (p+128) 64 (Generate.Generator.Multiply.scalarWords r))
    (iwds : WordsAt m (p+424) 64 (Generate.Generator.Multiply.scalarWords kinv)) :
    ∃ (b : Registers) (n : Ram), program.runBlock (dialect Extracted.programImage) ⟨.l105c3e,a,m⟩ =
        .call ⟨.l109f70,b,n⟩ (resume .l105cc5 0x105cc5) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[7] = ⟨64,p+192⟩ ∧ b[6] = ⟨64,p+8⟩ ∧
      b[2] = ⟨64,key⟩ ∧ b[1].width = 64 ∧ SavedRegs b a ∧
      RamWriteFrame m n (productSetupWrites p) ∧ memLoad n (p-8) 64 = 0x105cc5 ∧
      WordsAt n (p+8) 64 (Generate.Generator.Multiply.scalarWords r) ∧
      WordsAt n (p+160) 64 (Generate.Generator.Multiply.scalarWords kinv) := by
  let v := copyWords m (p+424) (p+160)
  let n := memStore (copyWords v (p+128) (p+8)) (p-8) (0x105cc5 : BitVec 64)
  refine ⟨?b,n,?run,?post⟩
  case run =>
    cfg_eval [rsp,r12,rbp]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l105c3e)
    dsimp only [n,v,copyWords]
    simp (disch := store_disch) only [BitVec.add_assoc, BitVec.reduceAdd,
      memLoad_memStore_of_rangeApart, ptr] <;> rfl
  case post =>
    refine ⟨rfl,rfl,rfl,?keyReg,rfl,?kept,?frame,?tag,?r,?i⟩
    case keyReg =>
      first | rfl | (congr 1; simp (disch := store_disch) only [memLoad_memStore_of_rangeApart,ptr])
    case kept => saved_regs
    case frame =>
      have low := window.readable.low
      dsimp only [n,v,copyWords]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      unfold productSetupWrites
      slot_state region
    case tag => exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    case r =>
      intro i hi
      rw [← rwds i hi]
      obtain rfl|rfl|rfl|rfl := show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by omega
      all_goals
        dsimp only [n,v]
        simp only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero]
        copy_simp
    case i =>
      intro i hi
      rw [← iwds i hi]
      obtain rfl|rfl|rfl|rfl := show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by omega
      all_goals
        dsimp only [n,v]
        simp only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero]
        copy_simp

theorem setupAdd {a : Registers} {m : Ram} {p : BitVec 64}
    (rsp : a[4].get 64 = p) (r12 : a[12].get 64 = p+8)
    (r13 : a[13].get 64 = p+656) (rbp : a[5].get 64 = p+192)
    (window : Writable Extracted.programImage m (p-8) 8) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l105cc5,a,m⟩ =
        .call ⟨.l10a2e0,b,memStore m (p-8) (0x105cd6 : BitVec 64)⟩ (resume .l105cd6 0x105cd6) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[7] = ⟨64,p+8⟩ ∧ b[6] = ⟨64,p+656⟩ ∧ b[2] = ⟨64,p+192⟩ ∧
      b[1] = a[1] ∧ b[8] = a[8] ∧ b[9] = a[9] ∧
      SavedRegs b (a.set 13 ⟨64,p+192⟩) := by
  refine ⟨?b,?run,?post⟩
  case run =>
    cfg_eval [rsp,r12,r13,rbp]
    run_call code_l105cc5
  case post => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,by saved_regs⟩

theorem setupFinal {a : Registers} {m : Ram} {p : BitVec 64}
    (rsp : a[4].get 64 = p) (r12 : a[12].get 64 = p+8)
    (r14 : a[14].get 64 = p+160) (r15 : a[15].get 64 = p+456)
    (window : Writable Extracted.programImage m (p-8) 8) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l105cd6,a,m⟩ =
        .call ⟨.l109f60,b,memStore m (p-8) (0x105ce7 : BitVec 64)⟩ (resume .l105ce7 0x105ce7) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[7] = ⟨64,p+456⟩ ∧ b[6] = ⟨64,p+160⟩ ∧ b[2] = ⟨64,p+8⟩ ∧
      b[1] = a[1] ∧ SavedRegs b (a.set 3 ⟨64,p+456⟩) := by
  refine ⟨?b,?run,?post⟩
  case run =>
    cfg_eval [rsp,r12,r14,r15]
    run_call code_l105cd6
  case post => exact ⟨rfl,rfl,rfl,rfl,rfl,by saved_regs⟩

end K256.Proofs.Signing.Composition.Attempt.Arithmetic
