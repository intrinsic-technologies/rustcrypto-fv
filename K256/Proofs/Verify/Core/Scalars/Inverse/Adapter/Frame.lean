import K256.Proofs.Verify.Core.Scalars.Inverse.Adapter.Setup
import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.State
import K256.Proofs.Verify.Core.Memory

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Adapter

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

abbrev base (fr : Activation) := fr.rsp - 584
abbrev stageWrites (x : BitVec 64) : List MemoryRegion := [⟨(x-8).toNat,104⟩]
abbrev writes (x : BitVec 64) : List MemoryRegion := [⟨(x-728).toNat,961⟩]

theorem stagedFrame (b : Registers) (m : Ram) {x : BitVec 64} (room : 8 ≤ x.toNat)
    (low : x.toNat + 96 ≤ 2^32) : RamWriteFrame m (staged b m x) (stageWrites x) := by
  have slot (d : BitVec 64) (hd : d.toNat ≤ 88) : InRegions (stageWrites x) (x+d) 8 := by
    refine ⟨_,List.mem_cons_self,?_⟩
    change (x-8).toNat ≤ _ ∧ _ + 8 ≤ (x-8).toNat + 104 ∧ _
    bv_omega
  have child : InRegions (stageWrites x) (x-8) 8 := by
    refine ⟨_,List.mem_cons_self,Nat.le_refl _,?_⟩
    change _ + 8 ≤ (x-8).toNat + 104 ∧ _; bv_omega
  unfold staged pushed
  apply RamWriteFrame.memStore _ _ child
  repeat' apply RamWriteFrame.memStore _ _ (slot _ (by decide))
  exact .refl _ _

theorem stagedSaved {b : Registers} {m : Ram} {x : BitVec 64} (i : Fin Reg.count) (d : BitVec 64)
    (hd : (i.val,d) ∈ [(3,48),(12,56),(13,64),(14,72),(15,80)]) :
    memLoad (staged b m x) (x+d) 64 = b[i].get 64 := by
  rcases i with ⟨i,hi⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hd
  rcases hd with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  all_goals simp (disch := store_disch) only [staged,memLoad_memStore_same,memLoad_memStore_of_rangeApart] <;> rfl

theorem stagedRet (b : Registers) (m : Ram) (x : BitVec 64) :
    memLoad (staged b m x) (x+88) 64 = 0x10519d := by
  simp (disch := store_disch) only [staged,pushed,memLoad_memStore_same,memLoad_memStore_of_rangeApart]

theorem calleeSaved {a : Registers} {m : Ram} {x : BitVec 64} {out : Output Value Ram Reg.count}
    (res : Generate.Generator.Affine.Invert.Core.CalleeResult a m (x-8) (x-8+16) 0x10a0f2 720 33 out)
    (room : 728 ≤ x.toNat) (low : x.toNat + 96 ≤ 2^32) (d : BitVec 64) (hd : 48 ≤ d.toNat ∧ d.toNat ≤ 88) :
    memLoad out.store (x+d) 64 = memLoad m (x+d) 64 := by
  apply res.frame.memLoad_eq
  refine ⟨by change _ + 8 ≤ 2^64; bv_omega,?_⟩
  intro reg hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl <;> right <;> dsimp <;> bv_omega

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}
    (e : Core.Entry fr a p digest r s)
include e

theorem writesWithin : RegionsWithin (writes (base fr)) [fr.region] := by
  intro reg hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨_,List.mem_cons_self,?_⟩
  have room := e.stackRoom
  have bot := e.low_toNat
  change fr.low.toNat ≤ (fr.rsp-584-728).toNat ∧ _ + 961 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
  bv_omega

theorem enterBatch {b c k : Registers} {m : Ram} (h : Reduced fr b m digest r s)
    (sp : k[4] = ⟨64,base fr-8⟩) (dst : k[7] = ⟨64,base fr+8⟩)
    (src : k[6] = ⟨64,base fr+320⟩) (cx : k[1] = ⟨64,0xb4f20099aa774ec1⟩)
    (dx : k[2] = ⟨64,0x2021a0⟩) (r8 : k[8] = ⟨64,0x202180⟩) (df : k[22] = ⟨1,0⟩) :
    Batch.Entry k (staged c m (base fr)) (base fr-8) s := by
  let x := base fr
  have room := e.stackRoom
  have top := e.low
  have bot := e.low_toNat
  have xr : 728 ≤ x.toNat := by dsimp only [x,base]; bv_omega
  have xl : x.toNat + 360 ≤ 2^32 := by dsimp only [x,base]; bv_omega
  have stage := stagedFrame c m (x := x) (by omega) (by omega)
  have within : RegionsWithin (stageWrites x) (writes x) := by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_cons_self,?_⟩
    change (x-728).toNat ≤ (x-8).toNat ∧ (x-8).toNat+104 ≤ (x-728).toNat+961
    bv_omega
  have area := (e.stack.of_frame h.frame).of_frame stage
  have align := h.atoms
  simp only [Fn104f20.frameAt,Fn104f20.frameAtG6,Atom.All,Atom.Holds] at align
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,aligned,_⟩ := align
  have dest : x-8+16 = x+8 := by bv_omega
  have source : x-8+328 = x+320 := by bv_omega
  have srcAddr : x+320 = localSp fr+224 := by dsimp only [x,base,localSp]; bv_omega
  refine ⟨⟨sp,by rw [dest]; exact dst,df,e.loaded_of_frame (h.frame.trans stage
    (fun reg hr => ?_)),by bv_omega,?_,?_,?_,by decide,?_,?_,?_⟩,?_,congrArg (Value.get 64) dx,
    congrArg (Value.get 64) cx,congrArg (Value.get 64) r8,?_,?_,by bv_omega,e.bounds.2.2.1,e.bounds.2.2.2⟩
  · obtain ⟨mid,hm,hlo,hhi⟩ := within reg hr
    obtain ⟨big,hb,lo,hi⟩ := writesWithin e mid hm
    exact ⟨big,hb,Nat.le_trans lo hlo,Nat.le_trans hhi hi⟩
  · change (fr.rsp-584-8).toNat % 16 = 8
    bv_omega
  · apply area.readable.sub <;> dsimp only [x,base] <;> bv_omega
  · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · apply area.sub <;> dsimp only [x,base] <;> bv_omega
  · apply area.sub <;> dsimp only [x,base] <;> bv_omega
  · right; bv_omega
  · rw [source]; exact congrArg (Value.get 64) src
  · apply area.readable.sub <;> dsimp only [x,base] <;> bv_omega
  · rw [source,srcAddr]
    apply h.sAt.of_frame stage (by decide)
    rw [← srcAddr]
    refine ⟨by change _ + 32 ≤ 2^64; bv_omega,?_⟩
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    right
    change (x-8).toNat+104 ≤ (x+320).toNat
    bv_omega

end K256.Proofs.Verify.Core.Scalars.Inverse.Adapter
