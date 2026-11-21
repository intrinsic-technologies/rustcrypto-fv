import K256.Proofs.Signing.UpdateV.Finalize.Memory
import K256.Proofs.Signing.UpdateV.Finalize.Prologue
import K256.Proofs.Signing.UpdateV.Finalize.Outer
import K256.Proofs.Signing.UpdateV.Finalize.Padding

namespace K256.Proofs.Signing.UpdateV.Finalize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

structure Finalized (entry b : Registers) (m t : Ram) (sp dst : BitVec 64) : Prop where
  rsp : b[4] = ⟨64,sp - 360⟩
  output : b[3] = ⟨64,dst⟩
  kept : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = entry[i]
  writes : RamWriteFrame m t [scratch sp]
  slots : ∀ i : Fin 6,
    memLoad t (sp - (#v[48,8,40,32,24,16] : Vector (BitVec 64) 6)[i]) 64 =
      entry[(#v[3,5,12,13,14,15] : Vector (Fin Reg.count) 6)[i]].get 64

private theorem savedOffsetBound (i : Fin 6) :
    ((#v[48,8,40,32,24,16] : Vector (BitVec 64) 6)[i]).toNat ≤ 48 := by
  revert i
  decide +kernel

set_option maxRecDepth 2048 in
theorem rounds {a : Registers} {m : Ram} {sp src dst : BitVec 64} {key input : ByteArray}
    (call : Call a m sp src dst) (state : HmacStateAt m src key input)
    (small : input.size % 64 < 56) :
    ∃ e u, Reaches .l107a50 a m .l107f2b e u ∧
      Finalized a e m u sp dst ∧
      Compression.StateAt u (sp - 360 + 72)
        (digestState (keyPad key 0x5c ++ SHA256.hashBytes (keyPad key 0x36 ++ input))) := by
  let base := sp - 360
  let msg := keyPad key 0x36 ++ input
  let pad := keyPad key 0x5c
  have depth := call.depth
  have limit := call.limit
  have ctxAbove := call.ctxAbove
  have srcLimit := call.ctxRead.low
  have baseNat : base.toNat = sp.toNat - 360 :=
    BitVec.toNat_sub_of_le (show (360 : BitVec 64) ≤ sp from by change 360 ≤ sp.toNat; omega)
  have botNat : (sp - 704).toNat = sp.toNat - 704 :=
    BitVec.toNat_sub_of_le (show (704 : BitVec 64) ≤ sp from depth)
  have eqBot : base - 344 = sp - 704 := by dsimp only [base]; bv_omega
  have add (k : BitVec 64) (hk : k.toNat ≤ 368) :
      (base+k).toNat = base.toNat + k.toNat := by rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]
  have src64 : (src+64).toNat = src.toNat + 64 := toNat_add_ofNat src 64 (by omega)
  have remSmall : msg.size % 64 < 56 := by dsimp only [msg]; rw [ByteArray.size_append,keyPad_size]; omega
  obtain ⟨b,t,p,f,outer,count⟩ := prologue call state.outer
  have outsideSrc : Outside [scratch sp] src 168 := by
    refine ⟨by omega,fun r hr => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change sp.toNat - 704 + 704 ≤ src.toNat
    omega
  have bodyStack : Writable Extracted.programImage t (base - 344) 656 := by
    rw [eqBot]; exact (call.stack.of_frame f.writes).sub (Nat.le_refl _) (by omega)
  have loaded : ∀ x ∈ Extracted.programImage, t[x.1]? = some x.2 := by
    exact Generate.Generator.Affine.Invert.Core.stackImage call.stack (by
      change RamWriteFrame m t [⟨(sp-704).toNat,704⟩]
      rw [botNat]; exact f.writes) call.image
  have widths (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) : b[i].width = 64 := by
    rcases i with ⟨i,_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | exact congrArg Value.width f.output | exact congrArg Value.width f.input |
        exact f.widths _ (by simp)
  obtain ⟨c,v,q,qsp,qkeep,qw,qframe,qzero,inner⟩ := padding false (sp := base) (src := src+64)
    f.rsp f.df widths (show b[15].get 64 + 64 = src+64 by rw [f.input]; rfl)
    (by omega) (by omega) ((call.ctxRead.of_frame f.writes).sub (by omega) (by omega))
    (by change base.toNat + 312 ≤ (src+64).toNat; omega) bodyStack loaded
    (innerBuffered (hmacAfter f.writes outsideSrc state)) remSmall
  have padOutside (k : BitVec 64) (hn : 272 ≤ k.toNat ∧ k.toNat ≤ 304) :
      Outside [paddingRegion base,⟨(base+271).toNat,1⟩] (base+k) (312-k.toNat) := by
    have left := add k (by omega)
    have used := add 271 (by decide)
    simp only [BitVec.reduceToNat] at used
    refine ⟨by omega,fun r hr => Or.inr ?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> dsimp [paddingRegion] <;> omega
  have preservedHash := stateAfter qframe (show Outside _ (base+272) 32 from by
    have h : Outside _ (base+272) 40 := padOutside 272 (by decide)
    exact ⟨by have := h.1; omega,fun r hr => by rcases h.2 r hr with _|_ <;> omega⟩) outer
  have stackV := bodyStack.of_frame qframe
  obtain ⟨d,w,r,rsp,rkeep,rwidth,rframe,outerState⟩ := outerBuffer (pad := pad) qsp
    (stackV.sub (by rw [eqBot,botNat]; omega) (by rw [eqBot,botNat]; omega))
    (keyPad_size _ _) remSmall inner preservedHash (qzero rfl)
    ((qframe.memLoad_eq (padOutside 304 (by decide))).trans count)
  have stackW := stackV.of_frame rframe
  let bodyRegions : List MemoryRegion := [⟨(base-344).toNat,656⟩]
  have withinPad : RegionsWithin [paddingRegion base,⟨(base+271).toNat,1⟩] bodyRegions := by
    intro rr hr
    have hu := add 271 (by decide)
    simp only [BitVec.reduceToNat] at hu
    refine ⟨_,List.mem_singleton_self _,?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> dsimp only [paddingRegion] <;> rw [eqBot,botNat] <;> omega
  have withinOuter : RegionsWithin [⟨(base+176).toNat,96⟩] bodyRegions := by
    intro rr hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_singleton_self _,?_⟩
    change (base-344).toNat ≤ (base+176).toNat ∧ (base+176).toNat + 96 ≤ (base-344).toNat + 656
    rw [eqBot,botNat,add 176 (by decide)]; simp only [BitVec.reduceToNat]; omega
  have bodyWrites := ((RamWriteFrame.refl t bodyRegions).trans qframe withinPad).trans rframe withinOuter
  have wk (i : Fin Reg.count) (hi : i.val ∈ savedRegs) : d[i] = b[i] := by
    apply (rkeep i ?_).trans (qkeep i hi)
    simp only [savedRegs,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    rcases hi with h|h|h|h|h <;> simp [h]
  have outerWidths (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) : d[i].width = 64 := by
    rcases i with ⟨i,_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | exact rwidth | exact congrArg Value.width ((wk 3 (by decide)).trans f.output) |
        exact (congrArg Value.width (rkeep _ (by simp))).trans (qw _ (by simp))
  have digestSize : (SHA256.hashBytes msg).size = 32 := Vector.size_toArray _
  have outerSmall : (pad ++ SHA256.hashBytes msg).size % 64 < 56 := by
    rw [ByteArray.size_append,keyPad_size,digestSize]; decide
  have src208 := add 208 (by decide)
  simp only [BitVec.reduceToNat] at src208
  obtain ⟨e,u,s,esp,ekeep,ew,eframe,_,result⟩ := padding true (sp := base) (src := base+208)
    rsp ((wk 22 (by decide)).trans f.df) outerWidths rfl (by omega) (by omega)
    (stackW.readable.sub (by rw [eqBot,botNat]; omega) (by rw [eqBot,botNat]; omega))
    (by change base.toNat + 208 ≤ (base+208).toNat; omega) stackW
    (Generate.Generator.Affine.Invert.Core.stackImage bodyStack bodyWrites loaded) outerState outerSmall
  have body := bodyWrites.trans eframe withinPad
  have total := f.writes.trans body (by
    intro rr hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_singleton_self _,?_⟩
    change sp.toNat - 704 ≤ (base-344).toNat ∧ (base-344).toNat + 656 ≤ sp.toNat-704+704
    rw [eqBot,botNat]; omega)
  have preserved (i : Fin Reg.count) (h : i.val ∈ savedRegs) := (ekeep i h).trans (wk i h)
  refine ⟨e,u,p.trans (q.trans (r.trans s)),⟨esp,(preserved 3 (by decide)).trans f.output,
    fun i hi => (preserved i (List.mem_cons_of_mem _ hi)).trans (f.kept i hi),total,?_⟩,result⟩
  intro i
  apply Eq.trans (body.memLoad_eq ?_) (f.slots i)
  let k := (#v[48,8,40,32,24,16] : Vector (BitVec 64) 6)[i]
  have hk : k.toNat ≤ 48 := savedOffsetBound i
  have pos : (sp-k).toNat = sp.toNat-k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  change Outside bodyRegions (sp-k) 8
  refine ⟨by omega, fun rr hr => Or.inr ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  change (base-344).toNat+656 ≤ (sp-k).toNat
  rw [eqBot,botNat]; omega

end K256.Proofs.Signing.UpdateV.Finalize
