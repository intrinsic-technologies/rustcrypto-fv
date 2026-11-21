import K256.Proofs.Sec1.Affine.Frame

namespace K256.Proofs.Sec1.Affine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

def coordinateWrites (fr : Activation) : List MemoryRegion :=
  [⟨(fr.rsp - 136 - 8 - 1048).toNat,1048⟩, ⟨(fr.rsp - 136).toNat,89⟩]

theorem frameAfterCoordinates {code : CodeMap} {fr : Activation} {args regs : Values Value Reg.count}
    {m next : Ram} (before : Atom.All code args m (Fn121480.frameAt .l121599 fr))
    (kept : ∀ i : Fin Reg.count, i.val ∈ [3,13,22,39,50,51] → regs[i] = args[i])
    (sp : regs[4] = ⟨64,fr.rsp - 136⟩)
    (writes : RamWriteFrame m next [⟨(fr.rsp - 1192).toNat,1145⟩]) :
    Atom.All code regs next (Fn121480.frameAt .l121599 fr) := by
  simp only [Fn121480.frameAt, Fn121480.frameAtG2, Atom.All, Atom.Holds] at before ⊢
  obtain ⟨_,df,bx,r13,mx,ft,fc,sbx,s12,s14,s15,sbp,read,ret,low,win,room,align,_⟩ := before
  change fr.low.toNat + 1192 ≤ fr.rsp.toNat at room
  have addr (k : BitVec 64) (hk : k.toNat ≤ 1192) :
      (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  have base : (fr.rsp - 1192).toNat = fr.rsp.toNat - 1192 := addr 1192 (by decide)
  have same (off : BitVec 64) (h : off.toNat ≤ 40) :
      memLoad next (fr.rsp - off) 64 = memLoad m (fr.rsp - off) 64 := by
    apply writes.memLoad_eq
    have bound := read.low
    have a := addr off (by omega)
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    change (fr.rsp - 1192).toNat + 1145 ≤ (fr.rsp - off).toNat
    omega
  have top := same 0 (by decide)
  rw [show fr.rsp - (0 : BitVec 64) = fr.rsp by bv_omega] at top
  exact ⟨sp,(kept 22 (by decide)).trans df,(kept 3 (by decide)).trans bx,
    (kept 13 (by decide)).trans r13,(kept 39 (by decide)).trans mx,
    (kept 50 (by decide)).trans ft,(kept 51 (by decide)).trans fc,
    (same 40 (by decide)).trans sbx,(same 32 (by decide)).trans s12,
    (same 24 (by decide)).trans s14,(same 16 (by decide)).trans s15,(same 8 (by decide)).trans sbp,
    read.of_frame writes,top.trans ret,low,win.of_frame writes,room,align,trivial⟩

theorem coordinateFrames {fr : Activation} {m entered after : Ram}
    (room : 1192 ≤ fr.rsp.toNat)
    (push : RamWriteFrame m entered [⟨(fr.rsp - 136 - 9).toNat,9⟩])
    (writes : RamWriteFrame entered after (coordinateWrites fr)) :
    RamWriteFrame m after [⟨(fr.rsp - 1192).toNat,1145⟩] := by
  have addr (k : BitVec 64) (hk : k.toNat ≤ 1192) :
      (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  have bot : (fr.rsp - 1192).toNat = fr.rsp.toNat - 1192 := addr 1192 (by decide)
  have top : (fr.rsp - 136).toNat = fr.rsp.toNat - 136 := addr 136 (by decide)
  have pushAddr : (fr.rsp - 136 - 9).toNat = fr.rsp.toNat - 145 := by
    rw [show fr.rsp - 136 - 9 = fr.rsp - 145 by bv_omega]; exact addr 145 (by decide)
  have childAddr : fr.rsp - 136 - 8 - 1048 = fr.rsp - 1192 := by bv_omega
  let region : MemoryRegion := ⟨(fr.rsp-1192).toNat,1145⟩
  have pushed := (RamWriteFrame.refl m [region]).trans push (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨region,List.mem_singleton_self _,by dsimp only [region]; omega,by dsimp only [region]; omega⟩)
  apply pushed.trans writes
  intro r hr
  simp only [coordinateWrites,List.mem_cons,List.not_mem_nil,or_false,childAddr] at hr
  rcases hr with rfl | rfl <;>
    exact ⟨region,List.mem_singleton_self _,by dsimp only [region]; omega,by dsimp only [region]; omega⟩

theorem prefixFrame {fr : Activation} {m saved entered : Ram} (room : 145 ≤ fr.rsp.toNat)
    (push : RamWriteFrame m saved [⟨(fr.rsp - 40).toNat,40⟩])
    (dispatch : RamWriteFrame saved entered [⟨(fr.rsp - 136 - 9).toNat,9⟩]) :
    RamWriteFrame m entered [⟨(fr.rsp - 145).toNat,145⟩] := by
  have a : (fr.rsp - 40).toNat = fr.rsp.toNat - 40 := BitVec.toNat_sub_of_le (by change 40 ≤ fr.rsp.toNat; omega)
  have b : (fr.rsp - 145).toNat = fr.rsp.toNat - 145 := BitVec.toNat_sub_of_le (by change 145 ≤ fr.rsp.toNat; omega)
  have c : fr.rsp - 136 - 9 = fr.rsp - 145 := by bv_omega
  let region : MemoryRegion := ⟨(fr.rsp-145).toNat,145⟩
  have saved' := (RamWriteFrame.refl m [region]).trans push (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨region,List.mem_singleton_self _,by dsimp only [region]; omega,by dsimp only [region]; omega⟩)
  apply saved'.trans dispatch
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨region,List.mem_singleton_self _,by dsimp only [region]; rw [c]; omega,by dsimp only [region]; rw [c]; omega⟩

end K256.Proofs.Sec1.Affine
