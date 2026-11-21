import K256.Proofs.Generate.Generator.Multiply.Prepare.State
import K256.Proofs.Generate.LIR.Fn105f30.Frame
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Resume.Frame

namespace K256.Proofs.Generate.Generator.Multiply.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

theorem Locals.of_frame {fr : Activation} {m n : Ram} {xs : List (BitVec 64 × BitVec 64)}
    {writes : List MemoryRegion} (locals : Locals fr m xs) (frame : RamWriteFrame m n writes)
    (apart : ∀ kv ∈ xs, Outside writes (sp fr + kv.1) 8) : Locals fr n xs :=
  fun kv h => (frame.memLoad_eq (apart kv h)).trans (locals kv h)

theorem frameAtoms {fr : Activation} {l l' : Label} {a b : Registers} {m n : Ram}
    {writes : List MemoryRegion}
    (old : Atom.All Extracted.programImage a m (Fn11c880.frameAt l fr))
    (source : Fn11c880.frameAt l fr = Fn11c880.frameAt .l11c9e7 fr)
    (target : Fn11c880.frameAt l' fr = Fn11c880.frameAt .l11c9e7 fr)
    (frame : RamWriteFrame m n writes)
    (saved : Outside writes (fr.rsp - 48) 56)
    (room : 48 ≤ fr.rsp.toNat)
    (image : ∀ v ∈ Extracted.programImage, n[v.1]? = some v.2)
    (keep : ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i]) :
    Atom.All Extracted.programImage b n (Fn11c880.frameAt l' fr) := by
  rw [source] at old
  rw [target]
  obtain ⟨rsp,df,mx,ft,fc,bx,r12,r13,r14,r15,bp,rd,ret,small,win,low,align,_,_,_,_,apart,_⟩ := old
  have off {k : Nat} (hk : k ≤ 48) : (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have kv : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by change (BitVec.ofNat 64 k).toNat ≤ fr.rsp.toNat; rw [kv]; omega),kv]
  have start : (fr.rsp - 48).toNat = fr.rsp.toNat - 48 := off (k := 48) (by decide)
  have same (k : Nat) (hk : k ≤ 48) :
      memLoad n (fr.rsp - BitVec.ofNat 64 k) 64 = memLoad m (fr.rsp - BitVec.ofNat 64 k) 64 := by
    apply frame.memLoad_eq
    apply Affine.outside_subregion saved
    · rw [off hk, start]; omega
    · rw [off hk, start]; change _ + 8 ≤ _; omega
  have last := same 0 (by decide)
  rw [show fr.rsp - BitVec.ofNat 64 0 = fr.rsp from BitVec.sub_zero _] at last
  have sectionMem : rodataSection ∈ Extracted.programSections := by simp [rodataSection, Extracted.programSections]
  have got := Fn105f30.callSlots_loaded sectionMem image
  obtain ⟨rd₁, val₁⟩ := got (0x203de0,0x129770) (by decide)
  obtain ⟨rd₂, val₂⟩ := got (0x203e20,0x100a20) (by decide)
  exact ⟨(keep 4 (by decide)).trans rsp, (keep 22 (by decide)).trans df,
    (keep 39 (by decide)).trans mx, (keep 50 (by decide)).trans ft, (keep 51 (by decide)).trans fc,
    (same 48 (by decide)).trans bx, (same 40 (by decide)).trans r12, (same 32 (by decide)).trans r13,
    (same 24 (by decide)).trans r14, (same 16 (by decide)).trans r15, (same 8 (by decide)).trans bp,
    Readable.of_frame rd frame, last.trans ret, small, Writable.of_frame win frame, low, align,
    rd₁, val₁, rd₂, val₂, apart, trivial⟩


def childBase (fr : Activation) (a : Registers) : Activation :=
  { fr with
    rsp := sp fr - 8
    rbx := a[3].get 64
    rbp := a[5].get 64
    r12 := a[12].get 64
    r13 := a[13].get 64
    r14 := a[14].get 64
    r15 := a[15].get 64 }

abbrev child (fr : Activation) (a : Registers) (m : Ram) (ret : BitVec 64) :=
  Sample.compareChild (childBase fr a) a m ret

theorem childEntry {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat}
    (entry : CoreEntry fr initial d) (info : FrameInfo) (empty : info.callSlots = [])
    (depth : 0 < info.window ∧ info.window ≤ 536)
    (args : ParseSignature.ArgumentWidths a) (saved : SavedWidths a)
    (rsp : a[4] = ⟨64,sp fr - 8⟩) (df : a[22] = ⟨1,0⟩)
    (mx : a[39] = ⟨32,fr.mxcsr⟩) (ft : a[50] = ⟨16,fr.ftw⟩) (fc : a[51] = ⟨16,fr.fcw⟩)
    {regions : List MemoryRegion} (written : RamWriteFrame fr.original m regions)
    {ret : BitVec 64} (tag : memLoad m (sp fr - 8) 64 = ret) (small : ret.toNat < 2^32) :
    Atom.All Extracted.programImage a m (info.entryAtoms (child fr a m ret)) := by
  have old := entry.atoms
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,win,_,align,_⟩ := old
  change Writable Extracted.programImage fr.original (fr.rsp - 3800) 3800 at win
  change fr.rsp.toNat % 16 = 8 at align
  have depthBound := entry.room
  change 3800 ≤ fr.rsp.toNat at depthBound
  have start : (fr.rsp - 3800).toNat = fr.rsp.toNat - 3800 :=
    BitVec.toNat_sub_of_le (by exact depthBound)
  have top : (sp fr - 8).toNat = fr.rsp.toNat - 3264 := by
    rw [show sp fr - 8 = fr.rsp - 3264 by unfold sp; bv_omega]
    exact BitVec.toNat_sub_of_le (by change 3264 ≤ fr.rsp.toNat; omega)
  have w := win.of_frame written
  have size : (BitVec.ofNat 64 info.window).toNat = info.window :=
    Nat.mod_eq_of_lt (by omega)
  have bot : (sp fr - 8 - BitVec.ofNat 64 info.window).toNat = fr.rsp.toNat - 3264 - info.window := by
    rw [BitVec.toNat_sub_of_le (by change (BitVec.ofNat 64 info.window).toNat ≤ _; rw [size, top]; omega),top,size]
  refine Sample.sampleChildEntry (base := childBase fr a) info empty depth.1 rsp ?keep args ?read tag small ?write ?room ?align
  case keep =>
    have gp (v : Value) (h : v.width = 64) : v = ⟨64,v.get 64⟩ := by
      cases v with
      | mk width bits => cases h; rfl
    intro ⟨i, hi⟩ hm
    simp only [Sample.nonzeroPreserved, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact df
      | exact mx
      | exact ft
      | exact fc
      | exact gp _ (saved 3 (by decide))
      | exact gp _ (saved 5 (by decide))
      | exact gp _ (saved 12 (by decide))
      | exact gp _ (saved 13 (by decide))
      | exact gp _ (saved 14 (by decide))
      | exact gp _ (saved 15 (by decide))
  case read =>
    exact w.readable.sub (by change (fr.rsp - 3800).toNat ≤ (sp fr - 8).toNat; omega)
      (by change (sp fr - 8).toNat + 8 ≤ (fr.rsp - 3800).toNat + 3800; omega)
  case write =>
    exact w.sub (by change (fr.rsp - 3800).toNat ≤ (sp fr - 8 - _).toNat; omega)
      (by change (sp fr - 8 - _).toNat + info.window ≤ (fr.rsp - 3800).toNat + 3800; omega)
  case room =>
    change fr.low.toNat + info.window ≤ (sp fr - 8).toNat
    rw [entry.low, start, top]
    omega
  case align =>
    change (sp fr - 8).toNat % 16 = 8
    omega

end K256.Proofs.Generate.Generator.Multiply.Prepare
