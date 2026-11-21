import K256.Proofs.Generate.LIR.Fn10a410.Frame
import K256.Proofs.Generate.Generator.Multiply.Prepare.Frame
import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Transport
import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Additions.Call

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

def windowChild (fr : Activation) (b : Registers) (m : Ram) (tag : BitVec 64) : Activation :=
  Prepare.child fr b m tag

theorem WindowCall.entry {fr : Activation} {a b initial : Registers} {m : Ram} {d k : Nat}
    {site child resume : Label} {tag : BitVec 64}
    (entry : CoreEntry fr initial d) (s : RoundState fr d k site a m)
    (layout : Fn11c880.frameAt site fr = Fn11c880.frameAt .l11d7d0 fr)
    (c : WindowCall fr site child resume tag a b m)
    (info : FrameInfo) (empty : info.callSlots = []) (pos : 0 < info.window)
    (small : info.window ≤ 0x218) (retLow : tag.toNat < 2^32) :
    let n := memStore m (roundSp fr - 8) tag
    Atom.All Extracted.programImage b n (info.entryAtoms (windowChild fr b n tag)) := by
  intro n
  have atoms := s.atoms
  rw [layout] at atoms
  obtain ⟨_,df,mx,ft,fc,_⟩ := atoms
  apply Prepare.childEntry entry info empty ⟨pos,small⟩ c.widths c.saved c.rsp
    ((c.control 22 (by decide)).trans df) ((c.control 39 (by decide)).trans mx)
    ((c.control 50 (by decide)).trans ft) ((c.control 51 (by decide)).trans fc)
    (regions := coreWrites fr) _ (memLoad_memStore_same _ _ _ (by decide) (by decide)) retLow
  apply s.memory.frame.memStore
  refine ⟨fr.region,.head _,?_⟩
  have room := entry.room
  have high := entry.high
  simp (disch := decide) [InRegion,Activation.region,entry.low,entry.stackOffset] <;> omega

theorem WindowCall.returned {fr : Activation} {a b : Registers} {m : Ram} {site child resume : Label}
    {tag : BitVec 64} {out : Output Value Ram Reg.count} (c : WindowCall fr site child resume tag a b m)
    {d k : Nat} (s : RoundState fr d k site a m)
    (layout : Fn11c880.frameAt site fr = Fn11c880.frameAt .l11d7d0 fr)
    (exec : program.Exec (dialect Extracted.programImage)
      ⟨⟨child,b,memStore m (roundSp fr - 8) tag⟩, []⟩ out) (ret : out.tag = some ⟨64,tag⟩)
    (done_ : Atom.All Extracted.programImage out.values out.store
      (Fn10a410.doneAt (windowChild fr b (memStore m (roundSp fr - 8) tag) tag))) :
    Reaches site a m resume out.values out.store ∧ SavedWidths out.values ∧
    out.values[4] = ⟨64,roundSp fr⟩ ∧
    (∀ j : Fin Reg.count, j.val ∈ [22,39,50,51] → out.values[j] = a[j]) ∧
    ∀ j : Fin Reg.count, j.val ∈ Activation.calleeSavedNumbers → out.values[j] = b[j] := by
  have atoms := s.atoms
  rw [layout] at atoms
  obtain ⟨_,df,mx,ft,fc,_⟩ := atoms
  obtain ⟨sp,preserved⟩ := Sample.sampleChildReturn (base := Prepare.childBase fr b)
    (a := b) (tag := tag) (m := memStore m (roundSp fr - 8) tag) (out := out) done_
  have same (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) :
      out.values[i] = b[i] := by
    have width := c.saved i hi
    have eqv (v : Value) (w : v.width = 64) : Value.mk 64 (v.get 64) = v := by
      cases v with
      | mk width bits => cases w; rfl
    obtain ⟨i,h⟩ := i
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact (preserved _ (by simp [Sample.nonzeroPreserved])).trans (eqv _ width)
  refine ⟨Sample.reachesAfterSampleCall c.step exec ret [],?_,?_,?_,same⟩
  · intro i h
    rw [same i h]
    exact c.saved i h
  · change out.values[4] = ⟨64,roundSp fr - 8 + 8⟩ at sp
    simpa only [BitVec.sub_add_cancel] using sp
  · rintro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    · exact (preserved 22 (by decide)).trans df.symm
    · exact (preserved 39 (by decide)).trans mx.symm
    · exact (preserved 50 (by decide)).trans ft.symm
    · exact (preserved 51 (by decide)).trans fc.symm

end K256.Proofs.Generate.Generator.Multiply
