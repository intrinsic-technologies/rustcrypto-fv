import ChaCha20Poly1305.Proofs.Decrypt.Absorb
import ChaCha20Poly1305.Proofs.Decrypt.InitCall

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305

def zone (sp : BitVec 64) : List MemoryRegion := [⟨sp.toNat-96,488⟩]
def work (sp : BitVec 64) : List MemoryRegion :=
  [⟨sp.toNat-96,96⟩,⟨sp.toNat+32,56⟩,⟨sp.toNat+160,16⟩,⟨sp.toNat+372,20⟩]
def saved (sp : BitVec 64) : List MemoryRegion := [⟨sp.toNat+8,16⟩,⟨sp.toNat+192,16⟩]

theorem PadScope.move {fr fr' src n m m' rs} (g : PadScope fr src n m) (f : RamWriteFrame m m' rs)
    (incl : RegionsWithin rs (zone fr.rsp)) (sp : fr'.rsp=fr.rsp) (ctx : fr'.rdi=fr.rdi) :
    PadScope fr' src n m' := by
  have z := widen f incl
  have lo := g.floor
  have gt := g.got
  refine ⟨⟨sp ▸ g.below.of_frame f,ctx ▸ g.ctx.of_frame f,g.buf.of_frame f,sp ▸ g.floor,
      sp ▸ g.align,sp ▸ g.stackCode,ctx ▸ g.ctxCode,by rw [sp,ctx]; exact g.stackCtx,
      sp ▸ g.stackBuf,ctx ▸ g.ctxBuf⟩,sp ▸ g.area.of_frame f,by rw [ctx,sp]; exact g.ctxAt,
      sp ▸ g.apart,sp ▸ g.code,sp ▸ g.got,g.copyRead.of_frame f,(z.memLoad_eq ?_).trans g.copyAddr,
      g.fillRead.of_frame f,(z.memLoad_eq ?_).trans g.fillAddr⟩
  all_goals simp [zone,Outside]; all_goals omega

theorem savedZone {sp : BitVec 64} (lo : 96≤sp.toNat) : RegionsWithin (saved sp) (zone sp) := by
  simp [RegionsWithin,saved,zone]; omega
theorem workZone {sp : BitVec 64} (lo : 96≤sp.toNat) : RegionsWithin (work sp) (zone sp) := by
  simp [RegionsWithin,work,zone]; omega
theorem padWork {fr src n m} (g : PadScope fr src n m) : RegionsWithin (padRegions fr) (work fr.rsp) := by
  have lo := g.area.readable.low
  simp [RegionsWithin,padRegions,regions,work,g.ctxAt]; bv_omega

theorem padKeepR {fr src n m m' r rs rs'} (g : PadScope fr src n m) (f : RamWriteFrame m m' (work fr.rsp))
    (hr : Atom.All fnCode rs m (rData fr.rdi r)) : Atom.All fnCode rs' m' (rData fr.rdi r) := by
  have lo := g.area.readable.low
  have sp := g.floor
  apply ChaChaRound.keepFrame _ f hr
  intro t ht
  simp only [rData,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl
  all_goals simp [ChaChaRound.pass,Outside,work,g.ctxAt] <;> bv_omega

theorem endShape (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) (tag : BitVec 64) :
    let e := endFr ct fr src s tag
    e.rsp=fr.rsp ∧ e.rdi=fr.rdi ∧ e.r15=fr.r15 ∧ e.mxcsr=fr.mxcsr ∧ e.ftw=fr.ftw ∧ e.fcw=fr.fcw := by
  cases ct <;> by_cases h : s.size%16=0 <;> simp [endFr,h,testFr,afterBlocks,lastFr,moved,afterFill,baseFr]

end ChaCha20Poly1305.Proofs.Decrypt.Hash
