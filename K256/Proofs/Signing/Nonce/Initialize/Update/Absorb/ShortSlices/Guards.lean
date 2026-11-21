import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices.Descriptor
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def copyAt (second : Bool) : Label := if second then .l1047d0 else .l104200
def resumeAt (second : Bool) : Label := if second then .l1047df else .l104211
def returnAddress (second : Bool) : BitVec 64 := if second then 0x1047df else 0x104211

theorem runCopy {fr : Activation} {input : Input} {m : Ram} {a c : Verify.Core.Registers}
    {rs : List MemoryRegion} (env : Environment fr input) (written : RamWriteFrame fr.original m rs)
    (second last : Bool)
    (called : program.runBlock (dialect Extracted.programImage) ⟨copyAt second,a,m⟩ =
      .call ⟨.l12a820,c,pushed fr second m⟩ (Verify.Core.Lincomb.callResume (resumeAt second) (returnAddress second)))
    (rsp : c[4].get 64 = sp fr - 8) (di : c[7].get 64 = destination fr second last)
    (si : c[6].get 64 = source fr last) (dx : c[2].get 64 = BitVec.ofNat 64 (length last))
    (df : c[22].get 1 = 0) (src : Readable m (source fr last) (length last)) :
    ∃ b, Verify.Core.Reaches (copyAt second) a m (resumeAt second) b (copied fr second last m) ∧
      b[4] = ⟨64, sp fr⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,9,10,11,12,13,14,15,22,39,50,51] → b[i] = c[i]) := by
  let off := (if second then 328 else 160) + 64 + used last
  have addr : destination fr second last = sp fr + BitVec.ofNat 64 off := by
    cases second <;> cases last <;> simp only [destination,context,off,used,
      Bool.false_eq_true,ite_false,ite_true,BitVec.add_assoc,BitVec.reduceAdd] <;> rfl
  have fits : off + length last ≤ 664 := by cases second <;> cases last <;> decide
  have small : (returnAddress second).toNat < 2^32 := by cases second <;> decide
  have dep := env.depth
  have lim := env.limit
  have separate : (source fr last).toNat + length last ≤ (sp fr).toNat + off ∨
      (sp fr).toNat + off + length last ≤ (source fr last).toNat := by
    dsimp only [off]
    cases second <;> cases last <;> short_address
  obtain ⟨b, run, back, kept, _⟩ := copyCall env written fits small called rsp (di.trans addr)
    si dx df src separate
  refine ⟨b, ?_, back, kept⟩
  unfold copied
  rw [addr]
  exact run

theorem guards {fr : Activation} {input : Input} {a : Verify.Core.Registers} {m : Ram}
    {state : State} (env : Environment fr input) (second last : Bool)
    (live : Live (loopAt second) fr a m state) :
    Writable Extracted.programImage m (sp fr - 8) 8 ∧
    Writable Extracted.programImage m (context fr second + 127) 1 ∧
    Readable m (sp fr + 8) 8 ∧ Readable m 0x203dd0 8 ∧ memLoad m 0x203dd0 64 = 0x12a820 ∧
    Writable Extracted.programImage (copied fr second last m) (context fr second + 127) 1 ∧
    Readable (result fr second last m) (sp fr + 8) 8 := by
  have dep := env.depth
  have lim := env.limit
  have wpush : Writable Extracted.programImage m (sp fr - 8) 8 := by
    apply stackWritable env live.writes <;> try rw [env.low]
    all_goals short_address
  have wmark : Writable Extracted.programImage m (context fr second + 127) 1 := by
    apply stackWritable env live.writes <;> try rw [env.low]
    all_goals cases second <;> short_address
  have slot : Writable Extracted.programImage m (sp fr + 8) 8 := by
    apply stackWritable env live.writes <;> try rw [env.low]
    all_goals short_address
  have tail : FrameTail fr a m := by
    cases second
    · exact live.atoms.2.2.2.2.2.2.2
    · exact live.atoms.2.2.2.2.2
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,got,target,rest⟩ := tail
  exact ⟨wpush,wmark,slot.readable,got,target,wmark.of_frame (copiedFrame env second last m),
    slot.readable.of_frame (resultFrame env second last m)⟩

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices
