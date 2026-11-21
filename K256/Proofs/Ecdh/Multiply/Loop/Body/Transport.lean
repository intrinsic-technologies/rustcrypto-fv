import K256.Proofs.Ecdh.Multiply.Loop.Local
import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Transport
import K256.Proofs.Ecdh.Multiply.Loop.Body.State
import K256.Proofs.Ecdh.Multiply.Loop.Memory

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

open_generator_loop Body.Transport (roundInWindow windowBounds)

syntax "peer_round_within" " using " term:max : tactic
macro_rules
  | `(tactic| peer_round_within using $e:term) => `(tactic| (
      have room := PeerCoreEntry.room $e
      have high := PeerCoreEntry.high $e
      simp (disch := decide) [RegionsWithin,windowWrites,roundWrites,doubleWrites,
        Lift.reduceAddOffset,Lift.reduceSubOffset,Lift.reduceAddNeg,Lift.reduceSubNeg,
        BitVec.reduceAdd,BitVec.reduceSub,PeerCoreEntry.stackOffset $e,PeerCoreEntry.aboveStack $e,
        BitVec.reduceToNat] <;> omega))

private theorem windowOutside {fr : Activation} {a : Registers} {d : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr a d peer) {addr : BitVec 64} {len : Nat} (bound : addr.toNat + len ≤ 2^64)
    (side : addr.toNat + len ≤ fr.rsp.toNat - 0xed8 ∨ fr.rsp.toNat - 0x30 ≤ addr.toNat) :
    Outside (windowWrites (fr.rsp - 0xcb8)) addr len := by
  refine ⟨bound,fun r hr => ?_⟩
  have base := entry.stackOffset 0xcb8 (by decide)
  change (fr.rsp - 3256).toNat = fr.rsp.toNat - 3256 at base
  have room := entry.room
  obtain ⟨lo,hi⟩ := windowBounds _ (by omega) r hr
  omega

theorem PeerWindowMemory.afterWrites {fr : Activation} {a : Registers} {d : Nat} {peer : Projective} {m n : Ram}
    (entry : PeerCoreEntry fr a d peer) (s : PeerWindowMemory fr m d peer)
    (frame : RamWriteFrame m n (windowWrites (fr.rsp - 0xcb8))) : PeerWindowMemory fr n d peer := by
  have room := entry.room
  have high := entry.high
  have base := entry.stackOffset 0xcb8 (by decide)
  change (fr.rsp - 3256).toNat = fr.rsp.toNat - 3256 at base
  apply s.of_frame frame
  · intro r hr
    obtain ⟨lo,hi⟩ := windowBounds _ (by omega) r hr
    refine ⟨fr.region,.head _,?_⟩
    simp only [Activation.region,entry.low,entry.stackOffset 3800 (by decide),BitVec.reduceToNat]
    omega
  · apply windowOutside entry <;> rw [entry.tablePtr,entry.aboveStack 4192 (by decide)] <;>
      simp only [BitVec.reduceToNat] <;> omega
  · apply windowOutside entry <;> rw [entry.tablePtr,BitVec.add_assoc,
      show (4192 : BitVec 64) + 960 = 5152 by decide,entry.aboveStack 5152 (by decide)] <;> simp only [BitVec.reduceToNat] <;> omega
  · apply windowOutside entry <;> rw [entry.digitPtr,entry.aboveStack 128 (by decide)] <;>
      simp only [BitVec.reduceToNat] <;> omega
  · apply windowOutside entry <;> rw [entry.digitPtr,BitVec.add_assoc,
      show (128 : BitVec 64) + 33 = 161 by decide,entry.aboveStack 161 (by decide)] <;> simp only [BitVec.reduceToNat] <;> omega
  · intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp (disch := decide) [Outside,windowWrites,roundWrites,Lift.reduceAddOffset,entry.stackOffset] <;> omega

theorem peerWindowAtomsAfterWrites {fr : Activation} {initial a b : Registers} {d : Nat} {peer : Projective} {m n : Ram}
    {l t : Label} (entry : PeerCoreEntry fr initial d peer)
    (sourceAt : Fn11c880.frameAt l fr = Fn11c880.frameAt .l11d7d0 fr)
    (targetAt : Fn11c880.frameAt t fr = Fn11c880.frameAt .l11d7d0 fr)
    (atoms : Atom.All Extracted.programImage a m (Fn11c880.frameAt l fr))
    (frame : RamWriteFrame m n (windowWrites (fr.rsp - 0xcb8)))
    (keep : ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i]) :
    Atom.All Extracted.programImage b n (Fn11c880.frameAt t fr) := by
  rw [sourceAt] at atoms
  rw [targetAt]
  simp only [Fn11c880.frameAt,Fn11c880.frameAtG2,Atom.All,Atom.Holds] at atoms ⊢
  obtain ⟨rsp,df,mx,ft,fc,bx,r12,r13,r14,r15,bp,retRead,ret,retLow,stack,low,align,
    gotRead1,got1,gotRead2,got2,sep,_⟩ := atoms
  have room := entry.room
  have high := entry.high
  have same (k : BitVec 64) (hk : k.toNat ≤ 48) :
      memLoad n (fr.rsp - k) 64 = memLoad m (fr.rsp - k) 64 := by
    apply frame.memLoad_eq
    apply windowOutside entry <;> rw [entry.stackOffset _ (by omega)] <;> omega
  have got (ptr : BitVec 64) (h₁ : 0x203de0 ≤ ptr.toNat) (h₂ : ptr.toNat ≤ 0x203e20) :
      memLoad n ptr 64 = memLoad m ptr 64 := by
    apply frame.memLoad_eq
    apply windowOutside entry <;> simp only [Nat.reduceDiv] <;> omega
  refine ⟨(keep 4 (by decide)).trans rsp,(keep 22 (by decide)).trans df,(keep 39 (by decide)).trans mx,
    (keep 50 (by decide)).trans ft,(keep 51 (by decide)).trans fc,(same 48 (by decide)).trans bx,
    (same 40 (by decide)).trans r12,(same 32 (by decide)).trans r13,(same 24 (by decide)).trans r14,
    (same 16 (by decide)).trans r15,(same 8 (by decide)).trans bp,retRead.of_frame frame,?_,
    retLow,stack.of_frame frame,low,align,gotRead1.of_frame frame,(got _ (by decide) (by decide)).trans got1,
    gotRead2.of_frame frame,(got _ (by decide) (by decide)).trans got2,sep,trivial⟩
  apply (frame.memLoad_eq _).trans ret
  apply windowOutside entry <;> omega

theorem PeerRoundState.afterFrame {fr : Activation} {initial a b : Registers} {d k : Nat} {peer : Projective}
    {m n : Ram} {l t : Label} (entry : PeerCoreEntry fr initial d peer) (s : PeerRoundState fr d peer k l a m)
    (frame : RamWriteFrame m n (roundWrites (fr.rsp - 0xcb8)))
    (atoms : Atom.All Extracted.programImage b n (Fn11c880.frameAt t fr))
    (widths : ParseSignature.ArgumentWidths b) (saved : SavedWidths b) : PeerRoundState fr d peer k t b n := by
  have room := entry.room
  have high := entry.high
  have mem := s.memory.afterWrites entry ((RamWriteFrame.refl _ _).trans frame (roundInWindow _))
  refine ⟨atoms,widths,saved,mem,(frame.memLoad_eq ?_).trans s.count,(frame.memLoad_eq ?_).trans s.pointer⟩
  all_goals simp (disch := decide) [Outside,roundWrites,entry.stackOffset] <;> omega

theorem PeerRoundState.afterWrites {fr : Activation} {initial a b : Registers} {d k : Nat} {peer : Projective}
    {m n : Ram} {l t : Label} (entry : PeerCoreEntry fr initial d peer) (s : PeerRoundState fr d peer k l a m)
    (sourceAt : Fn11c880.frameAt l fr = Fn11c880.frameAt .l11d7d0 fr)
    (targetAt : Fn11c880.frameAt t fr = Fn11c880.frameAt .l11d7d0 fr)
    (frame : RamWriteFrame m n (roundWrites (fr.rsp - 0xcb8)))
    (keep : ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i])
    (widths : ParseSignature.ArgumentWidths b) (saved : SavedWidths b) : PeerRoundState fr d peer k t b n :=
  s.afterFrame entry frame (peerWindowAtomsAfterWrites entry sourceAt targetAt s.atoms
    ((RamWriteFrame.refl _ _).trans frame (roundInWindow _)) keep) widths saved

end K256.Proofs.Generate.Generator.Multiply
