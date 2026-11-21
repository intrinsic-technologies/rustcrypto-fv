import ChaCha20Poly1305.Proofs.Decrypt.WrapAuth
import ChaCha20Poly1305.Proofs.Decrypt.WrapEnd

namespace ChaCha20Poly1305.Proofs.Decrypt.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash Detached
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 800000
set_option maxRecDepth 8000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] Packet.good Packet.src Packet.dst Packet.x memLoad memStore

structure Supplied (root : Activation) (p : Packet) (total la : BitVec 64) (a : lifted.Location) : Prop where
  label : a.label=.l10158b
  frame : RamWriteFrame root.original a.store (root.region :: commonFoot p total)
  abi : Atom.All fnCode a.arguments a.store (savedABI root)
  live : Atom.All fnCode a.arguments a.store (Detached.live (wframe root p total))
  input : Atom.All fnCode a.arguments a.store (oldData p la (wframe root p total))
  len : total.toNat=p.n.toNat+16
  small : total.toNat<2^32
  heap : p.buf.toNat+total.toNat≤root.rsp.toNat-1008 ∨ root.rsp.toNat+8≤p.buf.toNat
  ro : p.buf.toNat+total.toNat≤0x2013a8 ∨ 0x2013e8≤p.buf.toNat
  vec0 : memLoad a.store ((wframe root p total).rsp+8) 64=total
  vec1 : memLoad a.store ((wframe root p total).rsp+16) 64=p.buf
  output : p.good=true → ∃ cap, Delivery (wframe root p total).rsp root.r9 p.buf p.n cap a.store

theorem suffix (root : Activation) (p : Packet) (total la : BitVec 64) (a : lifted.Location)
    (g : Supplied root p total la a) : Runs a (Completed p root total) := by
  let f := wframe root p total
  have regs := g.abi
  unpack_atoms regs []
  have floor : root.low.toNat+1008≤root.rsp.toNat := by assumption
  have stk : Writable fnCode a.store (root.rsp-1008) 1008 := by assumption
  have low := stk.readable.low
  have sp : f.rsp=root.rsp-136 := rfl
  have sfloor : 872≤f.rsp.toNat := by rw [sp]; bv_omega
  have align : f.rsp.toNat%16=0 := by rw [sp]; bv_omega
  have area : Writable fnCode a.store (f.rsp-872) 960 := stk.sub (by rw [sp]; bv_omega) (by rw [sp]; bv_omega)
  have size := g.len
  have n : f.r14-16=p.n := by change total-16=p.n; bv_omega
  apply openTag p f la a g.input g.live area sfloor align (show 16≤total.toNat by omega) n rfl g.label g.vec0 g.vec1 _
  intro b q
  have old := g.input
  unpack_atoms old []
  have ph : RegionsWithin (phaseWrites f.rsp p.buf p.n.toNat) (tailFoot p root total) := by
    cases hg : p.good <;> simp [RegionsWithin,phaseWrites,tailFoot,hg,sp] <;> bv_omega
  have dst (hg : p.good=true) (pos : 0<p.n.toNat) :
      root.r9.toNat+p.n.toNat≤root.rsp.toNat-1008 ∨ root.rsp.toNat+8≤root.r9.toNat := by
    obtain ⟨_,d⟩ := g.output hg
    have h := d.stack pos
    change _≤(root.rsp-136).toNat-872 ∨ (root.rsp-136).toNat+144≤_ at h
    bv_omega
  have dlow (hg : p.good=true) (pos : 0<p.n.toNat) : root.r9.toNat+p.n.toNat≤2^32 := by
    obtain ⟨_,d⟩ := g.output hg
    exact (d.write pos).readable.low
  cases hg : p.good
  · have bs : Atom.All fnCode b.arguments b.store (basic f) := by
      have h := q.regs; unpack_atoms h [f]; join_atoms [f] <;> assumption
    apply leave p root total a.store b g.frame (widen q.frame ph) g.abi floor g.heap dst
      (by simpa [nextWrapper,hg] using q.label) bs (fun h => False.elim (Bool.noConfusion (hg.symm.trans h))) dlow
  · obtain ⟨cap,d⟩ := g.output hg
    have s := d.slot
    have outside : Outside (phaseWrites f.rsp p.buf p.n.toNat) (f.rsp+168) 8 := by
      change _≤f.rsp.toNat+168 ∨ f.rsp.toNat+176≤_ at s
      simp [Outside,phaseWrites]; rw [sp] at *; bv_omega
    have dg := d.after q.frame (q.frame.memLoad_eq outside)
    have got : memLoad b.store 0x2013a8 64=0x102dc0 := by
      apply (q.frame.memLoad_eq _).trans (show memLoad a.store 0x2013a8 64=0x102dc0 by assumption)
      have ro := (show f.rsp.toNat+88≤0x2013a8 ∨ 0x2013e8+872≤f.rsp.toNat by assumption)
      have hr := g.ro
      simp [Outside,phaseWrites]
      bv_omega
    have code : f.rsp.toNat+88≤0x1001f0 ∨ 0x102e00+872≤f.rsp.toNat := by assumption
    have gs : f.rsp.toNat+88≤0x2013a8 ∨ 0x2013e8+872≤f.rsp.toNat := by assumption
    have sep : p.buf.toNat+p.n.toNat≤f.rsp.toNat-872 ∨ f.rsp.toNat+88≤p.buf.toNat := by
      have h := g.heap; rw [sp]; bv_omega
    let e := afterD f p.n
    have rd : Readable b.store p.buf p.n.toNat := (show Writable fnCode a.store p.buf p.n.toNat by assumption).readable.of_frame q.frame
    apply deliver e total cap b p.dst (by change p.n.toNat≤total.toNat; omega) g.small sfloor align (area.of_frame q.frame)
      code rd sep ((show Readable a.store 0x2013a8 8 by assumption).of_frame q.frame) got gs dg
      q.vec0 q.vec1 q.vec2 (q.bytes hg) (by simpa [nextWrapper,hg] using q.label) q.regs _
    rintro t ⟨tl,tr,out,tf⟩
    apply leave p root total a.store t g.frame ((widen q.frame ph).trans tf ?_) g.abi floor g.heap dst
      (by simpa [hg] using tl) tr (fun _ => out) dlow
    simp [RegionsWithin,deliveryWrites,tailFoot,hg,e,afterD,f,wframe]; bv_omega

end ChaCha20Poly1305.Proofs.Decrypt.Wrapper
