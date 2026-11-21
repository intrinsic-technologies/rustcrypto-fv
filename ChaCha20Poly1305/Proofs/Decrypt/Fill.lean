import ChaCha20Poly1305.Proofs.Decrypt.ActiveFrames
import ChaCha20Poly1305.Proofs.Decrypt.Copy
import ChaCha20Poly1305.Proofs.Decrypt.FillFacts
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn102d70.Frame

namespace ChaCha20Poly1305.Proofs.Decrypt.Fill

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted
open ChaCha20Poly1305.Proofs.Decrypt.Copy (ptr ptr_ptr region headCount quadCount tailCount counts)

@[refine_layout] def core : LayoutCore Copy.program Empty.semantics lifted Unit where
  start := fun _ => .l102d70
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms := fun _ _ fr _ =>
    [.writable fr.rdi fr.rdx.toNat, .fact (fr.rsi = 0),
     .fact (fr.rdi.toNat + fr.rdx.toNat ≤ 0x102d70 ∨ 0x102db5 ≤ fr.rdi.toNat),
     .fact (fr.rdi.toNat + fr.rdx.toNat ≤ fr.rsp.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat)]
  Result := Unit
  output := fun _ => ⟨#v[], none, ()⟩
  done := fun _ fr _ => [.gpr 0 fr.rdi, .mem fr.rdi (8*fr.rdx.toNat) 0]
  footprint := fun _ fr => [⟨fr.rdi.toNat, fr.rdx.toNat⟩]

set_option maxRecDepth 12000
set_option maxHeartbeats 400000
set_option pp.maxSteps 400

theorem segments {fr : Activation} {m : Ram}
    (inp : Writable fnCode m fr.rdi fr.rdx.toNat)
    (hc : fr.rdi.toNat + fr.rdx.toNat ≤ 0x102d70 ∨ 0x102db5 ≤ fr.rdi.toNat)
    (hs : fr.rdi.toNat + fr.rdx.toNat ≤ fr.rsp.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (sr : Readable m fr.rsp 8) (hr : memLoad m fr.rsp 64 = fr.ret) :
    let d := fr.rdi
    let n := fr.rdx
    let h := headCount d n
    let q := quadCount d n
    let t := tailCount d n
    let m1 := memFill m d (0#8) h.toNat
    let m2 := memFill m1 (ptr d h.toNat) (0#64) q.toNat
    let td := ptr (ptr d h.toNat) (8*q.toNat)
    let m3 := memFill m2 td (0#8) t.toNat
    RepStosOk fnCode m 0 d h 1 0x102da4 2 ∧
    RepStosOk fnCode m1 0 (ptr d h.toNat) q 8 0x102da9 3 ∧
    RepStosOk fnCode m2 0 td t 1 0x102daf 2 ∧
    RamWriteFrame m m3 [region d n.toNat] ∧ memLoad m3 d (8*n.toNat) = 0 ∧
    LoadOk m3 fr.rsp 8 ∧ memLoad m3 fr.rsp 64 = fr.ret := by
  dsimp only
  generalize hd : fr.rdi = d at *
  generalize hn : fr.rdx = n at *
  have tot := counts d n
  generalize hh : headCount d n = h at *
  generalize hq : quadCount d n = q at *
  generalize ht : tailCount d n = t at *
  have a := start m d n.toNat
  have ptr_zero (x : BitVec 64) : ptr x 0 = x := by unfold ptr; bv_omega
  have g1 := guard inp a (count := h) (size := 1) (by omega) (p := 0x102da4) (k := 2) (by decide)
    (by change _ ≤ 0x102da4 ∨ 0x102da4 + 2 ≤ _; omega)
  have p1 := advance inp a 8 h.toNat (by omega)
  simp only [Nat.zero_add, ptr_zero, Nat.mul_div_cancel_left _ (by decide : 0 < 8)] at g1 p1
  have g2 := guard inp p1 (count := q) (size := 8) (by omega) (p := 0x102da9) (k := 3) (by decide)
    (by change _ ≤ 0x102da9 ∨ 0x102da9 + 3 ≤ _; omega)
  have p2 := advance inp p1 64 q.toNat (by omega)
  rw [show 64 * q.toNat / 8 = 8*q.toNat by omega] at p2
  have g3 := guard inp p2 (count := t) (size := 1) (by omega) (p := 0x102daf) (k := 2) (by decide)
    (by change _ ≤ 0x102daf ∨ 0x102daf + 2 ≤ _; omega)
  have p3 := advance inp p2 8 t.toNat (by omega)
  rw [show 8*t.toNat/8 = t.toNat by omega, tot] at p3
  simp only [ptr_ptr]
  have rr := sr.of_frame p3.frame
  refine ⟨g1,g2,g3,p3.frame,memLoad_eq_of_memByte (by omega) ?_,⟨rr.low,rr.present⟩,
    (p3.frame.memLoad_eq ?_).trans hr⟩
  · intro i hi
    rw [show storedByte (0 : BitVec (8*n.toNat)) i = 0 by
      change UInt8.ofNat (0 >>> (8*i)) = 0; simp]
    exact p3.zero i (by omega)
  · refine ⟨by have := sr.low; omega, ?_⟩
    simpa only [List.mem_singleton, forall_eq, region] using hs.symm

theorem blocks :
    ∀ l, (Layout.withFrame Fn102d70.active Fn102d70.doneAt core).BlockSimulation fnCode l := by
  intro l
  cases l
  x86_refine [Copy.program]
  all_goals
    obtain ⟨g1,g2,g3,frame,zero,read,ret⟩ := segments (fr := fr) (m := mem)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    have hz : fr.rsi = 0 := by assumption
    try simp only [hz, cmpSpec_CF, decide_eq_true_eq, ← setWidth_sub _ _ (show 32 ≤ 64 by decide)]
  · exact ret
  · exact zero
  · apply hframe.trans frame
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨_, .tail _ (.head _), Nat.le_refl _, Nat.le_refl _⟩
  · exact Or.inr g1
  · exact Or.inr g2
  · exact Or.inr g3
  · exact read
  · exact (congrArg BitVec.toNat ret) ▸ (show fr.ret.toNat < 2^32 by assumption)

end ChaCha20Poly1305.Proofs.Decrypt.Fill
