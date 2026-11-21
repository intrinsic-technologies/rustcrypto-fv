import ChaCha20Poly1305.Proofs.Decrypt.ActiveFrames
import ChaCha20Poly1305.Proofs.Decrypt.CopyFacts
import ChaCha20Poly1305.Proofs.Decrypt.Empty
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Functions
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn102dc0.Frame

namespace ChaCha20Poly1305.Proofs.Decrypt.Copy

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted

def program : Program (fun _ => _root_.Empty) Unit (fun _ => 0) 0 :=
  ⟨fun _ => .terminate (.ret #v[])⟩

@[refine_layout] def core : LayoutCore program Empty.semantics lifted Unit where
  start := fun _ => .l102dc0
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms := fun _ _ fr _ =>
    [.readable fr.rsi fr.rdx.toNat, .writable fr.rdi fr.rdx.toNat,
     .fact (fr.rsi.toNat + fr.rdx.toNat ≤ fr.rdi.toNat ∨
       fr.rdi.toNat + fr.rdx.toNat ≤ fr.rsi.toNat),
     .fact (fr.rdi.toNat + fr.rdx.toNat ≤ 0x102dc0 ∨ 0x102def ≤ fr.rdi.toNat),
     .fact (fr.rdi.toNat + fr.rdx.toNat ≤ fr.rsp.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat),
     .mem fr.rsi (8*fr.rdx.toNat) (memLoad fr.original fr.rsi (8*fr.rdx.toNat))]
  Result := Unit
  output := fun _ => ⟨#v[], none, ()⟩
  done := fun _ fr _ => [.gpr 0 fr.rdi, .mem fr.rdi (8*fr.rdx.toNat) (memLoad fr.original fr.rsi (8*fr.rdx.toNat))]
  footprint := fun _ fr => [⟨fr.rdi.toNat, fr.rdx.toNat⟩]

set_option maxRecDepth 10000
set_option maxHeartbeats 220000
set_option pp.maxSteps 240

def headCount (d n : BitVec 64) : BitVec 64 :=
  let a := BitVec.setWidth 64 (-BitVec.setWidth 32 d &&& 7)
  if n.toNat < a.toNat then n else a

def quadCount (d n : BitVec 64) := (n - headCount d n) >>> 3
def tailCount (d n : BitVec 64) := BitVec.setWidth 64 (BitVec.setWidth 32 (n - headCount d n) &&& 7)

theorem counts (d n : BitVec 64) :
    (headCount d n).toNat + 8*(quadCount d n).toNat + (tailCount d n).toNat = n.toNat := by
  have h : headCount d n ≤ n := by unfold headCount; dsimp only; split <;> simp_all [BitVec.le_def] <;> omega
  have he (x : Nat) : x &&& 7 = x % 8 := Nat.and_two_pow_sub_one_eq_mod x 3
  simp only [quadCount, tailCount, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_sub_of_le h, Nat.shiftRight_eq_div_pow]
  change (headCount d n).toNat + 8*((n.toNat - (headCount d n).toNat)/8) +
    (((n.toNat - (headCount d n).toNat) % 2^32 &&& 7) % 2^64) = n.toNat
  rw [he]
  change (headCount d n).toNat ≤ n.toNat at h
  omega

theorem segments {fr : Activation} {m : Ram}
    (inp : Input fnCode m fr.rsi fr.rdi fr.rdx.toNat)
    (hc : fr.rdi.toNat + fr.rdx.toNat ≤ 0x102dc0 ∨ 0x102def ≤ fr.rdi.toNat)
    (hs : fr.rdi.toNat + fr.rdx.toNat ≤ fr.rsp.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (sr : Readable m fr.rsp 8) (hr : memLoad m fr.rsp 64 = fr.ret) :
    let d := fr.rdi
    let s := fr.rsi
    let n := fr.rdx
    let h := headCount d n
    let q := quadCount d n
    let t := tailCount d n
    let m1 := memCopy m d s h.toNat
    let m2 := memCopy m1 (ptr d h.toNat) (ptr s h.toNat) (8*q.toNat)
    let td := ptr (ptr d h.toNat) (8*q.toNat)
    let ts := ptr (ptr s h.toNat) (8*q.toNat)
    let m3 := memCopy m2 td ts t.toNat
    RepMovsOk fnCode m 0 s d h 1 1060311 2 ∧
    RepMovsOk fnCode m1 0 (ptr s h.toNat) (ptr d h.toNat) q 8 1060323 3 ∧
    RepMovsOk fnCode m2 0 ts td t 1 1060332 2 ∧
    RamWriteFrame m m3 [region d n.toNat] ∧
    memLoad m3 d (8*n.toNat) = memLoad m s (8*n.toNat) ∧
    LoadOk m3 fr.rsp 8 ∧ memLoad m3 fr.rsp 64 = fr.ret := by
  dsimp only
  generalize hd : fr.rdi = d at *
  generalize hx : fr.rsi = s at *
  generalize hn : fr.rdx = n at *
  have tot := counts d n
  generalize hh : headCount d n = h at *
  generalize hq : quadCount d n = q at *
  generalize ht : tailCount d n = t at *
  have a := start m s d n.toNat
  have g1 := guard inp a (count := h) (size := 1) (by omega) (p := 1060311) (k := 2) (by decide)
    (by change _ ≤ 1060311 ∨ 1060311 + 2 ≤ _; omega)
  have p1 := advance inp a h.toNat (by omega)
  have ptr_zero (x : BitVec 64) : ptr x 0 = x := by unfold ptr; bv_omega
  simp only [Nat.zero_add, ptr_zero] at g1 p1
  have g2 := guard inp p1 (count := q) (size := 8) (by omega) (p := 1060323) (k := 3) (by decide)
    (by change _ ≤ 1060323 ∨ 1060323 + 3 ≤ _; omega)
  have p2 := advance inp p1 (8*q.toNat) (by omega)
  have g3 := guard inp p2 (count := t) (size := 1) (by omega) (p := 1060332) (k := 2) (by decide)
    (by change _ ≤ 1060332 ∨ 1060332 + 2 ≤ _; omega)
  have p3 := advance inp p2 t.toNat (by omega)
  rw [tot] at p3
  simp only [ptr_ptr]
  have rr := sr.of_frame p3.frame
  refine ⟨g1, g2, g3, p3.frame, memLoad_congr (fun k hk => p3.copied k (by omega)),
    ⟨rr.low, rr.present⟩, (p3.frame.memLoad_eq ?_).trans hr⟩
  refine ⟨by have := sr.low; omega, ?_⟩
  simpa only [List.mem_singleton, forall_eq, region] using hs.symm

theorem blocks :
    ∀ l, (Layout.withFrame Fn102dc0.active Fn102dc0.doneAt core).BlockSimulation fnCode l := by
  intro l
  cases l
  x86_refine [program]
  all_goals
    obtain ⟨g1, g2, g3, frame, bytes, read, ret⟩ := segments (fr := fr) (m := mem)
      ⟨by assumption, by assumption, by assumption⟩ (by assumption) (by assumption)
      (by assumption) (by assumption)
    try simp only [cmpSpec_CF, decide_eq_true_eq, ← setWidth_sub _ _ (show 32 ≤ 64 by decide)]
  · exact ret
  · exact bytes.trans (by assumption)
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

end ChaCha20Poly1305.Proofs.Decrypt.Copy
