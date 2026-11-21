import K256.Proofs.Sec1.SqrtLaterProducts.Early.Memory
import K256.Proofs.Sec1.SqrtChainExecution.Stages

namespace K256.Proofs.Sec1.SqrtLaterProducts.Early

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open SqrtChainExecution

abbrev StandardFrame (code : CodeMap) (fr : Activation) (args : Values Value Reg.count) (m : Ram) :=
  Atom.All code args m (LIR.Fn115950.frameAt .l116316 fr)

structure Window (code : CodeMap) (fr : Activation) (args : Values Value Reg.count) (m : Ram)
    (sp : Word) : Prop where
  rsp : args[4].get 64 = sp
  value : sp.toNat = fr.rsp.toNat - 440
  room : fr.low.toNat + 552 ≤ fr.rsp.toNat
  stackLow : fr.rsp.toNat + 8 ≤ 2^32
  writable : Writable code m (sp - 8) 440
  full : Writable code m (sp - 112) 552
  workspace : Writable code m (sp - 112) 192
  align : sp.toNat % 16 = 0

theorem window {code fr args m} (frame : StandardFrame code fr args m) :
    Window code fr args m (fr.rsp - 440) := by
  obtain ⟨hsp, _, _, _, _, _, _, _, _, _, _, _, rd, _, _, wr, room, align, _⟩ := frame
  change Readable m fr.rsp 8 at rd
  change Writable code m (fr.rsp - 552) 552 at wr
  change fr.low.toNat + 552 ≤ fr.rsp.toNat at room
  change fr.rsp.toNat % 16 = 8 at align
  change args[4] = ⟨64, fr.rsp - 440⟩ at hsp
  have sub (k : Word) (hk : k.toNat ≤ 552) :
      (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  have sb := sub 440 (by decide)
  change (fr.rsp - 440).toNat = fr.rsp.toNat - 440 at sb
  refine ⟨by rw [hsp]; rfl, sb, room, rd.low, ?_, ?_, ?_, by omega⟩
  · rw [BitVec.sub_sub, show (440 + 8 : Word) = 448 by decide]
    apply wr.sub <;> rw [sub 552 (by decide), sub 448 (by decide)] <;>
      simp only [show (552 : Word).toNat = 552 by decide, show (448 : Word).toNat = 448 by decide] <;> omega
  · rw [BitVec.sub_sub, show (440 + 112 : Word) = 552 by decide]
    exact wr
  · rw [BitVec.sub_sub, show (440 + 112 : Word) = 552 by decide]
    exact wr.sub (Nat.le_refl _) (by omega)

theorem Window.blockBounds {code fr args m sp} (w : Window code fr args m sp)
    (g : Geometry code fr) {start finish : Nat} (hs : 0x100000 ≤ start)
    (ht : finish + 8 ≤ 0x12aa00) :
    8 ≤ sp.toNat ∧ sp.toNat + 432 ≤ 2^32 ∧
    (sp.toNat + 432 ≤ start ∨ finish + 8 ≤ sp.toNat) := by
  have := w.value
  have := w.room
  have := w.stackLow
  rcases g.stackCode with h | h <;> omega

theorem standardFrameOfWrites {code fr args m} {b : Values Value Reg.count} {n : Ram}
    (frame : StandardFrame code fr args m) (rsp : b[4] = ⟨64, fr.rsp - 440⟩)
    (control : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = args[i])
    (writes : RamWriteFrame m n [scratchRegion (fr.rsp - 440)]) :
    StandardFrame code fr b n := by
  obtain ⟨_, df, mx, ftw, fcw, o, bx, r12, r13, r14, r15, bp, rd, ret, low, wr, room, al, _⟩ := frame
  change Readable m fr.rsp 8 at rd
  change Writable code m (fr.rsp - 552) 552 at wr
  change fr.low.toNat + 552 ≤ fr.rsp.toNat at room
  have bound := rd.low
  have hb : (fr.rsp - 440 - 8).toNat = fr.rsp.toNat - 448 := by
    rw [BitVec.sub_sub, show (440 + 8 : Word) = 448 by decide]
    exact BitVec.toNat_sub_of_le (by change 448 ≤ fr.rsp.toNat; omega)
  have slot (k : Word) (hk : k.toNat ≤ 56) :
      memLoad n (fr.rsp - k) 64 = memLoad m (fr.rsp - k) 64 := by
    apply writes.memLoad_eq
    have hs := BitVec.toNat_sub_of_le (x := fr.rsp) (y := k) (by rw [BitVec.le_def]; omega)
    refine ⟨by rw [hs]; change fr.rsp.toNat - k.toNat + 8 ≤ _; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    change (fr.rsp - 440 - 8).toNat + 392 ≤ (fr.rsp - k).toNat
    rw [hb, hs]
    omega
  have hret : memLoad n fr.rsp 64 = memLoad m fr.rsp 64 := by
    simpa only [show fr.rsp - (0 : Word) = fr.rsp by bv_omega] using slot 0 (by decide)
  exact ⟨rsp, (control 22 (by decide)).trans df, (control 39 (by decide)).trans mx,
    (control 50 (by decide)).trans ftw, (control 51 (by decide)).trans fcw,
    (slot 56 (by decide)).trans o, (slot 48 (by decide)).trans bx, (slot 40 (by decide)).trans r12,
    (slot 32 (by decide)).trans r13, (slot 24 (by decide)).trans r14, (slot 16 (by decide)).trans r15,
    (slot 8 (by decide)).trans bp, rd.of_frame writes, hret.trans ret, low, wr.of_frame writes,
    room, al, trivial⟩

theorem Window.regionBounds {code fr args m sp} (w : Window code fr args m sp) :
    fr.low.toNat ≤ (scratchRegion sp).start ∧
      (scratchRegion sp).start + (scratchRegion sp).size ≤ fr.rsp.toNat := by
  have := w.value
  have := w.room
  change fr.low.toNat ≤ (sp - 8).toNat ∧ (sp - 8).toNat + 392 ≤ fr.rsp.toNat
  rw [BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; omega)]
  change fr.low.toNat ≤ sp.toNat - 8 ∧ sp.toNat - 8 + 392 ≤ fr.rsp.toNat
  omega

theorem preservedSource {code fr args m n sp a} (w : Window code fr args m sp)
    (geo : Geometry code fr) (source : WordsAt m fr.rsi 64 (a : Limbs))
    (rd : Readable m fr.rsi 40) (writes : RamWriteFrame m n [scratchRegion sp]) :
    WordsAt n fr.rsi 64 a := by
  apply source.of_frame writes (by decide)
  change Outside _ fr.rsi 40
  have := rd.low
  obtain ⟨lo, hi⟩ := w.regionBounds
  refine ⟨by omega, ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  rcases geo.sourceStack with h | h <;> omega

theorem extendWrites {code fr args m n sp} (w : Window code fr args m sp)
    (before : RamWriteFrame fr.original m [fr.region, ⟨fr.rdi.toNat, 41⟩])
    (writes : RamWriteFrame m n [scratchRegion sp]) :
    RamWriteFrame fr.original n [fr.region, ⟨fr.rdi.toNat, 41⟩] := by
  apply before.trans writes
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  obtain ⟨lo, hi⟩ := w.regionBounds
  refine ⟨fr.region, List.mem_cons_self, lo, ?_⟩
  change _ ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
  have := w.room
  omega

end K256.Proofs.Sec1.SqrtLaterProducts.Early
