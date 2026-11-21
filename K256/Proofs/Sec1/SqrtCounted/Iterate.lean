import K256.Proofs.Sec1.SqrtCounted.Frame

namespace K256.Proofs.Sec1.SqrtCounted

open X86 X86.Machine X86.UserProcess X86Proofs Prelude CFG Lift Refine LIR
open Sqrt Common.Field

abbrev Saved (site : SquareLoop) (a b : Values Value Reg.count) :=
  ∀ r : Fin Reg.count, r.val ∈ [3,5,12,13,14,15,22,39,50,51] →
    r ≠ site.countReg → b[r] = a[r]

structure LoopState (site : SquareLoop) (code : CodeMap) (fr : Activation)
    (base : Word) (n : Nat) (words : Limbs) (a : Values Value Reg.count) (m : Ram) : Prop where
  frame : LoopFrame code a m fr
  src : a[site.srcReg].get 64 = base
  dst : a[site.dstReg].get 64 = base + 40
  counter : a[site.countReg] = ⟨64, BitVec.ofNat 64 n⟩
  widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → a[i].width = 64
  input : WordsAt m base 64 words
  volatile : ∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → a[i].width = 64

theorem iterate {site : SquareLoop} {code : CodeMap} {fr : Activation} {base : Word}
    (body : ∀ {a m n words}, LoopState site code fr base (n + 1) words a m →
      n < 2^64 → ∃ b m',
      Parser.Reaches code site.head a m (if n = 0 then site.exit else site.head) b m' ∧
      LoopState site code fr base n (squareWords words) b m' ∧
      WordsAt m' (base + 40) 64 (squareWords words) ∧ Saved site a b ∧
      RamWriteFrame m m' [roundStack base])
    (n : Nat) (hn : n < 2^64) {a m words}
    (hs : LoopState site code fr base (n+1) words a m) :
    ∃ b m', Parser.Reaches code site.head a m site.exit b m' ∧
      LoopState site code fr base 0 (SqrtChain.iter squareWords (n+1) words) b m' ∧
      WordsAt m' (base + 40) 64 (SqrtChain.iter squareWords (n+1) words) ∧
      Saved site a b ∧ RamWriteFrame m m' [roundStack base] := by
  induction n generalizing a m words with
  | zero =>
    obtain ⟨b, m', run, state, out, saved, frame⟩ := body hs hn
    exact ⟨b, m', run, state, out, saved, frame⟩
  | succ n ih =>
    obtain ⟨b, m', run, state, _, saved, frame⟩ := body hs hn
    obtain ⟨z, mz, hz, zs, zo, zr, zf⟩ := ih (by omega) state
    exact ⟨z, mz, run.trans hz, zs, zo,
      fun i hi ne => (zr i hi ne).trans (saved i hi ne),
      frame.trans zf (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)⟩

end K256.Proofs.Sec1.SqrtCounted
