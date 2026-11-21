import K256.Proofs.Generate.Generator.Multiply.State

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def doublesLabel (n : Nat) : Label := if n = 0 then .l11f5e5 else .l11d810

structure DoublesState (fr : Activation) (p : Projective) (count : Nat)
    (a : Registers) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn11c880.frameAt (doublesLabel count) fr)
  widths : ParseSignature.ArgumentWidths a
  savedWidths : SavedWidths a
  count : a[1].get 64 = BitVec.ofNat 64 count
  mask : a[5].get 64 = 0x1000003d10
  temp : a[12].get 64 = fr.rsp - 0xcb8 + 0x490
  savedMask : memLoad m (fr.rsp - 0xcb8 + 0x1c8) 64 = 0xfffffffffff8
  acc : p.Stored m (fr.rsp - 0xb90)

def DoubleStep (writes : BitVec 64 → List MemoryRegion) : Prop :=
  ∀ {fr : Activation} {p : Projective} {a : Registers} {m : Ram} {n : Nat},
    n + 1 ≤ 4 → DoublesState fr p (n+1) a m →
    ∃ b mem, Reaches (doublesLabel (n+1)) a m (doublesLabel n) b mem ∧
      DoublesState fr p.double n b mem ∧ RamWriteFrame m mem (writes (fr.rsp - 0xcb8))

def repeatDouble : Nat → Projective → Projective
  | 0, p => p
  | n+1, p => repeatDouble n p.double

theorem repeatDoubles {writes : BitVec 64 → List MemoryRegion} (step : DoubleStep writes) {fr : Activation} {a : Registers} {m : Ram}
    {p : Projective} {n : Nat} (bound : n ≤ 4) (state : DoublesState fr p n a m) :
    ∃ b mem, Reaches (doublesLabel n) a m .l11f5e5 b mem ∧
      DoublesState fr (repeatDouble n p) 0 b mem ∧ RamWriteFrame m mem (writes (fr.rsp - 0xcb8)) := by
  induction n generalizing p a m with
  | zero => exact ⟨a, m, .refl _, state, RamWriteFrame.refl _ _⟩
  | succ n ih =>
    obtain ⟨b, mem, first, next, frame⟩ := step bound state
    obtain ⟨c, out, rest, done, finalFrame⟩ := ih (by omega) next
    exact ⟨c, out, first.trans rest, done,
      frame.trans finalFrame (fun r h => ⟨r, h, Nat.le_refl _, Nat.le_refl _⟩)⟩

end K256.Proofs.Generate.Generator.Multiply
