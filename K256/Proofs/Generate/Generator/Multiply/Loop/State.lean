import K256.Proofs.Generate.Generator.Multiply.Loop.Countdown
import K256.Proofs.Generate.Generator.Multiply.Prepare.State
import K256.Proofs.Generate.Generator.Multiply.Round

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

def windowValue (d k : Nat) :=
  Curve.signedWindow (firstBase d) (secondBase d) (32-k)
    (Curve.radixRemaining (firstComponent d).natAbs k) (Curve.radixRemaining (secondComponent d).natAbs k)

structure WindowMemory (fr : Activation) (m : Ram) (d : Nat) : Prop where
  frame : RamWriteFrame fr.original m (coreWrites fr)
  firstTable : TableAt m fr.rcx (firstBase d)
  secondTable : TableAt m (fr.rcx + 960) (secondBase d)
  firstDigits : WordsAt m fr.r9 8 (Vector.ofFn fun i : Fin 33 => Radix.byte (firstComponent d).natAbs i.val)
  secondDigits : WordsAt m (fr.r9 + 33) 8 (Vector.ofFn fun i : Fin 33 => Radix.byte (secondComponent d).natAbs i.val)
  locals : ∀ kv ∈ ([(0x1a0,1),(0x1c0,fr.rcx),(0x1c8,0xfffffffffff8),(0x248,fr.rdi),
      (0x258,66),(0x260,66),(0x268,66)] : List (BitVec 64 × BitVec 64)),
    memLoad m (fr.rsp - 0xcb8 + kv.1) 64 = kv.2

structure WindowHead (fr : Activation) (a : Registers) (m : Ram) (d k : Nat) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn11c880.frameAt (windowLabel (BitVec.ofNat 64 k)) fr)
  widths : ParseSignature.ArgumentWidths a
  saved : SavedWidths a
  memory : WindowMemory fr m d
  acc : ∃ p : Projective, p.valid ∧ p.Stored m (fr.rsp - 0xb90) ∧ p.value = windowValue d k
  count : a[1] = ⟨64, BitVec.ofNat 64 k⟩
  pointer : a[2] = ⟨64, fr.r9 + BitVec.ofNat 64 (32+k)⟩
  temp : a[12].get 64 = fr.rsp - 0xcb8 + 0x490

theorem windowRoundValue {d k : Nat} (bound : k < 32) {p l r : Projective}
    (pv : p.valid) (lv : l.valid) (rv : r.valid)
    (acc : p.value = windowValue d (k+1))
    (left : l.value = Curve.selectDigit (firstBase d)
      (Curve.radixDigit (Curve.radixRemaining (firstComponent d).natAbs k)))
    (right : r.value = Curve.selectDigit (secondBase d)
      (Curve.radixDigit (Curve.radixRemaining (secondComponent d).natAbs k))) :
    (p.round l r).valid ∧ (p.round l r).value = windowValue d k := by
  obtain ⟨valid, eq⟩ := Projective.round_correct p l r pv lv rv
  refine ⟨valid, ?_⟩
  rw [eq, acc, left, right]
  unfold windowValue
  rw [show 32-k = (32-(k+1))+1 by omega]
  simp only [Curve.signedWindow, Curve.radixQuotient_remaining]

end K256.Proofs.Generate.Generator.Multiply
