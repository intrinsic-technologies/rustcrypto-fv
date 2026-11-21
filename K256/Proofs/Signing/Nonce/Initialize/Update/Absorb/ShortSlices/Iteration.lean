import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Loop
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Frame
import K256.Proofs.Verify.Hash.Update.Copy

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def offset (last : Bool) : Nat := if last then 32 else 16
def length (last : Bool) : Nat := if last then 0 else 32
def used (last : Bool) : Nat := if last then 33 else 1
def source (fr : Activation) (last : Bool) : BitVec 64 := if last then 1 else fr.rsp + 208
def target (second last : Bool) : Label :=
  if last then (if second then .l1048ba else .l10430c) else loopAt second
def destination (fr : Activation) (second last : Bool) : BitVec 64 :=
  context fr second + 64 + BitVec.ofNat 64 (used last)
def pushed (fr : Activation) (second : Bool) (m : Ram) :=
  memStore m (sp fr - 8) (if second then 0x1047df else 0x104211 : BitVec 64)
def copied (fr : Activation) (second last : Bool) (m : Ram) :=
  memCopy (pushed fr second m) (destination fr second last) (source fr last) (length last)
def result (fr : Activation) (second last : Bool) (m : Ram) :=
  memStore (copied fr second last m) (context fr second + 127) (33 : BitVec 8)

def Runs (second : Bool) : Prop :=
  ∀ {fr : Activation} {secret reduced : ByteArray} {state : State} {a : Verify.Core.Registers}
    {m : Ram} (last : Bool), Environment fr (.seeded secret reduced) →
    Live (loopAt second) fr a m state → Slots fr m → Cursor second fr a (offset last) →
    memLoad m (context fr second + 127) 8 = BitVec.ofNat 8 (used last) →
    ∃ b, Verify.Core.Reaches (loopAt second) a m (target second last) b (result fr second last m) ∧
      Cursor second fr b (offset last + 16) ∧
      (∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i]) ∧
      (second = false → b[14] = a[14]) ∧
      (∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → b[i].width = 64)

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices
