import K256.Proofs.Signing.Nonce.Initialize.Update.State

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

namespace Absorb

def taggedValue (second : Bool) (state : State) : ByteArray :=
  state.value ++ ⟨#[tag second]⟩

def loopAt (second : Bool) : Label := if second then .l1047fb else .l10422b

def afterPrefix (second : Bool) (input : Input) : Label :=
  if seeded input then loopAt second else digestAt second input

structure Cursor (second : Bool) (fr : Activation) (a : Verify.Core.Registers)
    (offset : Nat) : Prop where
  buf : a[13] = ⟨64, context fr second + 64⟩
  slice : (if second then a[14] else a[15]) = ⟨64, fr.rsi + BitVec.ofNat 64 offset⟩
  hash : second = true → a[5] = ⟨64, context fr second + 128⟩
  stop : second = true → a[15] = ⟨64, fr.rsi + 48⟩

end Absorb

end K256.Proofs.Signing.Nonce.Initialize.Update
