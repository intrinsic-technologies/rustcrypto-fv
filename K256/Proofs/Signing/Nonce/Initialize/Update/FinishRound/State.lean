import K256.Proofs.Signing.Nonce.Initialize.Update.State
import K256.Proofs.Verify.Choice

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2

def finalizeAt (second : Bool) (input : Input) : Label :=
  if second then .l1048d8 else if seeded input then .l10432a else .l1046c0

def keyAt (second : Bool) (input : Input) : Label :=
  if second then .l104918 else if seeded input then .l10435b else .l1046f1

def digestPtr (fr : Activation) (second : Bool) := sp fr + (if second then 128 else 16)

def nextKey (second : Bool) (input : Input) (state : State) :=
  HMAC.hmac SHA256.hashBytes 64 state.key (message second input state)

def valueReturn (second : Bool) (input : Input) : BitVec 64 :=
  if !second && seeded input then 0x10438b else 0x104951

structure ValueCall (second : Bool) (input : Input) (fr : Activation) (b : Verify.Core.Registers)
    (n : Ram) (state : State) : Prop where
  live : Live (keyAt second input) fr (b.set 4 ⟨64, sp fr⟩) n state
  widths : ParseSignature.ArgumentWidths b
  rsp : b[4] = ⟨64, sp fr - 8⟩
  dst : b[7] = ⟨64, fr.rdi⟩
  returned : memLoad n (sp fr - 8) 64 = valueReturn second input
  bx : (!second && seeded input) = true → b[3] = ⟨64, fr.rdi⟩
  slots : seeded input = true → Slots fr n

end K256.Proofs.Signing.Nonce.Initialize.Update
