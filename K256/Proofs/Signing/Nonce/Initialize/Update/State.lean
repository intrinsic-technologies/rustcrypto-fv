import K256.Proofs.Signing.Nonce.Initialize.State
import K256.Proofs.Verify.LIR.Fn103f30.Frame
import K256.Proofs.Signing.UpdateV.State

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

inductive Input where
  | empty
  | seeded (secret reduced : ByteArray)

def Input.apply (input : Input) (state : State) : State :=
  match input with
  | .empty => Drbg.updateRound 0 ByteArray.empty state
  | .seeded secret reduced =>
    let data := secret ++ reduced
    Drbg.updateRound 1 data (Drbg.updateRound 0 data state)

def Input.At (input : Input) (fr : Activation) : Prop :=
  match input with
  | .empty => fr.rdx = 0
  | .seeded s h =>
    let sp := fr.rsp
    let m := fr.original
    fr.rdi = sp + 16 ∧ fr.rsi = sp + 112 ∧ fr.rdx = 3 ∧
      sp.toNat + 352 < 2^32 ∧ Readable m fr.rsi 48 ∧
      memLoad m fr.rsi 64 = sp + 320 ∧ memLoad m (fr.rsi + 8) 64 = 32 ∧
      memLoad m (fr.rsi + 16) 64 = sp + 208 ∧ memLoad m (fr.rsi + 24) 64 = 32 ∧
      memLoad m (fr.rsi + 32) 64 = 1 ∧ memLoad m (fr.rsi + 40) 64 = 0 ∧
      (⟨(sp + 320).toNat,32⟩ : MemoryRegion).HasBytes m s ∧
      (⟨(sp + 208).toNat,32⟩ : MemoryRegion).HasBytes m h

namespace Update

def seeded : Input → Bool
  | .empty => false
  | .seeded _ _ => true

def seed : Input → ByteArray
  | .empty => ByteArray.empty
  | .seeded s h => s ++ h

abbrev sp (fr : Activation) := fr.rsp - 712

def start (second : Bool) : Label := if second then .l10438b else .l103f30
def appendAt (second : Bool) : Label := if second then .l104579 else .l10416d
def digestAt (second : Bool) (input : Input) : Label :=
  if second then .l1048ba else if seeded input then .l10430c else .l1046a2
def resume (second : Bool) (input : Input) : Label :=
  if !second && seeded input then .l10438b else .l104951
def context (fr : Activation) (second : Bool) := sp fr + (if second then 328 else 160)
def tag (second : Bool) : UInt8 := if second then 1 else 0
def message (second : Bool) (input : Input) (state : State) :=
  state.value ++ ⟨#[tag second]⟩ ++ seed input

structure Environment (fr : Activation) (input : Input) : Prop where
  image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2
  depth : 1920 ≤ fr.rsp.toNat
  low : fr.low = fr.rsp - 1920
  limit : fr.rsp.toNat + 8 < 2^32
  dataLow : fr.rdi.toNat + 64 < 2^32
  apart : fr.rdi.toNat + 64 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat
  writable : Writable Extracted.programImage fr.original fr.rdi 64
  slices : input.At fr
  stack : Writable Extracted.programImage fr.original (fr.rsp - 1920) 1920

structure Live (l : Label) (fr : Activation) (a : Verify.Core.Registers) (m : Ram)
    (state : State) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn103f30.frameAt l fr)
  writes : RamWriteFrame fr.original m [fr.region, ⟨fr.rdi.toNat,64⟩]
  bytes : StateAt m fr.rdi state
  widths : l = .l104951 → ParseSignature.ArgumentWidths a
  savedWidths : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → a[i].width = 64

structure Slots (fr : Activation) (m : Ram) : Prop where
  stop : memLoad m (sp fr + 8) 64 = fr.rsi + 48
  value : memLoad m (sp fr + 112) 64 = fr.rdi + 32
  state : memLoad m (sp fr + 120) 64 = fr.rdi

end Update

end K256.Proofs.Signing.Nonce.Initialize
