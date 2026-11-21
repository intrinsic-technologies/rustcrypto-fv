import Sha2.Spec
import Sha2.Proofs.NIST.SHA512
import Sha2.Proofs.Common.Machine.Code

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512

open Sha2.Spec Sha2.Spec.Program Standards.NIST

inductive Form where
  | slices
  | digest
  | reset (stage : Fin 3)
  | finalizeIntoReset (second : Bool)
  | traitFinalizeIntoReset (second : Bool)
  deriving DecidableEq

def Form.frameBytes : Form → Nat
  | .slices => 632
  | .digest => 600
  | .reset _ => 424
  | .finalizeIntoReset _ => 632
  | .traitFinalizeIntoReset _ => 648

def Form.stackBytes : Form → Nat
  | .slices => 1184
  | .digest => 1152
  | .reset _ => 976
  | .finalizeIntoReset _ => 1184
  | .traitFinalizeIntoReset _ => 1200

inductive Variant where
  | sha384
  | sha512
  | sha512_224
  | sha512_256
  deriving DecidableEq

def Variant.textOffset (v : Variant) (form : Form := .slices) : Nat :=
  match form, v with
  | .slices, .sha384 => 0x3b80
  | .slices, .sha512 => 0x97b0
  | .slices, .sha512_224 => 0x5ab0
  | .slices, .sha512_256 => 0x7910
  | .digest, .sha384 => 0x3880
  | .digest, .sha512 => 0x9490
  | .digest, .sha512_224 => 0x57d0
  | .digest, .sha512_256 => 0x7630

  | .reset _, .sha384 => 0x46f0
  | .reset _, .sha512 => 0xa380
  | .reset _, .sha512_224 => 0x65c0
  | .reset _, .sha512_256 => 0x8420
  | .finalizeIntoReset _, .sha384 => 0x3f70
  | .finalizeIntoReset _, .sha512 => 0x9bc0
  | .finalizeIntoReset _, .sha512_224 => 0x5e80
  | .finalizeIntoReset _, .sha512_256 => 0x7ce0
  | .traitFinalizeIntoReset _, .sha384 => 0x4fc0
  | .traitFinalizeIntoReset _, .sha512 => 0xac90
  | .traitFinalizeIntoReset _, .sha512_224 => 0x6e60
  | .traitFinalizeIntoReset _, .sha512_256 => 0x8cc0

def Variant.pc (v : Variant) (offset : Nat) (form : Form := .slices) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 (v.textOffset form + offset)

def Variant.outputBytes : Variant → Nat
  | .sha384 => 48
  | .sha512 => 64
  | .sha512_224 => 28
  | .sha512_256 => 32

def Variant.routine (v : Variant) (form : Form := .slices) : Routine where
  entryAddress := v.pc 0 form
  minStackBytes := form.stackBytes
  outputBytes := v.outputBytes

def Variant.initialHash : Variant → Array UInt64
  | .sha384 => NIST.SHA512.initialHash384
  | .sha512 => NIST.SHA512.initialHash
  | .sha512_224 => NIST.SHA512.initialHash224
  | .sha512_256 => NIST.SHA512.initialHash256

def Variant.hash (v : Variant) (input : ByteArray) : ByteArray :=
  match v with
  | .sha384 => NIST.SHA512.sha384 input
  | .sha512 => NIST.SHA512.sha512 input
  | .sha512_224 => NIST.SHA512.sha512_224 input
  | .sha512_256 => NIST.SHA512.sha512_256 input

def Variant.digest (v : Variant) (input : ByteArray) : Vector UInt8 v.outputBytes :=
  match v with
  | .sha384 => (SHA2.SHA384 (SHA2.bytesToBits input)).bytes
  | .sha512 => (SHA2.SHA512 (SHA2.bytesToBits input)).bytes
  | .sha512_224 => (SHA2.SHA512_224 (SHA2.bytesToBits input)).bytes
  | .sha512_256 => (SHA2.SHA512_256 (SHA2.bytesToBits input)).bytes

def Variant.epilogueOffset (v : Variant) (form : Form := .slices) : Nat :=
  match form, v with
  | .slices, .sha384 => 0x3dc
  | .slices, .sha512 => 0x3fa
  | .slices, .sha512_224 => 0x3bd
  | .slices, .sha512_256 => 0x3be
  | .digest, .sha384 => 0x2e8
  | .digest, .sha512 => 0x306
  | .digest, .sha512_224 => 0x2c9
  | .digest, .sha512_256 => 0x2ca

  | .reset _, .sha384 => 0x8be
  | .reset _, .sha512 => 0x8fc
  | .reset _, .sha512_224 => 0x87f
  | .reset _, .sha512_256 => 0x880
  | .finalizeIntoReset _, .sha384 => 0x761
  | .finalizeIntoReset _, .sha512 => 0x79f
  | .finalizeIntoReset _, .sha512_224 => 0x724
  | .finalizeIntoReset _, .sha512_256 => 0x725
  | .traitFinalizeIntoReset _, .sha384 => 0x7f9
  | .traitFinalizeIntoReset _, .sha512 => 0x837
  | .traitFinalizeIntoReset _, .sha512_224 => 0x7ba
  | .traitFinalizeIntoReset _, .sha512_256 => 0x7bb

theorem Variant.routine_sha384_reset :
    Variant.sha384.routine (.reset 1) = Sha2.Spec.Program.sha384Reset := rfl

theorem Variant.routine_sha512_reset :
    Variant.sha512.routine (.reset 1) = Sha2.Spec.Program.sha512Reset := rfl

theorem Variant.routine_sha512_224_reset :
    Variant.sha512_224.routine (.reset 1) = Sha2.Spec.Program.sha512_224Reset := rfl

theorem Variant.routine_sha512_256_reset :
    Variant.sha512_256.routine (.reset 1) = Sha2.Spec.Program.sha512_256Reset := rfl

theorem Variant.routine_sha384_finalizeIntoReset :
    Variant.sha384.routine (.finalizeIntoReset false) = Sha2.Spec.Program.sha384FinalizeIntoReset := rfl

theorem Variant.routine_sha512_finalizeIntoReset :
    Variant.sha512.routine (.finalizeIntoReset false) = Sha2.Spec.Program.sha512FinalizeIntoReset := rfl

theorem Variant.routine_sha512_224_finalizeIntoReset :
    Variant.sha512_224.routine (.finalizeIntoReset false) = Sha2.Spec.Program.sha512_224FinalizeIntoReset := rfl

theorem Variant.routine_sha512_256_finalizeIntoReset :
    Variant.sha512_256.routine (.finalizeIntoReset false) = Sha2.Spec.Program.sha512_256FinalizeIntoReset := rfl

theorem Variant.routine_sha384_traitFinalizeIntoReset :
    Variant.sha384.routine (.traitFinalizeIntoReset false) = Sha2.Spec.Program.sha384TraitFinalizeIntoReset := rfl

theorem Variant.routine_sha512_traitFinalizeIntoReset :
    Variant.sha512.routine (.traitFinalizeIntoReset false) = Sha2.Spec.Program.sha512TraitFinalizeIntoReset := rfl

theorem Variant.routine_sha512_224_traitFinalizeIntoReset :
    Variant.sha512_224.routine (.traitFinalizeIntoReset false) = Sha2.Spec.Program.sha512_224TraitFinalizeIntoReset := rfl

theorem Variant.routine_sha512_256_traitFinalizeIntoReset :
    Variant.sha512_256.routine (.traitFinalizeIntoReset false) = Sha2.Spec.Program.sha512_256TraitFinalizeIntoReset := rfl

theorem Variant.routine_sha384 : Variant.sha384.routine = Sha2.Spec.Program.sha384DigestSlices := rfl

theorem Variant.routine_sha512 : Variant.sha512.routine = Sha2.Spec.Program.sha512DigestSlices := rfl

theorem Variant.routine_sha512_224 : Variant.sha512_224.routine = Sha2.Spec.Program.sha512_224DigestSlices := rfl

theorem Variant.routine_sha512_256 : Variant.sha512_256.routine = Sha2.Spec.Program.sha512_256DigestSlices := rfl

theorem Variant.routine_sha384_digest :
    Variant.sha384.routine .digest = Sha2.Spec.Program.sha384Digest := rfl

theorem Variant.routine_sha512_digest :
    Variant.sha512.routine .digest = Sha2.Spec.Program.sha512Digest := rfl

theorem Variant.routine_sha512_224_digest :
    Variant.sha512_224.routine .digest = Sha2.Spec.Program.sha512_224Digest := rfl

theorem Variant.routine_sha512_256_digest :
    Variant.sha512_256.routine .digest = Sha2.Spec.Program.sha512_256Digest := rfl

theorem Variant.pc_add (v : Variant) (offset count : Nat) (form : Form := .slices) :
    v.pc offset form + BitVec.ofNat 64 count = v.pc (offset + count) form := by
  simp only [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]

theorem Variant.pc_inProgram (v : Variant) {offset : Nat} (bound : offset < 1024)
    (form : Form := .slices) : InProgram (v.pc offset form) := by
  apply Sha2.Proofs.Common.Machine.inProgram_of_textOffset
  cases form <;> cases v <;> simp only [Variant.textOffset] <;> omega

def Form.twoOutputs : Form → Bool
  | .slices | .digest => false
  | _ => true

def Form.secondOutput : Form → Bool
  | .reset stage => stage.val == 2
  | .finalizeIntoReset second | .traitFinalizeIntoReset second => second
  | _ => false

def Form.writeRegionCount (form : Form) : Nat := if form.twoOutputs then 3 else 2

def Form.canFinalize : Form → Prop
  | .reset stage => stage.val ≠ 0
  | _ => True

def Form.isTerminal : Form → Prop
  | .reset stage => stage.val = 2
  | .finalizeIntoReset second | .traitFinalizeIntoReset second => second = true
  | _ => True

def Form.outputRegister (form : Form) : X86.Syntax.Reg :=
  match form with
  | .digest => .rdx
  | _ => if form.secondOutput then .r8 else .rcx

end Sha2.Proofs.Wrapper512
