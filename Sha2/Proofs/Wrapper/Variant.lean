import Sha2.Spec
import Sha2.Proofs.NIST.SHA256
import Sha2.Proofs.Common.Machine.Code

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper

open Sha2.Spec Sha2.Spec.Program Standards.NIST

inductive Variant where
  | sha224
  | sha256
  deriving DecidableEq

def Variant.textOffset : Variant → Nat
  | .sha224 => 0x2b0
  | .sha256 => 0x1eb0

def Variant.pc (v : Variant) (offset : Nat) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 (v.textOffset + offset)

def Variant.outputBytes : Variant → Nat
  | .sha224 => 28
  | .sha256 => 32

def Variant.routine (v : Variant) : Routine where
  entryAddress := v.pc 0
  minStackBytes := 816
  outputBytes := v.outputBytes

def Variant.initialHash : Variant → Array UInt32
  | .sha224 => #[0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
      0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4]
  | .sha256 => NIST.SHA256.initialHash

def Variant.digest (v : Variant) (input : ByteArray) : Vector UInt8 v.outputBytes :=
  match v with
  | .sha224 => (SHA2.SHA224 (SHA2.bytesToBits input)).bytes
  | .sha256 => (SHA2.SHA256 (SHA2.bytesToBits input)).bytes

def Variant.hash (v : Variant) (input : ByteArray) : ByteArray :=
  match v with
  | .sha224 => ⟨(v.digest input).toArray⟩
  | .sha256 => NIST.SHA256.sha256 input

def Variant.serializeHash (v : Variant) (hash : Array UInt32) : ByteArray :=
  let bytes := hash.foldl (fun output word => output ++ NIST.Encoding.natToOctets 4 word.toNat)
    ByteArray.empty
  match v with
  | .sha224 => bytes.extract 0 28
  | .sha256 => bytes

def Variant.epilogueOffset : Variant → Nat
  | .sha224 => 0x383
  | .sha256 => 0x38f

theorem Variant.routine_sha224 : Variant.sha224.routine = sha224DigestSlices := rfl

theorem Variant.routine_sha256 : Variant.sha256.routine = sha256DigestSlices := rfl

theorem Variant.pc_add (v : Variant) (offset count : Nat) :
    v.pc offset + BitVec.ofNat 64 count = v.pc (offset + count) := by
  simp only [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]

theorem Variant.pc_inProgram (v : Variant) {offset : Nat} (bound : offset < 1024) :
    InProgram (v.pc offset) := by
  apply Sha2.Proofs.Common.Machine.inProgram_of_textOffset
  cases v <;> simp only [Variant.textOffset] <;> omega

theorem Variant.initialHash_size (v : Variant) : v.initialHash.size = 8 := by
  cases v <;> decide +kernel

end Sha2.Proofs.Wrapper
