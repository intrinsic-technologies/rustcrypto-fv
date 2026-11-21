import Sha3.Spec.Program

namespace Sha3.Proofs

open Sha3.Spec.Program

inductive Variant where
  | sha224 | sha256 | sha384 | sha512
  deriving DecidableEq

namespace Variant

def lanes : Variant → Nat
  | .sha224 => 18 | .sha256 => 17 | .sha384 => 13 | .sha512 => 9

def rate (v : Variant) : Nat := 8 * v.lanes

def digestBytes (v : Variant) (fullState : Bool := false) : Nat :=
  if fullState then 200 else
    match v with
    | .sha224 => 28 | .sha256 => 32 | .sha384 => 48 | .sha512 => 64

def suffix (keccak : Bool := false) : UInt8 := if keccak then 0x01 else 0x06

def entry (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : Routine :=
  if fullState then keccak256_full_digest_slices else
    match v, keccak with
    | .sha224, false => sha3_224_digest_slices
    | .sha224, true => keccak224_digest_slices
    | .sha256, false => sha3_256_digest_slices
    | .sha256, true => keccak256_digest_slices
    | .sha384, false => sha3_384_digest_slices
    | .sha384, true => keccak384_digest_slices
    | .sha512, false => sha3_512_digest_slices
    | .sha512, true => keccak512_digest_slices

def resetEntry (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : Routine :=
  if fullState then keccak256_full_reset else
    match v, keccak with
    | .sha224, false => sha3_224_reset
    | .sha224, true => keccak224_reset
    | .sha256, false => sha3_256_reset
    | .sha256, true => keccak256_reset
    | .sha384, false => sha3_384_reset
    | .sha384, true => keccak384_reset
    | .sha512, false => sha3_512_reset
    | .sha512, true => keccak512_reset

def finalizeResetEntry (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : Routine :=
  if fullState then keccak256_full_fixed_finalize_into_reset else
    match v, keccak with
    | .sha224, false => sha3_224_fixed_finalize_into_reset
    | .sha224, true => keccak224_fixed_finalize_into_reset
    | .sha256, false => sha3_256_fixed_finalize_into_reset
    | .sha256, true => keccak256_fixed_finalize_into_reset
    | .sha384, false => sha3_384_fixed_finalize_into_reset
    | .sha384, true => keccak384_fixed_finalize_into_reset
    | .sha512, false => sha3_512_fixed_finalize_into_reset
    | .sha512, true => keccak512_fixed_finalize_into_reset

def digestEntry (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : Routine :=
  if fullState then keccak256_full_digest else
    match v, keccak with
    | .sha224, false => sha3_224_digest
    | .sha224, true => keccak224_digest
    | .sha256, false => sha3_256_digest
    | .sha256, true => keccak256_digest
    | .sha384, false => sha3_384_digest
    | .sha384, true => keccak384_digest
    | .sha512, false => sha3_512_digest
    | .sha512, true => keccak512_digest

def finalizeFixedResetEntry (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : Routine :=
  if fullState then keccak256_full_finalize_fixed_reset else
    match v, keccak with
    | .sha224, false => sha3_224_finalize_fixed_reset
    | .sha224, true => keccak224_finalize_fixed_reset
    | .sha256, false => sha3_256_finalize_fixed_reset
    | .sha256, true => keccak256_finalize_fixed_reset
    | .sha384, false => sha3_384_finalize_fixed_reset
    | .sha384, true => keccak384_finalize_fixed_reset
    | .sha512, false => sha3_512_finalize_fixed_reset
    | .sha512, true => keccak512_finalize_fixed_reset

def digestFinalizeIntoResetEntry (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : Routine :=
  if fullState then keccak256_full_digest_finalize_into_reset else
    match v, keccak with
    | .sha224, false => sha3_224_digest_finalize_into_reset
    | .sha224, true => keccak224_digest_finalize_into_reset
    | .sha256, false => sha3_256_digest_finalize_into_reset
    | .sha256, true => keccak256_digest_finalize_into_reset
    | .sha384, false => sha3_384_digest_finalize_into_reset
    | .sha384, true => keccak384_digest_finalize_into_reset
    | .sha512, false => sha3_512_digest_finalize_into_reset
    | .sha512, true => keccak512_digest_finalize_into_reset

def digestFinalizeResetEntry (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : Routine :=
  if fullState then keccak256_full_digest_finalize_reset else
    match v, keccak with
    | .sha224, false => sha3_224_digest_finalize_reset
    | .sha224, true => keccak224_digest_finalize_reset
    | .sha256, false => sha3_256_digest_finalize_reset
    | .sha256, true => keccak256_digest_finalize_reset
    | .sha384, false => sha3_384_digest_finalize_reset
    | .sha384, true => keccak384_digest_finalize_reset
    | .sha512, false => sha3_512_digest_finalize_reset
    | .sha512, true => keccak512_digest_finalize_reset

def updateAddress : Variant → BitVec 64
  | .sha224 => 0x1008a0 | .sha256 => 0x100580
  | .sha384 => 0x1002b0 | .sha512 => 0x100000

def finalizeAddress (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    BitVec 64 :=
  if fullState then 0x106430 else
    match v, keccak with
    | .sha224, false => 0x1064e0 | .sha224, true => 0x1066c0
    | .sha256, false => 0x106860 | .sha256, true => 0x106790
    | .sha384, false => 0x106930 | .sha384, true => 0x106230
    | .sha512, false => 0x1065b0 | .sha512, true => 0x106320

def finalizeResetAddress (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    BitVec 64 :=
  if fullState then 0x106480 else
    match v, keccak with
    | .sha224, false => 0x106540 | .sha224, true => 0x106720
    | .sha256, false => 0x1068c0 | .sha256, true => 0x1067f0
    | .sha384, false => 0x1069a0 | .sha384, true => 0x1062a0
    | .sha512, false => 0x106630 | .sha512, true => 0x1063a0

theorem rate_pos (v : Variant) : 0 < v.rate := by cases v <;> decide +kernel

theorem rate_le (v : Variant) : v.rate ≤ 200 := by cases v <;> decide +kernel

theorem digestBytes_le (v : Variant) : v.digestBytes ≤ v.rate := by
  cases v <;> decide +kernel

theorem digestBytes_le_state (v : Variant) (fullState : Bool := false) :
    v.digestBytes fullState ≤ 200 := by cases fullState <;> cases v <;> decide +kernel

theorem entry_digestBytes (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) :
    (v.entry keccak fullState).outputBytes = v.digestBytes fullState := by
  cases fullState <;> cases keccak <;> cases v <;> rfl

theorem resetEntry_digestBytes (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) :
    (v.resetEntry keccak fullState).outputBytes = v.digestBytes fullState := by
  cases fullState <;> cases keccak <;> cases v <;> rfl

theorem finalizeResetEntry_digestBytes (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) :
    (v.finalizeResetEntry keccak fullState).outputBytes = v.digestBytes fullState := by
  cases fullState <;> cases keccak <;> cases v <;> rfl

theorem digestEntry_digestBytes (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) :
    (v.digestEntry keccak fullState).outputBytes = v.digestBytes fullState := by
  cases fullState <;> cases keccak <;> cases v <;> rfl

theorem finalizeFixedResetEntry_digestBytes (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) :
    (v.finalizeFixedResetEntry keccak fullState).outputBytes = v.digestBytes fullState := by
  cases fullState <;> cases keccak <;> cases v <;> rfl

theorem digestFinalizeIntoResetEntry_digestBytes (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) :
    (v.digestFinalizeIntoResetEntry keccak fullState).outputBytes = v.digestBytes fullState := by
  cases fullState <;> cases keccak <;> cases v <;> rfl

theorem digestFinalizeResetEntry_digestBytes (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) :
    (v.digestFinalizeResetEntry keccak fullState).outputBytes = v.digestBytes fullState := by
  cases fullState <;> cases keccak <;> cases v <;> rfl

end Variant

end Sha3.Proofs
