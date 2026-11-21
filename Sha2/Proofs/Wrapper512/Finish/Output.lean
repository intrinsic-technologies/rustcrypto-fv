import Sha2.Proofs.Common.Machine.FrameMemory
import Sha2.Proofs.Common.Encoding.Serialize.Stack
import Sha2.Proofs.Common.Instructions.CrossPageStore.Immediate
import Sha2.Proofs.Wrapper512.Dispatch.Store
import Sha2.Proofs.Common.Encoding.Serialize.Convert.SavePointer
import Sha2.Proofs.Wrapper512.Finish.Contract
import Sha2.Proofs.Wrapper512.Finish.Epilogue
import Sha2.Proofs.Common.Instructions.Bswap
import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.Instructions.CrossPageStore.Compose
import Sha2.Proofs.Common.Instructions.CrossPageStore.Legacy
import Sha2.Proofs.Common.Instructions.CrossPageStore.Range
import Sha2.Proofs.Common.Memory.LoadBytes
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Finish.Output

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.SHA512

def hashOffset (form : Form) : Nat := form.frameBytes - form.finalMemory.hash

def pointerRegister (v : Variant) (form : Form) : BitVec 4 :=
  match form with
  | .digest => 3
  | .traitFinalizeIntoReset false => if v = .sha512 then 13 else 5
  | _ => match v with
    | .sha384 => 9
    | .sha512 => 11
    | .sha512_224 | .sha512_256 => 7

def outputAddress (v : Variant) (s : RamState) (form : Form := .slices) : BitVec 64 :=
  match form with
  | .digest | .traitFinalizeIntoReset false =>
    (.reg ((pointerRegister v form).setWidth 5) : Operand 64).read s
  | _ => memLoad s.external
    (rspOf s + BitVec.ofNat 64 (form.frameBytes - form.outputSlot)) 64

attribute [local x86_compose] CrossPageStore.movM32R32LegacyEffect outputAddress encodeBswapR64
  BitVec.setWidth_setWidth_of_le BitVec.setWidth_eq gprNumber hashOffset pointerRegister

structure Pre (v : Variant) (s : RamState) (form : Form := .slices) : Prop where
  rip : s.RIP = v.pc (v.serializeOffset form) form
  readable : ∀ i ∈ ((List.range 8).map (fun j => BitVec.ofNat 64 (hashOffset form + 8*j)) ++
    (if form = .digest ∨ form = .traitFinalizeIntoReset false then []
      else [BitVec.ofNat 64 (form.frameBytes - form.outputSlot)])),
    MemReadable s (rspOf s + i) 8
  writable : ∀ i : Nat, i + 8 ≤ v.outputBytes →
    CrossPageStore.Writable s (outputAddress v s form + BitVec.ofNat 64 i) 8
  codeApart : ∀ i : Nat, i + 8 ≤ v.outputBytes →
    ∀ offset len : Nat, offset + len ≤ 71757 →
    RangeApart (outputAddress v s form + BitVec.ofNat 64 i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len
  writablePartial : v = .sha512_224 → CrossPageStore.Writable s (outputAddress v s form + 24) 4
  codeApartPartial : v = .sha512_224 → ∀ offset len : Nat, offset + len ≤ 71757 →
    RangeApart (outputAddress v s form + 24) 4
      (Extracted.textAddress + BitVec.ofNat 64 offset) len
  finalizes : form.canFinalize
  resetHashPointer : form = .reset 1 →
    (.reg 14 : Operand 64).read s = rspOf s + 128
  resetWritable : form = .reset 1 →
    ∀ i ∈ ([128,136,144,152,160,168,176,184,192,200] : List (BitVec 64)),
    CrossPageStore.Writable s (rspOf s + i) 8
  resetCodeApart : form = .reset 1 →
    ∀ i ∈ ([128,136,144,152,160,168,176,184,192,200] : List (BitVec 64)),
    ∀ offset len : Nat, offset + len ≤ 71757 →
    RangeApart (rspOf s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len
  resetTailWritable : form = .reset 1 → CrossPageStore.Writable s (rspOf s + 127) 1
  resetTailCodeApart : form = .reset 1 → ∀ offset len : Nat, offset + len ≤ 71757 →
    RangeApart (rspOf s + 127) 1 (Extracted.textAddress + BitVec.ofNat 64 offset) len
  resetOutputApart : form = .reset 1 →
    RangeApart (outputAddress v s form) v.outputBytes (rspOf s + 127) 81

def bytes (v : Variant) (form : Form := .slices) : List UInt8 :=
  match form, v with
  | .slices, .sha384 => [0x48,0x8b,0x84,0x24,0xa0,0x0,0x0,0x0,0x48,0x8b,0x8c,0x24,0xa8,0x0,0x0,0x0,0x48,0xf,0xc8,0x48,0xf,0xc9,0x48,0x8b,0x94,0x24,0xb0,0x0,0x0,0x0,0x48,0xf,0xca,0x48,0x8b,0xb4,0x24,0xb8,0x0,0x0,0x0,0x48,0xf,0xce,0x48,0x8b,0xbc,0x24,0xc0,0x0,0x0,0x0,0x48,0xf,0xcf,0x4c,0x8b,0x84,0x24,0xc8,0x0,0x0,0x0,0x49,0xf,0xc8,0x4c,0x8b,0x4c,0x24,0x8,0x49,0x89,0x1,0x49,0x89,0x49,0x8,0x49,0x89,0x51,0x10,0x49,0x89,0x71,0x18,0x49,0x89,0x79,0x20,0x4d,0x89,0x41,0x28]
  | .slices, .sha512 => [0x48,0x8b,0x84,0x24,0xa0,0x0,0x0,0x0,0x48,0x8b,0x8c,0x24,0xa8,0x0,0x0,0x0,0x48,0xf,0xc8,0x48,0xf,0xc9,0x48,0x8b,0x94,0x24,0xb0,0x0,0x0,0x0,0x48,0xf,0xca,0x48,0x8b,0xb4,0x24,0xb8,0x0,0x0,0x0,0x48,0xf,0xce,0x48,0x8b,0xbc,0x24,0xc0,0x0,0x0,0x0,0x48,0xf,0xcf,0x4c,0x8b,0x84,0x24,0xc8,0x0,0x0,0x0,0x49,0xf,0xc8,0x4c,0x8b,0x8c,0x24,0xd0,0x0,0x0,0x0,0x49,0xf,0xc9,0x4c,0x8b,0x94,0x24,0xd8,0x0,0x0,0x0,0x49,0xf,0xca,0x4c,0x8b,0x5c,0x24,0x8,0x49,0x89,0x3,0x49,0x89,0x4b,0x8,0x49,0x89,0x53,0x10,0x49,0x89,0x73,0x18,0x49,0x89,0x7b,0x20,0x4d,0x89,0x43,0x28,0x4d,0x89,0x4b,0x30,0x4d,0x89,0x53,0x38]
  | .slices, .sha512_224 => [0x48,0x8b,0x84,0x24,0xa0,0x0,0x0,0x0,0x48,0x8b,0x8c,0x24,0xa8,0x0,0x0,0x0,0x48,0xf,0xc8,0x48,0xf,0xc9,0x48,0x8b,0x94,0x24,0xb0,0x0,0x0,0x0,0x48,0xf,0xca,0x48,0x8b,0xb4,0x24,0xb8,0x0,0x0,0x0,0x48,0xf,0xce,0x48,0x8b,0x7c,0x24,0x8,0x48,0x89,0x7,0x48,0x89,0x4f,0x8,0x48,0x89,0x57,0x10,0x89,0x77,0x18]
  | .slices, .sha512_256 => [0x48,0x8b,0x84,0x24,0xa0,0x0,0x0,0x0,0x48,0x8b,0x8c,0x24,0xa8,0x0,0x0,0x0,0x48,0xf,0xc8,0x48,0xf,0xc9,0x48,0x8b,0x94,0x24,0xb0,0x0,0x0,0x0,0x48,0xf,0xca,0x48,0x8b,0xb4,0x24,0xb8,0x0,0x0,0x0,0x48,0xf,0xce,0x48,0x8b,0x7c,0x24,0x8,0x48,0x89,0x7,0x48,0x89,0x4f,0x8,0x48,0x89,0x57,0x10,0x48,0x89,0x77,0x18]
  | .digest, .sha384 => [0x48,0x8b,0x84,0x24,0x80,0x0,0x0,0x0,0x48,0x8b,0x8c,0x24,0x88,0x0,0x0,0x0,0x48,0xf,0xc8,0x48,0xf,0xc9,0x48,0x8b,0x94,0x24,0x90,0x0,0x0,0x0,0x48,0xf,0xca,0x48,0x8b,0xb4,0x24,0x98,0x0,0x0,0x0,0x48,0xf,0xce,0x48,0x8b,0xbc,0x24,0xa0,0x0,0x0,0x0,0x48,0xf,0xcf,0x4c,0x8b,0x84,0x24,0xa8,0x0,0x0,0x0,0x49,0xf,0xc8,0x48,0x89,0x3,0x48,0x89,0x4b,0x8,0x48,0x89,0x53,0x10,0x48,0x89,0x73,0x18,0x48,0x89,0x7b,0x20,0x4c,0x89,0x43,0x28]
  | .digest, .sha512 => [0x48,0x8b,0x84,0x24,0x80,0x0,0x0,0x0,0x48,0x8b,0x8c,0x24,0x88,0x0,0x0,0x0,0x48,0xf,0xc8,0x48,0xf,0xc9,0x48,0x8b,0x94,0x24,0x90,0x0,0x0,0x0,0x48,0xf,0xca,0x48,0x8b,0xb4,0x24,0x98,0x0,0x0,0x0,0x48,0xf,0xce,0x48,0x8b,0xbc,0x24,0xa0,0x0,0x0,0x0,0x48,0xf,0xcf,0x4c,0x8b,0x84,0x24,0xa8,0x0,0x0,0x0,0x49,0xf,0xc8,0x4c,0x8b,0x8c,0x24,0xb0,0x0,0x0,0x0,0x49,0xf,0xc9,0x4c,0x8b,0x94,0x24,0xb8,0x0,0x0,0x0,0x49,0xf,0xca,0x48,0x89,0x3,0x48,0x89,0x4b,0x8,0x48,0x89,0x53,0x10,0x48,0x89,0x73,0x18,0x48,0x89,0x7b,0x20,0x4c,0x89,0x43,0x28,0x4c,0x89,0x4b,0x30,0x4c,0x89,0x53,0x38]
  | .digest, .sha512_224 => [0x48,0x8b,0x84,0x24,0x80,0x0,0x0,0x0,0x48,0x8b,0x8c,0x24,0x88,0x0,0x0,0x0,0x48,0xf,0xc8,0x48,0xf,0xc9,0x48,0x8b,0x94,0x24,0x90,0x0,0x0,0x0,0x48,0xf,0xca,0x48,0x8b,0xb4,0x24,0x98,0x0,0x0,0x0,0x48,0xf,0xce,0x48,0x89,0x3,0x48,0x89,0x4b,0x8,0x48,0x89,0x53,0x10,0x89,0x73,0x18]
  | .digest, .sha512_256 => [0x48,0x8b,0x84,0x24,0x80,0x0,0x0,0x0,0x48,0x8b,0x8c,0x24,0x88,0x0,0x0,0x0,0x48,0xf,0xc8,0x48,0xf,0xc9,0x48,0x8b,0x94,0x24,0x90,0x0,0x0,0x0,0x48,0xf,0xca,0x48,0x8b,0xb4,0x24,0x98,0x0,0x0,0x0,0x48,0xf,0xce,0x48,0x89,0x3,0x48,0x89,0x4b,0x8,0x48,0x89,0x53,0x10,0x48,0x89,0x73,0x18]

  | .reset 1, .sha384 => [0x48,0x8b,0x8c,0x24,0x80,0x00,0x00,0x00,0x48,0x8b,0x84,0x24,0x88,0x00,0x00,0x00,0x48,0x8b,0x94,0x24,0x90,0x00,0x00,0x00,0x48,0x8b,0xb4,0x24,0x98,0x00,0x00,0x00,0x48,0x8b,0xbc,0x24,0xa0,0x00,0x00,0x00,0x4c,0x8b,0x84,0x24,0xa8,0x00,0x00,0x00,0x49,0xb9,0x07,0xd5,0x7c,0x36,0x2a,0x29,0x9a,0x62,0x4d,0x89,0x4e,0x08,0x49,0xb9,0x39,0x59,0x0e,0xf7,0xd8,0xec,0x2f,0x15,0x4d,0x89,0x4e,0x18,0x49,0xb9,0x11,0x15,0x58,0x68,0x87,0x4a,0xb4,0x8e,0x4d,0x89,0x4e,0x28,0x49,0xb9,0xa4,0x4f,0xfa,0xbe,0x1d,0x48,0xb5,0x47,0x4d,0x89,0x4e,0x38,0x49,0xb9,0xa7,0x8f,0xf9,0x64,0x0d,0x2e,0x0c,0xdb,0x4d,0x89,0x4e,0x30,0x49,0xb9,0x31,0x0b,0xc0,0xff,0x67,0x26,0x33,0x67,0x4d,0x89,0x4e,0x20,0x49,0xb9,0x17,0xdd,0x70,0x30,0x5a,0x01,0x59,0x91,0x4d,0x89,0x4e,0x10,0x49,0xb9,0xd8,0x9e,0x05,0xc1,0x5d,0x9d,0xbb,0xcb,0x4d,0x89,0x0e,0x48,0x0f,0xc9,0x48,0xc7,0x84,0x24,0xc8,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x48,0xc7,0x84,0x24,0xc0,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0xc6,0x44,0x24,0x7f,0x00,0x4c,0x8b,0x8c,0x24,0xe8,0x00,0x00,0x00,0x49,0x89,0x09,0x48,0x0f,0xc8,0x48,0x0f,0xca,0x49,0x89,0x41,0x08,0x49,0x89,0x51,0x10,0x48,0x0f,0xce,0x49,0x89,0x71,0x18,0x48,0x0f,0xcf,0x49,0x89,0x79,0x20,0x49,0x0f,0xc8,0x4d,0x89,0x41,0x28]
  | .reset 2, .sha384 => [0x48,0x8b,0x84,0x24,0x80,0x00,0x00,0x00,0x48,0x8b,0x8c,0x24,0x88,0x00,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0x90,0x00,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0x98,0x00,0x00,0x00,0x48,0x0f,0xce,0x48,0x8b,0xbc,0x24,0xa0,0x00,0x00,0x00,0x48,0x0f,0xcf,0x4c,0x8b,0x84,0x24,0xa8,0x00,0x00,0x00,0x49,0x0f,0xc8,0x4c,0x8b,0x8c,0x24,0xf0,0x00,0x00,0x00,0x49,0x89,0x01,0x49,0x89,0x49,0x08,0x49,0x89,0x51,0x10,0x49,0x89,0x71,0x18,0x49,0x89,0x79,0x20,0x4d,0x89,0x41,0x28]
  | .reset 1, .sha512 => [0x48,0x8b,0x8c,0x24,0x80,0x00,0x00,0x00,0x48,0x8b,0x84,0x24,0x88,0x00,0x00,0x00,0x48,0x8b,0x94,0x24,0x90,0x00,0x00,0x00,0x48,0x8b,0xb4,0x24,0x98,0x00,0x00,0x00,0x48,0x8b,0xbc,0x24,0xa0,0x00,0x00,0x00,0x4c,0x8b,0x84,0x24,0xa8,0x00,0x00,0x00,0x4c,0x8b,0x8c,0x24,0xb0,0x00,0x00,0x00,0x4c,0x8b,0x94,0x24,0xb8,0x00,0x00,0x00,0x49,0xbb,0x79,0x21,0x7e,0x13,0x19,0xcd,0xe0,0x5b,0x4d,0x89,0x5e,0x38,0x49,0xbb,0x1f,0x6c,0x3e,0x2b,0x8c,0x68,0x05,0x9b,0x4d,0x89,0x5e,0x28,0x49,0xbb,0xf1,0x36,0x1d,0x5f,0x3a,0xf5,0x4f,0xa5,0x4d,0x89,0x5e,0x18,0x49,0xbb,0x3b,0xa7,0xca,0x84,0x85,0xae,0x67,0xbb,0x4d,0x89,0x5e,0x08,0x49,0xbb,0x6b,0xbd,0x41,0xfb,0xab,0xd9,0x83,0x1f,0x4d,0x89,0x5e,0x30,0x49,0xbb,0xd1,0x82,0xe6,0xad,0x7f,0x52,0x0e,0x51,0x4d,0x89,0x5e,0x20,0x49,0xbb,0x2b,0xf8,0x94,0xfe,0x72,0xf3,0x6e,0x3c,0x4d,0x89,0x5e,0x10,0x49,0xbb,0x08,0xc9,0xbc,0xf3,0x67,0xe6,0x09,0x6a,0x4d,0x89,0x1e,0x48,0x0f,0xc9,0x48,0xc7,0x84,0x24,0xc8,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x48,0xc7,0x84,0x24,0xc0,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0xc6,0x44,0x24,0x7f,0x00,0x4c,0x8b,0x9c,0x24,0xe8,0x00,0x00,0x00,0x49,0x89,0x0b,0x48,0x0f,0xc8,0x49,0x89,0x43,0x08,0x48,0x0f,0xca,0x49,0x89,0x53,0x10,0x48,0x0f,0xce,0x48,0x0f,0xcf,0x49,0x89,0x73,0x18,0x49,0x89,0x7b,0x20,0x49,0x0f,0xc8,0x4d,0x89,0x43,0x28,0x49,0x0f,0xc9,0x4d,0x89,0x4b,0x30,0x49,0x0f,0xca,0x4d,0x89,0x53,0x38]
  | .reset 2, .sha512 => [0x48,0x8b,0x84,0x24,0x80,0x00,0x00,0x00,0x48,0x8b,0x8c,0x24,0x88,0x00,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0x90,0x00,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0x98,0x00,0x00,0x00,0x48,0x0f,0xce,0x48,0x8b,0xbc,0x24,0xa0,0x00,0x00,0x00,0x48,0x0f,0xcf,0x4c,0x8b,0x84,0x24,0xa8,0x00,0x00,0x00,0x49,0x0f,0xc8,0x4c,0x8b,0x8c,0x24,0xb0,0x00,0x00,0x00,0x49,0x0f,0xc9,0x4c,0x8b,0x94,0x24,0xb8,0x00,0x00,0x00,0x49,0x0f,0xca,0x4c,0x8b,0x9c,0x24,0xf0,0x00,0x00,0x00,0x49,0x89,0x03,0x49,0x89,0x4b,0x08,0x49,0x89,0x53,0x10,0x49,0x89,0x73,0x18,0x49,0x89,0x7b,0x20,0x4d,0x89,0x43,0x28,0x4d,0x89,0x4b,0x30,0x4d,0x89,0x53,0x38]
  | .reset 1, .sha512_224 => [0x48,0x8b,0x84,0x24,0x80,0x00,0x00,0x00,0x48,0x8b,0x8c,0x24,0x88,0x00,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0x90,0x00,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0x98,0x00,0x00,0x00,0x48,0x0f,0xce,0x48,0xbf,0xd6,0xd4,0xdc,0x89,0x66,0x99,0xe1,0x73,0x49,0x89,0x7e,0x08,0x48,0xbf,0xcf,0x9f,0x2f,0x58,0x14,0xd5,0x9d,0x67,0x49,0x89,0x7e,0x18,0x48,0xbf,0x42,0x89,0xc4,0x04,0x73,0x6f,0xe3,0x77,0x49,0x89,0x7e,0x28,0x48,0xbf,0xa1,0x92,0xd6,0x91,0xad,0xe6,0x12,0x11,0x49,0x89,0x7e,0x38,0x48,0xbf,0xc8,0x36,0x1d,0x6a,0xa8,0x85,0x9d,0x3f,0x49,0x89,0x7e,0x30,0x48,0xbf,0xa8,0x4d,0xd4,0x7b,0x69,0x2b,0x6d,0x0f,0x49,0x89,0x7e,0x20,0x48,0xbf,0x82,0x9c,0xff,0x32,0xae,0xb7,0xfa,0x1d,0x49,0x89,0x7e,0x10,0x48,0xbf,0xa2,0x4d,0x54,0x19,0xc8,0x37,0x3d,0x8c,0x49,0x89,0x3e,0x48,0xc7,0x84,0x24,0xc8,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x48,0xc7,0x84,0x24,0xc0,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0xc6,0x44,0x24,0x7f,0x00,0x48,0x8b,0xbc,0x24,0xe8,0x00,0x00,0x00,0x48,0x89,0x07,0x48,0x89,0x4f,0x08,0x48,0x89,0x57,0x10,0x89,0x77,0x18]
  | .reset 2, .sha512_224 => [0x48,0x8b,0x84,0x24,0x80,0x00,0x00,0x00,0x48,0x8b,0x8c,0x24,0x88,0x00,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0x90,0x00,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0x98,0x00,0x00,0x00,0x48,0x0f,0xce,0x48,0x8b,0xbc,0x24,0xf0,0x00,0x00,0x00,0x48,0x89,0x07,0x48,0x89,0x4f,0x08,0x48,0x89,0x57,0x10,0x89,0x77,0x18]
  | .reset 1, .sha512_256 => [0x48,0x8b,0x84,0x24,0x80,0x00,0x00,0x00,0x48,0x8b,0x8c,0x24,0x88,0x00,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0x90,0x00,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0x98,0x00,0x00,0x00,0x48,0x0f,0xce,0x48,0xbf,0xc2,0x64,0x4c,0xc8,0xa3,0x5f,0x55,0x9f,0x49,0x89,0x7e,0x08,0x48,0xbf,0xbd,0xea,0x40,0x59,0x19,0x77,0x38,0x96,0x49,0x89,0x7e,0x18,0x48,0xbf,0x92,0x39,0x86,0x53,0x25,0x1e,0x5e,0xbe,0x49,0x89,0x7e,0x28,0x48,0xbf,0xa2,0x2c,0xc5,0x81,0xdc,0x2d,0xb7,0x0e,0x49,0x89,0x7e,0x38,0x48,0xbf,0xaa,0xb8,0x85,0x2c,0xfc,0x99,0x01,0x2b,0x49,0x89,0x7e,0x30,0x48,0xbf,0xe3,0xff,0x8e,0xa8,0xe2,0x3e,0x28,0x96,0x49,0x89,0x7e,0x20,0x48,0xbf,0x51,0xb1,0x53,0x6f,0x6b,0xb8,0x93,0x23,0x49,0x89,0x7e,0x10,0x48,0xbf,0x2c,0xf7,0x2b,0xfc,0x94,0x21,0x31,0x22,0x49,0x89,0x3e,0x48,0xc7,0x84,0x24,0xc8,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x48,0xc7,0x84,0x24,0xc0,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0xc6,0x44,0x24,0x7f,0x00,0x48,0x8b,0xbc,0x24,0xe8,0x00,0x00,0x00,0x48,0x89,0x07,0x48,0x89,0x4f,0x08,0x48,0x89,0x57,0x10,0x48,0x89,0x77,0x18]
  | .reset 2, .sha512_256 => [0x48,0x8b,0x84,0x24,0x80,0x00,0x00,0x00,0x48,0x8b,0x8c,0x24,0x88,0x00,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0x90,0x00,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0x98,0x00,0x00,0x00,0x48,0x0f,0xce,0x48,0x8b,0xbc,0x24,0xf0,0x00,0x00,0x00,0x48,0x89,0x07,0x48,0x89,0x4f,0x08,0x48,0x89,0x57,0x10,0x48,0x89,0x77,0x18]
  | .finalizeIntoReset false, .sha384 => [0x48,0x8b,0x84,0x24,0x90,0x00,0x00,0x00,0x48,0x8b,0x8c,0x24,0x98,0x00,0x00,0x00,0x48,0x0f,0xc8,0x48,0x8b,0x94,0x24,0xa0,0x00,0x00,0x00,0x48,0x8b,0xb4,0x24,0xa8,0x00,0x00,0x00,0x48,0x8b,0xbc,0x24,0xb0,0x00,0x00,0x00,0x4c,0x8b,0x84,0x24,0xb8,0x00,0x00,0x00,0x4c,0x8b,0x8c,0x24,0xe0,0x00,0x00,0x00,0x49,0x89,0x01,0x48,0x0f,0xc9,0x49,0x89,0x49,0x08,0x48,0x0f,0xca,0x48,0x0f,0xce,0x49,0x89,0x51,0x10,0x49,0x89,0x71,0x18,0x48,0x0f,0xcf,0x49,0x89,0x79,0x20,0x49,0x0f,0xc8,0x4d,0x89,0x41,0x28]
  | .finalizeIntoReset true, .sha384 => [0x48,0x8b,0x84,0x24,0x70,0x01,0x00,0x00,0x48,0x8b,0x8c,0x24,0x78,0x01,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0x80,0x01,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0x88,0x01,0x00,0x00,0x48,0x0f,0xce,0x48,0x8b,0xbc,0x24,0x90,0x01,0x00,0x00,0x48,0x0f,0xcf,0x4c,0x8b,0x84,0x24,0x98,0x01,0x00,0x00,0x49,0x0f,0xc8,0x4c,0x8b,0x8c,0x24,0xe8,0x00,0x00,0x00,0x49,0x89,0x01,0x49,0x89,0x49,0x08,0x49,0x89,0x51,0x10,0x49,0x89,0x71,0x18,0x49,0x89,0x79,0x20,0x4d,0x89,0x41,0x28]
  | .finalizeIntoReset false, .sha512 => [0x48,0x8b,0x84,0x24,0x90,0x00,0x00,0x00,0x48,0x8b,0x8c,0x24,0x98,0x00,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0xa0,0x00,0x00,0x00,0x48,0x8b,0xb4,0x24,0xa8,0x00,0x00,0x00,0x48,0x8b,0xbc,0x24,0xb0,0x00,0x00,0x00,0x4c,0x8b,0x84,0x24,0xb8,0x00,0x00,0x00,0x4c,0x8b,0x8c,0x24,0xc0,0x00,0x00,0x00,0x4c,0x8b,0x94,0x24,0xc8,0x00,0x00,0x00,0x4c,0x8b,0x9c,0x24,0xe0,0x00,0x00,0x00,0x49,0x89,0x03,0x49,0x89,0x4b,0x08,0x48,0x0f,0xca,0x49,0x89,0x53,0x10,0x48,0x0f,0xce,0x49,0x89,0x73,0x18,0x48,0x0f,0xcf,0x49,0x0f,0xc8,0x49,0x89,0x7b,0x20,0x4d,0x89,0x43,0x28,0x49,0x0f,0xc9,0x4d,0x89,0x4b,0x30,0x49,0x0f,0xca,0x4d,0x89,0x53,0x38]
  | .finalizeIntoReset true, .sha512 => [0x48,0x8b,0x84,0x24,0x70,0x01,0x00,0x00,0x48,0x8b,0x8c,0x24,0x78,0x01,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0x80,0x01,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0x88,0x01,0x00,0x00,0x48,0x0f,0xce,0x48,0x8b,0xbc,0x24,0x90,0x01,0x00,0x00,0x48,0x0f,0xcf,0x4c,0x8b,0x84,0x24,0x98,0x01,0x00,0x00,0x49,0x0f,0xc8,0x4c,0x8b,0x8c,0x24,0xa0,0x01,0x00,0x00,0x49,0x0f,0xc9,0x4c,0x8b,0x94,0x24,0xa8,0x01,0x00,0x00,0x49,0x0f,0xca,0x4c,0x8b,0x9c,0x24,0xe8,0x00,0x00,0x00,0x49,0x89,0x03,0x49,0x89,0x4b,0x08,0x49,0x89,0x53,0x10,0x49,0x89,0x73,0x18,0x49,0x89,0x7b,0x20,0x4d,0x89,0x43,0x28,0x4d,0x89,0x4b,0x30,0x4d,0x89,0x53,0x38]
  | .finalizeIntoReset false, .sha512_224 => [0x48,0x8b,0x84,0x24,0x90,0x00,0x00,0x00,0x48,0x8b,0x8c,0x24,0x98,0x00,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0xa0,0x00,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0xa8,0x00,0x00,0x00,0x48,0x0f,0xce,0x48,0x8b,0xbc,0x24,0xe0,0x00,0x00,0x00,0x48,0x89,0x07,0x48,0x89,0x4f,0x08,0x48,0x89,0x57,0x10,0x89,0x77,0x18]
  | .finalizeIntoReset true, .sha512_224 => [0x48,0x8b,0x84,0x24,0x70,0x01,0x00,0x00,0x48,0x8b,0x8c,0x24,0x78,0x01,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0x80,0x01,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0x88,0x01,0x00,0x00,0x48,0x0f,0xce,0x48,0x8b,0xbc,0x24,0xe8,0x00,0x00,0x00,0x48,0x89,0x07,0x48,0x89,0x4f,0x08,0x48,0x89,0x57,0x10,0x89,0x77,0x18]
  | .finalizeIntoReset false, .sha512_256 => [0x48,0x8b,0x84,0x24,0x90,0x00,0x00,0x00,0x48,0x8b,0x8c,0x24,0x98,0x00,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0xa0,0x00,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0xa8,0x00,0x00,0x00,0x48,0x0f,0xce,0x48,0x8b,0xbc,0x24,0xe0,0x00,0x00,0x00,0x48,0x89,0x07,0x48,0x89,0x4f,0x08,0x48,0x89,0x57,0x10,0x48,0x89,0x77,0x18]
  | .finalizeIntoReset true, .sha512_256 => [0x48,0x8b,0x84,0x24,0x70,0x01,0x00,0x00,0x48,0x8b,0x8c,0x24,0x78,0x01,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0x80,0x01,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0x88,0x01,0x00,0x00,0x48,0x0f,0xce,0x48,0x8b,0xbc,0x24,0xe8,0x00,0x00,0x00,0x48,0x89,0x07,0x48,0x89,0x4f,0x08,0x48,0x89,0x57,0x10,0x48,0x89,0x77,0x18]
  | .traitFinalizeIntoReset false, .sha384 => [0x48,0x8b,0x84,0x24,0x80,0x01,0x00,0x00,0x48,0x8b,0x8c,0x24,0x88,0x01,0x00,0x00,0x48,0x0f,0xc8,0x48,0x8b,0x94,0x24,0x90,0x01,0x00,0x00,0x48,0x8b,0xb4,0x24,0x98,0x01,0x00,0x00,0x48,0x8b,0xbc,0x24,0xa0,0x01,0x00,0x00,0x4c,0x8b,0x84,0x24,0xa8,0x01,0x00,0x00,0x48,0x89,0x45,0x00,0x48,0x0f,0xc9,0x48,0x89,0x4d,0x08,0x48,0x0f,0xca,0x48,0x0f,0xce,0x48,0x89,0x55,0x10,0x48,0x89,0x75,0x18,0x48,0x0f,0xcf,0x48,0x89,0x7d,0x20,0x49,0x0f,0xc8,0x4c,0x89,0x45,0x28]
  | .traitFinalizeIntoReset true, .sha384 => [0x48,0x8b,0x84,0x24,0xa0,0x00,0x00,0x00,0x48,0x8b,0x8c,0x24,0xa8,0x00,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0xb0,0x00,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0xb8,0x00,0x00,0x00,0x48,0x0f,0xce,0x48,0x8b,0xbc,0x24,0xc0,0x00,0x00,0x00,0x48,0x0f,0xcf,0x4c,0x8b,0x84,0x24,0xc8,0x00,0x00,0x00,0x49,0x0f,0xc8,0x4c,0x8b,0x8c,0x24,0xf8,0x00,0x00,0x00,0x49,0x89,0x01,0x49,0x89,0x49,0x08,0x49,0x89,0x51,0x10,0x49,0x89,0x71,0x18,0x49,0x89,0x79,0x20,0x4d,0x89,0x41,0x28]
  | .traitFinalizeIntoReset false, .sha512 => [0x48,0x8b,0x84,0x24,0x80,0x01,0x00,0x00,0x48,0x8b,0x8c,0x24,0x88,0x01,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0x90,0x01,0x00,0x00,0x48,0x8b,0xb4,0x24,0x98,0x01,0x00,0x00,0x48,0x8b,0xbc,0x24,0xa0,0x01,0x00,0x00,0x4c,0x8b,0x84,0x24,0xa8,0x01,0x00,0x00,0x4c,0x8b,0x8c,0x24,0xb0,0x01,0x00,0x00,0x4c,0x8b,0x94,0x24,0xb8,0x01,0x00,0x00,0x49,0x89,0x45,0x00,0x49,0x89,0x4d,0x08,0x48,0x0f,0xca,0x49,0x89,0x55,0x10,0x48,0x0f,0xce,0x49,0x89,0x75,0x18,0x48,0x0f,0xcf,0x49,0x0f,0xc8,0x49,0x89,0x7d,0x20,0x4d,0x89,0x45,0x28,0x49,0x0f,0xc9,0x4d,0x89,0x4d,0x30,0x49,0x0f,0xca,0x4d,0x89,0x55,0x38]
  | .traitFinalizeIntoReset true, .sha512 => [0x48,0x8b,0x84,0x24,0xa0,0x00,0x00,0x00,0x48,0x8b,0x8c,0x24,0xa8,0x00,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0xb0,0x00,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0xb8,0x00,0x00,0x00,0x48,0x0f,0xce,0x48,0x8b,0xbc,0x24,0xc0,0x00,0x00,0x00,0x48,0x0f,0xcf,0x4c,0x8b,0x84,0x24,0xc8,0x00,0x00,0x00,0x49,0x0f,0xc8,0x4c,0x8b,0x8c,0x24,0xd0,0x00,0x00,0x00,0x49,0x0f,0xc9,0x4c,0x8b,0x94,0x24,0xd8,0x00,0x00,0x00,0x49,0x0f,0xca,0x4c,0x8b,0x9c,0x24,0xf8,0x00,0x00,0x00,0x49,0x89,0x03,0x49,0x89,0x4b,0x08,0x49,0x89,0x53,0x10,0x49,0x89,0x73,0x18,0x49,0x89,0x7b,0x20,0x4d,0x89,0x43,0x28,0x4d,0x89,0x4b,0x30,0x4d,0x89,0x53,0x38]
  | .traitFinalizeIntoReset false, .sha512_224 => [0x48,0x8b,0x84,0x24,0x80,0x01,0x00,0x00,0x48,0x8b,0x8c,0x24,0x88,0x01,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0x90,0x01,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0x98,0x01,0x00,0x00,0x48,0x0f,0xce,0x48,0x89,0x45,0x00,0x48,0x89,0x4d,0x08,0x48,0x89,0x55,0x10,0x89,0x75,0x18]
  | .traitFinalizeIntoReset true, .sha512_224 => [0x48,0x8b,0x84,0x24,0xa0,0x00,0x00,0x00,0x48,0x8b,0x8c,0x24,0xa8,0x00,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0xb0,0x00,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0xb8,0x00,0x00,0x00,0x48,0x0f,0xce,0x48,0x8b,0xbc,0x24,0xf8,0x00,0x00,0x00,0x48,0x89,0x07,0x48,0x89,0x4f,0x08,0x48,0x89,0x57,0x10,0x89,0x77,0x18]
  | .traitFinalizeIntoReset false, .sha512_256 => [0x48,0x8b,0x84,0x24,0x80,0x01,0x00,0x00,0x48,0x8b,0x8c,0x24,0x88,0x01,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0x90,0x01,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0x98,0x01,0x00,0x00,0x48,0x0f,0xce,0x48,0x89,0x45,0x00,0x48,0x89,0x4d,0x08,0x48,0x89,0x55,0x10,0x48,0x89,0x75,0x18]
  | .traitFinalizeIntoReset true, .sha512_256 => [0x48,0x8b,0x84,0x24,0xa0,0x00,0x00,0x00,0x48,0x8b,0x8c,0x24,0xa8,0x00,0x00,0x00,0x48,0x0f,0xc8,0x48,0x0f,0xc9,0x48,0x8b,0x94,0x24,0xb0,0x00,0x00,0x00,0x48,0x0f,0xca,0x48,0x8b,0xb4,0x24,0xb8,0x00,0x00,0x00,0x48,0x0f,0xce,0x48,0x8b,0xbc,0x24,0xf8,0x00,0x00,0x00,0x48,0x89,0x07,0x48,0x89,0x4f,0x08,0x48,0x89,0x57,0x10,0x48,0x89,0x77,0x18]
  | .reset ⟨0, _⟩, _ => []

def resetWrites (v : Variant) (s : RamState) (form : Form) : List Write :=
  if form = .reset 1 then [
    ⟨(.mem (rspOf s + 128) : Operand 64), v.initialHash[0]!.toBitVec⟩,
    ⟨(.mem (rspOf s + 136) : Operand 64), v.initialHash[1]!.toBitVec⟩,
    ⟨(.mem (rspOf s + 144) : Operand 64), v.initialHash[2]!.toBitVec⟩,
    ⟨(.mem (rspOf s + 152) : Operand 64), v.initialHash[3]!.toBitVec⟩,
    ⟨(.mem (rspOf s + 160) : Operand 64), v.initialHash[4]!.toBitVec⟩,
    ⟨(.mem (rspOf s + 168) : Operand 64), v.initialHash[5]!.toBitVec⟩,
    ⟨(.mem (rspOf s + 176) : Operand 64), v.initialHash[6]!.toBitVec⟩,
    ⟨(.mem (rspOf s + 184) : Operand 64), v.initialHash[7]!.toBitVec⟩,
    ⟨(.mem (rspOf s + 192) : Operand 64), 0⟩,
    ⟨(.mem (rspOf s + 200) : Operand 64), 0⟩,
    ⟨(.mem (rspOf s + 127) : Operand 8), 0⟩]
  else []

def effect (v : Variant) (s : RamState) (form : Form := .slices) : Effect :=
  { rip := v.pc (v.outputEndOffset form) form
    writes := (match v with
    | .sha384 => [
      ⟨(.reg 0 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + (if form = .reset 1 then 8 else 0))) : Operand 64).read s)⟩,
      ⟨(.reg 1 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + (if form = .reset 1 then 0 else 8))) : Operand 64).read s)⟩,
      ⟨(.reg 2 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 16)) : Operand 64).read s)⟩,
      ⟨(.reg 6 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 24)) : Operand 64).read s)⟩,
      ⟨(.reg 7 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 32)) : Operand 64).read s)⟩,
      ⟨(.reg 8 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 40)) : Operand 64).read s)⟩,
      ⟨(.reg 9 : Operand 64), if form ≠ .digest ∧ form ≠ .traitFinalizeIntoReset false then outputAddress v s form else (.reg 9 : Operand 64).read s⟩,
      ⟨(.mem (outputAddress v s form + 0) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 0)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 8) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 8)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 16) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 16)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 24) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 24)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 32) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 32)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 40) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 40)) : Operand 64).read s)⟩]
    | .sha512 => [
      ⟨(.reg 0 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + (if form = .reset 1 then 8 else 0))) : Operand 64).read s)⟩,
      ⟨(.reg 1 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + (if form = .reset 1 then 0 else 8))) : Operand 64).read s)⟩,
      ⟨(.reg 2 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 16)) : Operand 64).read s)⟩,
      ⟨(.reg 6 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 24)) : Operand 64).read s)⟩,
      ⟨(.reg 7 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 32)) : Operand 64).read s)⟩,
      ⟨(.reg 8 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 40)) : Operand 64).read s)⟩,
      ⟨(.reg 9 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 48)) : Operand 64).read s)⟩,
      ⟨(.reg 10 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 56)) : Operand 64).read s)⟩,
      ⟨(.reg 11 : Operand 64), if form ≠ .digest ∧ form ≠ .traitFinalizeIntoReset false then outputAddress v s form else (.reg 11 : Operand 64).read s⟩,
      ⟨(.mem (outputAddress v s form + 0) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 0)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 8) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 8)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 16) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 16)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 24) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 24)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 32) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 32)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 40) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 40)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 48) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 48)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 56) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 56)) : Operand 64).read s)⟩]
    | .sha512_224 => [
      ⟨(.reg 0 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 0)) : Operand 64).read s)⟩,
      ⟨(.reg 1 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 8)) : Operand 64).read s)⟩,
      ⟨(.reg 2 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 16)) : Operand 64).read s)⟩,
      ⟨(.reg 6 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 24)) : Operand 64).read s)⟩,
      ⟨(.reg 7 : Operand 64), if form ≠ .digest ∧ form ≠ .traitFinalizeIntoReset false then outputAddress v s form else (.reg 7 : Operand 64).read s⟩,
      ⟨(.mem (outputAddress v s form + 0) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 0)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 8) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 8)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 16) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 16)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 24) : Operand 32), (bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 24)) : Operand 64).read s)).setWidth 32⟩]
    | .sha512_256 => [
      ⟨(.reg 0 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 0)) : Operand 64).read s)⟩,
      ⟨(.reg 1 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 8)) : Operand 64).read s)⟩,
      ⟨(.reg 2 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 16)) : Operand 64).read s)⟩,
      ⟨(.reg 6 : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 24)) : Operand 64).read s)⟩,
      ⟨(.reg 7 : Operand 64), if form ≠ .digest ∧ form ≠ .traitFinalizeIntoReset false then outputAddress v s form else (.reg 7 : Operand 64).read s⟩,
      ⟨(.mem (outputAddress v s form + 0) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 0)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 8) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 8)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 16) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 16)) : Operand 64).read s)⟩,
      ⟨(.mem (outputAddress v s form + 24) : Operand 64), bswap64 ((.mem (rspOf s + BitVec.ofNat 64 (hashOffset form + 24)) : Operand 64).read s)⟩]) ++ resetWrites v s form
  }


theorem reset_memory_read_after_output {v : Variant} {s : RamState}
    (hP : Pre v s (.reset 1)) (mem : Ram) {n : Nat} (value : BitVec n)
    (off reset : BitVec 64) (k : Nat) (ho : off.toNat + n / 8 ≤ v.outputBytes)
    (hr : 127 ≤ reset.toNat) (hk : reset.toNat + k / 8 ≤ 208) :
    memLoad (memStore mem (outputAddress v s (.reset 1) + off) value)
      (rspOf s + reset) k = memLoad mem (rspOf s + reset) k := by
  apply memLoad_memStore_of_rangeApart
  intro i hi j hj
  have h := hP.resetOutputApart rfl (off.toNat+i) (by omega)
    (reset.toNat-127+j) (by omega)
  have decomp : 127 + (reset.toNat - 127 + j) = reset.toNat + j := by omega
  have addr : rspOf s + 127 + BitVec.ofNat 64 (reset.toNat-127+j) =
      rspOf s + reset + BitVec.ofNat 64 j := by
    calc
      _ = rspOf s + BitVec.ofNat 64 (127 + (reset.toNat-127+j)) := by
        simp only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
      _ = rspOf s + BitVec.ofNat 64 (reset.toNat+j) := by rw [decomp]
      _ = _ := by simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc]
  rw [addr] at h
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc] using h

theorem reset_memory_read_after_output_base {v : Variant} {s : RamState}
    (hP : Pre v s (.reset 1)) (mem : Ram) {n : Nat} (value : BitVec n)
    (reset : BitVec 64) (k : Nat) (ho : n / 8 ≤ v.outputBytes)
    (hr : 127 ≤ reset.toNat) (hk : reset.toNat + k / 8 ≤ 208) :
    memLoad (memStore mem (outputAddress v s (.reset 1)) value)
      (rspOf s + reset) k = memLoad mem (rspOf s + reset) k := by
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    reset_memory_read_after_output hP mem value 0 reset k
      (by change 0 + n / 8 ≤ v.outputBytes; simpa only [Nat.zero_add] using ho) hr hk


def resetPrefixEffect (v : Variant) (s : RamState) : Effect :=
  { rip := v.pc (match v with
      | .sha384 => 1466
      | .sha512 => 1482
      | .sha512_224 => 1459
      | .sha512_256 => 1459) (.reset 1)
    writes := (match v with
      | .sha384 => [
        ⟨(.reg 1 : Operand 64), bswap64 ((.mem (rspOf s + 128) : Operand 64).read s)⟩,
        ⟨(.reg 0 : Operand 64), ((.mem (rspOf s + 136) : Operand 64).read s)⟩,
        ⟨(.reg 2 : Operand 64), ((.mem (rspOf s + 144) : Operand 64).read s)⟩,
        ⟨(.reg 6 : Operand 64), ((.mem (rspOf s + 152) : Operand 64).read s)⟩,
        ⟨(.reg 7 : Operand 64), ((.mem (rspOf s + 160) : Operand 64).read s)⟩,
        ⟨(.reg 8 : Operand 64), ((.mem (rspOf s + 168) : Operand 64).read s)⟩,
        ⟨(.reg 9 : Operand 64), v.initialHash[0]!.toBitVec⟩]
      | .sha512 => [
        ⟨(.reg 1 : Operand 64), bswap64 ((.mem (rspOf s + 128) : Operand 64).read s)⟩,
        ⟨(.reg 0 : Operand 64), ((.mem (rspOf s + 136) : Operand 64).read s)⟩,
        ⟨(.reg 2 : Operand 64), ((.mem (rspOf s + 144) : Operand 64).read s)⟩,
        ⟨(.reg 6 : Operand 64), ((.mem (rspOf s + 152) : Operand 64).read s)⟩,
        ⟨(.reg 7 : Operand 64), ((.mem (rspOf s + 160) : Operand 64).read s)⟩,
        ⟨(.reg 8 : Operand 64), ((.mem (rspOf s + 168) : Operand 64).read s)⟩,
        ⟨(.reg 9 : Operand 64), ((.mem (rspOf s + 176) : Operand 64).read s)⟩,
        ⟨(.reg 10 : Operand 64), ((.mem (rspOf s + 184) : Operand 64).read s)⟩,
        ⟨(.reg 11 : Operand 64), v.initialHash[0]!.toBitVec⟩]
      | .sha512_224 => [
        ⟨(.reg 0 : Operand 64), bswap64 ((.mem (rspOf s + 128) : Operand 64).read s)⟩,
        ⟨(.reg 1 : Operand 64), bswap64 ((.mem (rspOf s + 136) : Operand 64).read s)⟩,
        ⟨(.reg 2 : Operand 64), bswap64 ((.mem (rspOf s + 144) : Operand 64).read s)⟩,
        ⟨(.reg 6 : Operand 64), bswap64 ((.mem (rspOf s + 152) : Operand 64).read s)⟩,
        ⟨(.reg 7 : Operand 64), v.initialHash[0]!.toBitVec⟩]
      | .sha512_256 => [
        ⟨(.reg 0 : Operand 64), bswap64 ((.mem (rspOf s + 128) : Operand 64).read s)⟩,
        ⟨(.reg 1 : Operand 64), bswap64 ((.mem (rspOf s + 136) : Operand 64).read s)⟩,
        ⟨(.reg 2 : Operand 64), bswap64 ((.mem (rspOf s + 144) : Operand 64).read s)⟩,
        ⟨(.reg 6 : Operand 64), bswap64 ((.mem (rspOf s + 152) : Operand 64).read s)⟩,
        ⟨(.reg 7 : Operand 64), v.initialHash[0]!.toBitVec⟩]
      ) ++ (resetWrites v s (.reset 1)).take 8 }

attribute [local x86_compose] resetPrefixEffect resetWrites List.take


def resetLoadedEffect (v : Variant) (s : RamState) : Effect :=
  { rip := v.pc (match v with
      | .sha384 => 1503
      | .sha512 => 1519
      | .sha512_224 => 1496
      | .sha512_256 => 1496) (.reset 1)
    writes := (match v with
      | .sha384 => [
        ⟨(.reg 1 : Operand 64), bswap64 ((.mem (rspOf s + 128) : Operand 64).read s)⟩,
        ⟨(.reg 0 : Operand 64), ((.mem (rspOf s + 136) : Operand 64).read s)⟩,
        ⟨(.reg 2 : Operand 64), ((.mem (rspOf s + 144) : Operand 64).read s)⟩,
        ⟨(.reg 6 : Operand 64), ((.mem (rspOf s + 152) : Operand 64).read s)⟩,
        ⟨(.reg 7 : Operand 64), ((.mem (rspOf s + 160) : Operand 64).read s)⟩,
        ⟨(.reg 8 : Operand 64), ((.mem (rspOf s + 168) : Operand 64).read s)⟩,
        ⟨(.reg 9 : Operand 64), outputAddress v s (.reset 1)⟩]
      | .sha512 => [
        ⟨(.reg 1 : Operand 64), bswap64 ((.mem (rspOf s + 128) : Operand 64).read s)⟩,
        ⟨(.reg 0 : Operand 64), ((.mem (rspOf s + 136) : Operand 64).read s)⟩,
        ⟨(.reg 2 : Operand 64), ((.mem (rspOf s + 144) : Operand 64).read s)⟩,
        ⟨(.reg 6 : Operand 64), ((.mem (rspOf s + 152) : Operand 64).read s)⟩,
        ⟨(.reg 7 : Operand 64), ((.mem (rspOf s + 160) : Operand 64).read s)⟩,
        ⟨(.reg 8 : Operand 64), ((.mem (rspOf s + 168) : Operand 64).read s)⟩,
        ⟨(.reg 9 : Operand 64), ((.mem (rspOf s + 176) : Operand 64).read s)⟩,
        ⟨(.reg 10 : Operand 64), ((.mem (rspOf s + 184) : Operand 64).read s)⟩,
        ⟨(.reg 11 : Operand 64), outputAddress v s (.reset 1)⟩]
      | .sha512_224 => [
        ⟨(.reg 0 : Operand 64), bswap64 ((.mem (rspOf s + 128) : Operand 64).read s)⟩,
        ⟨(.reg 1 : Operand 64), bswap64 ((.mem (rspOf s + 136) : Operand 64).read s)⟩,
        ⟨(.reg 2 : Operand 64), bswap64 ((.mem (rspOf s + 144) : Operand 64).read s)⟩,
        ⟨(.reg 6 : Operand 64), bswap64 ((.mem (rspOf s + 152) : Operand 64).read s)⟩,
        ⟨(.reg 7 : Operand 64), outputAddress v s (.reset 1)⟩]
      | .sha512_256 => [
        ⟨(.reg 0 : Operand 64), bswap64 ((.mem (rspOf s + 128) : Operand 64).read s)⟩,
        ⟨(.reg 1 : Operand 64), bswap64 ((.mem (rspOf s + 136) : Operand 64).read s)⟩,
        ⟨(.reg 2 : Operand 64), bswap64 ((.mem (rspOf s + 144) : Operand 64).read s)⟩,
        ⟨(.reg 6 : Operand 64), bswap64 ((.mem (rspOf s + 152) : Operand 64).read s)⟩,
        ⟨(.reg 7 : Operand 64), outputAddress v s (.reset 1)⟩]
      ) ++ resetWrites v s (.reset 1) }

def resetSuffixPointer (v : Variant) (s : RamState) : BitVec 64 :=
  (.reg ((pointerRegister v (.reset 1)).setWidth 5) : Operand 64).read s

def resetSuffixEffect (v : Variant) (s : RamState) : Effect :=
  { rip := v.pc (v.outputEndOffset (.reset 1)) (.reset 1)
    writes := match v with
      | .sha384 => [
        ⟨(.reg 1 : Operand 64), ((.reg 1 : Operand 64).read s)⟩,
        ⟨(.reg 0 : Operand 64), bswap64 ((.reg 0 : Operand 64).read s)⟩,
        ⟨(.reg 2 : Operand 64), bswap64 ((.reg 2 : Operand 64).read s)⟩,
        ⟨(.reg 6 : Operand 64), bswap64 ((.reg 6 : Operand 64).read s)⟩,
        ⟨(.reg 7 : Operand 64), bswap64 ((.reg 7 : Operand 64).read s)⟩,
        ⟨(.reg 8 : Operand 64), bswap64 ((.reg 8 : Operand 64).read s)⟩,
        ⟨(.reg 9 : Operand 64), resetSuffixPointer v s⟩,
        ⟨(.mem (resetSuffixPointer v s + 0) : Operand 64), ((.reg 1 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 8) : Operand 64), bswap64 ((.reg 0 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 16) : Operand 64), bswap64 ((.reg 2 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 24) : Operand 64), bswap64 ((.reg 6 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 32) : Operand 64), bswap64 ((.reg 7 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 40) : Operand 64), bswap64 ((.reg 8 : Operand 64).read s)⟩]
      | .sha512 => [
        ⟨(.reg 1 : Operand 64), ((.reg 1 : Operand 64).read s)⟩,
        ⟨(.reg 0 : Operand 64), bswap64 ((.reg 0 : Operand 64).read s)⟩,
        ⟨(.reg 2 : Operand 64), bswap64 ((.reg 2 : Operand 64).read s)⟩,
        ⟨(.reg 6 : Operand 64), bswap64 ((.reg 6 : Operand 64).read s)⟩,
        ⟨(.reg 7 : Operand 64), bswap64 ((.reg 7 : Operand 64).read s)⟩,
        ⟨(.reg 8 : Operand 64), bswap64 ((.reg 8 : Operand 64).read s)⟩,
        ⟨(.reg 9 : Operand 64), bswap64 ((.reg 9 : Operand 64).read s)⟩,
        ⟨(.reg 10 : Operand 64), bswap64 ((.reg 10 : Operand 64).read s)⟩,
        ⟨(.reg 11 : Operand 64), resetSuffixPointer v s⟩,
        ⟨(.mem (resetSuffixPointer v s + 0) : Operand 64), ((.reg 1 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 8) : Operand 64), bswap64 ((.reg 0 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 16) : Operand 64), bswap64 ((.reg 2 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 24) : Operand 64), bswap64 ((.reg 6 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 32) : Operand 64), bswap64 ((.reg 7 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 40) : Operand 64), bswap64 ((.reg 8 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 48) : Operand 64), bswap64 ((.reg 9 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 56) : Operand 64), bswap64 ((.reg 10 : Operand 64).read s)⟩]
      | .sha512_224 => [
        ⟨(.reg 0 : Operand 64), ((.reg 0 : Operand 64).read s)⟩,
        ⟨(.reg 1 : Operand 64), ((.reg 1 : Operand 64).read s)⟩,
        ⟨(.reg 2 : Operand 64), ((.reg 2 : Operand 64).read s)⟩,
        ⟨(.reg 6 : Operand 64), ((.reg 6 : Operand 64).read s)⟩,
        ⟨(.reg 7 : Operand 64), resetSuffixPointer v s⟩,
        ⟨(.mem (resetSuffixPointer v s + 0) : Operand 64), ((.reg 0 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 8) : Operand 64), ((.reg 1 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 16) : Operand 64), ((.reg 2 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 24) : Operand 32), (((.reg 6 : Operand 64).read s)).setWidth 32⟩]
      | .sha512_256 => [
        ⟨(.reg 0 : Operand 64), ((.reg 0 : Operand 64).read s)⟩,
        ⟨(.reg 1 : Operand 64), ((.reg 1 : Operand 64).read s)⟩,
        ⟨(.reg 2 : Operand 64), ((.reg 2 : Operand 64).read s)⟩,
        ⟨(.reg 6 : Operand 64), ((.reg 6 : Operand 64).read s)⟩,
        ⟨(.reg 7 : Operand 64), resetSuffixPointer v s⟩,
        ⟨(.mem (resetSuffixPointer v s + 0) : Operand 64), ((.reg 0 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 8) : Operand 64), ((.reg 1 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 16) : Operand 64), ((.reg 2 : Operand 64).read s)⟩,
        ⟨(.mem (resetSuffixPointer v s + 24) : Operand 64), ((.reg 6 : Operand 64).read s)⟩] }

attribute [local x86_compose] resetLoadedEffect resetSuffixPointer resetSuffixEffect

attribute [local x86_compose] Variant.pc Variant.textOffset Variant.serializeOffset
  Variant.outputEndOffset Variant.epilogueOffset Form.frameBytes Form.finalMemory Form.outputSlot
  ResetLayout.reset ResetLayout.finalizeIntoReset ResetLayout.traitFinalizeIntoReset
  ResetLayout.resetMemory ResetLayout.finalizeMemory ResetLayout.cloneMemory
  resetPrefixEffect resetWrites List.take resetLoadedEffect resetSuffixPointer resetSuffixEffect
  List.getElem!_cons_zero List.getElem!_cons_succ movM8Imm8Effect
attribute [local x86_local] Dispatch.Store.byteStore_local

def resetSuffixComponents (v : Variant) (s : RamState) : List Component :=
  [.reg 0,.reg 1,.reg 2,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,.reg 11,
    .mem (resetSuffixPointer v s) v.outputBytes,.rip]

set_option maxHeartbeats 600000 in
theorem resetSuffix_frame {v : Variant} {s t : RamState}
    (h : (resetSuffixEffect v s).Holds s t) : AgreesExcept (resetSuffixComponents v s) s t := by
  have cover {off len : Nat} (bound : off + len ≤ v.outputBytes) {a : BitVec 64}
      (ha : (Component.mem (resetSuffixPointer v s + BitVec.ofNat 64 off) len).Covers a) :
      ∃ c ∈ resetSuffixComponents v s, c.Covers a := by
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨.mem (resetSuffixPointer v s) v.outputBytes, by simp [resetSuffixComponents], off+i, by omega, ?_⟩
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  apply Common.Encoding.Serialize.agrees_of_footprint h.agrees
  · intro c hc hm
    cases v with
    | sha384 =>
      simp only [resetSuffixEffect, Effect.components, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
      all_goals simp_all [resetSuffixComponents, Component.isMem]
    | sha512 =>
      simp only [resetSuffixEffect, Effect.components, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
      all_goals simp_all [resetSuffixComponents, Component.isMem]
    | sha512_224 =>
      simp only [resetSuffixEffect, Effect.components, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
      all_goals simp_all [resetSuffixComponents, Component.isMem]
    | sha512_256 =>
      simp only [resetSuffixEffect, Effect.components, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
      all_goals simp_all [resetSuffixComponents, Component.isMem]
  · intro c hc a ha
    cases v with
    | sha384 =>
      simp only [resetSuffixEffect, Effect.components, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
      all_goals try exact ha.elim
      · exact cover (off := 0) (len := 8) (by decide) ha
      · exact cover (off := 8) (len := 8) (by decide) ha
      · exact cover (off := 16) (len := 8) (by decide) ha
      · exact cover (off := 24) (len := 8) (by decide) ha
      · exact cover (off := 32) (len := 8) (by decide) ha
      · exact cover (off := 40) (len := 8) (by decide) ha
    | sha512 =>
      simp only [resetSuffixEffect, Effect.components, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
      all_goals try exact ha.elim
      · exact cover (off := 0) (len := 8) (by decide) ha
      · exact cover (off := 8) (len := 8) (by decide) ha
      · exact cover (off := 16) (len := 8) (by decide) ha
      · exact cover (off := 24) (len := 8) (by decide) ha
      · exact cover (off := 32) (len := 8) (by decide) ha
      · exact cover (off := 40) (len := 8) (by decide) ha
      · exact cover (off := 48) (len := 8) (by decide) ha
      · exact cover (off := 56) (len := 8) (by decide) ha
    | sha512_224 =>
      simp only [resetSuffixEffect, Effect.components, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
      all_goals try exact ha.elim
      · exact cover (off := 0) (len := 8) (by decide) ha
      · exact cover (off := 8) (len := 8) (by decide) ha
      · exact cover (off := 16) (len := 8) (by decide) ha
      · exact cover (off := 24) (len := 4) (by decide) ha
    | sha512_256 =>
      simp only [resetSuffixEffect, Effect.components, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
      all_goals try exact ha.elim
      · exact cover (off := 0) (len := 8) (by decide) ha
      · exact cover (off := 8) (len := 8) (by decide) ha
      · exact cover (off := 16) (len := 8) (by decide) ha
      · exact cover (off := 24) (len := 8) (by decide) ha

theorem resetSuffix_pointer {v : Variant} {s t : RamState}
    (h : (resetLoadedEffect v s).Holds s t) :
    resetSuffixPointer v t = outputAddress v s (.reset 1) := by
  have hw := h.writes
  cases v <;> simp only [resetLoadedEffect, List.cons_append, List.nil_append, Write.AllHold] at hw
  · exact hw.2.2.2.2.2.2.1
  · exact hw.2.2.2.2.2.2.2.2.1
  · exact hw.2.2.2.2.1
  · exact hw.2.2.2.2.1

theorem resetSuffix_read_reset {v : Variant} {s t u : RamState}
    (pre : Pre v s (.reset 1)) (loaded : (resetLoadedEffect v s).Holds s t)
    (suffix : (resetSuffixEffect v t).Holds t u) (off n : Nat)
    (start : 127 ≤ off) (bound : off + n / 8 ≤ 208) :
    (Operand.mem (rspOf s + BitVec.ofNat 64 off) : Operand n).read u =
      (Operand.mem (rspOf s + BitVec.ofNat 64 off) : Operand n).read t := by
  apply Common.Encoding.Serialize.read_mem_of_agrees (resetSuffix_frame suffix)
  intro i hi c hc covered
  simp only [resetSuffixComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  obtain ⟨j,hj,eq⟩ := covered
  rw [resetSuffix_pointer loaded] at eq
  apply pre.resetOutputApart rfl j hj (off-127+i) (by omega)
  rw [← eq]
  have split : 127 + (off-127+i) = off+i := by omega
  calc
    _ = rspOf s + BitVec.ofNat 64 (off+i) := by rw [BitVec.ofNat_add, BitVec.add_assoc]
    _ = rspOf s + BitVec.ofNat 64 (127+(off-127+i)) := by rw [split]
    _ = _ := by simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2048 in
theorem reset_effect_compose {v : Variant} {s t u : RamState}
    (pre : Pre v s (.reset 1)) (loaded : (resetLoadedEffect v s).Holds s t)
    (suffix : (resetSuffixEffect v t).Holds t u) : (effect v s (.reset 1)).Holds s u := by
  have pointer := resetSuffix_pointer loaded
  refine ⟨suffix.rip, ?_, by trivial, ?_⟩
  · have hp := loaded.writes
    have hs := suffix.writes
    have m128 := resetSuffix_read_reset pre loaded suffix 128 64 (by decide) (by decide)
    have m136 := resetSuffix_read_reset pre loaded suffix 136 64 (by decide) (by decide)
    have m144 := resetSuffix_read_reset pre loaded suffix 144 64 (by decide) (by decide)
    have m152 := resetSuffix_read_reset pre loaded suffix 152 64 (by decide) (by decide)
    have m160 := resetSuffix_read_reset pre loaded suffix 160 64 (by decide) (by decide)
    have m168 := resetSuffix_read_reset pre loaded suffix 168 64 (by decide) (by decide)
    have m176 := resetSuffix_read_reset pre loaded suffix 176 64 (by decide) (by decide)
    have m184 := resetSuffix_read_reset pre loaded suffix 184 64 (by decide) (by decide)
    have m192 := resetSuffix_read_reset pre loaded suffix 192 64 (by decide) (by decide)
    have m200 := resetSuffix_read_reset pre loaded suffix 200 64 (by decide) (by decide)
    have m127 := resetSuffix_read_reset pre loaded suffix 127 8 (by decide) (by decide)
    cases v
    all_goals simp only [resetLoadedEffect, resetSuffixEffect, effect, resetWrites, List.cons_append, List.nil_append, Write.AllHold, hashOffset, Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, reduceIte, Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hp hs ⊢
    · rcases hp with ⟨p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17⟩
      rcases hs with ⟨q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12⟩
      simp_all only [resetSuffixPointer, pointerRegister, BitVec.ofNat_eq_ofNat, and_true, true_and]
      all_goals rw [ite_eq_left (show Form.reset 1 ≠ Form.digest ∧ Form.reset 1 ≠ Form.traitFinalizeIntoReset false from ⟨by decide, by decide⟩)]
    · rcases hp with ⟨p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19⟩
      rcases hs with ⟨q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14,q15,q16⟩
      simp_all only [resetSuffixPointer, pointerRegister, BitVec.ofNat_eq_ofNat, and_true, true_and]
      all_goals rw [ite_eq_left (show Form.reset 1 ≠ Form.digest ∧ Form.reset 1 ≠ Form.traitFinalizeIntoReset false from ⟨by decide, by decide⟩)]
    · rcases hp with ⟨p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩
      rcases hs with ⟨q0,q1,q2,q3,q4,q5,q6,q7,q8⟩
      simp_all only [resetSuffixPointer, pointerRegister, BitVec.ofNat_eq_ofNat, and_true, true_and]
      all_goals rw [ite_eq_left (show Form.reset 1 ≠ Form.digest ∧ Form.reset 1 ≠ Form.traitFinalizeIntoReset false from ⟨by decide, by decide⟩)]
    · rcases hp with ⟨p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15⟩
      rcases hs with ⟨q0,q1,q2,q3,q4,q5,q6,q7,q8⟩
      simp_all only [resetSuffixPointer, pointerRegister, BitVec.ofNat_eq_ofNat, and_true, true_and]
      all_goals rw [ite_eq_left (show Form.reset 1 ≠ Form.digest ∧ Form.reset 1 ≠ Form.traitFinalizeIntoReset false from ⟨by decide, by decide⟩)]
  · apply (loaded.agrees.trans suffix.agrees).mono
    intro c hc
    cases v
    all_goals simp only [resetLoadedEffect, resetSuffixEffect, effect, resetWrites, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc ⊢
    all_goals rw [pointer] at hc
    · rcases hc with hc | hc
      · rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) | rfl
        all_goals simp only [eq_self, true_or, or_true]
      · rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals simp only [eq_self, true_or, or_true]
    · rcases hc with hc | hc
      · rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) | rfl
        all_goals simp only [eq_self, true_or, or_true]
      · rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals simp only [eq_self, true_or, or_true]
    · rcases hc with hc | hc
      · rcases hc with ((rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) | rfl
        all_goals simp only [eq_self, true_or, or_true]
      · rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals simp only [eq_self, true_or, or_true]
    · rcases hc with hc | hc
      · rcases hc with ((rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) | rfl
        all_goals simp only [eq_self, true_or, or_true]
      · rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals simp only [eq_self, true_or, or_true]

theorem code {v : Variant} {s : RamState} {form : Form} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc (v.serializeOffset form) form) (bytes v form)) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset form + v.serializeOffset form) (bytes v form)
  all_goals
    cases form
    all_goals try (
      rename_i second
      have _ : Bool := second
      cases second)
    all_goals try (
      rename_i stage
      have _ : Fin 3 := stage
      have choices : stage = (0 : Fin 3) ∨ stage = 1 ∨ stage = 2 := by
        rcases stage with ⟨n, bound⟩
        rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      rcases choices with (rfl | rfl | rfl))
  all_goals cases v <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
theorem machine_sha384_resetPrefix [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre .sha384 s (.reset 1))
      (codeRange (Variant.sha384.pc (Variant.sha384.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha384 (.reset 1)))
      (Effect.post (fun s => resetPrefixEffect .sha384 s)) := by
  advance_begin (mov_r64_m64_effect_step 0x104c08 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 128)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case pre => intro s hP; exact ⟨hP.rip, hP.readable 128 (by decide +kernel)⟩
  case «next» =>
    intro s hP
    exact boundary_ne_program outside (inProgram_of_textOffset 0x4c10 (by decide))
  advance_then (mov_r64_m64_effect_step 0x104c10 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 136)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 8 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 136 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c18 (by decide))
  advance_then (mov_r64_m64_effect_step 0x104c18 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 144)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 16 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 144 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c20 (by decide))
  advance_then (mov_r64_m64_effect_step 0x104c20 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 152)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 24 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 152 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c28 (by decide))
  advance_then (mov_r64_m64_effect_step 0x104c28 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 160)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 32 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 160 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c30 (by decide))
  advance_then (mov_r64_m64_effect_step 0x104c30 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d32 168)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 40 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 168 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c38 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x104c38 0x49 0xb9 (by simp [RexWPrefix]) (by decide) (Variant.sha384.initialHash[1]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 48 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c42 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104c42 0x4d (by simp [RexWPrefix]) 9 (.base 14 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 58 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 136 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 136 (by decide +kernel) 0x4c42 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 136 (by decide +kernel) 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c46 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x104c46 0x49 0xb9 (by simp [RexWPrefix]) (by decide) (Variant.sha384.initialHash[3]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 62 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c50 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104c50 0x4d (by simp [RexWPrefix]) 9 (.base 14 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 72 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 152 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 152 (by decide +kernel) 0x4c50 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 152 (by decide +kernel) 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c54 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x104c54 0x49 0xb9 (by simp [RexWPrefix]) (by decide) (Variant.sha384.initialHash[5]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 76 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c5e (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104c5e 0x4d (by simp [RexWPrefix]) 9 (.base 14 (.d8 40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 86 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 168 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 168 (by decide +kernel) 0x4c5e 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 168 (by decide +kernel) 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c62 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x104c62 0x49 0xb9 (by simp [RexWPrefix]) (by decide) (Variant.sha384.initialHash[7]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 90 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c6c (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104c6c 0x4d (by simp [RexWPrefix]) 9 (.base 14 (.d8 56)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 100 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 184 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 184 (by decide +kernel) 0x4c6c 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 184 (by decide +kernel) 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c70 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x104c70 0x49 0xb9 (by simp [RexWPrefix]) (by decide) (Variant.sha384.initialHash[6]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 104 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c7a (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104c7a 0x4d (by simp [RexWPrefix]) 9 (.base 14 (.d8 48)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 114 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 176 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 176 (by decide +kernel) 0x4c7a 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 176 (by decide +kernel) 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c7e (by decide))
  advance_then (mov_r64_imm64_effect_step 0x104c7e 0x49 0xb9 (by simp [RexWPrefix]) (by decide) (Variant.sha384.initialHash[4]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 118 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c88 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104c88 0x4d (by simp [RexWPrefix]) 9 (.base 14 (.d8 32)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 128 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 160 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 160 (by decide +kernel) 0x4c88 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 160 (by decide +kernel) 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c8c (by decide))
  advance_then (mov_r64_imm64_effect_step 0x104c8c 0x49 0xb9 (by simp [RexWPrefix]) (by decide) (Variant.sha384.initialHash[2]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 132 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c96 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104c96 0x4d (by simp [RexWPrefix]) 9 (.base 14 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 142 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 144 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 144 (by decide +kernel) 0x4c96 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 144 (by decide +kernel) 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4c9a (by decide))
  advance_then (mov_r64_imm64_effect_step 0x104c9a 0x49 0xb9 (by simp [RexWPrefix]) (by decide) (Variant.sha384.initialHash[0]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 146 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4ca4 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104ca4 0x4d (by simp [RexWPrefix]) 9 (.base 14 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 156 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 128 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 128 (by decide +kernel) 0x4ca4 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 128 (by decide +kernel) 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4ca7 (by decide))
  advance_then (bswap_r64_effect_step 0x104ca7 1)
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 159 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4caa (by decide))
  apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t hP hH
  have pointer := hP.resetHashPointer rfl
  simp only [BitVec.ofNat_eq_ofNat] at pointer
  apply hH.weaken
  · x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
  · x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
theorem machine_sha384_resetLoaded [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre .sha384 s (.reset 1))
      (codeRange (Variant.sha384.pc (Variant.sha384.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha384 (.reset 1)))
      (Effect.post (fun s => resetLoadedEffect .sha384 s)) := by
  suffices continuation :
      AdvanceTriple boundary (fun s => Pre .sha384 s (.reset 1))
        (codeRange (Variant.sha384.pc (Variant.sha384.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha384 (.reset 1)))
        (Effect.post (fun s => resetPrefixEffect .sha384 s)) →
      AdvanceTriple boundary (fun s => Pre .sha384 s (.reset 1))
        (codeRange (Variant.sha384.pc (Variant.sha384.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha384 (.reset 1)))
        (Effect.post (fun s => resetLoadedEffect .sha384 s)) from
    continuation (machine_sha384_resetPrefix boundary outside)
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x104caa 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl 0)
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 162 12
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 200 (by decide +kernel)
    · x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 200 (by decide +kernel) 0x4caa 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 200 (by decide +kernel) 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4cb6 (by decide))
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x104cb6 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl 0)
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 174 12
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 192 (by decide +kernel)
    · x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 192 (by decide +kernel) 0x4cb6 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 192 (by decide +kernel) 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4cc2 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x104cc2 (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl 0)
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 186 5
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact (hP.resetTailWritable rfl).toMemWritable
    · x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetTailCodeApart rfl 0x4cc2 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetTailCodeApart rfl 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4cc7 (by decide))
  advance_then (mov_r64_m64_effect_step 0x104cc7 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d32 232)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 191 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 232 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4ccf (by decide))
  apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t hP hH
  have pointer := hP.resetHashPointer rfl
  simp only [BitVec.ofNat_eq_ofNat] at pointer
  apply hH.weaken
  · x86_norm [resetLoadedEffect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [resetLoadedEffect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [resetLoadedEffect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
  · x86_norm [resetLoadedEffect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
theorem machine_sha384_resetSuffix [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104ccf ∧
      (∀ i : Nat, i + 8 ≤ Variant.sha384.outputBytes →
        CrossPageStore.Writable s (resetSuffixPointer .sha384 s + BitVec.ofNat 64 i) 8) ∧
      ∀ i : Nat, i + 8 ≤ Variant.sha384.outputBytes → ∀ off len : Nat, off + len ≤ 71757 →
        RangeApart (resetSuffixPointer .sha384 s + BitVec.ofNat 64 i) 8
          (Extracted.textAddress + BitVec.ofNat 64 off) len)
      (codeRange (Variant.sha384.pc (Variant.sha384.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha384 (.reset 1)))
      (Effect.post (fun s => resetSuffixEffect .sha384 s)) := by
  advance_begin (CrossPageStore.mov_m64_r64_effect_step_any 0x104ccf 0x49 (by simp [RexWPrefix]) 1 (.base 9 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 199 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case pre =>
    intro s hP
    refine ⟨hP.1, ?_, ?_⟩
    · x86_norm
      simpa [resetSuffixPointer, pointerRegister, Operand.read] using hP.2.1 0 (by decide)
    · x86_norm
      simpa [resetSuffixPointer, pointerRegister, Operand.read, Extracted.textAddress] using
        hP.2.2 0 (by decide) 19663 3 (by decide)
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    simpa [resetSuffixPointer, pointerRegister, Operand.read, Extracted.textAddress] using
      hP.2.2 0 (by decide) 19464 237 (by decide)
  case «next» =>
    intro s hP
    exact boundary_ne_program outside (inProgram_of_textOffset 19666 (by decide))
  advance_then (bswap_r64_effect_step 0x104cd2 0)
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 202 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [resetSuffixPointer, pointerRegister]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4cd5 (by decide))
  advance_then (bswap_r64_effect_step 0x104cd5 2)
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 205 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [resetSuffixPointer, pointerRegister]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4cd8 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104cd8 0x49 (by simp [RexWPrefix]) 0 (.base 9 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 208 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [resetSuffixPointer, pointerRegister]) ?_ ?_, ?_, ?_⟩
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.2.1 8 (by decide)
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.2.2 8 (by decide) 0x4cd8 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [resetSuffixPointer, pointerRegister]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.2.2 8 (by decide) 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4cdc (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104cdc 0x49 (by simp [RexWPrefix]) 2 (.base 9 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 212 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [resetSuffixPointer, pointerRegister]) ?_ ?_, ?_, ?_⟩
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.2.1 16 (by decide)
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.2.2 16 (by decide) 0x4cdc 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [resetSuffixPointer, pointerRegister]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.2.2 16 (by decide) 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4ce0 (by decide))
  advance_then (bswap_r64_effect_step 0x104ce0 6)
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 216 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [resetSuffixPointer, pointerRegister]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4ce3 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104ce3 0x49 (by simp [RexWPrefix]) 6 (.base 9 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 219 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [resetSuffixPointer, pointerRegister]) ?_ ?_, ?_, ?_⟩
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.2.1 24 (by decide)
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.2.2 24 (by decide) 0x4ce3 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [resetSuffixPointer, pointerRegister]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.2.2 24 (by decide) 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4ce7 (by decide))
  advance_then (bswap_r64_effect_step 0x104ce7 7)
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 223 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [resetSuffixPointer, pointerRegister]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4cea (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104cea 0x49 (by simp [RexWPrefix]) 7 (.base 9 (.d8 32)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 226 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [resetSuffixPointer, pointerRegister]) ?_ ?_, ?_, ?_⟩
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.2.1 32 (by decide)
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.2.2 32 (by decide) 0x4cea 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [resetSuffixPointer, pointerRegister]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.2.2 32 (by decide) 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4cee (by decide))
  advance_then (bswap_r64_effect_step 0x104cee 8)
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 230 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [resetSuffixPointer, pointerRegister]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4cf1 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104cf1 0x4d (by simp [RexWPrefix]) 8 (.base 9 (.d8 40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x104c08 (bytes .sha384 (.reset 1)) 233 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [resetSuffixPointer, pointerRegister]) ?_ ?_, ?_, ?_⟩
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.2.1 40 (by decide)
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.2.2 40 (by decide) 0x4cf1 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [resetSuffixPointer, pointerRegister]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.2.2 40 (by decide) 0x4c08 237 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x4cf5 (by decide))
  apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t hP hH
  have writes := hH.writes
  have saved1 := hH.agrees.read (n := 64) (r := 1) (by x86_norm)
  have saved9 := hH.agrees.read (n := 64) (r := 9) (by x86_norm)
  refine ⟨?_, ?_, by trivial, ?_⟩
  · simpa only [resetSuffixEffect, Variant.pc, Variant.textOffset, Variant.outputEndOffset, ResetLayout.reset, Extracted.textAddress, Nat.reduceAdd, List.getElem!_cons_succ, List.getElem!_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hH.rip
  · x86_norm [resetSuffixEffect, resetSuffixPointer, pointerRegister] at writes ⊢
    rcases writes with ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10⟩
    exact ⟨saved1, w1, w2, w5, w7, w9, saved9, w0, w3, w4, w6, w8, w10⟩
  · apply hH.agrees.mono
    x86_norm [resetSuffixEffect, resetSuffixPointer, pointerRegister]


set_option maxRecDepth 2048 in
theorem machine_sha384_reset1 [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre .sha384 s (.reset 1))
      (codeRange (Variant.sha384.pc (Variant.sha384.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha384 (.reset 1)))
      (Effect.post (fun s => effect .sha384 s (.reset 1))) := by
  intro s ready loaded pre
  obtain ⟨n, t, run, readyT, loadedT, firstEffect⟩ := machine_sha384_resetLoaded boundary outside s ready loaded pre
  have pointer := resetSuffix_pointer firstEffect
  have suffixPre : t.RIP = 0x104ccf ∧
      (∀ i : Nat, i + 8 ≤ Variant.sha384.outputBytes →
        CrossPageStore.Writable t (resetSuffixPointer .sha384 t + BitVec.ofNat 64 i) 8) ∧
      (∀ i : Nat, i + 8 ≤ Variant.sha384.outputBytes → ∀ off len : Nat, off + len ≤ 71757 →
        RangeApart (resetSuffixPointer .sha384 t + BitVec.ofNat 64 i) 8
          (Extracted.textAddress + BitVec.ofNat 64 off) len) := by
    refine ⟨?_, ?_, ?_⟩
    · change t.RIP = (BitVec.ofNat 64 1068239)
      simpa only [resetLoadedEffect, Variant.pc, Variant.textOffset, Extracted.textAddress,
        Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using firstEffect.rip
    · intro i hi
      rw [pointer]
      exact ⟨(pre.writable i hi).toMemReadable.of_holds firstEffect, (pre.writable i hi).tables⟩
    · intro i hi off len bound
      rw [pointer]
      exact pre.codeApart i hi off len bound
  obtain ⟨m, u, run', readyU, loadedU, suffix⟩ := machine_sha384_resetSuffix boundary outside t readyT loadedT suffixPre
  exact ⟨n+m, u, run.trans run', readyU, loadedU, reset_effect_compose pre firstEffect suffix⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
theorem machine_sha512_resetPrefix [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre .sha512 s (.reset 1))
      (codeRange (Variant.sha512.pc (Variant.sha512.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha512 (.reset 1)))
      (Effect.post (fun s => resetPrefixEffect .sha512 s)) := by
  advance_begin (mov_r64_m64_effect_step 0x10a898 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 128)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case pre => intro s hP; exact ⟨hP.rip, hP.readable 128 (by decide +kernel)⟩
  case «next» =>
    intro s hP
    exact boundary_ne_program outside (inProgram_of_textOffset 0xa8a0 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a8a0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 136)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 8 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 136 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa8a8 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a8a8 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 144)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 16 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 144 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa8b0 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a8b0 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 152)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 24 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 152 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa8b8 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a8b8 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 160)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 32 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 160 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa8c0 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a8c0 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d32 168)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 40 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 168 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa8c8 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a8c8 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d32 176)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 48 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 176 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa8d0 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a8d0 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d32 184)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 56 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 184 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa8d8 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a8d8 0x49 0xbb (by simp [RexWPrefix]) (by decide) (Variant.sha512.initialHash[7]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 64 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa8e2 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10a8e2 0x4d (by simp [RexWPrefix]) 11 (.base 14 (.d8 56)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 74 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 184 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 184 (by decide +kernel) 0xa8e2 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 184 (by decide +kernel) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa8e6 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a8e6 0x49 0xbb (by simp [RexWPrefix]) (by decide) (Variant.sha512.initialHash[5]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 78 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa8f0 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10a8f0 0x4d (by simp [RexWPrefix]) 11 (.base 14 (.d8 40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 88 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 168 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 168 (by decide +kernel) 0xa8f0 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 168 (by decide +kernel) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa8f4 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a8f4 0x49 0xbb (by simp [RexWPrefix]) (by decide) (Variant.sha512.initialHash[3]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 92 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa8fe (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10a8fe 0x4d (by simp [RexWPrefix]) 11 (.base 14 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 102 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 152 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 152 (by decide +kernel) 0xa8fe 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 152 (by decide +kernel) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa902 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a902 0x49 0xbb (by simp [RexWPrefix]) (by decide) (Variant.sha512.initialHash[1]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 106 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa90c (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10a90c 0x4d (by simp [RexWPrefix]) 11 (.base 14 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 116 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 136 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 136 (by decide +kernel) 0xa90c 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 136 (by decide +kernel) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa910 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a910 0x49 0xbb (by simp [RexWPrefix]) (by decide) (Variant.sha512.initialHash[6]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 120 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa91a (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10a91a 0x4d (by simp [RexWPrefix]) 11 (.base 14 (.d8 48)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 130 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 176 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 176 (by decide +kernel) 0xa91a 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 176 (by decide +kernel) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa91e (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a91e 0x49 0xbb (by simp [RexWPrefix]) (by decide) (Variant.sha512.initialHash[4]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 134 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa928 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10a928 0x4d (by simp [RexWPrefix]) 11 (.base 14 (.d8 32)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 144 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 160 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 160 (by decide +kernel) 0xa928 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 160 (by decide +kernel) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa92c (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a92c 0x49 0xbb (by simp [RexWPrefix]) (by decide) (Variant.sha512.initialHash[2]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 148 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa936 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10a936 0x4d (by simp [RexWPrefix]) 11 (.base 14 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 158 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 144 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 144 (by decide +kernel) 0xa936 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 144 (by decide +kernel) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa93a (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a93a 0x49 0xbb (by simp [RexWPrefix]) (by decide) (Variant.sha512.initialHash[0]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 162 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa944 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10a944 0x4d (by simp [RexWPrefix]) 11 (.base 14 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 172 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 128 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 128 (by decide +kernel) 0xa944 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 128 (by decide +kernel) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa947 (by decide))
  advance_then (bswap_r64_effect_step 0x10a947 1)
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 175 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa94a (by decide))
  apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t hP hH
  have pointer := hP.resetHashPointer rfl
  simp only [BitVec.ofNat_eq_ofNat] at pointer
  apply hH.weaken
  · x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
  · x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
theorem machine_sha512_resetLoaded [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre .sha512 s (.reset 1))
      (codeRange (Variant.sha512.pc (Variant.sha512.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha512 (.reset 1)))
      (Effect.post (fun s => resetLoadedEffect .sha512 s)) := by
  suffices continuation :
      AdvanceTriple boundary (fun s => Pre .sha512 s (.reset 1))
        (codeRange (Variant.sha512.pc (Variant.sha512.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha512 (.reset 1)))
        (Effect.post (fun s => resetPrefixEffect .sha512 s)) →
      AdvanceTriple boundary (fun s => Pre .sha512 s (.reset 1))
        (codeRange (Variant.sha512.pc (Variant.sha512.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha512 (.reset 1)))
        (Effect.post (fun s => resetLoadedEffect .sha512 s)) from
    continuation (machine_sha512_resetPrefix boundary outside)
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x10a94a 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl 0)
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 178 12
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 200 (by decide +kernel)
    · x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 200 (by decide +kernel) 0xa94a 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 200 (by decide +kernel) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa956 (by decide))
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x10a956 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl 0)
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 190 12
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 192 (by decide +kernel)
    · x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 192 (by decide +kernel) 0xa956 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 192 (by decide +kernel) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa962 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10a962 (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl 0)
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 202 5
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact (hP.resetTailWritable rfl).toMemWritable
    · x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetTailCodeApart rfl 0xa962 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetTailCodeApart rfl 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa967 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a967 0x4c (by simp [RexWPrefix]) 11 (.sib 4 none 0 (.d32 232)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 207 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 232 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa96f (by decide))
  apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t hP hH
  have pointer := hP.resetHashPointer rfl
  simp only [BitVec.ofNat_eq_ofNat] at pointer
  apply hH.weaken
  · x86_norm [resetLoadedEffect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [resetLoadedEffect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [resetLoadedEffect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
  · x86_norm [resetLoadedEffect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
theorem machine_sha512_resetSuffix [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10a96f ∧
      (∀ i : Nat, i + 8 ≤ Variant.sha512.outputBytes →
        CrossPageStore.Writable s (resetSuffixPointer .sha512 s + BitVec.ofNat 64 i) 8) ∧
      ∀ i : Nat, i + 8 ≤ Variant.sha512.outputBytes → ∀ off len : Nat, off + len ≤ 71757 →
        RangeApart (resetSuffixPointer .sha512 s + BitVec.ofNat 64 i) 8
          (Extracted.textAddress + BitVec.ofNat 64 off) len)
      (codeRange (Variant.sha512.pc (Variant.sha512.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha512 (.reset 1)))
      (Effect.post (fun s => resetSuffixEffect .sha512 s)) := by
  advance_begin (CrossPageStore.mov_m64_r64_effect_step_any 0x10a96f 0x49 (by simp [RexWPrefix]) 1 (.base 11 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 215 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case pre =>
    intro s hP
    refine ⟨hP.1, ?_, ?_⟩
    · x86_norm
      simpa [resetSuffixPointer, pointerRegister, Operand.read] using hP.2.1 0 (by decide)
    · x86_norm
      simpa [resetSuffixPointer, pointerRegister, Operand.read, Extracted.textAddress] using
        hP.2.2 0 (by decide) 43375 3 (by decide)
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    simpa [resetSuffixPointer, pointerRegister, Operand.read, Extracted.textAddress] using
      hP.2.2 0 (by decide) 43160 267 (by decide)
  case «next» =>
    intro s hP
    exact boundary_ne_program outside (inProgram_of_textOffset 43378 (by decide))
  advance_then (bswap_r64_effect_step 0x10a972 0)
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 218 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [resetSuffixPointer, pointerRegister]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa975 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10a975 0x49 (by simp [RexWPrefix]) 0 (.base 11 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 221 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [resetSuffixPointer, pointerRegister]) ?_ ?_, ?_, ?_⟩
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.1 8 (by decide)
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.2 8 (by decide) 0xa975 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.2 8 (by decide) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa979 (by decide))
  advance_then (bswap_r64_effect_step 0x10a979 2)
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 225 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [resetSuffixPointer, pointerRegister]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa97c (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10a97c 0x49 (by simp [RexWPrefix]) 2 (.base 11 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 228 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [resetSuffixPointer, pointerRegister]) ?_ ?_, ?_, ?_⟩
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.1 16 (by decide)
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.2 16 (by decide) 0xa97c 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.2 16 (by decide) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa980 (by decide))
  advance_then (bswap_r64_effect_step 0x10a980 6)
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 232 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [resetSuffixPointer, pointerRegister]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa983 (by decide))
  advance_then (bswap_r64_effect_step 0x10a983 7)
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 235 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [resetSuffixPointer, pointerRegister]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa986 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10a986 0x49 (by simp [RexWPrefix]) 6 (.base 11 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 238 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [resetSuffixPointer, pointerRegister]) ?_ ?_, ?_, ?_⟩
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.1 24 (by decide)
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.2 24 (by decide) 0xa986 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.2 24 (by decide) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa98a (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10a98a 0x49 (by simp [RexWPrefix]) 7 (.base 11 (.d8 32)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 242 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [resetSuffixPointer, pointerRegister]) ?_ ?_, ?_, ?_⟩
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.1 32 (by decide)
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.2 32 (by decide) 0xa98a 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.2 32 (by decide) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa98e (by decide))
  advance_then (bswap_r64_effect_step 0x10a98e 8)
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 246 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [resetSuffixPointer, pointerRegister]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa991 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10a991 0x4d (by simp [RexWPrefix]) 8 (.base 11 (.d8 40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 249 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [resetSuffixPointer, pointerRegister]) ?_ ?_, ?_, ?_⟩
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.1 40 (by decide)
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.2 40 (by decide) 0xa991 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.2 40 (by decide) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa995 (by decide))
  advance_then (bswap_r64_effect_step 0x10a995 9)
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 253 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [resetSuffixPointer, pointerRegister]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa998 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10a998 0x4d (by simp [RexWPrefix]) 9 (.base 11 (.d8 48)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 256 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [resetSuffixPointer, pointerRegister]) ?_ ?_, ?_, ?_⟩
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.1 48 (by decide)
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.2 48 (by decide) 0xa998 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.2 48 (by decide) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa99c (by decide))
  advance_then (bswap_r64_effect_step 0x10a99c 10)
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 260 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [resetSuffixPointer, pointerRegister]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa99f (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10a99f 0x4d (by simp [RexWPrefix]) 10 (.base 11 (.d8 56)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x10a898 (bytes .sha512 (.reset 1)) 263 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [resetSuffixPointer, pointerRegister]) ?_ ?_, ?_, ?_⟩
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.1 56 (by decide)
    · x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.2 56 (by decide) 0xa99f 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [resetSuffixPointer, pointerRegister]
      simpa [resetSuffixPointer, pointerRegister, rspOf, Operand.read, Extracted.textAddress] using hP.2.2 56 (by decide) 0xa898 267 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa9a3 (by decide))
  apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t hP hH
  have writes := hH.writes
  have saved1 := hH.agrees.read (n := 64) (r := 1) (by x86_norm)
  have saved11 := hH.agrees.read (n := 64) (r := 11) (by x86_norm)
  refine ⟨?_, ?_, by trivial, ?_⟩
  · simpa only [resetSuffixEffect, Variant.pc, Variant.textOffset, Variant.outputEndOffset, ResetLayout.reset, Extracted.textAddress, Nat.reduceAdd, List.getElem!_cons_succ, List.getElem!_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hH.rip
  · x86_norm [resetSuffixEffect, resetSuffixPointer, pointerRegister] at writes ⊢
    rcases writes with ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14⟩
    exact ⟨saved1, w1, w3, w5, w6, w9, w11, w13, saved11, w0, w2, w4, w7, w8, w10, w12, w14⟩
  · apply hH.agrees.mono
    x86_norm [resetSuffixEffect, resetSuffixPointer, pointerRegister]


set_option maxRecDepth 2048 in
theorem machine_sha512_reset1 [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre .sha512 s (.reset 1))
      (codeRange (Variant.sha512.pc (Variant.sha512.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha512 (.reset 1)))
      (Effect.post (fun s => effect .sha512 s (.reset 1))) := by
  intro s ready loaded pre
  obtain ⟨n, t, run, readyT, loadedT, firstEffect⟩ := machine_sha512_resetLoaded boundary outside s ready loaded pre
  have pointer := resetSuffix_pointer firstEffect
  have suffixPre : t.RIP = 0x10a96f ∧
      (∀ i : Nat, i + 8 ≤ Variant.sha512.outputBytes →
        CrossPageStore.Writable t (resetSuffixPointer .sha512 t + BitVec.ofNat 64 i) 8) ∧
      (∀ i : Nat, i + 8 ≤ Variant.sha512.outputBytes → ∀ off len : Nat, off + len ≤ 71757 →
        RangeApart (resetSuffixPointer .sha512 t + BitVec.ofNat 64 i) 8
          (Extracted.textAddress + BitVec.ofNat 64 off) len) := by
    refine ⟨?_, ?_, ?_⟩
    · change t.RIP = (BitVec.ofNat 64 1091951)
      simpa only [resetLoadedEffect, Variant.pc, Variant.textOffset, Extracted.textAddress,
        Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using firstEffect.rip
    · intro i hi
      rw [pointer]
      exact ⟨(pre.writable i hi).toMemReadable.of_holds firstEffect, (pre.writable i hi).tables⟩
    · intro i hi off len bound
      rw [pointer]
      exact pre.codeApart i hi off len bound
  obtain ⟨m, u, run', readyU, loadedU, suffix⟩ := machine_sha512_resetSuffix boundary outside t readyT loadedT suffixPre
  exact ⟨n+m, u, run.trans run', readyU, loadedU, reset_effect_compose pre firstEffect suffix⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
theorem machine_sha512_224_resetPrefix [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre .sha512_224 s (.reset 1))
      (codeRange (Variant.sha512_224.pc (Variant.sha512_224.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha512_224 (.reset 1)))
      (Effect.post (fun s => resetPrefixEffect .sha512_224 s)) := by
  advance_begin (mov_r64_m64_effect_step 0x106ad8 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case pre => intro s hP; exact ⟨hP.rip, hP.readable 128 (by decide +kernel)⟩
  case «next» =>
    intro s hP
    exact boundary_ne_program outside (inProgram_of_textOffset 0x6ae0 (by decide))
  advance_then (mov_r64_m64_effect_step 0x106ae0 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 136)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 8 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 136 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6ae8 (by decide))
  advance_then (bswap_r64_effect_step 0x106ae8 0)
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 16 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6aeb (by decide))
  advance_then (bswap_r64_effect_step 0x106aeb 1)
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 19 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6aee (by decide))
  advance_then (mov_r64_m64_effect_step 0x106aee 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 144)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 22 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 144 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6af6 (by decide))
  advance_then (bswap_r64_effect_step 0x106af6 2)
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 30 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6af9 (by decide))
  advance_then (mov_r64_m64_effect_step 0x106af9 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 152)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 33 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 152 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b01 (by decide))
  advance_then (bswap_r64_effect_step 0x106b01 6)
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 41 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b04 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x106b04 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_224.initialHash[1]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 44 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b0e (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106b0e 0x49 (by simp [RexWPrefix]) 7 (.base 14 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 54 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 136 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 136 (by decide +kernel) 0x6b0e 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 136 (by decide +kernel) 0x6ad8 206 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b12 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x106b12 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_224.initialHash[3]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 58 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b1c (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106b1c 0x49 (by simp [RexWPrefix]) 7 (.base 14 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 68 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 152 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 152 (by decide +kernel) 0x6b1c 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 152 (by decide +kernel) 0x6ad8 206 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b20 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x106b20 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_224.initialHash[5]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 72 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b2a (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106b2a 0x49 (by simp [RexWPrefix]) 7 (.base 14 (.d8 40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 82 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 168 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 168 (by decide +kernel) 0x6b2a 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 168 (by decide +kernel) 0x6ad8 206 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b2e (by decide))
  advance_then (mov_r64_imm64_effect_step 0x106b2e 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_224.initialHash[7]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 86 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b38 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106b38 0x49 (by simp [RexWPrefix]) 7 (.base 14 (.d8 56)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 96 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 184 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 184 (by decide +kernel) 0x6b38 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 184 (by decide +kernel) 0x6ad8 206 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b3c (by decide))
  advance_then (mov_r64_imm64_effect_step 0x106b3c 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_224.initialHash[6]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 100 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b46 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106b46 0x49 (by simp [RexWPrefix]) 7 (.base 14 (.d8 48)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 110 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 176 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 176 (by decide +kernel) 0x6b46 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 176 (by decide +kernel) 0x6ad8 206 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b4a (by decide))
  advance_then (mov_r64_imm64_effect_step 0x106b4a 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_224.initialHash[4]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 114 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b54 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106b54 0x49 (by simp [RexWPrefix]) 7 (.base 14 (.d8 32)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 124 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 160 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 160 (by decide +kernel) 0x6b54 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 160 (by decide +kernel) 0x6ad8 206 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b58 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x106b58 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_224.initialHash[2]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 128 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b62 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106b62 0x49 (by simp [RexWPrefix]) 7 (.base 14 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 138 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 144 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 144 (by decide +kernel) 0x6b62 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 144 (by decide +kernel) 0x6ad8 206 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b66 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x106b66 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_224.initialHash[0]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 142 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b70 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106b70 0x49 (by simp [RexWPrefix]) 7 (.base 14 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 152 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 128 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 128 (by decide +kernel) 0x6b70 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 128 (by decide +kernel) 0x6ad8 206 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b73 (by decide))
  apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t hP hH
  have pointer := hP.resetHashPointer rfl
  simp only [BitVec.ofNat_eq_ofNat] at pointer
  apply hH.weaken
  · x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
  · x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
theorem machine_sha512_224_reset1 [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre .sha512_224 s (.reset 1))
      (codeRange (Variant.sha512_224.pc (Variant.sha512_224.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha512_224 (.reset 1)))
      (Effect.post (fun s => effect .sha512_224 s (.reset 1))) := by
  suffices continuation :
      AdvanceTriple boundary (fun s => Pre .sha512_224 s (.reset 1))
        (codeRange (Variant.sha512_224.pc (Variant.sha512_224.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha512_224 (.reset 1)))
        (Effect.post (fun s => resetPrefixEffect .sha512_224 s)) →
      AdvanceTriple boundary (fun s => Pre .sha512_224 s (.reset 1))
        (codeRange (Variant.sha512_224.pc (Variant.sha512_224.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha512_224 (.reset 1)))
        (Effect.post (fun s => effect .sha512_224 s (.reset 1))) from
    continuation (machine_sha512_224_resetPrefix boundary outside)
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x106b73 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl 0)
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 155 12
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 200 (by decide +kernel)
    · x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 200 (by decide +kernel) 0x6b73 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 200 (by decide +kernel) 0x6ad8 206 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b7f (by decide))
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x106b7f 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl 0)
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 167 12
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 192 (by decide +kernel)
    · x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 192 (by decide +kernel) 0x6b7f 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 192 (by decide +kernel) 0x6ad8 206 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b8b (by decide))
  advance_then (mov_m8_imm8_effect_step 0x106b8b (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl 0)
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 179 5
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact (hP.resetTailWritable rfl).toMemWritable
    · x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetTailCodeApart rfl 0x6b8b 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetTailCodeApart rfl 0x6ad8 206 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b90 (by decide))
  advance_then (mov_r64_m64_effect_step 0x106b90 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 232)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 184 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 232 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b98 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106b98 0x48 (by simp [RexWPrefix]) 0 (.base 7 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 192 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.writable 0 (by decide)
    · x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.codeApart 0 (by decide) 0x6b98 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.codeApart 0 (by decide) 0x6ad8 206 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b9b (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106b9b 0x48 (by simp [RexWPrefix]) 1 (.base 7 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 195 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.writable 8 (by decide)
    · x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.codeApart 8 (by decide) 0x6b9b 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.codeApart 8 (by decide) 0x6ad8 206 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6b9f (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106b9f 0x48 (by simp [RexWPrefix]) 2 (.base 7 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 199 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.writable 16 (by decide)
    · x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.codeApart 16 (by decide) 0x6b9f 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.codeApart 16 (by decide) 0x6ad8 206 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6ba3 (by decide))
  advance_then (CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x106ba3 6 (.base 7 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x106ad8 (bytes .sha512_224 (.reset 1)) 203 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.writablePartial rfl
    · x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.codeApartPartial rfl 0x6ba3 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [outputAddress, Form.frameBytes, show Form.outputSlot (.reset 1) = 192 from rfl, Nat.reduceSub, reduceIte, rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.codeApartPartial rfl 0x6ad8 206 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6ba6 (by decide))
  apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t hP hH
  have pointer := hP.resetHashPointer rfl
  simp only [BitVec.ofNat_eq_ofNat] at pointer
  have reads := reset_memory_read_after_output hP
  have baseReads := reset_memory_read_after_output_base hP
  x86_norm at reads baseReads
  apply hH.weaken
  · x86_norm [effect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reads, baseReads]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [effect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reads, baseReads]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [effect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reads, baseReads]
  · x86_norm [effect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reads, baseReads]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
theorem machine_sha512_256_resetPrefix [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre .sha512_256 s (.reset 1))
      (codeRange (Variant.sha512_256.pc (Variant.sha512_256.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha512_256 (.reset 1)))
      (Effect.post (fun s => resetPrefixEffect .sha512_256 s)) := by
  advance_begin (mov_r64_m64_effect_step 0x108938 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case pre => intro s hP; exact ⟨hP.rip, hP.readable 128 (by decide +kernel)⟩
  case «next» =>
    intro s hP
    exact boundary_ne_program outside (inProgram_of_textOffset 0x8940 (by decide))
  advance_then (mov_r64_m64_effect_step 0x108940 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 136)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 8 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 136 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x8948 (by decide))
  advance_then (bswap_r64_effect_step 0x108948 0)
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 16 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x894b (by decide))
  advance_then (bswap_r64_effect_step 0x10894b 1)
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 19 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x894e (by decide))
  advance_then (mov_r64_m64_effect_step 0x10894e 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 144)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 22 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 144 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x8956 (by decide))
  advance_then (bswap_r64_effect_step 0x108956 2)
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 30 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x8959 (by decide))
  advance_then (mov_r64_m64_effect_step 0x108959 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 152)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 33 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 152 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x8961 (by decide))
  advance_then (bswap_r64_effect_step 0x108961 6)
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 41 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x8964 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x108964 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_256.initialHash[1]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 44 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x896e (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10896e 0x49 (by simp [RexWPrefix]) 7 (.base 14 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 54 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 136 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 136 (by decide +kernel) 0x896e 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 136 (by decide +kernel) 0x8938 207 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x8972 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x108972 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_256.initialHash[3]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 58 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x897c (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10897c 0x49 (by simp [RexWPrefix]) 7 (.base 14 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 68 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 152 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 152 (by decide +kernel) 0x897c 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 152 (by decide +kernel) 0x8938 207 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x8980 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x108980 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_256.initialHash[5]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 72 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x898a (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10898a 0x49 (by simp [RexWPrefix]) 7 (.base 14 (.d8 40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 82 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 168 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 168 (by decide +kernel) 0x898a 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 168 (by decide +kernel) 0x8938 207 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x898e (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10898e 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_256.initialHash[7]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 86 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x8998 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x108998 0x49 (by simp [RexWPrefix]) 7 (.base 14 (.d8 56)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 96 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 184 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 184 (by decide +kernel) 0x8998 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 184 (by decide +kernel) 0x8938 207 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x899c (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10899c 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_256.initialHash[6]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 100 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x89a6 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1089a6 0x49 (by simp [RexWPrefix]) 7 (.base 14 (.d8 48)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 110 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 176 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 176 (by decide +kernel) 0x89a6 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 176 (by decide +kernel) 0x8938 207 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x89aa (by decide))
  advance_then (mov_r64_imm64_effect_step 0x1089aa 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_256.initialHash[4]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 114 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x89b4 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1089b4 0x49 (by simp [RexWPrefix]) 7 (.base 14 (.d8 32)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 124 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 160 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 160 (by decide +kernel) 0x89b4 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 160 (by decide +kernel) 0x8938 207 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x89b8 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x1089b8 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_256.initialHash[2]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 128 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x89c2 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1089c2 0x49 (by simp [RexWPrefix]) 7 (.base 14 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 138 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 144 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 144 (by decide +kernel) 0x89c2 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 144 (by decide +kernel) 0x8938 207 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x89c6 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x1089c6 0x48 0xbf (by simp [RexWPrefix]) (by decide) (Variant.sha512_256.initialHash[0]!.toBitVec))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 142 10
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨hH.rip_of (by x86_norm [pointer]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64Imm64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x89d0 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1089d0 0x49 (by simp [RexWPrefix]) 7 (.base 14 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 152 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 128 (by decide +kernel)
    · x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 128 (by decide +kernel) 0x89d0 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer, BitVec.add_assoc]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 128 (by decide +kernel) 0x8938 207 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x89d3 (by decide))
  apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t hP hH
  have pointer := hP.resetHashPointer rfl
  simp only [BitVec.ofNat_eq_ofNat] at pointer
  apply hH.weaken
  · x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]
  · x86_norm [resetPrefixEffect, List.take, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reset_memory_read_after_output hP, reset_memory_read_after_output_base hP]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
theorem machine_sha512_256_reset1 [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre .sha512_256 s (.reset 1))
      (codeRange (Variant.sha512_256.pc (Variant.sha512_256.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha512_256 (.reset 1)))
      (Effect.post (fun s => effect .sha512_256 s (.reset 1))) := by
  suffices continuation :
      AdvanceTriple boundary (fun s => Pre .sha512_256 s (.reset 1))
        (codeRange (Variant.sha512_256.pc (Variant.sha512_256.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha512_256 (.reset 1)))
        (Effect.post (fun s => resetPrefixEffect .sha512_256 s)) →
      AdvanceTriple boundary (fun s => Pre .sha512_256 s (.reset 1))
        (codeRange (Variant.sha512_256.pc (Variant.sha512_256.serializeOffset (.reset 1)) (.reset 1)) (bytes .sha512_256 (.reset 1)))
        (Effect.post (fun s => effect .sha512_256 s (.reset 1))) from
    continuation (machine_sha512_256_resetPrefix boundary outside)
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x1089d3 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl 0)
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 155 12
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 200 (by decide +kernel)
    · x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 200 (by decide +kernel) 0x89d3 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 200 (by decide +kernel) 0x8938 207 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x89df (by decide))
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x1089df 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl 0)
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 167 12
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetWritable rfl 192 (by decide +kernel)
    · x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 192 (by decide +kernel) 0x89df 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetCodeApart rfl 192 (by decide +kernel) 0x8938 207 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x89eb (by decide))
  advance_then (mov_m8_imm8_effect_step 0x1089eb (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl 0)
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 179 5
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact (hP.resetTailWritable rfl).toMemWritable
    · x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetTailCodeApart rfl 0x89eb 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Extracted.textAddress] using hP.resetTailCodeApart rfl 0x8938 207 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x89f0 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1089f0 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 232)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 184 8
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [pointer]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [pointer]
      exact hP.readable 232 (by decide +kernel)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x89f8 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1089f8 0x48 (by simp [RexWPrefix]) 0 (.base 7 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 192 3
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa [outputAddress, Form.frameBytes, Form.outputSlot, rspOf, Operand.read, Extracted.textAddress] using hP.writable 0 (by decide)
    · x86_norm [pointer]
      simpa [outputAddress, Form.frameBytes, Form.outputSlot, rspOf, Operand.read, Extracted.textAddress] using hP.codeApart 0 (by decide) 0x89f8 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa [outputAddress, Form.frameBytes, Form.outputSlot, rspOf, Operand.read, Extracted.textAddress] using hP.codeApart 0 (by decide) 0x8938 207 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x89fb (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1089fb 0x48 (by simp [RexWPrefix]) 1 (.base 7 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 195 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa [outputAddress, Form.frameBytes, Form.outputSlot, rspOf, Operand.read, Extracted.textAddress] using hP.writable 8 (by decide)
    · x86_norm [pointer]
      simpa [outputAddress, Form.frameBytes, Form.outputSlot, rspOf, Operand.read, Extracted.textAddress] using hP.codeApart 8 (by decide) 0x89fb 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa [outputAddress, Form.frameBytes, Form.outputSlot, rspOf, Operand.read, Extracted.textAddress] using hP.codeApart 8 (by decide) 0x8938 207 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x89ff (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1089ff 0x48 (by simp [RexWPrefix]) 2 (.base 7 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 199 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa [outputAddress, Form.frameBytes, Form.outputSlot, rspOf, Operand.read, Extracted.textAddress] using hP.writable 16 (by decide)
    · x86_norm [pointer]
      simpa [outputAddress, Form.frameBytes, Form.outputSlot, rspOf, Operand.read, Extracted.textAddress] using hP.codeApart 16 (by decide) 0x89ff 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa [outputAddress, Form.frameBytes, Form.outputSlot, rspOf, Operand.read, Extracted.textAddress] using hP.codeApart 16 (by decide) 0x8938 207 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x8a03 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x108a03 0x48 (by simp [RexWPrefix]) 6 (.base 7 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  case sub =>
    have subset := codeRange_slice_subset 0x108938 (bytes .sha512_256 (.reset 1)) 203 4
    apply List.Subset.trans (l₂ := _) ?_ subset
    decide +kernel
  case mid =>
    intro s t hP hH hO
    have pointer := hP.resetHashPointer rfl
    simp only [BitVec.ofNat_eq_ofNat] at pointer
    refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [pointer]) ?_ ?_, ?_, ?_⟩
    · x86_norm [pointer]
      simpa [outputAddress, Form.frameBytes, Form.outputSlot, rspOf, Operand.read, Extracted.textAddress] using hP.writable 24 (by decide)
    · x86_norm [pointer]
      simpa [outputAddress, Form.frameBytes, Form.outputSlot, rspOf, Operand.read, Extracted.textAddress] using hP.codeApart 24 (by decide) 0x8a03 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [pointer]
      simpa [outputAddress, Form.frameBytes, Form.outputSlot, rspOf, Operand.read, Extracted.textAddress] using hP.codeApart 24 (by decide) 0x8938 207 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x8a07 (by decide))
  apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t hP hH
  have pointer := hP.resetHashPointer rfl
  simp only [BitVec.ofNat_eq_ofNat] at pointer
  have reads := reset_memory_read_after_output hP
  have baseReads := reset_memory_read_after_output_base hP
  x86_norm at reads baseReads
  apply hH.weaken
  · x86_norm [effect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reads, baseReads]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [effect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reads, baseReads]
    all_goals solve_by_elim (maxDepth := 6) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [effect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reads, baseReads]
  · x86_norm [effect, resetWrites, outputAddress, pointerRegister, hashOffset, pointer, reads, baseReads]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem machine_sha384 [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (form : Form := .slices) :
    AdvanceTriple boundary (fun s => Pre .sha384 s form) (codeRange (Variant.sha384.pc (Variant.sha384.serializeOffset form) form) (bytes .sha384 form))
      (Effect.post (fun s => effect .sha384 s form)) := by
  let f := form
  cases form
  all_goals try (
    rename_i second
    have _ : Bool := second
    cases second)
  all_goals try (
    rename_i stage
    have _ : Fin 3 := stage
    have choices : stage = (0 : Fin 3) ∨ stage = 1 ∨ stage = 2 := by
      rcases stage with ⟨n, bound⟩
      rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    rcases choices with (rfl | rfl | rfl))
  case reset.inl =>
    intro s _ _ hP
    exact False.elim (hP.finalizes rfl)
  case reset.inr.inl =>
    exact machine_sha384_reset1 boundary outside
  case finalizeIntoReset.false =>
    let f : Form := .finalizeIntoReset false
    advance_begin (mov_r64_m64_effect_step 0x1042c8 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 144)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case pre =>
      intro s h
      exact ⟨h.rip, h.readable 144 (by decide +kernel)⟩
    case «next» =>
      intro s h
      exact boundary_ne_program outside (inProgram_of_textOffset 0x42d0 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1042d0 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 152)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 8 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 152 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x42d8 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x1042d8 0)
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 16 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x42db (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1042db 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 160)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 19 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 160 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x42e3 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1042e3 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 168)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 27 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 168 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x42eb (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1042eb 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 176)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 35 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 176 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x42f3 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1042f3 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 184)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 43 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 184 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x42fb (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1042fb 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 224)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 51 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 224 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x4303 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104303 0x49 (by simp [RexWPrefix]) 0 (.base 9 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 59 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 0 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0x4303 3 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0x42c8 97 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x4306 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x104306 1)
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 62 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x4309 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104309 0x49 (by simp [RexWPrefix]) 1 (.base 9 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 65 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 8 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0x4309 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0x42c8 97 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x430d (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x10430d 2)
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 69 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x4310 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x104310 6)
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 72 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x4313 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104313 0x49 (by simp [RexWPrefix]) 2 (.base 9 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 75 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 16 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0x4313 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0x42c8 97 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x4317 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104317 0x49 (by simp [RexWPrefix]) 6 (.base 9 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 79 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 24 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 24 (by decide +kernel) 0x4317 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 24 (by decide +kernel) 0x42c8 97 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x431b (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x10431b 7)
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 83 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x431e (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10431e 0x49 (by simp [RexWPrefix]) 7 (.base 9 (.d8 32)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 86 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 32 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 32 (by decide +kernel) 0x431e 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 32 (by decide +kernel) 0x42c8 97 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x4322 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x104322 8)
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 90 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x4325 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x104325 0x4d (by simp [RexWPrefix]) 0 (.base 9 (.d8 40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1042c8 (bytes .sha384 f) 93 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 40 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 40 (by decide +kernel) 0x4325 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 40 (by decide +kernel) 0x42c8 97 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x4329 (by decide +kernel))
    advance_finish [effect, outputAddress, resetWrites]
  case traitFinalizeIntoReset.false =>
    let f : Form := .traitFinalizeIntoReset false
    advance_begin (mov_r64_m64_effect_step 0x1053a0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 384)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case pre =>
      intro s h
      exact ⟨h.rip, h.readable 384 (by decide +kernel)⟩
    case «next» =>
      intro s h
      exact boundary_ne_program outside (inProgram_of_textOffset 0x53a8 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1053a8 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 392)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 8 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 392 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53b0 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x1053b0 0)
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 16 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53b3 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1053b3 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 400)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 19 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 400 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53bb (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1053bb 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 408)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 27 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 408 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53c3 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1053c3 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 416)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 35 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 416 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53cb (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1053cb 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 424)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 43 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 424 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53d3 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1053d3 0x48 (by simp [RexWPrefix]) 0 (.base 5 (.d8 0)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 51 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 0 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0x53d3 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0x53a0 90 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53d7 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x1053d7 1)
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 55 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53da (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1053da 0x48 (by simp [RexWPrefix]) 1 (.base 5 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 58 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 8 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0x53da 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0x53a0 90 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53de (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x1053de 2)
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 62 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53e1 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x1053e1 6)
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 65 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53e4 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1053e4 0x48 (by simp [RexWPrefix]) 2 (.base 5 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 68 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 16 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0x53e4 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0x53a0 90 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53e8 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1053e8 0x48 (by simp [RexWPrefix]) 6 (.base 5 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 72 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 24 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 24 (by decide +kernel) 0x53e8 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 24 (by decide +kernel) 0x53a0 90 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53ec (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x1053ec 7)
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 76 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53ef (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1053ef 0x48 (by simp [RexWPrefix]) 7 (.base 5 (.d8 32)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 79 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 32 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 32 (by decide +kernel) 0x53ef 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 32 (by decide +kernel) 0x53a0 90 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53f3 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x1053f3 8)
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 83 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53f6 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1053f6 0x4c (by simp [RexWPrefix]) 0 (.base 5 (.d8 40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1053a0 (bytes .sha384 f) 86 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 40 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 40 (by decide +kernel) 0x53f6 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 40 (by decide +kernel) 0x53a0 90 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x53fa (by decide +kernel))
    apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
    intro s t _ hH
    have saved := hH.agrees.read (n := 64) (r := 9) (by x86_norm)
    have writes := hH.writes
    refine ⟨?_, ?_, ?_, ?_⟩
    · change t.RIP = 0x1053fa
      exact hH.rip
    · simp only [effect, resetWrites, Write.AllHold, outputAddress, reduceCtorEq, reduceIte, List.append_nil, pointerRegister] at writes ⊢
      rcases writes with ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11⟩
      exact ⟨w0, w2, w4, w5, w8, w10, saved, w1, w3, w6, w7, w9, w11⟩
    · trivial
    · apply hH.agrees.mono
      x86_norm [effect, outputAddress, resetWrites]

  all_goals (
    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 0)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_begin instruction
    case pre => intro s h; exact ⟨h.rip, h.readable (BitVec.ofNat _ (hashOffset f + 0)) (by decide +kernel)⟩
    case «next» =>
      intro s h
      have boundaryAfter := boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f06 else if f = .digest then 0x3b17 else if f = .reset 2 then 0x4f55 else if f = .finalizeIntoReset true then 0x4678 else 0x5760) (by decide +kernel))
      intro bad
      apply boundaryAfter
      rw [← bad]
      x86_norm [f]

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x103f06 else if f = .digest then 0x103b17 else if f = .reset 2 then 0x104f55 else if f = .finalizeIntoReset true then 0x104678 else 0x105760) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) 8 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 8)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f0e else if f = .digest then 0x3b1f else if f = .reset 2 then 0x4f5d else if f = .finalizeIntoReset true then 0x4680 else 0x5768) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x103f0e else if f = .digest then 0x103b1f else if f = .reset 2 then 0x104f5d else if f = .finalizeIntoReset true then 0x104680 else 0x105768) 0)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) 16 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f11 else if f = .digest then 0x3b22 else if f = .reset 2 then 0x4f60 else if f = .finalizeIntoReset true then 0x4683 else 0x576b) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x103f11 else if f = .digest then 0x103b22 else if f = .reset 2 then 0x104f60 else if f = .finalizeIntoReset true then 0x104683 else 0x10576b) 1)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) 19 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f14 else if f = .digest then 0x3b25 else if f = .reset 2 then 0x4f63 else if f = .finalizeIntoReset true then 0x4686 else 0x576e) (by decide +kernel))

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x103f14 else if f = .digest then 0x103b25 else if f = .reset 2 then 0x104f63 else if f = .finalizeIntoReset true then 0x104686 else 0x10576e) 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 16)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) 22 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 16)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f1c else if f = .digest then 0x3b2d else if f = .reset 2 then 0x4f6b else if f = .finalizeIntoReset true then 0x468e else 0x5776) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x103f1c else if f = .digest then 0x103b2d else if f = .reset 2 then 0x104f6b else if f = .finalizeIntoReset true then 0x10468e else 0x105776) 2)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) 30 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f1f else if f = .digest then 0x3b30 else if f = .reset 2 then 0x4f6e else if f = .finalizeIntoReset true then 0x4691 else 0x5779) (by decide +kernel))

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x103f1f else if f = .digest then 0x103b30 else if f = .reset 2 then 0x104f6e else if f = .finalizeIntoReset true then 0x104691 else 0x105779) 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 24)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) 33 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 24)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f27 else if f = .digest then 0x3b38 else if f = .reset 2 then 0x4f76 else if f = .finalizeIntoReset true then 0x4699 else 0x5781) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x103f27 else if f = .digest then 0x103b38 else if f = .reset 2 then 0x104f76 else if f = .finalizeIntoReset true then 0x104699 else 0x105781) 6)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) 41 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f2a else if f = .digest then 0x3b3b else if f = .reset 2 then 0x4f79 else if f = .finalizeIntoReset true then 0x469c else 0x5784) (by decide +kernel))

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x103f2a else if f = .digest then 0x103b3b else if f = .reset 2 then 0x104f79 else if f = .finalizeIntoReset true then 0x10469c else 0x105784) 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 32)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) 44 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 32)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f32 else if f = .digest then 0x3b43 else if f = .reset 2 then 0x4f81 else if f = .finalizeIntoReset true then 0x46a4 else 0x578c) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x103f32 else if f = .digest then 0x103b43 else if f = .reset 2 then 0x104f81 else if f = .finalizeIntoReset true then 0x1046a4 else 0x10578c) 7)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) 52 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f35 else if f = .digest then 0x3b46 else if f = .reset 2 then 0x4f84 else if f = .finalizeIntoReset true then 0x46a7 else 0x578f) (by decide +kernel))

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x103f35 else if f = .digest then 0x103b46 else if f = .reset 2 then 0x104f84 else if f = .finalizeIntoReset true then 0x1046a7 else 0x10578f) 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 40)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) 55 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 40)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f3d else if f = .digest then 0x3b4e else if f = .reset 2 then 0x4f8c else if f = .finalizeIntoReset true then 0x46af else 0x5797) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x103f3d else if f = .digest then 0x103b4e else if f = .reset 2 then 0x104f8c else if f = .finalizeIntoReset true then 0x1046af else 0x105797) 8)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) 63 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f40 else if f = .digest then 0x3b51 else if f = .reset 2 then 0x4f8f else if f = .finalizeIntoReset true then 0x46b2 else 0x579a) (by decide +kernel))

    try (
    have hs : f ≠ .digest := by decide
    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x103f40 else if f = .digest then 0x103b51 else if f = .reset 2 then 0x104f8f else if f = .finalizeIntoReset true then 0x1046b2 else 0x10579a) 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (if f = .slices then .d8 8 else .d32 (BitVec.ofNat 32 (f.frameBytes - f.outputSlot)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) 66 (if f = .slices then 5 else 8)
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat 64 (f.frameBytes - f.outputSlot)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f45 else if f = .digest then 0x3b51 else if f = .reset 2 then 0x4f97 else if f = .finalizeIntoReset true then 0x46ba else 0x57a2) (by decide +kernel)))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x103f45 else if f = .digest then 0x103b51 else if f = .reset 2 then 0x104f97 else if f = .finalizeIntoReset true then 0x1046ba else 0x1057a2) (if f = .digest then 0x48 else 0x49) (by simp [f, RexWPrefix]) 0 (.base (if f = .digest then 3 else 9) .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) (71 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 0 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 0 (by decide +kernel) (if f = .slices then 0x3f45 else if f = .digest then 0x3b51 else if f = .reset 2 then 0x4f97 else if f = .finalizeIntoReset true then 0x46ba else 0x57a2) 3 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 0 (by decide +kernel) (if f = .slices then 0x3efe else if f = .digest then 0x3b0f else if f = .reset 2 then 0x4f4d else if f = .finalizeIntoReset true then 0x4670 else 0x5758) (94 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f48 else if f = .digest then 0x3b54 else if f = .reset 2 then 0x4f9a else if f = .finalizeIntoReset true then 0x46bd else 0x57a5) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x103f48 else if f = .digest then 0x103b54 else if f = .reset 2 then 0x104f9a else if f = .finalizeIntoReset true then 0x1046bd else 0x1057a5) (if f = .digest then 0x48 else 0x49) (by simp [f, RexWPrefix]) 1 (.base (if f = .digest then 3 else 9) (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) (74 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 8 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 8 (by decide +kernel) (if f = .slices then 0x3f48 else if f = .digest then 0x3b54 else if f = .reset 2 then 0x4f9a else if f = .finalizeIntoReset true then 0x46bd else 0x57a5) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 8 (by decide +kernel) (if f = .slices then 0x3efe else if f = .digest then 0x3b0f else if f = .reset 2 then 0x4f4d else if f = .finalizeIntoReset true then 0x4670 else 0x5758) (94 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f4c else if f = .digest then 0x3b58 else if f = .reset 2 then 0x4f9e else if f = .finalizeIntoReset true then 0x46c1 else 0x57a9) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x103f4c else if f = .digest then 0x103b58 else if f = .reset 2 then 0x104f9e else if f = .finalizeIntoReset true then 0x1046c1 else 0x1057a9) (if f = .digest then 0x48 else 0x49) (by simp [f, RexWPrefix]) 2 (.base (if f = .digest then 3 else 9) (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) (78 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 16 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 16 (by decide +kernel) (if f = .slices then 0x3f4c else if f = .digest then 0x3b58 else if f = .reset 2 then 0x4f9e else if f = .finalizeIntoReset true then 0x46c1 else 0x57a9) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 16 (by decide +kernel) (if f = .slices then 0x3efe else if f = .digest then 0x3b0f else if f = .reset 2 then 0x4f4d else if f = .finalizeIntoReset true then 0x4670 else 0x5758) (94 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f50 else if f = .digest then 0x3b5c else if f = .reset 2 then 0x4fa2 else if f = .finalizeIntoReset true then 0x46c5 else 0x57ad) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x103f50 else if f = .digest then 0x103b5c else if f = .reset 2 then 0x104fa2 else if f = .finalizeIntoReset true then 0x1046c5 else 0x1057ad) (if f = .digest then 0x48 else 0x49) (by simp [f, RexWPrefix]) 6 (.base (if f = .digest then 3 else 9) (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) (82 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 24 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 24 (by decide +kernel) (if f = .slices then 0x3f50 else if f = .digest then 0x3b5c else if f = .reset 2 then 0x4fa2 else if f = .finalizeIntoReset true then 0x46c5 else 0x57ad) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 24 (by decide +kernel) (if f = .slices then 0x3efe else if f = .digest then 0x3b0f else if f = .reset 2 then 0x4f4d else if f = .finalizeIntoReset true then 0x4670 else 0x5758) (94 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f54 else if f = .digest then 0x3b60 else if f = .reset 2 then 0x4fa6 else if f = .finalizeIntoReset true then 0x46c9 else 0x57b1) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x103f54 else if f = .digest then 0x103b60 else if f = .reset 2 then 0x104fa6 else if f = .finalizeIntoReset true then 0x1046c9 else 0x1057b1) (if f = .digest then 0x48 else 0x49) (by simp [f, RexWPrefix]) 7 (.base (if f = .digest then 3 else 9) (.d8 32)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) (86 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 32 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 32 (by decide +kernel) (if f = .slices then 0x3f54 else if f = .digest then 0x3b60 else if f = .reset 2 then 0x4fa6 else if f = .finalizeIntoReset true then 0x46c9 else 0x57b1) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 32 (by decide +kernel) (if f = .slices then 0x3efe else if f = .digest then 0x3b0f else if f = .reset 2 then 0x4f4d else if f = .finalizeIntoReset true then 0x4670 else 0x5758) (94 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f58 else if f = .digest then 0x3b64 else if f = .reset 2 then 0x4faa else if f = .finalizeIntoReset true then 0x46cd else 0x57b5) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x103f58 else if f = .digest then 0x103b64 else if f = .reset 2 then 0x104faa else if f = .finalizeIntoReset true then 0x1046cd else 0x1057b5) (if f = .digest then 0x4c else 0x4d) (by simp [f, RexWPrefix]) 0 (.base (if f = .digest then 3 else 9) (.d8 40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x103efe else if f = .digest then 0x103b0f else if f = .reset 2 then 0x104f4d else if f = .finalizeIntoReset true then 0x104670 else 0x105758) (bytes .sha384 f) (90 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 40 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 40 (by decide +kernel) (if f = .slices then 0x3f58 else if f = .digest then 0x3b64 else if f = .reset 2 then 0x4faa else if f = .finalizeIntoReset true then 0x46cd else 0x57b5) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 40 (by decide +kernel) (if f = .slices then 0x3efe else if f = .digest then 0x3b0f else if f = .reset 2 then 0x4f4d else if f = .finalizeIntoReset true then 0x4670 else 0x5758) (94 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x3f5c else if f = .digest then 0x3b68 else if f = .reset 2 then 0x4fae else if f = .finalizeIntoReset true then 0x46d1 else 0x57b9) (by decide +kernel))

    try simp only [f] at *
    first
    | have nondigest : f ≠ .digest := by decide
      advance_finish [effect, outputAddress, resetWrites]
    | apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
      intro s t _ hH
      have saved := hH.agrees.read (n := 64) (r := 9) (by x86_norm)
      have writes := hH.writes
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [effect, Variant.pc, Variant.outputEndOffset, Variant.epilogueOffset, Variant.textOffset,
          Extracted.textAddress, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hH.rip
      · simp only [effect, resetWrites, Write.AllHold, outputAddress, reduceCtorEq, reduceIte, List.append_nil, pointerRegister] at writes ⊢
        rcases writes with ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11⟩
        all_goals first | assumption | exact ⟨w0, w1, w2, w3, w4, w5, saved, w6, w7, w8, w9, w10, w11⟩
      · trivial
      · apply hH.agrees.mono
        x86_norm [effect, outputAddress, resetWrites])

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem machine_sha512 [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (form : Form := .slices) :
    AdvanceTriple boundary (fun s => Pre .sha512 s form) (codeRange (Variant.sha512.pc (Variant.sha512.serializeOffset form) form) (bytes .sha512 form))
      (Effect.post (fun s => effect .sha512 s form)) := by
  let f := form
  cases form
  all_goals try (
    rename_i second
    have _ : Bool := second
    cases second)
  all_goals try (
    rename_i stage
    have _ : Fin 3 := stage
    have choices : stage = (0 : Fin 3) ∨ stage = 1 ∨ stage = 2 := by
      rcases stage with ⟨n, bound⟩
      rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    rcases choices with (rfl | rfl | rfl))
  case reset.inl =>
    intro s _ _ hP
    exact False.elim (hP.finalizes rfl)
  case reset.inr.inl =>
    exact machine_sha512_reset1 boundary outside
  case finalizeIntoReset.false =>
    let f : Form := .finalizeIntoReset false
    advance_begin (mov_r64_m64_effect_step 0x109f18 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 144)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case pre =>
      intro s h
      exact ⟨h.rip, h.readable 144 (by decide +kernel)⟩
    case «next» =>
      intro s h
      exact boundary_ne_program outside (inProgram_of_textOffset 0x9f20 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x109f20 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 152)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 8 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 152 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f28 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x109f28 0)
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 16 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f2b (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x109f2b 1)
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 19 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f2e (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x109f2e 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 160)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 22 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 160 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f36 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x109f36 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 168)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 30 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 168 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f3e (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x109f3e 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 176)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 38 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 176 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f46 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x109f46 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 184)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 46 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 184 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f4e (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x109f4e 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 192)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 54 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 192 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f56 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x109f56 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 200)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 62 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 200 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f5e (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x109f5e 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 224)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 70 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 224 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f66 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x109f66 0x49 (by simp [RexWPrefix]) 0 (.base 11 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 78 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 0 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0x9f66 3 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0x9f18 127 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f69 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x109f69 0x49 (by simp [RexWPrefix]) 1 (.base 11 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 81 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 8 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0x9f69 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0x9f18 127 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f6d (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x109f6d 2)
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 85 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f70 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x109f70 0x49 (by simp [RexWPrefix]) 2 (.base 11 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 88 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 16 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0x9f70 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0x9f18 127 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f74 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x109f74 6)
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 92 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f77 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x109f77 0x49 (by simp [RexWPrefix]) 6 (.base 11 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 95 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 24 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 24 (by decide +kernel) 0x9f77 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 24 (by decide +kernel) 0x9f18 127 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f7b (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x109f7b 7)
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 99 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f7e (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x109f7e 8)
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 102 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f81 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x109f81 0x49 (by simp [RexWPrefix]) 7 (.base 11 (.d8 32)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 105 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 32 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 32 (by decide +kernel) 0x9f81 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 32 (by decide +kernel) 0x9f18 127 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f85 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x109f85 0x4d (by simp [RexWPrefix]) 0 (.base 11 (.d8 40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 109 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 40 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 40 (by decide +kernel) 0x9f85 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 40 (by decide +kernel) 0x9f18 127 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f89 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x109f89 9)
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 113 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f8c (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x109f8c 0x4d (by simp [RexWPrefix]) 1 (.base 11 (.d8 48)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 116 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 48 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 48 (by decide +kernel) 0x9f8c 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 48 (by decide +kernel) 0x9f18 127 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f90 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x109f90 10)
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 120 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f93 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x109f93 0x4d (by simp [RexWPrefix]) 2 (.base 11 (.d8 56)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x109f18 (bytes .sha512 f) 123 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 56 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 56 (by decide +kernel) 0x9f93 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 56 (by decide +kernel) 0x9f18 127 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f97 (by decide +kernel))
    advance_finish [effect, outputAddress, resetWrites]
  case traitFinalizeIntoReset.false =>
    let f : Form := .traitFinalizeIntoReset false
    advance_begin (mov_r64_m64_effect_step 0x10b070 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 384)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case pre =>
      intro s h
      exact ⟨h.rip, h.readable 384 (by decide +kernel)⟩
    case «next» =>
      intro s h
      exact boundary_ne_program outside (inProgram_of_textOffset 0xb078 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x10b078 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 392)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 8 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 392 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb080 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x10b080 0)
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 16 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb083 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x10b083 1)
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 19 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb086 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x10b086 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 400)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 22 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 400 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb08e (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x10b08e 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 408)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 30 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 408 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb096 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x10b096 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 416)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 38 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 416 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb09e (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x10b09e 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 424)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 46 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 424 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0a6 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x10b0a6 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 432)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 54 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 432 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0ae (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x10b0ae 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 440)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 62 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 440 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0b6 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10b0b6 0x49 (by simp [RexWPrefix]) 0 (.base 13 (.d8 0)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 70 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 0 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0xb0b6 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0xb070 120 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0ba (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10b0ba 0x49 (by simp [RexWPrefix]) 1 (.base 13 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 74 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 8 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0xb0ba 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0xb070 120 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0be (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x10b0be 2)
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 78 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0c1 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10b0c1 0x49 (by simp [RexWPrefix]) 2 (.base 13 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 81 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 16 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0xb0c1 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0xb070 120 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0c5 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x10b0c5 6)
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 85 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0c8 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10b0c8 0x49 (by simp [RexWPrefix]) 6 (.base 13 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 88 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 24 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 24 (by decide +kernel) 0xb0c8 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 24 (by decide +kernel) 0xb070 120 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0cc (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x10b0cc 7)
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 92 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0cf (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x10b0cf 8)
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 95 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0d2 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10b0d2 0x49 (by simp [RexWPrefix]) 7 (.base 13 (.d8 32)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 98 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 32 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 32 (by decide +kernel) 0xb0d2 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 32 (by decide +kernel) 0xb070 120 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0d6 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10b0d6 0x4d (by simp [RexWPrefix]) 0 (.base 13 (.d8 40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 102 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 40 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 40 (by decide +kernel) 0xb0d6 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 40 (by decide +kernel) 0xb070 120 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0da (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x10b0da 9)
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 106 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0dd (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10b0dd 0x4d (by simp [RexWPrefix]) 1 (.base 13 (.d8 48)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 109 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 48 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 48 (by decide +kernel) 0xb0dd 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 48 (by decide +kernel) 0xb070 120 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0e1 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x10b0e1 10)
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 113 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0e4 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10b0e4 0x4d (by simp [RexWPrefix]) 2 (.base 13 (.d8 56)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x10b070 (bytes .sha512 f) 116 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 56 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 56 (by decide +kernel) 0xb0e4 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 56 (by decide +kernel) 0xb070 120 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0xb0e8 (by decide +kernel))
    apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
    intro s t _ hH
    have saved := hH.agrees.read (n := 64) (r := 11) (by x86_norm)
    have writes := hH.writes
    refine ⟨?_, ?_, ?_, ?_⟩
    · change t.RIP = 0x10b0e8
      exact hH.rip
    · simp only [effect, resetWrites, Write.AllHold, outputAddress, reduceCtorEq, reduceIte, List.append_nil, pointerRegister] at writes ⊢
      rcases writes with ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩
      exact ⟨w0, w1, w4, w6, w8, w9, w12, w14, saved, w2, w3, w5, w7, w10, w11, w13, w15⟩
    · trivial
    · apply hH.agrees.mono
      x86_norm [effect, outputAddress, resetWrites]

  all_goals (
    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 0)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_begin instruction
    case pre => intro s h; exact ⟨h.rip, h.readable (BitVec.ofNat _ (hashOffset f + 0)) (by decide +kernel)⟩
    case «next» =>
      intro s h
      have boundaryAfter := boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b36 else if f = .digest then 0x9727 else if f = .reset 2 then 0xac05 else if f = .finalizeIntoReset true then 0xa2e8 else 0xb450) (by decide +kernel))
      intro bad
      apply boundaryAfter
      rw [← bad]
      x86_norm [f]

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x109b36 else if f = .digest then 0x109727 else if f = .reset 2 then 0x10ac05 else if f = .finalizeIntoReset true then 0x10a2e8 else 0x10b450) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 8 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 8)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b3e else if f = .digest then 0x972f else if f = .reset 2 then 0xac0d else if f = .finalizeIntoReset true then 0xa2f0 else 0xb458) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x109b3e else if f = .digest then 0x10972f else if f = .reset 2 then 0x10ac0d else if f = .finalizeIntoReset true then 0x10a2f0 else 0x10b458) 0)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 16 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b41 else if f = .digest then 0x9732 else if f = .reset 2 then 0xac10 else if f = .finalizeIntoReset true then 0xa2f3 else 0xb45b) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x109b41 else if f = .digest then 0x109732 else if f = .reset 2 then 0x10ac10 else if f = .finalizeIntoReset true then 0x10a2f3 else 0x10b45b) 1)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 19 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b44 else if f = .digest then 0x9735 else if f = .reset 2 then 0xac13 else if f = .finalizeIntoReset true then 0xa2f6 else 0xb45e) (by decide +kernel))

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x109b44 else if f = .digest then 0x109735 else if f = .reset 2 then 0x10ac13 else if f = .finalizeIntoReset true then 0x10a2f6 else 0x10b45e) 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 16)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 22 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 16)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b4c else if f = .digest then 0x973d else if f = .reset 2 then 0xac1b else if f = .finalizeIntoReset true then 0xa2fe else 0xb466) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x109b4c else if f = .digest then 0x10973d else if f = .reset 2 then 0x10ac1b else if f = .finalizeIntoReset true then 0x10a2fe else 0x10b466) 2)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 30 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b4f else if f = .digest then 0x9740 else if f = .reset 2 then 0xac1e else if f = .finalizeIntoReset true then 0xa301 else 0xb469) (by decide +kernel))

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x109b4f else if f = .digest then 0x109740 else if f = .reset 2 then 0x10ac1e else if f = .finalizeIntoReset true then 0x10a301 else 0x10b469) 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 24)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 33 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 24)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b57 else if f = .digest then 0x9748 else if f = .reset 2 then 0xac26 else if f = .finalizeIntoReset true then 0xa309 else 0xb471) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x109b57 else if f = .digest then 0x109748 else if f = .reset 2 then 0x10ac26 else if f = .finalizeIntoReset true then 0x10a309 else 0x10b471) 6)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 41 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b5a else if f = .digest then 0x974b else if f = .reset 2 then 0xac29 else if f = .finalizeIntoReset true then 0xa30c else 0xb474) (by decide +kernel))

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x109b5a else if f = .digest then 0x10974b else if f = .reset 2 then 0x10ac29 else if f = .finalizeIntoReset true then 0x10a30c else 0x10b474) 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 32)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 44 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 32)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b62 else if f = .digest then 0x9753 else if f = .reset 2 then 0xac31 else if f = .finalizeIntoReset true then 0xa314 else 0xb47c) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x109b62 else if f = .digest then 0x109753 else if f = .reset 2 then 0x10ac31 else if f = .finalizeIntoReset true then 0x10a314 else 0x10b47c) 7)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 52 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b65 else if f = .digest then 0x9756 else if f = .reset 2 then 0xac34 else if f = .finalizeIntoReset true then 0xa317 else 0xb47f) (by decide +kernel))

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x109b65 else if f = .digest then 0x109756 else if f = .reset 2 then 0x10ac34 else if f = .finalizeIntoReset true then 0x10a317 else 0x10b47f) 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 40)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 55 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 40)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b6d else if f = .digest then 0x975e else if f = .reset 2 then 0xac3c else if f = .finalizeIntoReset true then 0xa31f else 0xb487) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x109b6d else if f = .digest then 0x10975e else if f = .reset 2 then 0x10ac3c else if f = .finalizeIntoReset true then 0x10a31f else 0x10b487) 8)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 63 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b70 else if f = .digest then 0x9761 else if f = .reset 2 then 0xac3f else if f = .finalizeIntoReset true then 0xa322 else 0xb48a) (by decide +kernel))

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x109b70 else if f = .digest then 0x109761 else if f = .reset 2 then 0x10ac3f else if f = .finalizeIntoReset true then 0x10a322 else 0x10b48a) 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 48)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 66 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 48)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b78 else if f = .digest then 0x9769 else if f = .reset 2 then 0xac47 else if f = .finalizeIntoReset true then 0xa32a else 0xb492) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x109b78 else if f = .digest then 0x109769 else if f = .reset 2 then 0x10ac47 else if f = .finalizeIntoReset true then 0x10a32a else 0x10b492) 9)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 74 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b7b else if f = .digest then 0x976c else if f = .reset 2 then 0xac4a else if f = .finalizeIntoReset true then 0xa32d else 0xb495) (by decide +kernel))

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x109b7b else if f = .digest then 0x10976c else if f = .reset 2 then 0x10ac4a else if f = .finalizeIntoReset true then 0x10a32d else 0x10b495) 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 56)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 77 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 56)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b83 else if f = .digest then 0x9774 else if f = .reset 2 then 0xac52 else if f = .finalizeIntoReset true then 0xa335 else 0xb49d) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x109b83 else if f = .digest then 0x109774 else if f = .reset 2 then 0x10ac52 else if f = .finalizeIntoReset true then 0x10a335 else 0x10b49d) 10)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 85 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b86 else if f = .digest then 0x9777 else if f = .reset 2 then 0xac55 else if f = .finalizeIntoReset true then 0xa338 else 0xb4a0) (by decide +kernel))

    try (
    have hs : f ≠ .digest := by decide
    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x109b86 else if f = .digest then 0x109777 else if f = .reset 2 then 0x10ac55 else if f = .finalizeIntoReset true then 0x10a338 else 0x10b4a0) 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (if f = .slices then .d8 8 else .d32 (BitVec.ofNat 32 (f.frameBytes - f.outputSlot)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) 88 (if f = .slices then 5 else 8)
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat 64 (f.frameBytes - f.outputSlot)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b8b else if f = .digest then 0x9777 else if f = .reset 2 then 0xac5d else if f = .finalizeIntoReset true then 0xa340 else 0xb4a8) (by decide +kernel)))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x109b8b else if f = .digest then 0x109777 else if f = .reset 2 then 0x10ac5d else if f = .finalizeIntoReset true then 0x10a340 else 0x10b4a8) (if f = .digest then 0x48 else 0x49) (by simp [f, RexWPrefix]) 0 (.base (if f = .digest then 3 else 11) .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) (93 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 0 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 0 (by decide +kernel) (if f = .slices then 0x9b8b else if f = .digest then 0x9777 else if f = .reset 2 then 0xac5d else if f = .finalizeIntoReset true then 0xa340 else 0xb4a8) 3 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 0 (by decide +kernel) (if f = .slices then 0x9b2e else if f = .digest then 0x971f else if f = .reset 2 then 0xabfd else if f = .finalizeIntoReset true then 0xa2e0 else 0xb448) (124 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b8e else if f = .digest then 0x977a else if f = .reset 2 then 0xac60 else if f = .finalizeIntoReset true then 0xa343 else 0xb4ab) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x109b8e else if f = .digest then 0x10977a else if f = .reset 2 then 0x10ac60 else if f = .finalizeIntoReset true then 0x10a343 else 0x10b4ab) (if f = .digest then 0x48 else 0x49) (by simp [f, RexWPrefix]) 1 (.base (if f = .digest then 3 else 11) (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) (96 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 8 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 8 (by decide +kernel) (if f = .slices then 0x9b8e else if f = .digest then 0x977a else if f = .reset 2 then 0xac60 else if f = .finalizeIntoReset true then 0xa343 else 0xb4ab) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 8 (by decide +kernel) (if f = .slices then 0x9b2e else if f = .digest then 0x971f else if f = .reset 2 then 0xabfd else if f = .finalizeIntoReset true then 0xa2e0 else 0xb448) (124 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b92 else if f = .digest then 0x977e else if f = .reset 2 then 0xac64 else if f = .finalizeIntoReset true then 0xa347 else 0xb4af) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x109b92 else if f = .digest then 0x10977e else if f = .reset 2 then 0x10ac64 else if f = .finalizeIntoReset true then 0x10a347 else 0x10b4af) (if f = .digest then 0x48 else 0x49) (by simp [f, RexWPrefix]) 2 (.base (if f = .digest then 3 else 11) (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) (100 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 16 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 16 (by decide +kernel) (if f = .slices then 0x9b92 else if f = .digest then 0x977e else if f = .reset 2 then 0xac64 else if f = .finalizeIntoReset true then 0xa347 else 0xb4af) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 16 (by decide +kernel) (if f = .slices then 0x9b2e else if f = .digest then 0x971f else if f = .reset 2 then 0xabfd else if f = .finalizeIntoReset true then 0xa2e0 else 0xb448) (124 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b96 else if f = .digest then 0x9782 else if f = .reset 2 then 0xac68 else if f = .finalizeIntoReset true then 0xa34b else 0xb4b3) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x109b96 else if f = .digest then 0x109782 else if f = .reset 2 then 0x10ac68 else if f = .finalizeIntoReset true then 0x10a34b else 0x10b4b3) (if f = .digest then 0x48 else 0x49) (by simp [f, RexWPrefix]) 6 (.base (if f = .digest then 3 else 11) (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) (104 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 24 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 24 (by decide +kernel) (if f = .slices then 0x9b96 else if f = .digest then 0x9782 else if f = .reset 2 then 0xac68 else if f = .finalizeIntoReset true then 0xa34b else 0xb4b3) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 24 (by decide +kernel) (if f = .slices then 0x9b2e else if f = .digest then 0x971f else if f = .reset 2 then 0xabfd else if f = .finalizeIntoReset true then 0xa2e0 else 0xb448) (124 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b9a else if f = .digest then 0x9786 else if f = .reset 2 then 0xac6c else if f = .finalizeIntoReset true then 0xa34f else 0xb4b7) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x109b9a else if f = .digest then 0x109786 else if f = .reset 2 then 0x10ac6c else if f = .finalizeIntoReset true then 0x10a34f else 0x10b4b7) (if f = .digest then 0x48 else 0x49) (by simp [f, RexWPrefix]) 7 (.base (if f = .digest then 3 else 11) (.d8 32)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) (108 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 32 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 32 (by decide +kernel) (if f = .slices then 0x9b9a else if f = .digest then 0x9786 else if f = .reset 2 then 0xac6c else if f = .finalizeIntoReset true then 0xa34f else 0xb4b7) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 32 (by decide +kernel) (if f = .slices then 0x9b2e else if f = .digest then 0x971f else if f = .reset 2 then 0xabfd else if f = .finalizeIntoReset true then 0xa2e0 else 0xb448) (124 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9b9e else if f = .digest then 0x978a else if f = .reset 2 then 0xac70 else if f = .finalizeIntoReset true then 0xa353 else 0xb4bb) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x109b9e else if f = .digest then 0x10978a else if f = .reset 2 then 0x10ac70 else if f = .finalizeIntoReset true then 0x10a353 else 0x10b4bb) (if f = .digest then 0x4c else 0x4d) (by simp [f, RexWPrefix]) 0 (.base (if f = .digest then 3 else 11) (.d8 40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) (112 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 40 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 40 (by decide +kernel) (if f = .slices then 0x9b9e else if f = .digest then 0x978a else if f = .reset 2 then 0xac70 else if f = .finalizeIntoReset true then 0xa353 else 0xb4bb) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 40 (by decide +kernel) (if f = .slices then 0x9b2e else if f = .digest then 0x971f else if f = .reset 2 then 0xabfd else if f = .finalizeIntoReset true then 0xa2e0 else 0xb448) (124 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9ba2 else if f = .digest then 0x978e else if f = .reset 2 then 0xac74 else if f = .finalizeIntoReset true then 0xa357 else 0xb4bf) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x109ba2 else if f = .digest then 0x10978e else if f = .reset 2 then 0x10ac74 else if f = .finalizeIntoReset true then 0x10a357 else 0x10b4bf) (if f = .digest then 0x4c else 0x4d) (by simp [f, RexWPrefix]) 1 (.base (if f = .digest then 3 else 11) (.d8 48)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) (116 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 48 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 48 (by decide +kernel) (if f = .slices then 0x9ba2 else if f = .digest then 0x978e else if f = .reset 2 then 0xac74 else if f = .finalizeIntoReset true then 0xa357 else 0xb4bf) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 48 (by decide +kernel) (if f = .slices then 0x9b2e else if f = .digest then 0x971f else if f = .reset 2 then 0xabfd else if f = .finalizeIntoReset true then 0xa2e0 else 0xb448) (124 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9ba6 else if f = .digest then 0x9792 else if f = .reset 2 then 0xac78 else if f = .finalizeIntoReset true then 0xa35b else 0xb4c3) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x109ba6 else if f = .digest then 0x109792 else if f = .reset 2 then 0x10ac78 else if f = .finalizeIntoReset true then 0x10a35b else 0x10b4c3) (if f = .digest then 0x4c else 0x4d) (by simp [f, RexWPrefix]) 2 (.base (if f = .digest then 3 else 11) (.d8 56)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x109b2e else if f = .digest then 0x10971f else if f = .reset 2 then 0x10abfd else if f = .finalizeIntoReset true then 0x10a2e0 else 0x10b448) (bytes .sha512 f) (120 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 56 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 56 (by decide +kernel) (if f = .slices then 0x9ba6 else if f = .digest then 0x9792 else if f = .reset 2 then 0xac78 else if f = .finalizeIntoReset true then 0xa35b else 0xb4c3) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 56 (by decide +kernel) (if f = .slices then 0x9b2e else if f = .digest then 0x971f else if f = .reset 2 then 0xabfd else if f = .finalizeIntoReset true then 0xa2e0 else 0xb448) (124 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x9baa else if f = .digest then 0x9796 else if f = .reset 2 then 0xac7c else if f = .finalizeIntoReset true then 0xa35f else 0xb4c7) (by decide +kernel))

    try simp only [f] at *
    first
    | have nondigest : f ≠ .digest := by decide
      advance_finish [effect, outputAddress, resetWrites]
    | apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
      intro s t _ hH
      have saved := hH.agrees.read (n := 64) (r := 11) (by x86_norm)
      have writes := hH.writes
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [effect, Variant.pc, Variant.outputEndOffset, Variant.epilogueOffset, Variant.textOffset,
          Extracted.textAddress, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hH.rip
      · simp only [effect, resetWrites, Write.AllHold, outputAddress, reduceCtorEq, reduceIte, List.append_nil, pointerRegister] at writes ⊢
        rcases writes with ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩
        all_goals first | assumption | exact ⟨w0, w1, w2, w3, w4, w5, w6, w7, saved, w8, w9, w10, w11, w12, w13, w14, w15⟩
      · trivial
      · apply hH.agrees.mono
        x86_norm [effect, outputAddress, resetWrites])

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem machine_sha512_224 [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (form : Form := .slices) :
    AdvanceTriple boundary (fun s => Pre .sha512_224 s form) (codeRange (Variant.sha512_224.pc (Variant.sha512_224.serializeOffset form) form) (bytes .sha512_224 form))
      (Effect.post (fun s => effect .sha512_224 s form)) := by
  let f := form
  cases form
  all_goals try (
    rename_i second
    have _ : Bool := second
    cases second)
  all_goals try (
    rename_i stage
    have _ : Fin 3 := stage
    have choices : stage = (0 : Fin 3) ∨ stage = 1 ∨ stage = 2 := by
      rcases stage with ⟨n, bound⟩
      rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    rcases choices with (rfl | rfl | rfl))
  case reset.inl =>
    intro s _ _ hP
    exact False.elim (hP.finalizes rfl)
  case reset.inr.inl =>
    exact machine_sha512_224_reset1 boundary outside
  case finalizeIntoReset.false =>
    let f : Form := .finalizeIntoReset false
    advance_begin (mov_r64_m64_effect_step 0x1061d8 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 144)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case pre =>
      intro s h
      exact ⟨h.rip, h.readable 144 (by decide +kernel)⟩
    case «next» =>
      intro s h
      exact boundary_ne_program outside (inProgram_of_textOffset 0x61e0 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1061e0 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 152)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1061d8 (bytes .sha512_224 f) 8 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 152 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x61e8 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x1061e8 0)
    case sub =>
      have subset := codeRange_slice_subset 0x1061d8 (bytes .sha512_224 f) 16 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x61eb (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x1061eb 1)
    case sub =>
      have subset := codeRange_slice_subset 0x1061d8 (bytes .sha512_224 f) 19 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x61ee (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1061ee 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 160)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1061d8 (bytes .sha512_224 f) 22 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 160 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x61f6 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x1061f6 2)
    case sub =>
      have subset := codeRange_slice_subset 0x1061d8 (bytes .sha512_224 f) 30 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x61f9 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1061f9 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 168)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1061d8 (bytes .sha512_224 f) 33 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 168 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x6201 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x106201 6)
    case sub =>
      have subset := codeRange_slice_subset 0x1061d8 (bytes .sha512_224 f) 41 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x6204 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x106204 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 224)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1061d8 (bytes .sha512_224 f) 44 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 224 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x620c (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10620c 0x48 (by simp [RexWPrefix]) 0 (.base 7 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1061d8 (bytes .sha512_224 f) 52 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 0 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0x620c 3 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0x61d8 66 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x620f (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10620f 0x48 (by simp [RexWPrefix]) 1 (.base 7 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1061d8 (bytes .sha512_224 f) 55 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 8 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0x620f 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0x61d8 66 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x6213 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106213 0x48 (by simp [RexWPrefix]) 2 (.base 7 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1061d8 (bytes .sha512_224 f) 59 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 16 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0x6213 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0x61d8 66 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x6217 (by decide +kernel))
    advance_then (CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x106217 6 (.base 7 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1061d8 (bytes .sha512_224 f) 63 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writablePartial rfl
      · x86_norm [f]
        exact hP.codeApartPartial rfl 0x6217 3 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApartPartial rfl 0x61d8 66 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x621a (by decide +kernel))
    advance_finish [effect, outputAddress, resetWrites]
  case traitFinalizeIntoReset.false =>
    let f : Form := .traitFinalizeIntoReset false
    advance_begin (mov_r64_m64_effect_step 0x107240 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 384)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case pre =>
      intro s h
      exact ⟨h.rip, h.readable 384 (by decide +kernel)⟩
    case «next» =>
      intro s h
      exact boundary_ne_program outside (inProgram_of_textOffset 0x7248 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x107248 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 392)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x107240 (bytes .sha512_224 f) 8 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 392 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x7250 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x107250 0)
    case sub =>
      have subset := codeRange_slice_subset 0x107240 (bytes .sha512_224 f) 16 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x7253 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x107253 1)
    case sub =>
      have subset := codeRange_slice_subset 0x107240 (bytes .sha512_224 f) 19 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x7256 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x107256 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 400)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x107240 (bytes .sha512_224 f) 22 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 400 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x725e (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x10725e 2)
    case sub =>
      have subset := codeRange_slice_subset 0x107240 (bytes .sha512_224 f) 30 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x7261 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x107261 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 408)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x107240 (bytes .sha512_224 f) 33 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 408 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x7269 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x107269 6)
    case sub =>
      have subset := codeRange_slice_subset 0x107240 (bytes .sha512_224 f) 41 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x726c (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10726c 0x48 (by simp [RexWPrefix]) 0 (.base 5 (.d8 0)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x107240 (bytes .sha512_224 f) 44 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 0 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0x726c 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0x7240 59 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x7270 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x107270 0x48 (by simp [RexWPrefix]) 1 (.base 5 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x107240 (bytes .sha512_224 f) 48 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 8 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0x7270 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0x7240 59 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x7274 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x107274 0x48 (by simp [RexWPrefix]) 2 (.base 5 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x107240 (bytes .sha512_224 f) 52 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 16 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0x7274 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0x7240 59 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x7278 (by decide +kernel))
    advance_then (CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x107278 6 (.base 5 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x107240 (bytes .sha512_224 f) 56 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writablePartial rfl
      · x86_norm [f]
        exact hP.codeApartPartial rfl 0x7278 3 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApartPartial rfl 0x7240 59 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x727b (by decide +kernel))
    apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
    intro s t _ hH
    have saved := hH.agrees.read (n := 64) (r := 7) (by x86_norm)
    have writes := hH.writes
    refine ⟨?_, ?_, ?_, ?_⟩
    · change t.RIP = 0x10727b
      exact hH.rip
    · simp only [effect, resetWrites, Write.AllHold, outputAddress, reduceCtorEq, reduceIte, List.append_nil, pointerRegister] at writes ⊢
      rcases writes with ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩
      exact ⟨w0, w1, w2, w3, saved, w4, w5, w6, w7⟩
    · trivial
    · apply hH.agrees.mono
      x86_norm [effect, outputAddress, resetWrites]

  all_goals (
    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x105e2e else if f = .digest then 0x105a5f else if f = .reset 2 then 0x106dfd else if f = .finalizeIntoReset true then 0x106562 else 0x1075d8) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 0)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_begin instruction
    case pre => intro s h; exact ⟨h.rip, h.readable (BitVec.ofNat _ (hashOffset f + 0)) (by decide +kernel)⟩
    case «next» =>
      intro s h
      have boundaryAfter := boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x5e36 else if f = .digest then 0x5a67 else if f = .reset 2 then 0x6e05 else if f = .finalizeIntoReset true then 0x656a else 0x75e0) (by decide +kernel))
      intro bad
      apply boundaryAfter
      rw [← bad]
      x86_norm [f]

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x105e36 else if f = .digest then 0x105a67 else if f = .reset 2 then 0x106e05 else if f = .finalizeIntoReset true then 0x10656a else 0x1075e0) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x105e2e else if f = .digest then 0x105a5f else if f = .reset 2 then 0x106dfd else if f = .finalizeIntoReset true then 0x106562 else 0x1075d8) (bytes .sha512_224 f) 8 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 8)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x5e3e else if f = .digest then 0x5a6f else if f = .reset 2 then 0x6e0d else if f = .finalizeIntoReset true then 0x6572 else 0x75e8) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x105e3e else if f = .digest then 0x105a6f else if f = .reset 2 then 0x106e0d else if f = .finalizeIntoReset true then 0x106572 else 0x1075e8) 0)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x105e2e else if f = .digest then 0x105a5f else if f = .reset 2 then 0x106dfd else if f = .finalizeIntoReset true then 0x106562 else 0x1075d8) (bytes .sha512_224 f) 16 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x5e41 else if f = .digest then 0x5a72 else if f = .reset 2 then 0x6e10 else if f = .finalizeIntoReset true then 0x6575 else 0x75eb) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x105e41 else if f = .digest then 0x105a72 else if f = .reset 2 then 0x106e10 else if f = .finalizeIntoReset true then 0x106575 else 0x1075eb) 1)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x105e2e else if f = .digest then 0x105a5f else if f = .reset 2 then 0x106dfd else if f = .finalizeIntoReset true then 0x106562 else 0x1075d8) (bytes .sha512_224 f) 19 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x5e44 else if f = .digest then 0x5a75 else if f = .reset 2 then 0x6e13 else if f = .finalizeIntoReset true then 0x6578 else 0x75ee) (by decide +kernel))

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x105e44 else if f = .digest then 0x105a75 else if f = .reset 2 then 0x106e13 else if f = .finalizeIntoReset true then 0x106578 else 0x1075ee) 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 16)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x105e2e else if f = .digest then 0x105a5f else if f = .reset 2 then 0x106dfd else if f = .finalizeIntoReset true then 0x106562 else 0x1075d8) (bytes .sha512_224 f) 22 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 16)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x5e4c else if f = .digest then 0x5a7d else if f = .reset 2 then 0x6e1b else if f = .finalizeIntoReset true then 0x6580 else 0x75f6) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x105e4c else if f = .digest then 0x105a7d else if f = .reset 2 then 0x106e1b else if f = .finalizeIntoReset true then 0x106580 else 0x1075f6) 2)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x105e2e else if f = .digest then 0x105a5f else if f = .reset 2 then 0x106dfd else if f = .finalizeIntoReset true then 0x106562 else 0x1075d8) (bytes .sha512_224 f) 30 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x5e4f else if f = .digest then 0x5a80 else if f = .reset 2 then 0x6e1e else if f = .finalizeIntoReset true then 0x6583 else 0x75f9) (by decide +kernel))

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x105e4f else if f = .digest then 0x105a80 else if f = .reset 2 then 0x106e1e else if f = .finalizeIntoReset true then 0x106583 else 0x1075f9) 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 24)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x105e2e else if f = .digest then 0x105a5f else if f = .reset 2 then 0x106dfd else if f = .finalizeIntoReset true then 0x106562 else 0x1075d8) (bytes .sha512_224 f) 33 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 24)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x5e57 else if f = .digest then 0x5a88 else if f = .reset 2 then 0x6e26 else if f = .finalizeIntoReset true then 0x658b else 0x7601) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x105e57 else if f = .digest then 0x105a88 else if f = .reset 2 then 0x106e26 else if f = .finalizeIntoReset true then 0x10658b else 0x107601) 6)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x105e2e else if f = .digest then 0x105a5f else if f = .reset 2 then 0x106dfd else if f = .finalizeIntoReset true then 0x106562 else 0x1075d8) (bytes .sha512_224 f) 41 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x5e5a else if f = .digest then 0x5a8b else if f = .reset 2 then 0x6e29 else if f = .finalizeIntoReset true then 0x658e else 0x7604) (by decide +kernel))

    try (
    have hs : f ≠ .digest := by decide
    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x105e5a else if f = .digest then 0x105a8b else if f = .reset 2 then 0x106e29 else if f = .finalizeIntoReset true then 0x10658e else 0x107604) 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (if f = .slices then .d8 8 else .d32 (BitVec.ofNat 32 (f.frameBytes - f.outputSlot)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x105e2e else if f = .digest then 0x105a5f else if f = .reset 2 then 0x106dfd else if f = .finalizeIntoReset true then 0x106562 else 0x1075d8) (bytes .sha512_224 f) 44 (if f = .slices then 5 else 8)
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat 64 (f.frameBytes - f.outputSlot)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x5e5f else if f = .digest then 0x5a8b else if f = .reset 2 then 0x6e31 else if f = .finalizeIntoReset true then 0x6596 else 0x760c) (by decide +kernel)))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x105e5f else if f = .digest then 0x105a8b else if f = .reset 2 then 0x106e31 else if f = .finalizeIntoReset true then 0x106596 else 0x10760c) 0x48 (by simp [RexWPrefix]) 0 (.base (if f = .digest then 3 else 7) .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x105e2e else if f = .digest then 0x105a5f else if f = .reset 2 then 0x106dfd else if f = .finalizeIntoReset true then 0x106562 else 0x1075d8) (bytes .sha512_224 f) (49 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 0 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 0 (by decide +kernel) (if f = .slices then 0x5e5f else if f = .digest then 0x5a8b else if f = .reset 2 then 0x6e31 else if f = .finalizeIntoReset true then 0x6596 else 0x760c) 3 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 0 (by decide +kernel) (if f = .slices then 0x5e2e else if f = .digest then 0x5a5f else if f = .reset 2 then 0x6dfd else if f = .finalizeIntoReset true then 0x6562 else 0x75d8) (63 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x5e62 else if f = .digest then 0x5a8e else if f = .reset 2 then 0x6e34 else if f = .finalizeIntoReset true then 0x6599 else 0x760f) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x105e62 else if f = .digest then 0x105a8e else if f = .reset 2 then 0x106e34 else if f = .finalizeIntoReset true then 0x106599 else 0x10760f) 0x48 (by simp [RexWPrefix]) 1 (.base (if f = .digest then 3 else 7) (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x105e2e else if f = .digest then 0x105a5f else if f = .reset 2 then 0x106dfd else if f = .finalizeIntoReset true then 0x106562 else 0x1075d8) (bytes .sha512_224 f) (52 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 8 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 8 (by decide +kernel) (if f = .slices then 0x5e62 else if f = .digest then 0x5a8e else if f = .reset 2 then 0x6e34 else if f = .finalizeIntoReset true then 0x6599 else 0x760f) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 8 (by decide +kernel) (if f = .slices then 0x5e2e else if f = .digest then 0x5a5f else if f = .reset 2 then 0x6dfd else if f = .finalizeIntoReset true then 0x6562 else 0x75d8) (63 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x5e66 else if f = .digest then 0x5a92 else if f = .reset 2 then 0x6e38 else if f = .finalizeIntoReset true then 0x659d else 0x7613) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x105e66 else if f = .digest then 0x105a92 else if f = .reset 2 then 0x106e38 else if f = .finalizeIntoReset true then 0x10659d else 0x107613) 0x48 (by simp [RexWPrefix]) 2 (.base (if f = .digest then 3 else 7) (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x105e2e else if f = .digest then 0x105a5f else if f = .reset 2 then 0x106dfd else if f = .finalizeIntoReset true then 0x106562 else 0x1075d8) (bytes .sha512_224 f) (56 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 16 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 16 (by decide +kernel) (if f = .slices then 0x5e66 else if f = .digest then 0x5a92 else if f = .reset 2 then 0x6e38 else if f = .finalizeIntoReset true then 0x659d else 0x7613) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 16 (by decide +kernel) (if f = .slices then 0x5e2e else if f = .digest then 0x5a5f else if f = .reset 2 then 0x6dfd else if f = .finalizeIntoReset true then 0x6562 else 0x75d8) (63 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x5e6a else if f = .digest then 0x5a96 else if f = .reset 2 then 0x6e3c else if f = .finalizeIntoReset true then 0x65a1 else 0x7617) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m32_r32_legacy_effect_step_any (if f = .slices then 0x105e6a else if f = .digest then 0x105a96 else if f = .reset 2 then 0x106e3c else if f = .finalizeIntoReset true then 0x1065a1 else 0x107617) 6 (.base (if f = .digest then 3 else 7) (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x105e2e else if f = .digest then 0x105a5f else if f = .reset 2 then 0x106dfd else if f = .finalizeIntoReset true then 0x106562 else 0x1075d8) (bytes .sha512_224 f) (60 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writablePartial rfl
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApartPartial rfl (if f = .slices then 0x5e6a else if f = .digest then 0x5a96 else if f = .reset 2 then 0x6e3c else if f = .finalizeIntoReset true then 0x65a1 else 0x7617) 3 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApartPartial rfl (if f = .slices then 0x5e2e else if f = .digest then 0x5a5f else if f = .reset 2 then 0x6dfd else if f = .finalizeIntoReset true then 0x6562 else 0x75d8) (63 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x5e6d else if f = .digest then 0x5a99 else if f = .reset 2 then 0x6e3f else if f = .finalizeIntoReset true then 0x65a4 else 0x761a) (by decide +kernel))

    try simp only [f] at *
    first
    | have nondigest : f ≠ .digest := by decide
      advance_finish [effect, outputAddress, resetWrites]
    | apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
      intro s t _ hH
      have saved := hH.agrees.read (n := 64) (r := 7) (by x86_norm)
      have writes := hH.writes
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [effect, Variant.pc, Variant.outputEndOffset, Variant.epilogueOffset, Variant.textOffset,
          Extracted.textAddress, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hH.rip
      · simp only [effect, resetWrites, Write.AllHold, outputAddress, reduceCtorEq, reduceIte, List.append_nil, pointerRegister] at writes ⊢
        rcases writes with ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩
        all_goals first | assumption | exact ⟨w0, w1, w2, w3, saved, w4, w5, w6, w7⟩
      · trivial
      · apply hH.agrees.mono
        x86_norm [effect, outputAddress, resetWrites])

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem machine_sha512_256 [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (form : Form := .slices) :
    AdvanceTriple boundary (fun s => Pre .sha512_256 s form) (codeRange (Variant.sha512_256.pc (Variant.sha512_256.serializeOffset form) form) (bytes .sha512_256 form))
      (Effect.post (fun s => effect .sha512_256 s form)) := by
  let f := form
  cases form
  all_goals try (
    rename_i second
    have _ : Bool := second
    cases second)
  all_goals try (
    rename_i stage
    have _ : Fin 3 := stage
    have choices : stage = (0 : Fin 3) ∨ stage = 1 ∨ stage = 2 := by
      rcases stage with ⟨n, bound⟩
      rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    rcases choices with (rfl | rfl | rfl))
  case reset.inl =>
    intro s _ _ hP
    exact False.elim (hP.finalizes rfl)
  case reset.inr.inl =>
    exact machine_sha512_256_reset1 boundary outside
  case finalizeIntoReset.false =>
    let f : Form := .finalizeIntoReset false
    advance_begin (mov_r64_m64_effect_step 0x108038 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 144)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case pre =>
      intro s h
      exact ⟨h.rip, h.readable 144 (by decide +kernel)⟩
    case «next» =>
      intro s h
      exact boundary_ne_program outside (inProgram_of_textOffset 0x8040 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x108040 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 152)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x108038 (bytes .sha512_256 f) 8 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 152 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x8048 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x108048 0)
    case sub =>
      have subset := codeRange_slice_subset 0x108038 (bytes .sha512_256 f) 16 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x804b (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x10804b 1)
    case sub =>
      have subset := codeRange_slice_subset 0x108038 (bytes .sha512_256 f) 19 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x804e (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x10804e 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 160)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x108038 (bytes .sha512_256 f) 22 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 160 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x8056 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x108056 2)
    case sub =>
      have subset := codeRange_slice_subset 0x108038 (bytes .sha512_256 f) 30 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x8059 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x108059 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 168)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x108038 (bytes .sha512_256 f) 33 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 168 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x8061 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x108061 6)
    case sub =>
      have subset := codeRange_slice_subset 0x108038 (bytes .sha512_256 f) 41 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x8064 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x108064 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 224)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x108038 (bytes .sha512_256 f) 44 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 224 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x806c (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10806c 0x48 (by simp [RexWPrefix]) 0 (.base 7 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x108038 (bytes .sha512_256 f) 52 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 0 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0x806c 3 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0x8038 67 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x806f (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10806f 0x48 (by simp [RexWPrefix]) 1 (.base 7 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x108038 (bytes .sha512_256 f) 55 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 8 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0x806f 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0x8038 67 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x8073 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x108073 0x48 (by simp [RexWPrefix]) 2 (.base 7 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x108038 (bytes .sha512_256 f) 59 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 16 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0x8073 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0x8038 67 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x8077 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x108077 0x48 (by simp [RexWPrefix]) 6 (.base 7 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x108038 (bytes .sha512_256 f) 63 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 24 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 24 (by decide +kernel) 0x8077 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 24 (by decide +kernel) 0x8038 67 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x807b (by decide +kernel))
    advance_finish [effect, outputAddress, resetWrites]
  case traitFinalizeIntoReset.false =>
    let f : Form := .traitFinalizeIntoReset false
    advance_begin (mov_r64_m64_effect_step 0x1090a0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 384)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case pre =>
      intro s h
      exact ⟨h.rip, h.readable 384 (by decide +kernel)⟩
    case «next» =>
      intro s h
      exact boundary_ne_program outside (inProgram_of_textOffset 0x90a8 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1090a8 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 392)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1090a0 (bytes .sha512_256 f) 8 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 392 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x90b0 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x1090b0 0)
    case sub =>
      have subset := codeRange_slice_subset 0x1090a0 (bytes .sha512_256 f) 16 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x90b3 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x1090b3 1)
    case sub =>
      have subset := codeRange_slice_subset 0x1090a0 (bytes .sha512_256 f) 19 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x90b6 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1090b6 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 400)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1090a0 (bytes .sha512_256 f) 22 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 400 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x90be (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x1090be 2)
    case sub =>
      have subset := codeRange_slice_subset 0x1090a0 (bytes .sha512_256 f) 30 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x90c1 (by decide +kernel))
    advance_then (mov_r64_m64_effect_step 0x1090c1 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 408)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1090a0 (bytes .sha512_256 f) 33 8
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.readable 408 (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x90c9 (by decide +kernel))
    advance_then (bswap_r64_effect_step 0x1090c9 6)
    case sub =>
      have subset := codeRange_slice_subset 0x1090a0 (bytes .sha512_256 f) 41 3
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x90cc (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1090cc 0x48 (by simp [RexWPrefix]) 0 (.base 5 (.d8 0)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1090a0 (bytes .sha512_256 f) 44 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 0 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0x90cc 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 0 (by decide +kernel) 0x90a0 60 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x90d0 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1090d0 0x48 (by simp [RexWPrefix]) 1 (.base 5 (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1090a0 (bytes .sha512_256 f) 48 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 8 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0x90d0 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 8 (by decide +kernel) 0x90a0 60 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x90d4 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1090d4 0x48 (by simp [RexWPrefix]) 2 (.base 5 (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1090a0 (bytes .sha512_256 f) 52 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 16 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0x90d4 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 16 (by decide +kernel) 0x90a0 60 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x90d8 (by decide +kernel))
    advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1090d8 0x48 (by simp [RexWPrefix]) 6 (.base 5 (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case sub =>
      have subset := codeRange_slice_subset 0x1090a0 (bytes .sha512_256 f) 56 4
      simp only [f, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f]
        exact hP.writable 24 (by decide +kernel)
      · x86_norm [f]
        exact hP.codeApart 24 (by decide +kernel) 0x90d8 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f]
        exact hP.codeApart 24 (by decide +kernel) 0x90a0 60 (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x90dc (by decide +kernel))
    apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
    intro s t _ hH
    have saved := hH.agrees.read (n := 64) (r := 7) (by x86_norm)
    have writes := hH.writes
    refine ⟨?_, ?_, ?_, ?_⟩
    · change t.RIP = 0x1090dc
      exact hH.rip
    · simp only [effect, resetWrites, Write.AllHold, outputAddress, reduceCtorEq, reduceIte, List.append_nil, pointerRegister] at writes ⊢
      rcases writes with ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩
      exact ⟨w0, w1, w2, w3, saved, w4, w5, w6, w7⟩
    · trivial
    · apply hH.agrees.mono
      x86_norm [effect, outputAddress, resetWrites]

  all_goals (
    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x107c8e else if f = .digest then 0x1078bf else if f = .reset 2 then 0x108c5d else if f = .finalizeIntoReset true then 0x1083c2 else 0x109438) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 0)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_begin instruction
    case pre => intro s h; exact ⟨h.rip, h.readable (BitVec.ofNat _ (hashOffset f + 0)) (by decide +kernel)⟩
    case «next» =>
      intro s h
      have boundaryAfter := boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x7c96 else if f = .digest then 0x78c7 else if f = .reset 2 then 0x8c65 else if f = .finalizeIntoReset true then 0x83ca else 0x9440) (by decide +kernel))
      intro bad
      apply boundaryAfter
      rw [← bad]
      x86_norm [f]

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x107c96 else if f = .digest then 0x1078c7 else if f = .reset 2 then 0x108c65 else if f = .finalizeIntoReset true then 0x1083ca else 0x109440) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x107c8e else if f = .digest then 0x1078bf else if f = .reset 2 then 0x108c5d else if f = .finalizeIntoReset true then 0x1083c2 else 0x109438) (bytes .sha512_256 f) 8 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 8)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x7c9e else if f = .digest then 0x78cf else if f = .reset 2 then 0x8c6d else if f = .finalizeIntoReset true then 0x83d2 else 0x9448) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x107c9e else if f = .digest then 0x1078cf else if f = .reset 2 then 0x108c6d else if f = .finalizeIntoReset true then 0x1083d2 else 0x109448) 0)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x107c8e else if f = .digest then 0x1078bf else if f = .reset 2 then 0x108c5d else if f = .finalizeIntoReset true then 0x1083c2 else 0x109438) (bytes .sha512_256 f) 16 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x7ca1 else if f = .digest then 0x78d2 else if f = .reset 2 then 0x8c70 else if f = .finalizeIntoReset true then 0x83d5 else 0x944b) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x107ca1 else if f = .digest then 0x1078d2 else if f = .reset 2 then 0x108c70 else if f = .finalizeIntoReset true then 0x1083d5 else 0x10944b) 1)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x107c8e else if f = .digest then 0x1078bf else if f = .reset 2 then 0x108c5d else if f = .finalizeIntoReset true then 0x1083c2 else 0x109438) (bytes .sha512_256 f) 19 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x7ca4 else if f = .digest then 0x78d5 else if f = .reset 2 then 0x8c73 else if f = .finalizeIntoReset true then 0x83d8 else 0x944e) (by decide +kernel))

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x107ca4 else if f = .digest then 0x1078d5 else if f = .reset 2 then 0x108c73 else if f = .finalizeIntoReset true then 0x1083d8 else 0x10944e) 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 16)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x107c8e else if f = .digest then 0x1078bf else if f = .reset 2 then 0x108c5d else if f = .finalizeIntoReset true then 0x1083c2 else 0x109438) (bytes .sha512_256 f) 22 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 16)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x7cac else if f = .digest then 0x78dd else if f = .reset 2 then 0x8c7b else if f = .finalizeIntoReset true then 0x83e0 else 0x9456) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x107cac else if f = .digest then 0x1078dd else if f = .reset 2 then 0x108c7b else if f = .finalizeIntoReset true then 0x1083e0 else 0x109456) 2)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x107c8e else if f = .digest then 0x1078bf else if f = .reset 2 then 0x108c5d else if f = .finalizeIntoReset true then 0x1083c2 else 0x109438) (bytes .sha512_256 f) 30 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x7caf else if f = .digest then 0x78e0 else if f = .reset 2 then 0x8c7e else if f = .finalizeIntoReset true then 0x83e3 else 0x9459) (by decide +kernel))

    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x107caf else if f = .digest then 0x1078e0 else if f = .reset 2 then 0x108c7e else if f = .finalizeIntoReset true then 0x1083e3 else 0x109459) 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 (BitVec.ofNat _ (hashOffset f + 24)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x107c8e else if f = .digest then 0x1078bf else if f = .reset 2 then 0x108c5d else if f = .finalizeIntoReset true then 0x1083c2 else 0x109438) (bytes .sha512_256 f) 33 8
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat _ (hashOffset f + 24)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x7cb7 else if f = .digest then 0x78e8 else if f = .reset 2 then 0x8c86 else if f = .finalizeIntoReset true then 0x83eb else 0x9461) (by decide +kernel))

    have instruction := (bswap_r64_effect_step (if f = .slices then 0x107cb7 else if f = .digest then 0x1078e8 else if f = .reset 2 then 0x108c86 else if f = .finalizeIntoReset true then 0x1083eb else 0x109461) 6)
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x107c8e else if f = .digest then 0x1078bf else if f = .reset 2 then 0x108c5d else if f = .finalizeIntoReset true then 0x1083c2 else 0x109438) (bytes .sha512_256 f) 41 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [f]), ?_, ?_⟩
      · apply Effect.Avoids.of_noMem
        simp [bswapR64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x7cba else if f = .digest then 0x78eb else if f = .reset 2 then 0x8c89 else if f = .finalizeIntoReset true then 0x83ee else 0x9464) (by decide +kernel))

    try (
    have hs : f ≠ .digest := by decide
    have instruction := (mov_r64_m64_effect_step (if f = .slices then 0x107cba else if f = .digest then 0x1078eb else if f = .reset 2 then 0x108c89 else if f = .finalizeIntoReset true then 0x1083ee else 0x109464) 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (if f = .slices then .d8 8 else .d32 (BitVec.ofNat 32 (f.frameBytes - f.outputSlot)))) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x107c8e else if f = .digest then 0x1078bf else if f = .reset 2 then 0x108c5d else if f = .finalizeIntoReset true then 0x1083c2 else 0x109438) (bytes .sha512_256 f) 44 (if f = .slices then 5 else 8)
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [f]) (by x86_addr_obs) ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.readable (BitVec.ofNat 64 (f.frameBytes - f.outputSlot)) (by decide +kernel)
      · apply Effect.Avoids.of_noMem
        simp [movR64M64Effect, Effect.components, Component.Covers]
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x7cbf else if f = .digest then 0x78eb else if f = .reset 2 then 0x8c91 else if f = .finalizeIntoReset true then 0x83f6 else 0x946c) (by decide +kernel)))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x107cbf else if f = .digest then 0x1078eb else if f = .reset 2 then 0x108c91 else if f = .finalizeIntoReset true then 0x1083f6 else 0x10946c) 0x48 (by simp [RexWPrefix]) 0 (.base (if f = .digest then 3 else 7) .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x107c8e else if f = .digest then 0x1078bf else if f = .reset 2 then 0x108c5d else if f = .finalizeIntoReset true then 0x1083c2 else 0x109438) (bytes .sha512_256 f) (49 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 3
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 0 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 0 (by decide +kernel) (if f = .slices then 0x7cbf else if f = .digest then 0x78eb else if f = .reset 2 then 0x8c91 else if f = .finalizeIntoReset true then 0x83f6 else 0x946c) 3 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 0 (by decide +kernel) (if f = .slices then 0x7c8e else if f = .digest then 0x78bf else if f = .reset 2 then 0x8c5d else if f = .finalizeIntoReset true then 0x83c2 else 0x9438) (64 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x7cc2 else if f = .digest then 0x78ee else if f = .reset 2 then 0x8c94 else if f = .finalizeIntoReset true then 0x83f9 else 0x946f) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x107cc2 else if f = .digest then 0x1078ee else if f = .reset 2 then 0x108c94 else if f = .finalizeIntoReset true then 0x1083f9 else 0x10946f) 0x48 (by simp [RexWPrefix]) 1 (.base (if f = .digest then 3 else 7) (.d8 8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x107c8e else if f = .digest then 0x1078bf else if f = .reset 2 then 0x108c5d else if f = .finalizeIntoReset true then 0x1083c2 else 0x109438) (bytes .sha512_256 f) (52 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 8 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 8 (by decide +kernel) (if f = .slices then 0x7cc2 else if f = .digest then 0x78ee else if f = .reset 2 then 0x8c94 else if f = .finalizeIntoReset true then 0x83f9 else 0x946f) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 8 (by decide +kernel) (if f = .slices then 0x7c8e else if f = .digest then 0x78bf else if f = .reset 2 then 0x8c5d else if f = .finalizeIntoReset true then 0x83c2 else 0x9438) (64 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x7cc6 else if f = .digest then 0x78f2 else if f = .reset 2 then 0x8c98 else if f = .finalizeIntoReset true then 0x83fd else 0x9473) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x107cc6 else if f = .digest then 0x1078f2 else if f = .reset 2 then 0x108c98 else if f = .finalizeIntoReset true then 0x1083fd else 0x109473) 0x48 (by simp [RexWPrefix]) 2 (.base (if f = .digest then 3 else 7) (.d8 16)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x107c8e else if f = .digest then 0x1078bf else if f = .reset 2 then 0x108c5d else if f = .finalizeIntoReset true then 0x1083c2 else 0x109438) (bytes .sha512_256 f) (56 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 16 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 16 (by decide +kernel) (if f = .slices then 0x7cc6 else if f = .digest then 0x78f2 else if f = .reset 2 then 0x8c98 else if f = .finalizeIntoReset true then 0x83fd else 0x9473) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 16 (by decide +kernel) (if f = .slices then 0x7c8e else if f = .digest then 0x78bf else if f = .reset 2 then 0x8c5d else if f = .finalizeIntoReset true then 0x83c2 else 0x9438) (64 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x7cca else if f = .digest then 0x78f6 else if f = .reset 2 then 0x8c9c else if f = .finalizeIntoReset true then 0x8401 else 0x9477) (by decide +kernel))

    have instruction := (CrossPageStore.mov_m64_r64_effect_step_any (if f = .slices then 0x107cca else if f = .digest then 0x1078f6 else if f = .reset 2 then 0x108c9c else if f = .finalizeIntoReset true then 0x108401 else 0x109477) 0x48 (by simp [RexWPrefix]) 6 (.base (if f = .digest then 3 else 7) (.d8 24)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    simp only [f, reduceCtorEq, reduceIte] at instruction
    advance_then instruction
    case sub =>
      have subset := codeRange_slice_subset (if f = .slices then 0x107c8e else if f = .digest then 0x1078bf else if f = .reset 2 then 0x108c5d else if f = .finalizeIntoReset true then 0x1083c2 else 0x109438) (bytes .sha512_256 f) (60 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) 4
      simp only [f, reduceCtorEq, reduceIte] at subset ⊢
      apply List.Subset.trans (l₂ := _) ?_ subset
      decide +kernel
    case mid =>
      intro s t hP hH hO
      refine ⟨CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm [f]) ?_ ?_, ?_, ?_⟩
      · x86_norm [f, reduceCtorEq]
        exact hP.writable 24 (by decide +kernel)
      · x86_norm [f, reduceCtorEq]
        exact hP.codeApart 24 (by decide +kernel) (if f = .slices then 0x7cca else if f = .digest then 0x78f6 else if f = .reset 2 then 0x8c9c else if f = .finalizeIntoReset true then 0x8401 else 0x9477) 4 (by decide +kernel)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [f, reduceCtorEq]
        exact hP.codeApart 24 (by decide +kernel) (if f = .slices then 0x7c8e else if f = .digest then 0x78bf else if f = .reset 2 then 0x8c5d else if f = .finalizeIntoReset true then 0x83c2 else 0x9438) (64 - (if f = .digest then 5 else 0) + (if f = .slices ∨ f = .digest then 0 else 3)) (by decide +kernel)
      · exact boundary_ne_program outside (inProgram_of_textOffset (if f = .slices then 0x7cce else if f = .digest then 0x78fa else if f = .reset 2 then 0x8ca0 else if f = .finalizeIntoReset true then 0x8405 else 0x947b) (by decide +kernel))

    try simp only [f] at *
    first
    | have nondigest : f ≠ .digest := by decide
      advance_finish [effect, outputAddress, resetWrites]
    | apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
      intro s t _ hH
      have saved := hH.agrees.read (n := 64) (r := 7) (by x86_norm)
      have writes := hH.writes
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [effect, Variant.pc, Variant.outputEndOffset, Variant.epilogueOffset, Variant.textOffset,
          Extracted.textAddress, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hH.rip
      · simp only [effect, resetWrites, Write.AllHold, outputAddress, reduceCtorEq, reduceIte, List.append_nil, pointerRegister] at writes ⊢
        rcases writes with ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩
        all_goals first | assumption | exact ⟨w0, w1, w2, w3, saved, w4, w5, w6, w7⟩
      · trivial
      · apply hH.agrees.mono
        x86_norm [effect, outputAddress, resetWrites])

theorem machine [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (form : Form := .slices) :
    AdvanceTriple boundary (fun s => Pre v s form)
      (codeRange (v.pc (v.serializeOffset form) form) (bytes v form))
      (Effect.post (fun s => effect v s form)) := by
  cases v
  · exact machine_sha384 boundary outside form
  · exact machine_sha512 boundary outside form
  · exact machine_sha512_224 boundary outside form
  · exact machine_sha512_256 boundary outside form


theorem stack_address [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    (state : State v initial s form) (offset : BitVec 64) :
    rspOf s + offset = stackPtr initial - (BitVec.ofNat 64 form.frameBytes - offset) := by
  change stackPtr s + offset = _
  rw [state.rsp]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]

theorem outputAddress_eq [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {message : ByteArray} (input : Compressed v initial s message form) :
    outputAddress v s form = initial.regValue form.outputRegister := by
  have slot : form ≠ .digest → form.outputSlot ≤ form.frameBytes := by
    intro hd
    cases form <;> simp_all [Form.outputSlot, Form.frameBytes] <;> split <;> omega
  have address (hd : form ≠ .digest) : rspOf s + BitVec.ofNat 64 (form.frameBytes - form.outputSlot) =
      outputSavePointer initial form := by
    change stackPtr s + _ = _
    rw [input.rsp, stack_frame_address initial (by have := slot hd; omega)]
    simp only [outputSavePointer, Nat.sub_sub_self (slot hd)]
  cases form with
  | slices => simpa only [outputAddress, address (by simp), Form.outputRegister, Form.secondOutput, Bool.false_eq_true, reduceIte] using input.outputPointer
  | digest => exact input.outputPointer
  | reset stage =>
    simp only [outputAddress, address (by simp), Form.outputRegister, Form.secondOutput]
    exact input.outputPointer.1.resolve_right (by rintro ⟨h, _⟩; cases h)
  | finalizeIntoReset second =>
    simp only [outputAddress, address (by simp), Form.outputRegister, Form.secondOutput]
    exact input.outputPointer.1.resolve_right (by rintro ⟨h, _⟩; cases h)
  | traitFinalizeIntoReset second =>
    cases second with
    | false =>
      have h := input.traitOutputPointer rfl
      cases v <;> exact h
    | true =>
      simp only [outputAddress, address (by simp), Form.outputRegister, Form.secondOutput, reduceIte]
      exact input.outputPointer.1.resolve_right (by rintro ⟨h, _⟩; cases h)

theorem output_contains [Bindings] {v : Variant} {form : Form} {initial : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) {a : BitVec 64}
    (covered : (Component.mem (initial.regValue form.outputRegister) v.outputBytes).Covers a) :
    (v.outputRegion initial form).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  have bound := ctx.outputInMemory.2.1
  rw [v.outputRegion_eq initial form] at bound ⊢
  exact memoryRegion_contains_add bound (Nat.le_refl _) (Nat.le_refl _) hi

theorem output_writable [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (state : State v initial s form) :
    CrossPageStore.Writable s (initial.regValue form.outputRegister) v.outputBytes := by
  have read : MemReadable s (initial.regValue form.outputRegister) v.outputBytes := by
    apply Common.Encoding.Serialize.readable_of_grow _ state.allocated
    have bound := ctx.outputInMemory.2.1
    have allocated := ctx.outputInMemory.2.2
    rw [v.outputRegion_eq initial form] at bound allocated
    exact memoryRegion_memReadable bound allocated (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨read, tables_of_not_reserved (by cases v <;> decide) read.low ?_⟩
  intro i hi reserved
  exact (ctx.separation.2 (v.outputRegion initial form) (v.outputRegion_mem_writeRegions initial form)).2 _
    (output_contains ctx ⟨i, hi, rfl⟩) (.inr reserved)

theorem output_codeApart [Bindings] {v : Variant} {form : Form} {initial : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) {offset len : Nat} (bound : offset + len ≤ 71757) :
    RangeApart (initial.regValue form.outputRegister) v.outputBytes
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro i hi j hj eq
  apply (ctx.separation.2 (v.outputRegion initial form) (v.outputRegion_mem_writeRegions initial form)).2 _
    (output_contains ctx ⟨i, hi, rfl⟩)
  left
  rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset+j) (by omega)

theorem pre [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Compressed v initial s (message inputs) form) :
    Pre v s form := by
  have capacity : form.frameBytes ≤ (v.routine form).minStackBytes := by
    cases form <;> cases v <;> simp [Form.frameBytes, Variant.routine, Form.stackBytes]
  have stackMem : Stack.region initial (v.routine form).minStackBytes ∈
      (v.writeRegions initial form).toList := by
    cases form <;> simp [Variant.writeRegions, Form.writeRegionCount, Form.twoOutputs, Vector.toList]
  have avoids := (ctx.separation.2 _ stackMem).2
  have writable (offset len : Nat) (bound : offset + len ≤ form.frameBytes) (positive : 0 < len) :
      CrossPageStore.Writable s (rspOf s + BitVec.ofNat 64 offset) len := by
    change CrossPageStore.Writable s (stackPtr s + _) len
    rw [input.rsp]
    exact CrossPageStore.Writable.of_memWritable (stack_frame_writable ctx.stack capacity
      (fun a ha h => avoids a ha (.inr h)) input.allocated bound positive)
  have apart (offset len : Nat) (bound : offset + len ≤ form.frameBytes)
      (off size : Nat) (range : off + size ≤ 71757) :
      RangeApart (rspOf s + BitVec.ofNat 64 offset) len
        (Extracted.textAddress + BitVec.ofNat 64 off) size := by
    change RangeApart (stackPtr s + _) _ _ _
    rw [input.rsp]
    apply stack_frame_codeApart ctx.stack capacity (fun a ha h => avoids a ha (.inl h)) bound
    intro j hj
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset _ (by omega)
  refine ⟨input.rip, ?_, ?_, ?_, ?_, ?_, input.finalizes, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_append, List.mem_map, List.mem_range] at hi
    rcases hi with ⟨j, hj, rfl⟩ | hi
    · change MemReadable s (stackPtr s + _) 8
      rw [input.rsp]
      apply stack_frame_readable ctx.stack capacity input.allocated
      cases form with
      | slices | digest | reset _ => simp only [hashOffset, Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory]; omega
      | finalizeIntoReset second | traitFinalizeIntoReset second =>
        cases second <;> simp only [hashOffset, Form.frameBytes, Form.finalMemory, ResetLayout.finalizeMemory] <;> omega
    · split at hi
      · contradiction
      · simp only [List.mem_singleton] at hi
        subst i
        change MemReadable s (stackPtr s + _) 8
        rw [input.rsp]
        apply stack_frame_readable ctx.stack capacity input.allocated
        cases form <;> simp_all [Form.frameBytes, Form.outputSlot] <;> split <;> omega
  · intro i hi
    rw [outputAddress_eq input]
    exact (output_writable ctx input.toState).add i hi
  · intro i hi off len bound
    rw [outputAddress_eq input]
    exact RangeApart.add_left (h := output_codeApart ctx bound) i hi
  · intro hv
    subst v
    rw [outputAddress_eq input]
    exact (output_writable ctx input.toState).add 24 (by decide)
  · intro hv off len bound
    subst v
    rw [outputAddress_eq input]
    exact RangeApart.add_left (h := output_codeApart ctx bound) 24 (by decide)
  · intro hf
    subst form
    change s.regValue .r14 = stackPtr s + 128
    rw [input.resetHashPointer rfl, input.rsp]
    simp only [Form.frameBytes, ResetLayout.resetMemory, BitVec.ofNat_eq_ofNat]
    bv_omega
  · intro hf i hi
    subst form
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact writable _ 8 (by decide) (by decide)
  · intro hf i hi off len bound
    subst form
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact apart _ 8 (by decide) off len bound
  · intro hf
    subst form
    exact writable 127 1 (by decide) (by decide)
  · intro hf off len bound
    subst form
    exact apart 127 1 (by decide) off len bound
  · intro hf
    subst form
    rw [outputAddress_eq input]
    intro i hi j hj eq
    have out := output_contains ctx ⟨i, hi, rfl⟩
    have inside : (Stack.region initial (v.routine (.reset 1)).minStackBytes).Contains
        (rspOf s + 127 + BitVec.ofNat 64 j).toNat := by
      apply stack_frame_contains ctx.stack capacity (offset := 127) (len := 81) (by decide)
      change (Component.mem (stackPtr initial - 424 + 127) 81).Covers _
      change ∃ k < 81, rspOf s + 127 + BitVec.ofNat 64 j = stackPtr initial - 424 + 127 + BitVec.ofNat 64 k
      refine ⟨j, hj, ?_⟩
      change stackPtr s + _ + _ = _
      rw [input.rsp]
      rfl
    rw [← eq] at inside
    exact (List.pairwise_cons.mp ctx.separation.1).1
      (Stack.region initial (v.routine (.reset 1)).minStackBytes)
      (by simp) _ out inside

set_option maxRecDepth 2048 in
theorem payload [Bindings] {v : Variant} {form : Form} {initial s t : RamState} {inputs : Array Input}
  (ctx : Context v initial inputs form) (input : Compressed v initial s (message inputs) form)
  (output : State v initial t form) (h : (effect v s form).Holds s t)
  :
  (v.outputRegion initial form).HasBytes t.external (v.hash (message inputs)) := by
  obtain ⟨hash, hh, digest⟩ := input.digest
  have source : rspOf s + BitVec.ofNat 64 (hashOffset form) = stackPtr initial - BitVec.ofNat 64 form.finalMemory.hash := by
    have bound : form.finalMemory.hash ≤ form.frameBytes := by
      cases form with
      | slices | digest | reset _ => simp [Form.finalMemory, Form.frameBytes, ResetLayout.resetMemory]
      | finalizeIntoReset second | traitFinalizeIntoReset second => cases second <;> decide
    change stackPtr s + _ = _
    rw [input.rsp, stack_frame_address initial (by unfold hashOffset; omega)]
    simp only [hashOffset, Nat.sub_sub_self bound]
  have destination : outputAddress v s form = initial.regValue form.outputRegister := outputAddress_eq input
  have values : ∀ j < 8, memLoad s.external
      (rspOf s + BitVec.ofNat 64 (hashOffset form) + BitVec.ofNat 64 (8*j)) 64 = hash[j]!.toBitVec := by
    intro j hj
    apply Common.Memory.memLoad_of_loadBytes64
    rw [source]
    exact hh.2 j hj
  apply Serialize.compressed_output ctx input output hh.1 digest
  · intro j hj
    change memLoad t.external (initial.regValue form.outputRegister + BitVec.ofNat 64 (8*j)) 64 = _
    rw [← destination, ← values j (by cases v <;> simp only [Variant.outputBytes] at hj <;> omega)]
    have stores := h.writes
    cases v with
    | sha384 =>
      have bound : j < 6 := by change 8 * (j + 1) ≤ 48 at hj; omega
      simp only [effect, List.cons_append, List.nil_append, Write.AllHold, Operand.read] at stores
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using (Write.allHold_iff.mp (stores.2.2.2.2.2.2.2.2.2.2.2.2) _ (List.mem_cons_self))
    | sha512 =>
      have bound : j < 8 := by change 8 * (j + 1) ≤ 64 at hj; omega
      simp only [effect, List.cons_append, List.nil_append, Write.AllHold, Operand.read] at stores
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using (Write.allHold_iff.mp (stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) _ (List.mem_cons_self))
    | sha512_224 =>
      have bound : j < 3 := by change 8 * (j + 1) ≤ 28 at hj; omega
      simp only [effect, List.cons_append, List.nil_append, Write.AllHold, Operand.read] at stores
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with
        rfl | rfl | rfl
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.1
    | sha512_256 =>
      have bound : j < 4 := by change 8 * (j + 1) ≤ 32 at hj; omega
      simp only [effect, List.cons_append, List.nil_append, Write.AllHold, Operand.read] at stores
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with
        rfl | rfl | rfl | rfl
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.1
      · skip <;> simpa only [rspOf, Operand.read, BitVec.ofNat_add, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using (Write.allHold_iff.mp (stores.2.2.2.2.2.2.2.2) _ (List.mem_cons_self))
  · intro hv i hi
    subst v
    have stores := h.writes
    simp only [effect, List.cons_append, List.nil_append, Write.AllHold, Operand.read] at stores
    have allocated := (output_writable ctx output).toMemReadable.mem
    have wordBytes := Bytes.of_memLoad (n := 32) (a := outputAddress .sha512_224 s form + 24)
      (m := t.external) (by
        intro j hj
        rw [destination]
        simpa only [reduceIte, BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using allocated (24+j) (by
          change 24+j < 28
          change j < 4 at hj
          omega))
    have last := Write.allHold_iff.mp (stores.2.2.2.2.2.2.2.2) _ (List.mem_cons_self)
    change memLoad t.external (outputAddress .sha512_224 s form + 24) 32 = _ at last
    rw [last] at wordBytes
    skip
    all_goals
      have value := values 3 (by decide)
      simp only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] at value
      simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] at wordBytes
      rw [value] at wordBytes
      have byte := wordBytes i hi
      rw [destination] at byte
      simp only [storedByte_eq_extract,
        BitVec.extractLsb'_setWidth_of_le (by omega : 8 * i + 8 ≤ 32)] at byte
      simpa only [storedByte_eq_extract, BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using byte

def components (v : Variant) (initial : RamState) (form : Form := .slices) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .mem (initial.regValue form.outputRegister) v.outputBytes,
    .mem (stackPtr initial - 297) 81, .rip]

theorem output_covered [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {message : ByteArray} (input : Compressed v initial s message form) {offset len : Nat}
    (bound : offset + len ≤ v.outputBytes) {a : BitVec 64}
    (ha : (Component.mem (outputAddress v s form + BitVec.ofNat 64 offset) len).Covers a) :
    ∃ c ∈ components v initial form, c.Covers a := by
  obtain ⟨i, hi, rfl⟩ := ha
  refine ⟨.mem (initial.regValue form.outputRegister) v.outputBytes, by simp [components],
    offset+i, by omega, ?_⟩
  rw [outputAddress_eq input, BitVec.ofNat_add, BitVec.add_assoc]

theorem reset_covered [Bindings] {v : Variant} {initial s : RamState}
    {message : ByteArray} (input : Compressed v initial s message (.reset 1)) {offset len : Nat}
    (start : 127 ≤ offset) (bound : offset + len ≤ 208) {a : BitVec 64}
    (ha : (Component.mem (rspOf s + BitVec.ofNat 64 offset) len).Covers a) :
    ∃ c ∈ components v initial (.reset 1), c.Covers a := by
  obtain ⟨i, hi, rfl⟩ := ha
  refine ⟨.mem (stackPtr initial - 297) 81, by simp [components], offset-127+i, by omega, ?_⟩
  change stackPtr s + _ + _ = _
  rw [input.rsp]
  have split : offset = 127 + (offset-127) := by omega
  rw [split, BitVec.ofNat_add, BitVec.ofNat_add]
  simp only [Form.frameBytes, BitVec.ofNat_eq_ofNat]
  bv_omega


set_option maxHeartbeats 1000000 in
theorem frame [Bindings] {v : Variant} {form : Form} {initial s t : RamState}
    {message : ByteArray} (input : Compressed v initial s message form)
    (h : (effect v s form).Holds s t) : AgreesExcept (components v initial form) s t := by
  apply Common.Encoding.Serialize.agrees_of_footprint h.agrees
  · intro c hc hm
    by_cases hr : form = .reset 1
    · subst form
      cases v with
      | sha384 =>
        simp only [effect, resetWrites, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals simp_all [components, Component.isMem]
      | sha512 =>
        simp only [effect, resetWrites, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals simp_all [components, Component.isMem]
      | sha512_224 =>
        simp only [effect, resetWrites, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals simp_all [components, Component.isMem]
      | sha512_256 =>
        simp only [effect, resetWrites, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals simp_all [components, Component.isMem]
    · skip
      cases v with
      | sha384 =>
        simp only [effect, resetWrites, hr, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals simp_all [components, Component.isMem]
      | sha512 =>
        simp only [effect, resetWrites, hr, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals simp_all [components, Component.isMem]
      | sha512_224 =>
        simp only [effect, resetWrites, hr, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals simp_all [components, Component.isMem]
      | sha512_256 =>
        simp only [effect, resetWrites, hr, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals simp_all [components, Component.isMem]
  · intro c hc a ha
    by_cases hr : form = .reset 1
    · subst form
      cases v with
      | sha384 =>
        simp only [effect, resetWrites, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals try exact ha.elim
        · exact output_covered input (offset := 0) (len := 8) (by decide) ha
        · exact output_covered input (offset := 8) (len := 8) (by decide) ha
        · exact output_covered input (offset := 16) (len := 8) (by decide) ha
        · exact output_covered input (offset := 24) (len := 8) (by decide) ha
        · exact output_covered input (offset := 32) (len := 8) (by decide) ha
        · exact output_covered input (offset := 40) (len := 8) (by decide) ha
        · exact reset_covered input (offset := 128) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 136) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 144) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 152) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 160) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 168) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 176) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 184) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 192) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 200) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 127) (len := 1) (by decide) (by decide) ha
      | sha512 =>
        simp only [effect, resetWrites, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals try exact ha.elim
        · exact output_covered input (offset := 0) (len := 8) (by decide) ha
        · exact output_covered input (offset := 8) (len := 8) (by decide) ha
        · exact output_covered input (offset := 16) (len := 8) (by decide) ha
        · exact output_covered input (offset := 24) (len := 8) (by decide) ha
        · exact output_covered input (offset := 32) (len := 8) (by decide) ha
        · exact output_covered input (offset := 40) (len := 8) (by decide) ha
        · exact output_covered input (offset := 48) (len := 8) (by decide) ha
        · exact output_covered input (offset := 56) (len := 8) (by decide) ha
        · exact reset_covered input (offset := 128) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 136) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 144) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 152) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 160) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 168) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 176) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 184) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 192) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 200) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 127) (len := 1) (by decide) (by decide) ha
      | sha512_224 =>
        simp only [effect, resetWrites, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals try exact ha.elim
        · exact output_covered input (offset := 0) (len := 8) (by decide) ha
        · exact output_covered input (offset := 8) (len := 8) (by decide) ha
        · exact output_covered input (offset := 16) (len := 8) (by decide) ha
        · exact output_covered input (offset := 24) (len := 4) (by decide) ha
        · exact reset_covered input (offset := 128) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 136) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 144) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 152) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 160) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 168) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 176) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 184) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 192) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 200) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 127) (len := 1) (by decide) (by decide) ha
      | sha512_256 =>
        simp only [effect, resetWrites, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals try exact ha.elim
        · exact output_covered input (offset := 0) (len := 8) (by decide) ha
        · exact output_covered input (offset := 8) (len := 8) (by decide) ha
        · exact output_covered input (offset := 16) (len := 8) (by decide) ha
        · exact output_covered input (offset := 24) (len := 8) (by decide) ha
        · exact reset_covered input (offset := 128) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 136) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 144) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 152) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 160) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 168) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 176) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 184) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 192) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 200) (len := 8) (by decide) (by decide) ha
        · exact reset_covered input (offset := 127) (len := 1) (by decide) (by decide) ha
    · skip
      cases v with
      | sha384 =>
        simp only [effect, resetWrites, hr, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals try exact ha.elim
        · exact output_covered input (offset := 0) (len := 8) (by decide) ha
        · exact output_covered input (offset := 8) (len := 8) (by decide) ha
        · exact output_covered input (offset := 16) (len := 8) (by decide) ha
        · exact output_covered input (offset := 24) (len := 8) (by decide) ha
        · exact output_covered input (offset := 32) (len := 8) (by decide) ha
        · exact output_covered input (offset := 40) (len := 8) (by decide) ha
      | sha512 =>
        simp only [effect, resetWrites, hr, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals try exact ha.elim
        · exact output_covered input (offset := 0) (len := 8) (by decide) ha
        · exact output_covered input (offset := 8) (len := 8) (by decide) ha
        · exact output_covered input (offset := 16) (len := 8) (by decide) ha
        · exact output_covered input (offset := 24) (len := 8) (by decide) ha
        · exact output_covered input (offset := 32) (len := 8) (by decide) ha
        · exact output_covered input (offset := 40) (len := 8) (by decide) ha
        · exact output_covered input (offset := 48) (len := 8) (by decide) ha
        · exact output_covered input (offset := 56) (len := 8) (by decide) ha
      | sha512_224 =>
        simp only [effect, resetWrites, hr, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals try exact ha.elim
        · exact output_covered input (offset := 0) (len := 8) (by decide) ha
        · exact output_covered input (offset := 8) (len := 8) (by decide) ha
        · exact output_covered input (offset := 16) (len := 8) (by decide) ha
        · exact output_covered input (offset := 24) (len := 4) (by decide) ha
      | sha512_256 =>
        simp only [effect, resetWrites, hr, reduceIte, Effect.components, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, Write.component, Operand.component] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
        all_goals try exact ha.elim
        · exact output_covered input (offset := 0) (len := 8) (by decide) ha
        · exact output_covered input (offset := 8) (len := 8) (by decide) ha
        · exact output_covered input (offset := 16) (len := 8) (by decide) ha
        · exact output_covered input (offset := 24) (len := 8) (by decide) ha

theorem output_stack_disjoint [Bindings] {v : Variant} {form : Form} {initial : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs form) :
    (v.outputRegion initial form).Disjoint (Stack.region initial (v.routine form).minStackBytes) := by
  have separated := ctx.separation.1
  cases form with
  | slices | digest => exact List.pairwise_pair.mp separated
  | reset stage =>
    by_cases h : stage.val = 2 <;>
      simp_all [Variant.writeRegions, Variant.outputRegion, Form.secondOutput, Form.writeRegionCount,
        Form.twoOutputs, Vector.toList, List.pairwise_cons]
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    cases second <;> simp_all [Variant.writeRegions, Variant.outputRegion, Form.secondOutput,
      Form.writeRegionCount, Form.twoOutputs, Vector.toList, List.pairwise_cons]

theorem r12_preserved [Bindings] {v : Variant} {form : Form} {initial s t : RamState}
    (h : AgreesExcept (components v initial form) s t) : t.regValue .r12 = s.regValue .r12 := by
  exact h.read (n := 64) (r := 12) (by simp [components])

theorem slot_preserved [Bindings] {v : Variant} {form : Form} {initial s t : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs form)
    (h : AgreesExcept (components v initial form) s t) (offset : Nat)
    (capacity : offset ≤ (v.routine form).minStackBytes)
    (apart : offset ≤ 208 ∨ 305 ≤ offset) (size : 8 ≤ offset) :
    memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  congr 1
  apply h.byte
  intro c hc covered
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  · exact output_stack_disjoint ctx _ (output_contains ctx covered)
      (stackRegion_contains_sub ctx.stack.2.2.1 capacity size ⟨i, hi, rfl⟩)
  · obtain ⟨j, hj, eq⟩ := covered
    have offbound : offset < 2^64 := by
      have small : (v.routine form).minStackBytes < 2^64 := by
        cases form <;> cases v <;> simp [Variant.routine, Form.stackBytes]
      omega
    change i < 8 at hi
    bv_omega

theorem reset_window_contains [Bindings] {v : Variant} {form : Form} {initial : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs form) {a : BitVec 64}
    (ha : (Component.mem (stackPtr initial - 297) 81).Covers a) :
    (Stack.region initial (v.routine form).minStackBytes).Contains a.toNat := by
  exact stackRegion_contains_sub ctx.stack.2.2.1
    (by cases form <;> cases v <;> simp [Variant.routine, Form.stackBytes]) (by decide) ha

theorem narrow_frame [Bindings] {v : Variant} {form : Form} {initial s t : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs form)
    (h : AgreesExcept (components v initial form) s t) :
    MemoryWriteFrame s t #v[v.outputRegion initial form, Stack.region initial (v.routine form).minStackBytes] := by
  intro a outside
  apply h.byte
  intro c hc covered
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  · exact outside _ (by simp) (output_contains ctx covered)
  · exact outside _ (by simp) (reset_window_contains ctx covered)

theorem saved_contains [Bindings] {v : Variant} {form : Form} {initial : RamState} {inputs : Array Input}
  (ctx : Context v initial inputs form) {a : BitVec 64}
  (ha : (Component.mem (stackPtr initial - 48) 56).Covers a)
  :
  (Stack.region initial (v.routine form).minStackBytes).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := ha
  apply memoryRegion_contains_add ctx.stack.1 (len := 56) _ _ hi
  · change (Stack.region initial (v.routine form).minStackBytes).start ≤
      (stackPtr initial - BitVec.ofNat 64 48).toNat
    rw [stack_valid_sub_toNat ctx.stack (offset := 48) (by cases form <;> cases v <;> simp [Variant.routine, Form.stackBytes])]
    change (stackPtr initial).toNat - (v.routine form).minStackBytes ≤ (stackPtr initial).toNat - 48
    have : 48 ≤ (v.routine form).minStackBytes := by cases form <;> cases v <;> simp [Variant.routine, Form.stackBytes]
    omega
  · change (stackPtr initial - BitVec.ofNat 64 48).toNat + 56 ≤ _
    rw [stack_region_end, stack_valid_sub_toNat ctx.stack (offset := 48) (by cases form <;> cases v <;> simp [Variant.routine, Form.stackBytes])]
    have reserve : 48 ≤ (v.routine form).minStackBytes := by cases form <;> cases v <;> simp [Variant.routine, Form.stackBytes]
    have bounds := stack_valid_bounds ctx.stack
    have budget : (v.routine form).minStackBytes ≤ (stackPtr initial).toNat := ctx.stack.2.2.1
    omega

theorem state [Bindings] {v : Variant} {form : Form} {initial s t : RamState}
    {inputs : Array Input} {fuel : Nat} (ctx : Context v initial inputs form)
    (input : State v initial s form) (run : Advances (returnBoundary initial) fuel s t)
    (ready : ReadyToStep t) (h : AgreesExcept (components v initial form) s t) :
    State v initial t form := by
  have out := ReturnState.of_agrees (ReturnState.of_state input) ctx run ready h
    (by
      intro c hc a ha
      simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      · exact ⟨v.outputRegion initial form, Vector.mem_toList_iff.mp (v.outputRegion_mem_writeRegions initial form), output_contains ctx ha⟩
      · refine ⟨Stack.region initial (v.routine form).minStackBytes, ?_, reset_window_contains ctx ha⟩
        apply Vector.mem_toList_iff.mp
        cases form <;> simp [Variant.writeRegions, Form.writeRegionCount, Form.twoOutputs, Vector.toList])
    form.frameBytes ((h.read (n := 64) (r := 4) (by simp [components])).trans input.rsp)
    (by
      intro c hc a ha covered
      simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact covered.elim
      · exact output_stack_disjoint ctx a.toNat (output_contains ctx covered)
          (saved_contains ctx ha)
      · obtain ⟨i, hi, eqi⟩ := ha
        obtain ⟨j, hj, eqj⟩ := covered
        bv_omega)
    (by simp [components])
  exact ⟨out.execution, out.machine, out.loaded, out.allocated, out.saved,
    out.directionFlag, out.frame, (h.read (n := 64) (r := 4) (by simp [components])).trans input.rsp⟩

theorem preserved [Bindings] {v : Variant} {form : Form} {initial s t : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs form)
    (input : Preserved v initial s form) (current : State v initial t form)
    (h : AgreesExcept (components v initial form) s t) : Preserved v initial t form := by
  have slot (offset : Nat) (member : offset ∈ [184,192,200,208,400,408,608,616,624,632]) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    apply slot_preserved ctx h
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | decide | cases form <;> cases v <;> simp [Variant.routine, Form.stackBytes]
  have out := slot form.outputSlot (by cases form <;> simp [Form.outputSlot] <;> split <;> simp_all)
  have second := slot form.secondOutputSlot (by cases form <;> simp [Form.secondOutputSlot])
  have pointer := slot form.pointerSlot (by cases form <;> simp [Form.pointerSlot])
  have length := slot form.lengthSlot (by cases form <;> simp [Form.lengthSlot])
  have rbp : t.regValue .rbp = s.regValue .rbp := h.read (n := 64) (r := 5) (by simp [components])
  have rbx : t.regValue .rbx = s.regValue .rbx := h.read (n := 64) (r := 3) (by simp [components])
  have r13 : t.regValue .r13 = s.regValue .r13 := h.read (n := 64) (r := 13) (by simp [components])
  refine ⟨current, ?_, ?_, ?_⟩
  · cases form with
    | slices => exact out.trans input.outputPointer
    | digest => exact rbx.trans input.outputPointer
    | reset stage | finalizeIntoReset second | traitFinalizeIntoReset second =>
      have regs : t.regValue (if v = .sha512 then .r13 else .rbp) =
          s.regValue (if v = .sha512 then .r13 else .rbp) := by split <;> assumption
      simpa only [outputSavePointer, out, second, regs] using input.outputPointer
  · cases form <;> first | trivial | exact pointer.trans input.pointerTable
  · cases form <;> first | trivial | exact length.trans input.lengthTable

theorem reset_stores [Bindings] {v : Variant} {initial s t : RamState} {message : ByteArray}
    (input : Compressed v initial s message (.reset 1))
    (h : (effect v s (.reset 1)).Holds s t) :
    Write.AllHold t (Dispatch.Store.suffixEffect v t (.reset 2)).writes := by
  have rsp : rspOf t = rspOf s := (frame input h).read (n := 64) (r := 4) (by simp [components])
  have tail : Write.AllHold t (resetWrites v s (.reset 1)) := by
    apply Write.allHold_iff.mpr
    intro w hw
    apply Write.allHold_iff.mp h.writes w
    cases v <;> exact List.mem_append_right _ hw
  simp only [resetWrites, reduceIte, Write.AllHold] at tail
  dsimp only [Dispatch.Store.suffixEffect, Dispatch.Store.slotOffset]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  rw [rsp]
  simp only [Write.AllHold]
  rcases tail with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  exact ⟨h7,h6,h5,h4,h3,h2,h1,h0,h9,h8,h10⟩

theorem r15_preserved [Bindings] {v : Variant} {form : Form} {initial s t : RamState}
    (h : AgreesExcept (components v initial form) s t) : t.regValue .r15 = s.regValue .r15 := by
  exact h.read (n := 64) (r := 15) (by simp [components])


theorem stage [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Compressed v initial s (message inputs) form) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Preserved v initial t form ∧
      t.RIP = v.pc (v.outputEndOffset form) form ∧
      (v.outputRegion initial form).HasBytes t.external (v.hash (message inputs)) ∧
      MemoryWriteFrame s t #v[v.outputRegion initial form, Stack.region initial (v.routine form).minStackBytes] ∧
      AgreesExcept (components v initial form) s t ∧
      (form = .reset 1 → Write.AllHold t (Dispatch.Store.suffixEffect v t (.reset 2)).writes) := by
  obtain ⟨fuel, t, execution, ready, _, result⟩ := machine v (returnBoundary initial)
    ((valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2) form s
    (supportedMachine_readyToStep input.machine) (code input.loaded) (pre ctx input)
  have agrees := frame input result
  have current := state ctx input.toState execution ready agrees
  refine ⟨fuel, t, execution, preserved ctx input.toPreserved current agrees,
    result.rip, payload ctx input current result, narrow_frame ctx agrees, agrees, ?_⟩
  intro hf
  subst form
  exact reset_stores input result

theorem outputEnd_eq_epilogue (v : Variant) {form : Form} (terminal : form.isTerminal) :
    v.outputEndOffset form = v.epilogueOffset form := by
  cases form with
  | slices | digest => rfl
  | reset n =>
    have hn : n = 2 := Fin.ext terminal
    subst n
    cases v <;> rfl
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    cases second
    · contradiction
    · cases v <;> rfl

theorem run_preserving_frame [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Compressed v initial s (message inputs) form)
    (terminal : form.isTerminal := by first | assumption | trivial) :
    ∃ final, FinishResult v initial final inputs form ∧
      MemoryWriteFrame s final #v[v.outputRegion initial form, Stack.region initial (v.routine form).minStackBytes] := by
  obtain ⟨fuel, t, _, current, rip, bytes, writes, _, _⟩ := stage ctx input
  rw [outputEnd_eq_epilogue v terminal] at rip
  have output : v.readOutput initial t form = .ok (v.digest (message inputs)) := by
    apply readOutput_of_hasBytes
    rw [← hash_eq_digest]
    exact bytes
  obtain ⟨final, result, unchanged⟩ := Wrapper512.run_preserving_memory ctx current.toState rip output
  refine ⟨final, result, ?_⟩
  intro a outside
  rw [unchanged]
  exact writes a outside

theorem run [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Compressed v initial s (message inputs) form)
    (terminal : form.isTerminal := by first | assumption | trivial) :
    ∃ final, FinishResult v initial final inputs form := by
  obtain ⟨final, result, _⟩ := run_preserving_frame ctx input terminal
  exact ⟨final, result⟩

end Sha2.Proofs.Wrapper512.Finish.Output
