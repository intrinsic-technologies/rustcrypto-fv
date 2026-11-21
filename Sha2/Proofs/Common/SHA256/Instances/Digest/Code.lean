import Sha2.Proofs.Wrapper.Variant
import Sha2.Proofs.Common.SHA256.Blocks.Digest.Prepare
import Sha2.Proofs.Common.SHA256.Blocks.Digest.Normalize
import Sha2.Proofs.Common.SHA256.Serialize.Blocks
import Sha2.Proofs.Common.Machine.Prologue
import Sha2.Proofs.Common.Instructions.RepMovsq.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Digest

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

inductive Segment where
  | prologue | header | cloneSetup | clone | normalize | loadSwap | store | epilogue | ret

def Segment.entry (segment : Segment) (v : Wrapper.Variant := .sha256) : Nat :=
  match v, segment with
  | .sha224, .loadSwap => 0x100259
  | .sha224, .store => 0x100287
  | .sha224, .epilogue => 0x10029d
  | .sha224, .ret => 0x1002ad
  | v, segment => (match segment with
  | .prologue => 0x101bf0
  | .header => 0x101c00
  | .cloneSetup => 0x101cd2
  | .clone => 0x101ce2
  | .normalize => 0x101ce5
  | .loadSwap => 0x101e49
  | .store => 0x101e7f
  | .epilogue => 0x101e99
  | .ret => 0x101ea9) - (match v with | .sha224 => 0x1bf0 | .sha256 => 0)

def Segment.pc (segment : Segment) (v : Wrapper.Variant := .sha256) : BitVec 64 :=
  BitVec.ofNat 64 (segment.entry v)

def routine (v : Wrapper.Variant := .sha256) : Routine where
  entryAddress := Segment.prologue.pc v
  minStackBytes := 784
  outputBytes := v.outputBytes

def Segment.bytes (segment : Segment) (v : Wrapper.Variant := .sha256) : List UInt8 :=
  match segment with
  | .prologue => Prologue.bytes .five272
  | .header => Blocks.Digest.Header.bytes
  | .cloneSetup => Blocks.Digest.CloneSetup.bytes
  | .clone => [0xf3,0x48,0xa5]
  | .normalize => Blocks.Digest.Normalize.bytes
  | .loadSwap => Serialize.bytes (.loadSwap .at64 (v == .sha224))
  | .store => Serialize.bytes (.store .rbx (v == .sha224))
  | .epilogue => Epilogue.bytes .five272
  | .ret => [0xc3]

theorem Segment.inside (segment : Segment) (v : Wrapper.Variant := .sha256) :
    BlockInProgram (segment.pc v) (segment.bytes v).length := by
  have pc : segment.pc v = Extracted.textAddress + BitVec.ofNat 64 (segment.entry v - 0x100000) := by
    cases v <;> cases segment <;> decide +kernel
  rw [pc]
  apply blockInProgram_of_textOffset
  cases v <;> cases segment <;> decide +kernel

theorem Segment.code (segment : Segment) {s : RamState} (loaded : ProgramLoaded s) (v : Wrapper.Variant := .sha256) :
    CodeIn (codeRange (segment.pc v) (segment.bytes v)) s := by
  have pc : segment.pc v = Extracted.textAddress + BitVec.ofNat 64 (segment.entry v - 0x100000) := by
    cases v <;> cases segment <;> decide +kernel
  rw [pc]
  apply programText_slice (programLoaded_codeIn loaded)
  · cases v <;> cases segment <;> decide +kernel
  · cases v <;> cases segment <;> decide +kernel

end Sha2.Proofs.Common.SHA256.Instances.Digest
