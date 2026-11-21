import Sha2.Proofs.Common.SHA256.Initialize.Contract

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256.Initialize

inductive Initialization where
  | digest
  | resetInitial
  | resetDiscarded
  | resetOutput
  | finalizeInitial
  | finalizeReset
  | traitInitial
  | traitReset

def Initialization.entry (occ : Initialization)
    (v : Sha2.Proofs.Wrapper.Variant := .sha256) : Nat :=
  match v, occ with
  | .sha224, .digest => 0x100019
  | .sha224, .resetInitial => 0x100d64
  | .sha224, .resetDiscarded => 0x100ec0
  | .sha224, .resetOutput => 0x1011a9
  | .sha224, .finalizeInitial => 0x10067f
  | .sha224, .finalizeReset => 0x1009a4
  | .sha224, .traitInitial => 0x1014fc
  | .sha224, .traitReset => 0x101887
  | .sha256, .digest => 0x101c09
  | .sha256, .resetInitial => 0x102994
  | .sha256, .resetDiscarded => 0x102af0
  | .sha256, .resetOutput => 0x102de1
  | .sha256, .finalizeInitial => 0x10228f
  | .sha256, .finalizeReset => 0x1025c0
  | .sha256, .traitInitial => 0x10314c
  | .sha256, .traitReset => 0x1034e7

def Initialization.bufferOffset : Initialization → Nat
  | .digest => 168
  | .resetInitial | .resetDiscarded | .resetOutput => 0
  | .finalizeInitial | .finalizeReset => 8
  | .traitInitial | .traitReset => 112

def Initialization.hashBase : Initialization → BitVec 4
  | .resetDiscarded => 0
  | .resetOutput | .finalizeReset => 3
  | .traitReset => 5
  | _ => 4

def Initialization.temporary (occ : Initialization) (i : Fin 4)
    (v : Sha2.Proofs.Wrapper.Variant := .sha256) : BitVec 4 :=
  match occ with
  | .resetInitial => (#[7,6,2,1] : Array (BitVec 4))[i.val]!
  | .resetDiscarded => 1
  | .resetOutput => if v = .sha224 then 10 else 11
  | _ => 0

def initAddress (base : BitVec 4) (offset : Nat) : Address :=
  ⟨base, if offset = 0 ∧ regLow base ≠ 5 then .none
    else if offset < 128 then .d8 (BitVec.ofNat 8 offset)
    else .d32 (BitVec.ofNat 32 offset)⟩

def Initialization.word (occ : Initialization) (i : Fin 4)
    (v : Sha2.Proofs.Wrapper.Variant := .sha256) : WordStore v :=
  { index := i
    register := occ.temporary i v
    destination := initAddress occ.hashBase
      ((if occ.hashBase = 4 then occ.bufferOffset + 64 else 0) + 8 * i.val)
    loadConstant := true }

def Initialization.layout (occ : Initialization)
    (v : Sha2.Proofs.Wrapper.Variant := .sha256) : Layout v :=
  { start := BitVec.ofNat 64 (occ.entry v)
    words := #v[occ.word ⟨3, by decide⟩ v, occ.word ⟨2, by decide⟩ v,
      occ.word ⟨1, by decide⟩ v, occ.word ⟨0, by decide⟩ v]
    clear := ⟨initAddress 4 (occ.bufferOffset + 96), initAddress 4 (occ.bufferOffset + 63)⟩ }

theorem Initialization.valid (occ : Initialization)
    (v : Sha2.Proofs.Wrapper.Variant := .sha256) : (occ.layout v).Valid := by
  cases v <;> cases occ <;> constructor <;> decide +kernel

theorem Initialization.inside (occ : Initialization)
    (v : Sha2.Proofs.Wrapper.Variant := .sha256) :
    BlockInProgram (occ.layout v).start (occ.layout v).bytes.length := by
  have pc : (occ.layout v).start = Extracted.textAddress + BitVec.ofNat 64 (occ.entry v - 0x100000) := by
    cases v <;> cases occ <;> decide +kernel
  rw [pc]
  apply blockInProgram_of_textOffset
  cases v <;> cases occ <;> decide +kernel

theorem Initialization.code (occ : Initialization) {s : RamState} (loaded : ProgramLoaded s)
    (v : Sha2.Proofs.Wrapper.Variant := .sha256) :
    CodeIn (codeRange (occ.layout v).start (occ.layout v).bytes) s := by
  have pc : (occ.layout v).start = Extracted.textAddress + BitVec.ofNat 64 (occ.entry v - 0x100000) := by
    cases v <;> cases occ <;> decide +kernel
  rw [pc]
  apply programText_slice (programLoaded_codeIn loaded)
  · cases v <;> cases occ <;> decide +kernel
  · cases v <;> cases occ <;> decide +kernel

end Sha2.Proofs.Common.SHA256.Instances
