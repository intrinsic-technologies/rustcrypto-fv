import Sha2.Proofs.Wrapper.Variant
import Sha2.Proofs.Common.SHA256.Blocks.Digest.Select

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Digest

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256.Absorb.Direct

def absorbEntry (stage : Stage) (v : Wrapper.Variant := .sha256) : Nat :=
  (match stage with
  | .select => 0x101c65
  | .smallSetup => 0x101c6b
  | .smallStore => 0x101c7c
  | .bulkSetup => 0x101c86
  | .bulkTail => 0x101cb6
  | .tailSetup => 0x101cbe) - (if v = .sha224 then 0x1bf0 else 0)

def absorb (v : Wrapper.Variant := .sha256) : Layout :=
  { initialHash := v.initialHash
    frameBytes := 312
    bufferOffset := 168
    pc := fun stage => BitVec.ofNat 64 (absorbEntry stage v)
    bytes := Blocks.Digest.Absorb.bytes
    smallCall := ⟨BitVec.ofNat 64 (0x101c76 - (if v = .sha224 then 0x1bf0 else 0)),
      .memory (.rip (if v = .sha224 then 0x1001f4 else 0xfe604))⟩
    bulkCall := ⟨BitVec.ofNat 64 (0x101cb1 - (if v = .sha224 then 0x1bf0 else 0)),
      .relative (if v = .sha224 then 0xb41a else 0x982a)⟩
    tailCall := ⟨BitVec.ofNat 64 (0x101ccc - (if v = .sha224 then 0x1bf0 else 0)),
      .memory (.rip (if v = .sha224 then 0x10019e else 0xfe5ae))⟩
    exit := BitVec.ofNat 64 (0x101cd2 - (if v = .sha224 then 0x1bf0 else 0)) }

theorem absorb_wellFormed (v : Wrapper.Variant := .sha256) : WellFormed (absorb v) 784 := by
  cases v <;> constructor <;> decide +kernel

theorem absorb_flow (v : Wrapper.Variant := .sha256) : Flow (absorb v) := by
  refine ⟨by cases v <;> decide +kernel, by cases v <;> decide +kernel, by cases v <;> decide +kernel, ?_, ?_⟩
  · intro call member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨(if v = .sha224 then 0x1001f4 else 0xfe604), rfl, by cases v <;> decide +kernel⟩
    · exact ⟨(if v = .sha224 then 0x10019e else 0xfe5ae), rfl, by cases v <;> decide +kernel⟩
  · exact ⟨(if v = .sha224 then 0xb41a else 0x982a), rfl, by cases v <;> decide +kernel⟩

theorem absorb_inside (stage : Stage) (v : Wrapper.Variant := .sha256) :
    BlockInProgram ((absorb v).pc stage) ((absorb v).bytes stage).length := by
  have pc : (absorb v).pc stage = Extracted.textAddress + BitVec.ofNat 64 (absorbEntry stage v - 0x100000) := by
    cases v <;> cases stage <;> decide +kernel
  rw [pc]
  apply blockInProgram_of_textOffset
  cases v <;> cases stage <;> decide +kernel

theorem absorb_codeFacts (v : Wrapper.Variant := .sha256) : CodeFacts (absorb v) := by
  constructor
  · intro stage s loaded
    have pc : (absorb v).pc stage = Extracted.textAddress + BitVec.ofNat 64 (absorbEntry stage v - 0x100000) := by
      cases v <;> cases stage <;> decide +kernel
    rw [pc]
    apply programText_slice (programLoaded_codeIn loaded)
    · cases v <;> cases stage <;> decide +kernel
    · cases v <;> cases stage <;> decide +kernel
  · intro call member s loaded
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · cases v with
      | sha224 => exact programText_slice (programLoaded_codeIn loaded) 0x86 _ (by decide +kernel) (by decide +kernel)
      | sha256 => exact programText_slice (programLoaded_codeIn loaded) 0x1c76 _ (by decide +kernel) (by decide +kernel)
    · cases v with
      | sha224 => exact programText_slice (programLoaded_codeIn loaded) 0xc1 _ (by decide +kernel) (by decide +kernel)
      | sha256 => exact programText_slice (programLoaded_codeIn loaded) 0x1cb1 _ (by decide +kernel) (by decide +kernel)
    · cases v with
      | sha224 => exact programText_slice (programLoaded_codeIn loaded) 0xdc _ (by decide +kernel) (by decide +kernel)
      | sha256 => exact programText_slice (programLoaded_codeIn loaded) 0x1ccc _ (by decide +kernel) (by decide +kernel)
  · intro stage
    simpa only [BitVec.add_zero] using absorb_inside stage (v := v) 0 (Nat.zero_le _)
  · intro call member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · cases v with
      | sha224 => exact inProgram_of_textOffset 0x86 (by decide +kernel)
      | sha256 => exact inProgram_of_textOffset 0x1c76 (by decide +kernel)
    · cases v with
      | sha224 => exact inProgram_of_textOffset 0xc1 (by decide +kernel)
      | sha256 => exact inProgram_of_textOffset 0x1cb1 (by decide +kernel)
    · cases v with
      | sha224 => exact inProgram_of_textOffset 0xdc (by decide +kernel)
      | sha256 => exact inProgram_of_textOffset 0x1ccc (by decide +kernel)
  · cases v with
    | sha224 => exact inProgram_of_textOffset 0xe2 (by decide +kernel)
    | sha256 => exact inProgram_of_textOffset 0x1cd2 (by decide +kernel)

theorem absorb_blockContracts [Bindings] {v : Wrapper.Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) : BlockContracts (absorb v) boundary := by
  constructor
  intro stage sp s ready code pre
  have pre' : Blocks.Digest.Absorb.Pre ((absorb v).pc stage) stage s := by
    have rsp : rspOf s = sp := pre.rsp
    refine ⟨pre.rip, ?_, ?_, ?_, ?_⟩
    · rw [rsp]
      simpa [Layout.buffer, absorb, BitVec.add_assoc] using pre.tailWritable.toMemWritable
    · rw [rsp]
      simpa [Layout.buffer, absorb, BitVec.add_assoc] using pre.counterWritable
    · rw [rsp]
      simpa [Layout.buffer, absorb, BitVec.add_assoc] using pre.tailApart
    · rw [rsp]
      simpa [Layout.buffer, absorb, BitVec.add_assoc] using pre.counterApart
  have run : Sha2.Proofs.Common.Field.AdvanceTriple boundary
      (Blocks.Digest.Absorb.Pre ((absorb v).pc stage) stage)
      (codeRange ((absorb v).pc stage) ((absorb v).bytes stage))
      (Effect.post (Blocks.Digest.Absorb.effect ((absorb v).pc stage) stage)) := by
    cases stage with
    | select => exact Blocks.Digest.Absorb.select_run _ _ outside (absorb_inside _ (v := v)) (by
        cases v with
        | sha224 => exact inProgram_of_textOffset 0x96 (by decide +kernel)
        | sha256 => exact inProgram_of_textOffset 0x1c86 (by decide +kernel))
    | smallSetup => exact Blocks.Digest.Absorb.smallSetup_run _ _ outside (absorb_inside _ (v := v))
    | smallStore => exact Blocks.Digest.Absorb.smallStore_run _ _ outside (absorb_inside _ (v := v)) (by
        cases v with
        | sha224 => exact inProgram_of_textOffset 0xe2 (by decide +kernel)
        | sha256 => exact inProgram_of_textOffset 0x1cd2 (by decide +kernel))
    | bulkSetup => exact Blocks.Digest.Absorb.bulkSetup_run _ _ outside (absorb_inside _ (v := v))
    | bulkTail => exact Blocks.Digest.Absorb.bulkTail_run _ _ outside (absorb_inside _ (v := v))
    | tailSetup => exact Blocks.Digest.Absorb.tailSetup_run _ _ outside (absorb_inside _ (v := v))
  obtain ⟨fuel, t, steps, readyT, codeT, result⟩ := run s ready code pre'
  refine ⟨fuel, t, steps, readyT, codeT, ?_⟩
  have same : Blocks.Digest.Absorb.effect ((absorb v).pc stage) stage s = stage.effect (absorb v) sp s := by
    have rsp : rspOf s = sp := pre.rsp
    cases v <;> cases stage <;> simp [Blocks.Digest.Absorb.effect, Stage.effect, absorb,
      absorbEntry, Layout.buffer, rsp, BitVec.add_assoc]
  change (stage.effect (absorb v) sp s).Holds s t
  change (Blocks.Digest.Absorb.effect ((absorb v).pc stage) stage s).Holds s t at result
  rwa [same] at result

end Sha2.Proofs.Common.SHA256.Instances.Digest
