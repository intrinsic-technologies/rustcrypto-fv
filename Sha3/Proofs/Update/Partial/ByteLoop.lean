import Sha3.Proofs.Image
import Sha3.Proofs.Variant
import Sha3.Proofs.Update.Partial.ByteXor
import Sha3.Proofs.Update.Tail.Compare
import Sha3.Proofs.X86.Instructions.Inc.Triple
import X86Proofs.Program.ReadWrite.Bytes

namespace Sha3.Proofs.Update.Partial

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha3.Proofs.Finalize.Padding

inductive ByteLoopKind where
  | fill
  | short
  deriving DecidableEq

def ByteLoopKind.sourceReg : ByteLoopKind → BitVec 5
  | .fill => 6
  | .short => 3

def ByteLoopKind.destinationReg : ByteLoopKind → BitVec 5
  | .fill => 0
  | .short => 15

def ByteLoopKind.indexReg : ByteLoopKind → BitVec 5
  | .fill => 7
  | .short => 6

def ByteLoopKind.countReg : ByteLoopKind → BitVec 5
  | .fill => 1
  | .short => 2

def byteLoadMode : ByteLoopKind → AddrMode
  | .fill => .sib 6 (some 7) 0 .none
  | .short => .sib 3 (some 6) 0 .none

def byteStoreMode : ByteLoopKind → AddrMode
  | .fill => .sib 0 (some 7) 0 .none
  | .short => .sib 15 (some 6) 0 .none

def byteLoadBytes : ByteLoopKind → List UInt8
  | .fill => [0x44, 0x0f, 0xb6, 0x04, 0x3e]
  | .short => [0x44, 0x0f, 0xb6, 0x04, 0x33]

def byteStoreBytes : ByteLoopKind → List UInt8
  | .fill => [0x44, 0x30, 0x04, 0x38]
  | .short => [0x45, 0x30, 0x04, 0x37]

def byteIncModrm : ByteLoopKind → UInt8
  | .fill => 0xc7
  | .short => 0xc6

def byteCmpModrm : ByteLoopKind → UInt8
  | .fill => 0xf9
  | .short => 0xf2

def byteBytes (k : ByteLoopKind) : List UInt8 :=
  byteLoadBytes k ++ byteStoreBytes k ++
    [0x48, 0xff, byteIncModrm k, 0x48, 0x39, byteCmpModrm k, 0x75, 0xef]

def byteLoopAddress (k : ByteLoopKind) (v : Variant) : BitVec 64 :=
  match k with
  | .fill => v.updateAddress + 0xd0
  | .short => match v with
    | .sha224 => 0x100b90 | .sha256 => 0x100870
    | .sha384 => 0x100550 | .sha512 => 0x100280

theorem byteBytes_image (k : ByteLoopKind) (v : Variant) :
    let offset := (byteLoopAddress k v).toNat - Spec.Program.Extracted.textAddress.toNat
    byteLoopAddress k v = Spec.Program.Extracted.textAddress + BitVec.ofNat 64 offset ∧
      offset + 17 ≤ Spec.Program.Extracted.textBytes.size ∧
      Spec.Program.Extracted.textBytes.toListFrom offset 17 = byteBytes k := by
  cases k <;> cases v <;> decide +kernel

theorem byteBytes_subset (k : ByteLoopKind) (v : Variant) :
    ∀ byte ∈ codeRange (byteLoopAddress k v) (byteBytes k),
      byte ∈ Spec.Program.Extracted.programImage := by
  obtain ⟨hp, hbound, hbytes⟩ := byteBytes_image k v
  rw [hp]
  exact textSlice_subset_programImage hbound hbytes

theorem byteLoadMode_addr (k : ByteLoopKind) (s : RamState) (next : BitVec 64) :
    (byteLoadMode k).addr s next =
      (Operand.reg k.sourceReg : Operand 64).read s +
        (Operand.reg k.indexReg : Operand 64).read s := by
  cases k <;> simp [byteLoadMode, ByteLoopKind.sourceReg, ByteLoopKind.indexReg,
    AddrMode.addr, AddrMode.reg64, Disp.value]

theorem byteStoreMode_addr (k : ByteLoopKind) (s : RamState) (next : BitVec 64) :
    (byteStoreMode k).addr s next =
      (Operand.reg k.destinationReg : Operand 64).read s +
        (Operand.reg k.indexReg : Operand 64).read s := by
  cases k <;> simp [byteStoreMode, ByteLoopKind.destinationReg, ByteLoopKind.indexReg,
    AddrMode.addr, AddrMode.reg64, Disp.value]

theorem byte_load_effect [Bindings] (k : ByteLoopKind) (p : BitVec 64) :
    StepEffect (LoadPre p (fun s ↦ (byteLoadMode k).addr s (p + 5#64)) 1)
      (codeRange p (byteLoadBytes k)) (movzxR32M8Effect p 5 8 (byteLoadMode k)) := by
  cases k with
  | fill =>
    exact movzx_r_m8_rex_effect_step p 0x44 (by unfold RexPrefix; decide)
      32 (Or.inr rfl) (fun _ ↦ rfl) 0 (.sib 6 (some 7) 0 .none)
      ⟨by decide, by decide⟩ rfl rfl
  | short =>
    exact movzx_r_m8_rex_effect_step p 0x44 (by unfold RexPrefix; decide)
      32 (Or.inr rfl) (fun _ ↦ rfl) 0 (.sib 3 (some 6) 0 .none)
      ⟨by decide, by decide⟩ rfl rfl

theorem byte_store_effect [Bindings] (k : ByteLoopKind) (p : BitVec 64) :
    StepEffect (StorePreReadable p (storeAddrAt p (byteStoreMode k) 4) 1)
      (codeRange p (byteStoreBytes k)) (xorMREffect p 4 8 8 (byteStoreMode k)) := by
  cases k with
  | fill =>
    exact xor_m8_r8_rex_effect_step_of_readable p 0x44 (by unfold RexPrefix; decide)
      0 (.sib 0 (some 7) 0 .none) ⟨by decide, by decide⟩ rfl rfl
  | short =>
    exact xor_m8_r8_rex_effect_step_of_readable p 0x45 (by unfold RexPrefix; decide)
      0 (.sib 15 (some 6) 0 .none) ⟨by decide, by decide⟩ rfl rfl

theorem byte_compare_branch [Bindings] (boundary : ReturnBoundary) (code : CodeMap)
    (k : ByteLoopKind) (p : BitVec 64) (disp : BitVec 8) (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn code s) (hip : s.RIP = p)
    (hcmpCode : ∀ byte ∈ codeRange p [0x48, 0x39, byteCmpModrm k], byte ∈ code)
    (hjmpCode : ∀ byte ∈ codeRange (p + 3#64) (0x75 :: immBytes 8 disp), byte ∈ code)
    (htarget : (branchTarget (p + 3#64) 2 (disp.signExtend 64)).toNat < 2 ^ 32)
    (hne₁ : p + 3#64 ≠ boundary.rip) (hne₂ : p + 5#64 ≠ boundary.rip)
    (hne₃ : branchTarget (p + 3#64) 2 (disp.signExtend 64) ≠ boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn code t ∧
      t.RIP = (if ((Operand.reg k.countReg : Operand 64).read s -
          (Operand.reg k.indexReg : Operand 64).read s == 0#64) then p + 5#64
        else branchTarget (p + 3#64) 2 (disp.signExtend 64)) ∧
      AgreesExcept [.flags, .rip] s t := by
  have hcmp : StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x48, 0x39, byteCmpModrm k])
      (cmpR64R64Effect p k.countReg k.indexReg) := by
    cases k with
    | fill =>
      exact cmp_r64_r64_effect_step p 0x48 0xf9
        (by unfold RexWPrefix; decide) (by decide)
    | short =>
      exact cmp_r64_r64_effect_step p 0x48 0xf2
        (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨u, hrun₁, hready₁, hu⟩ := hcmp.advances hready (hcode.mono hcmpCode) hip hne₁
  have hc₁ : CodeIn code u :=
    hu.codeIn (cmpR64R64Effect_avoids p k.countReg k.indexReg s code) hcode
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      ((Operand.reg k.countReg : Operand 64).read s -
        (Operand.reg k.indexReg : Operand 64).read s == 0#64) :=
    hu.flags.2.2.2.1
  have hcc : condHolds 5#4 (StatusFlags.ofRFLAGS u.RFLAGS) =
      Bool.not ((Operand.reg k.countReg : Operand 64).read s -
        (Operand.reg k.indexReg : Operand 64).read s == 0#64) := by
    change Bool.not (StatusFlags.ofRFLAGS u.RFLAGS).ZF = _
    exact congrArg Bool.not hz
  have hnext : p + 3#64 + BitVec.ofNat 64 2 = p + 5#64 := by
    rw [BitVec.add_assoc]
    rfl
  have hbranch := jcc_rel8_effect_step (p + 3#64) 5#4 disp
  obtain ⟨t, hrun₂, hready₂, ht⟩ := hbranch.advances hready₁ (hc₁.mono hjmpCode)
    ⟨hu.rip, fun _ ↦ htarget⟩ (by
      dsimp only [jccEffect, branchEffect]
      split
      · exact hne₃
      · exact hnext ▸ hne₂)
  refine ⟨t, hrun₁.trans hrun₂, hready₂,
    ht.codeIn (branchEffect_avoids _ _ _ code) hc₁, ?_, ?_⟩
  · have hip' := ht.rip
    simp only [jccEffect, branchEffect, hcc, hnext] at hip'
    cases he : ((Operand.reg k.countReg : Operand 64).read s -
      (Operand.reg k.indexReg : Operand 64).read s == 0#64) <;> rw [he] at hip' <;> exact hip'
  · apply (hu.agrees.trans ht.agrees).mono
    simp only [cmpR64R64Effect_components, jccEffect, branchEffect_components]
    intro c hc
    simpa using hc

theorem byte_pair [Bindings] (boundary : ReturnBoundary) (code : CodeMap)
    (k : ByteLoopKind) (p : BitVec 64) (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn code s) (hip : s.RIP = p)
    (hloadCode : ∀ byte ∈ codeRange p (byteLoadBytes k), byte ∈ code)
    (hstoreCode : ∀ byte ∈ codeRange (p + 5#64) (byteStoreBytes k), byte ∈ code)
    (hsource : MemReadable s ((Operand.reg k.sourceReg : Operand 64).read s +
      (Operand.reg k.indexReg : Operand 64).read s) 1)
    (hdest : MemReadable s ((Operand.reg k.destinationReg : Operand 64).read s +
      (Operand.reg k.indexReg : Operand 64).read s) 1)
    (htables : ¬ Spec.Program.InPageTables ((Operand.reg k.destinationReg : Operand 64).read s +
      (Operand.reg k.indexReg : Operand 64).read s))
    (hseparate : ∀ byte ∈ code, byte.1 ≠ (Operand.reg k.destinationReg : Operand 64).read s +
      (Operand.reg k.indexReg : Operand 64).read s)
    (hne₁ : p + 5#64 ≠ boundary.rip) (hne₂ : p + 9#64 ≠ boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn code t ∧
      t.RIP = BitVec.add p 9#64 ∧
      t.external = memStore s.external
        ((Operand.reg k.destinationReg : Operand 64).read s +
          (Operand.reg k.indexReg : Operand 64).read s)
        (memLoad s.external ((Operand.reg k.destinationReg : Operand 64).read s +
            (Operand.reg k.indexReg : Operand 64).read s) 8 ^^^
          memLoad s.external ((Operand.reg k.sourceReg : Operand 64).read s +
            (Operand.reg k.indexReg : Operand 64).read s) 8) ∧
      AgreesExcept [.reg 8#5,
        .mem ((Operand.reg k.destinationReg : Operand 64).read s +
          (Operand.reg k.indexReg : Operand 64).read s) 1, .flags, .rip] s t := by
  have hnext : p + 5#64 + 4#64 = p + 9#64 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨t, hrun, hready', hcode', hip', hmemory, hframe⟩ :=
    load_xor_byte boundary code _ _ p 5 4 8#5 (byteLoadMode k) (byteStoreMode k)
      (byte_load_effect k p) (byte_store_effect k (p + 5#64))
      hloadCode hstoreCode hne₁ (by simpa only [BitVec.ofNat_eq_ofNat, hnext] using hne₂)
      s hready hcode hip (by simpa only [byteLoadMode_addr] using hsource)
      (by simpa only [byteStoreMode_addr] using hdest)
      (by
        intro u h
        simp only [byteStoreMode_addr,
          h.read (r := k.destinationReg) (by cases k <;> simp [ByteLoopKind.destinationReg]),
          h.read (r := k.indexReg) (by cases k <;> simp [ByteLoopKind.indexReg])])
      (by simpa only [byteStoreMode_addr] using htables)
      (by simpa only [byteStoreMode_addr] using hseparate)
  refine ⟨t, hrun, hready', hcode', hip'.trans hnext, ?_, ?_⟩
  · simpa only [byteStoreMode_addr, byteLoadMode_addr] using hmemory
  · simpa only [byteStoreMode_addr] using hframe

theorem byte_iteration [Bindings] (boundary : ReturnBoundary) (code : CodeMap)
    (k : ByteLoopKind) (p : BitVec 64) (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn code s)
    (hip : s.RIP = p)
    (hsub : ∀ byte ∈ codeRange p (byteBytes k), byte ∈ code)
    (hsource : MemReadable s ((Operand.reg k.sourceReg : Operand 64).read s +
      (Operand.reg k.indexReg : Operand 64).read s) 1)
    (hdest : MemReadable s ((Operand.reg k.destinationReg : Operand 64).read s +
      (Operand.reg k.indexReg : Operand 64).read s) 1)
    (htables : ¬ Spec.Program.InPageTables ((Operand.reg k.destinationReg : Operand 64).read s +
      (Operand.reg k.indexReg : Operand 64).read s))
    (hseparate : ∀ byte ∈ code, byte.1 ≠ (Operand.reg k.destinationReg : Operand 64).read s +
      (Operand.reg k.indexReg : Operand 64).read s)
    (hne : ∀ i ∈ [0, 5, 9, 12, 15, 17], p + BitVec.ofNat 64 i ≠ boundary.rip) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ CodeIn code t ∧
      t.RIP = (if ((Operand.reg k.countReg : Operand 64).read s -
          ((Operand.reg k.indexReg : Operand 64).read s + 1#64) == 0#64) then p + 17#64 else p) ∧
      (Operand.reg k.indexReg : Operand 64).read t =
        (Operand.reg k.indexReg : Operand 64).read s + 1#64 ∧
      t.external = memStore s.external
        ((Operand.reg k.destinationReg : Operand 64).read s +
          (Operand.reg k.indexReg : Operand 64).read s)
        (memLoad s.external ((Operand.reg k.destinationReg : Operand 64).read s +
            (Operand.reg k.indexReg : Operand 64).read s) 8 ^^^
          memLoad s.external ((Operand.reg k.sourceReg : Operand 64).read s +
            (Operand.reg k.indexReg : Operand 64).read s) 8) ∧
      AgreesExcept [.reg 8#5, .reg k.indexReg,
        .mem ((Operand.reg k.destinationReg : Operand 64).read s +
          (Operand.reg k.indexReg : Operand 64).read s) 1, .flags, .rip] s t := by
  have hsub₀ : ∀ byte ∈ codeRange p (byteLoadBytes k), byte ∈ code :=
    fun byte hb ↦ hsub byte (codeRange_mem_of_take (by cases k <;> decide +kernel) byte hb)
  have hsub₅ : ∀ byte ∈ codeRange (p + 5#64) (byteStoreBytes k), byte ∈ code :=
    fun byte hb ↦ hsub byte (codeRange_mem_of_drop 5 (by cases k <;> decide +kernel) byte hb)
  obtain ⟨u, hrun₁, hready₁, hc₁, huip, humem, huframe⟩ :=
    byte_pair boundary code k p s hready hcode hip hsub₀ hsub₅ hsource hdest htables
      hseparate (hne 5 (by simp)) (hne 9 (by simp))
  have hinc : StepEffect (fun s ↦ s.RIP = p + 9#64)
      (codeRange (p + 9#64) [0x48, 0xff, byteIncModrm k]) (incR64Effect (p + 9#64) k.indexReg) := by
    cases k with
    | fill =>
      exact inc_r64_effect_step (p + 9#64) 0x48 0xc7
        (by unfold RexWPrefix; decide) (by decide) (by decide)
    | short =>
      exact inc_r64_effect_step (p + 9#64) 0x48 0xc6
        (by unfold RexWPrefix; decide) (by decide) (by decide)
  have hsub₉ : ∀ byte ∈ codeRange (p + 9#64) [0x48, 0xff, byteIncModrm k], byte ∈ code :=
    fun byte hb ↦ hsub byte (codeRange_mem_of_drop 9 (by cases k <;> decide +kernel) byte hb)
  have hnext₁ : p + 9#64 + 3#64 = p + 12#64 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨v, hrun₂, hready₂, hv⟩ :=
    hinc.advances (boundary := boundary) hready₁ (hc₁.mono hsub₉) huip
    (by simpa only [incR64Effect, BitVec.ofNat_eq_ofNat, hnext₁] using hne 12 (by simp))
  have hc₂ : CodeIn code v := hv.codeIn (incR64Effect_avoids _ _ _ code) hc₁
  have hvip : v.RIP = BitVec.add p 12#64 := hv.rip.trans hnext₁
  have hindexU : (Operand.reg k.indexReg : Operand 64).read u =
      (Operand.reg k.indexReg : Operand 64).read s :=
    huframe.read (by cases k <;> simp [ByteLoopKind.indexReg])
  have hcountV : (Operand.reg k.countReg : Operand 64).read v =
      (Operand.reg k.countReg : Operand 64).read s :=
    (hv.agrees.read (by cases k <;> simp [ByteLoopKind.indexReg, ByteLoopKind.countReg])).trans
      (huframe.read (by cases k <;> simp [ByteLoopKind.indexReg, ByteLoopKind.countReg]))
  have hindexV : (Operand.reg k.indexReg : Operand 64).read v =
      (Operand.reg k.indexReg : Operand 64).read s + 1#64 := by
    have h := hv.writes
    change (Operand.reg k.indexReg : Operand 64).read v =
      (Operand.reg k.indexReg : Operand 64).read u + 1 at h
    simpa only [hindexU, BitVec.ofNat_eq_ofNat] using h
  have hsub₁₂ : ∀ byte ∈ codeRange (p + 12#64) [0x48, 0x39, byteCmpModrm k], byte ∈ code :=
    fun byte hb ↦ hsub byte (codeRange_mem_of_drop 12 (by cases k <;> decide +kernel) byte hb)
  have hsub₁₅ : ∀ byte ∈ codeRange (p + 12#64 + 3#64) (0x75 :: immBytes 8 0xef#8),
      byte ∈ code := by
    have he : p + 12#64 + 3#64 = p + 15#64 := by rw [BitVec.add_assoc]; rfl
    rw [he]
    exact fun byte hb ↦ hsub byte (codeRange_mem_of_drop 15 (by cases k <;> decide +kernel) byte hb)
  have htarget : branchTarget (p + 12#64 + 3#64) 2 (BitVec.signExtend 64 0xef#8) = p := by
    simp only [branchTarget, BitVec.add_assoc]
    change p + 0#64 = p
    exact BitVec.add_zero p
  have hlow : p.toNat < 2 ^ 32 := by
    cases k <;> exact (hcode _ (hsub _ List.mem_cons_self)).1
  have hnext₂ : p + 12#64 + 3#64 = p + 15#64 := by rw [BitVec.add_assoc]; rfl
  have hnext₃ : p + 12#64 + 5#64 = p + 17#64 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨t, hrun₃, hready₃, hc₃, htip, htframe⟩ :=
    byte_compare_branch boundary code k (p + 12#64) 0xef#8 v hready₂ hc₂ hvip hsub₁₂ hsub₁₅
      (by rw [htarget]; exact hlow) (by rw [hnext₂]; exact hne 15 (by simp))
      (by rw [hnext₃]; exact hne 17 (by simp))
      (by rw [htarget]; simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hne 0 (by simp))
  refine ⟨t, (hrun₁.trans hrun₂).trans hrun₃, hready₃, hc₃, ?_, ?_, ?_, ?_⟩
  · simpa only [hcountV, hindexV, htarget, hnext₃] using htip
  · exact (htframe.read (by simp)).trans hindexV
  · rw [htframe.external (by simp [Component.Covers]),
      hv.agrees.external (by simp [Component.Covers]), humem]
  · apply ((huframe.trans hv.agrees).trans htframe).mono
    simp only [incR64Effect_components]
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with ((rfl | rfl | rfl | rfl) | rfl | rfl | rfl) | rfl | rfl <;> simp

structure ByteInvariant (k : ByteLoopKind) (p source destination : BitVec 64)
    (offset count len : Nat) (initial input : Nat → UInt8) (i : Nat) (s : RamState) : Prop where
  rip : s.RIP = if i < count then p else p + 17#64
  countReg : (Operand.reg k.countReg : Operand 64).read s = BitVec.ofNat 64 count
  indexReg : (Operand.reg k.indexReg : Operand 64).read s = BitVec.ofNat 64 i
  sourceReg : (Operand.reg k.sourceReg : Operand 64).read s = source
  destinationReg : (Operand.reg k.destinationReg : Operand 64).read s =
    destination + BitVec.ofNat 64 offset
  sourceBytes : Bytes s.external source count (fun j ↦ input (offset + j))
  stateBytes : Bytes s.external destination len
    (fun j ↦ initial j ^^^ (if j < offset + i then input j else 0))

def byteClobbers (k : ByteLoopKind) (destination : BitVec 64) (len : Nat) : List Component :=
  [.reg 8#5, .reg k.indexReg, .mem destination len, .flags, .rip]

section ByteLoop

variable [Bindings] (boundary : ReturnBoundary) (code : CodeMap)
    (k : ByteLoopKind) (p source destination : BitVec 64) (offset count len : Nat)
    (initial input : Nat → UInt8)
    (hspan : offset + count ≤ len)
    (hsourceLow : source.toNat + count ≤ 2 ^ 32)
    (hdestLow : destination.toNat + len ≤ 2 ^ 32)
    (hapart : RangeApart destination len source count)
    (htables : ∀ i < len, ¬ Spec.Program.InPageTables (destination + BitVec.ofNat 64 i))
    (hseparate : ∀ byte ∈ code, ∀ i < len, byte.1 ≠ destination + BitVec.ofNat 64 i)
    (hsub : ∀ byte ∈ codeRange p (byteBytes k), byte ∈ code)
    (hne : ∀ i ∈ [0, 5, 9, 12, 15, 17], p + BitVec.ofNat 64 i ≠ boundary.rip)

include hspan hsourceLow hdestLow hapart htables hseparate hsub hne in
theorem byte_advance (i : Nat) (hi : i < count) :
    AdvanceTriple boundary 5 (ByteInvariant k p source destination offset count len initial input i)
      code (fun s t ↦
        ByteInvariant k p source destination offset count len initial input (i + 1) t ∧
        AgreesExcept (byteClobbers k destination len) s t) := by
  intro s hready hcode hs
  have hsrc : ((Operand.reg k.sourceReg : Operand 64).read s +
      (Operand.reg k.indexReg : Operand 64).read s) = source + BitVec.ofNat 64 i := by
    rw [hs.sourceReg, hs.indexReg]
  have hdst : ((Operand.reg k.destinationReg : Operand 64).read s +
      (Operand.reg k.indexReg : Operand 64).read s) =
        destination + BitVec.ofNat 64 (offset + i) := by
    rw [hs.destinationReg, hs.indexReg, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hir : s.RIP = p := by simpa only [hi, ↓reduceIte] using hs.rip
  have hsrcLow : (source + BitVec.ofNat 64 i).toNat + 1 ≤ 2 ^ 32 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hdstLow : (destination + BitVec.ofNat 64 (offset + i)).toNat + 1 ≤ 2 ^ 32 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  obtain ⟨t, hrun, hready', hcode', hip', hindex, hmemory, hframe⟩ :=
    byte_iteration boundary code k p s hready hcode hir hsub
      (by rw [hsrc]; exact (hs.sourceBytes.sub i 1 (by omega)).readable hsrcLow)
      (by rw [hdst]; exact (hs.stateBytes.sub (offset + i) 1 (by omega)).readable hdstLow)
      (by rw [hdst]; exact htables (offset + i) (by omega))
      (by rw [hdst]; exact fun byte hb ↦ hseparate byte hb (offset + i) (by omega)) hne
  have hindex' : (Operand.reg k.indexReg : Operand 64).read t = BitVec.ofNat 64 (i + 1) := by
    simpa only [hs.indexReg, ← BitVec.ofNat_add] using hindex
  have hip'' : t.RIP = if i + 1 < count then p else p + 17#64 := by
    rw [hs.countReg, hs.indexReg] at hip'
    have heq : (BitVec.ofNat 64 count - (BitVec.ofNat 64 i + 1#64) == 0#64) =
        decide (count = i + 1) := by
      simpa only [← BitVec.ofNat_add] using
        (Tail.sub_ofNat_beq_zero (n := 64) (a := count) (b := i + 1) (by omega) (by omega))
    rw [heq] at hip'
    by_cases he : count = i + 1
    · have hnot : ¬ i + 1 < count := by omega
      simpa only [he, decide_true, ↓reduceIte, hnot, Nat.lt_irrefl] using hip'
    · have hlt : i + 1 < count := by omega
      simpa only [he, decide_false, Bool.false_eq_true, ↓reduceIte, hlt] using hip'
  rw [hsrc, hdst, hs.sourceBytes.loadByte i hi] at hmemory
  refine ⟨t, hrun, hready', hcode', ⟨hip'', ?_, hindex', ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (hframe.read (by cases k <;> simp [ByteLoopKind.indexReg,
      ByteLoopKind.countReg])).trans hs.countReg
  · exact (hframe.read (by cases k <;> simp [ByteLoopKind.indexReg,
      ByteLoopKind.sourceReg])).trans hs.sourceReg
  · exact (hframe.read (by cases k <;> simp [ByteLoopKind.indexReg,
      ByteLoopKind.destinationReg])).trans hs.destinationReg
  · rw [hmemory]
    apply hs.sourceBytes.store_disjoint
    intro j hj k hk
    have hj0 : j = 0 := by omega
    subst j
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      hapart (offset + i) (by omega) k hk
  · rw [hmemory]
    simpa only [Nat.add_assoc] using xor_prefix_byte hs.stateBytes (by omega) (by omega)
  · rw [hdst] at hframe
    apply hframe.widen
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp_all [byteClobbers, Component.isMem]
    · intro x c hc hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact False.elim hx
      · exact False.elim hx
      · obtain ⟨j, hj, rfl⟩ := hx
        have hj0 : j = 0 := by omega
        subst j
        refine ⟨.mem destination len, by simp [byteClobbers], offset + i, by omega, ?_⟩
        simp only [BitVec.add_zero]
      · exact False.elim hx
      · exact False.elim hx

include hspan hsourceLow hdestLow hapart htables hseparate hsub hne in
theorem byte_loop :
    AdvanceTriple boundary (count * 5)
      (ByteInvariant k p source destination offset count len initial input 0) code
      (fun s t ↦ ByteInvariant k p source destination offset count len initial input count t ∧
        AgreesExcept (byteClobbers k destination len) s t) := by
  intro s hready hcode hs
  let invariant := fun i t ↦
    ByteInvariant k p source destination offset count len initial input i t ∧
      AgreesExcept (byteClobbers k destination len) s t
  have body : ∀ i, i < count → AdvanceTriple boundary 5 (invariant i) code
      (fun _ t ↦ invariant (i + 1) t) := by
    intro i hi u hready' hcode' hu
    obtain ⟨t, hrun, hready'', hcode'', ht, hframe⟩ :=
      byte_advance boundary code k p source destination offset count len initial input
        hspan hsourceLow hdestLow hapart htables hseparate hsub hne i hi u hready' hcode' hu.1
    refine ⟨t, hrun, hready'', hcode'', ht, (hu.2.trans hframe).mono ?_⟩
    intro c hc
    simpa only [List.mem_append, or_self] using hc
  exact AdvanceTriple.iterate count 5 body s hready hcode ⟨hs, AgreesExcept.refl _ s⟩

end ByteLoop

end Sha3.Proofs.Update.Partial
