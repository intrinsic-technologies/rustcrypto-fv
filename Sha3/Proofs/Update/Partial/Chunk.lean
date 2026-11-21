import Sha3.Proofs.Update.Partial.ByteXor
import Sha3.Proofs.Update.Tail.Compare
import Sha3.Proofs.X86.Instructions.Add.Imm8.Triple
import X86Proofs.Program.ReadWrite.Bytes

namespace Sha3.Proofs.Update.Partial

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha3.Proofs.Finalize.Padding

def chunkBytes : List UInt8 :=
  [0x44, 0x0f, 0xb6, 0x0c, 0x33, 0x45, 0x30, 0x4c, 0x30, 0xfd,
    0x44, 0x0f, 0xb6, 0x4c, 0x33, 0x01, 0x45, 0x30, 0x4c, 0x30, 0xfe,
    0x44, 0x0f, 0xb6, 0x4c, 0x33, 0x02, 0x45, 0x30, 0x4c, 0x30, 0xff,
    0x44, 0x0f, 0xb6, 0x4c, 0x33, 0x03, 0x45, 0x30, 0x0c, 0x30,
    0x48, 0x83, 0xc6, 0x04, 0x49, 0x39, 0xf2, 0x75, 0xcd]

theorem chunk_compare_branch [Bindings] (boundary : ReturnBoundary) (code : CodeMap)
    (p : BitVec 64) (disp : BitVec 8) (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn code s) (hip : s.RIP = p)
    (hcmpCode : ∀ byte ∈ codeRange p [0x49, 0x39, 0xf2], byte ∈ code)
    (hjmpCode : ∀ byte ∈ codeRange (p + 3#64) (0x75 :: immBytes 8 disp), byte ∈ code)
    (htarget : (branchTarget (p + 3#64) 2 (disp.signExtend 64)).toNat < 2 ^ 32)
    (hne₁ : p + 3#64 ≠ boundary.rip) (hne₂ : p + 5#64 ≠ boundary.rip)
    (hne₃ : branchTarget (p + 3#64) 2 (disp.signExtend 64) ≠ boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn code t ∧
      t.RIP = (if ((Operand.reg 10#5 : Operand 64).read s -
          (Operand.reg 6#5 : Operand 64).read s == 0#64) then p + 5#64
        else branchTarget (p + 3#64) 2 (disp.signExtend 64)) ∧
      AgreesExcept [.flags, .rip] s t := by
  have hcmp : StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x49, 0x39, 0xf2])
      (cmpR64R64Effect p 10#5 6#5) := by
    exact cmp_r64_r64_effect_step p 0x49 0xf2
      (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨u, hrun₁, hready₁, hu⟩ := hcmp.advances hready (hcode.mono hcmpCode) hip hne₁
  have hc₁ : CodeIn code u := hu.codeIn (cmpR64R64Effect_avoids p 10#5 6 s code) hcode
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      ((Operand.reg 10#5 : Operand 64).read s - (Operand.reg 6#5 : Operand 64).read s == 0#64) :=
    hu.flags.2.2.2.1
  have hcc : condHolds 5#4 (StatusFlags.ofRFLAGS u.RFLAGS) =
      Bool.not ((Operand.reg 10#5 : Operand 64).read s -
        (Operand.reg 6#5 : Operand 64).read s == 0#64) := by
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
    cases he : ((Operand.reg 10#5 : Operand 64).read s -
      (Operand.reg 6#5 : Operand 64).read s == 0#64) <;> rw [he] at hip' <;> exact hip'
  · apply (hu.agrees.trans ht.agrees).mono
    simp only [cmpR64R64Effect_components, jccEffect, branchEffect_components]
    intro c hc
    simpa using hc


def chunkLoadMode (i : Fin 4) : AddrMode :=
  .sib 3 (some 6) 0 (if i.val = 0 then .none else .d8 (BitVec.ofNat 8 i.val))

def chunkStoreMode (i : Fin 4) : AddrMode :=
  .sib 8 (some 6) 0 (if i.val = 3 then .none else .d8 (BitVec.ofNat 8 (253 + i.val)))

def chunkPairOffset (i : Nat) : Nat := if i < 4 then 11 * i - 1 else 42

theorem chunkLoadMode_spec (i : Fin 4) :
    (chunkLoadMode i).Valid ∧ (chunkLoadMode i).rexX = 0 ∧ (chunkLoadMode i).rexB = 0 ∧
    gprNumber 0#1 1#1 1#3 = 9#5 ∧
    ∀ s next, (chunkLoadMode i).addr s next =
      (Operand.reg 3#5 : Operand 64).read s + (Operand.reg 6#5 : Operand 64).read s +
        BitVec.ofNat 64 i.val := by
  finite_cases i <;> simp (config := { decide := true }) [chunkLoadMode, AddrMode.addr,
    AddrMode.reg64, Disp.value]

theorem chunkStoreMode_spec (i : Fin 4) :
    (chunkStoreMode i).Valid ∧ (chunkStoreMode i).rexX = 0 ∧ (chunkStoreMode i).rexB = 1 ∧
    ∀ s next, (chunkStoreMode i).addr s next =
      (Operand.reg 8#5 : Operand 64).read s + (Operand.reg 6#5 : Operand 64).read s +
        (BitVec.ofNat 64 i.val - 3#64) := by
  finite_cases i <;> simp (config := { decide := true }) [chunkStoreMode, AddrMode.addr,
    AddrMode.reg64, Disp.value]

theorem chunk_pair_next (p : BitVec 64) (i : Fin 4) :
    p + BitVec.ofNat 64 (chunkPairOffset i.val) +
        BitVec.ofNat 64 (4 + (chunkLoadMode i).tail.length) +
        BitVec.ofNat 64 (3 + (chunkStoreMode i).tail.length) =
      p + BitVec.ofNat 64 (chunkPairOffset (i.val + 1)) := by
  rw [BitVec.add_assoc, BitVec.add_assoc]
  congr 1
  revert i
  decide +kernel

theorem chunk_pair_slice (i : Fin 4) :
    (chunkBytes.drop (chunkPairOffset i.val)).take (4 + (chunkLoadMode i).tail.length) =
      [0x44, 0x0f, 0xb6, (chunkLoadMode i).modrm 1#3] ++ (chunkLoadMode i).tail ∧
    (chunkBytes.drop (chunkPairOffset i.val + 4 + (chunkLoadMode i).tail.length)).take
        (3 + (chunkStoreMode i).tail.length) =
      [0x45, 0x30, (chunkStoreMode i).modrm 1#3] ++ (chunkStoreMode i).tail := by
  revert i
  decide +kernel

theorem chunk_pair [Bindings] (boundary : ReturnBoundary) (code : CodeMap)
    (p : BitVec 64) (i : Fin 4) (s : RamState) (hready : ReadyToStep s) (hcode : CodeIn code s)
    (hip : s.RIP = p + BitVec.ofNat 64 (chunkPairOffset i.val))
    (hsub : ∀ byte ∈ codeRange p chunkBytes, byte ∈ code)
    (hsource : MemReadable s
      ((Operand.reg 3#5 : Operand 64).read s + (Operand.reg 6#5 : Operand 64).read s +
        BitVec.ofNat 64 i.val) 1)
    (hdest : MemReadable s
      ((Operand.reg 8#5 : Operand 64).read s + (Operand.reg 6#5 : Operand 64).read s +
        (BitVec.ofNat 64 i.val - 3#64)) 1)
    (htables : ¬ Spec.Program.InPageTables
      ((Operand.reg 8#5 : Operand 64).read s + (Operand.reg 6#5 : Operand 64).read s +
        (BitVec.ofNat 64 i.val - 3#64)))
    (hseparate : ∀ byte ∈ code, byte.1 ≠
      (Operand.reg 8#5 : Operand 64).read s + (Operand.reg 6#5 : Operand 64).read s +
        (BitVec.ofNat 64 i.val - 3#64))
    (hne₁ : p + BitVec.ofNat 64 (chunkPairOffset i.val) +
      BitVec.ofNat 64 (4 + (chunkLoadMode i).tail.length) ≠ boundary.rip)
    (hne₂ : p + BitVec.ofNat 64 (chunkPairOffset (i.val + 1)) ≠ boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn code t ∧
      t.RIP = BitVec.add p (BitVec.ofNat 64 (chunkPairOffset (i.val + 1))) ∧
      t.external = memStore s.external
        ((Operand.reg 8#5 : Operand 64).read s + (Operand.reg 6#5 : Operand 64).read s +
          (BitVec.ofNat 64 i.val - 3#64))
        (memLoad s.external
            ((Operand.reg 8#5 : Operand 64).read s + (Operand.reg 6#5 : Operand 64).read s +
              (BitVec.ofNat 64 i.val - 3#64)) 8 ^^^
          memLoad s.external
            ((Operand.reg 3#5 : Operand 64).read s + (Operand.reg 6#5 : Operand 64).read s +
              BitVec.ofNat 64 i.val) 8) ∧
      AgreesExcept [.reg 9#5,
        .mem ((Operand.reg 8#5 : Operand 64).read s + (Operand.reg 6#5 : Operand 64).read s +
          (BitVec.ofNat 64 i.val - 3#64)) 1, .flags, .rip] s t := by
  have hload := movzx_r_m8_rex_effect_step
    (p + BitVec.ofNat 64 (chunkPairOffset i.val)) 0x44
    (by unfold RexPrefix; decide) 32 (.inr rfl) (by intro; rfl) 1#3 (chunkLoadMode i)
    (chunkLoadMode_spec i).1 (chunkLoadMode_spec i).2.1.symm (chunkLoadMode_spec i).2.2.1.symm
  have hstore := xor_m8_r8_rex_effect_step_of_readable
    (p + BitVec.ofNat 64 (chunkPairOffset i.val) +
      BitVec.ofNat 64 (4 + (chunkLoadMode i).tail.length)) 0x45
    (by unfold RexPrefix; decide) 1#3 (chunkStoreMode i)
    (chunkStoreMode_spec i).1 (chunkStoreMode_spec i).2.1.symm
    (chunkStoreMode_spec i).2.2.1.symm
  have hloadCode : ∀ byte ∈ codeRange (p + BitVec.ofNat 64 (chunkPairOffset i.val))
      (0x44 :: 0x0f :: 0xb6 :: (chunkLoadMode i).modrm 1#3 :: (chunkLoadMode i).tail), byte ∈ code := by
    intro byte hb
    apply hsub byte
    apply codeRange_mem_of_drop (chunkPairOffset i.val) ?_ byte hb
    have hlen : (0x44 :: 0x0f :: 0xb6 :: (chunkLoadMode i).modrm 1#3 ::
        (chunkLoadMode i).tail).length = 4 + (chunkLoadMode i).tail.length := by
      simp only [List.length_cons]; omega
    rw [hlen]
    exact (chunk_pair_slice i).1
  have hstoreCode : ∀ byte ∈ codeRange
      (p + BitVec.ofNat 64 (chunkPairOffset i.val) + BitVec.ofNat 64 (4 + (chunkLoadMode i).tail.length))
      (0x45 :: 0x30 :: (chunkStoreMode i).modrm 1#3 :: (chunkStoreMode i).tail), byte ∈ code := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    intro byte hb
    apply hsub byte
    apply codeRange_mem_of_drop (chunkPairOffset i.val + (4 + (chunkLoadMode i).tail.length)) ?_ byte hb
    have hlen : (0x45 :: 0x30 :: (chunkStoreMode i).modrm 1#3 ::
        (chunkStoreMode i).tail).length = 3 + (chunkStoreMode i).tail.length := by
      simp only [List.length_cons]; omega
    rw [hlen]
    simpa only [Nat.add_assoc, List.cons_append, List.nil_append] using (chunk_pair_slice i).2
  have hstable : ∀ u, AgreesExcept [.reg 9#5, .rip] s u →
      (chunkStoreMode i).addr u
          (p + BitVec.ofNat 64 (chunkPairOffset i.val) +
            BitVec.ofNat 64 (4 + (chunkLoadMode i).tail.length) +
            BitVec.ofNat 64 (3 + (chunkStoreMode i).tail.length)) =
        (chunkStoreMode i).addr s
          (p + BitVec.ofNat 64 (chunkPairOffset i.val) +
            BitVec.ofNat 64 (4 + (chunkLoadMode i).tail.length) +
            BitVec.ofNat 64 (3 + (chunkStoreMode i).tail.length)) := by
    intro u h
    simp only [(chunkStoreMode_spec i).2.2.2, h.read (r := 8#5) (by simp),
      h.read (r := 6#5) (by simp)]
  obtain ⟨t, hrun, hready', hcode', hip', hmem, hframe⟩ :=
    load_xor_byte boundary code _ _ _ _ _ 9#5 (chunkLoadMode i) (chunkStoreMode i)
      hload hstore hloadCode hstoreCode hne₁ (by rw [chunk_pair_next]; exact hne₂)
      s hready hcode hip (by simpa only [(chunkLoadMode_spec i).2.2.2.2] using hsource)
      (by simpa only [(chunkStoreMode_spec i).2.2.2] using hdest) hstable
      (by simpa only [(chunkStoreMode_spec i).2.2.2] using htables)
      (by simpa only [(chunkStoreMode_spec i).2.2.2] using hseparate)
  refine ⟨t, hrun, hready', hcode', hip'.trans (chunk_pair_next p i), ?_, ?_⟩
  · simpa only [(chunkStoreMode_spec i).2.2.2, (chunkLoadMode_spec i).2.2.2.2] using hmem
  · simpa only [(chunkStoreMode_spec i).2.2.2] using hframe

structure ChunkInvariant (p source destination : BitVec 64) (count len : Nat)
    (initial input : Nat → UInt8) (offset phase : Nat) (s : RamState) : Prop where
  rip : s.RIP = if offset < count then p + BitVec.ofNat 64 (chunkPairOffset phase) else p + 51#64
  countReg : (Operand.reg 10#5 : Operand 64).read s = BitVec.ofNat 64 count
  indexReg : (Operand.reg 6#5 : Operand 64).read s = BitVec.ofNat 64 offset
  sourceReg : (Operand.reg 3#5 : Operand 64).read s = source
  destinationReg : (Operand.reg 8#5 : Operand 64).read s = destination + 3#64
  sourceBytes : Bytes s.external source count input
  stateBytes : Bytes s.external destination len
    (fun j ↦ initial j ^^^ (if j < offset + phase then input j else 0))

def chunkClobbers (destination : BitVec 64) (len : Nat) : List Component :=
  [.reg 9#5, .reg 6#5, .mem destination len, .flags, .rip]

section ChunkLoop

variable [Bindings] (boundary : ReturnBoundary) (code : CodeMap)
    (p source destination : BitVec 64) (count len : Nat)
    (initial input : Nat → UInt8)
    (hspan : count ≤ len)
    (hsourceLow : source.toNat + count ≤ 2 ^ 32)
    (hdestLow : destination.toNat + len ≤ 2 ^ 32)
    (hapart : RangeApart destination len source count)
    (htables : ∀ i < len, ¬ Spec.Program.InPageTables (destination + BitVec.ofNat 64 i))
    (hseparate : ∀ byte ∈ code, ∀ i < len, byte.1 ≠ destination + BitVec.ofNat 64 i)
    (hsub : ∀ byte ∈ codeRange p chunkBytes, byte ∈ code)
    (hne : ∀ i ≤ 51, p + BitVec.ofNat 64 i ≠ boundary.rip)

include hspan hsourceLow hdestLow hapart htables hseparate hsub hne in
 theorem chunk_byte_advance (offset phase : Nat) (hoffset : offset + 4 ≤ count) (hphase : phase < 4) :
    AdvanceTriple boundary 2 (ChunkInvariant p source destination count len initial input offset phase)
      code (fun s t ↦ ChunkInvariant p source destination count len initial input offset (phase + 1) t ∧
        AgreesExcept (chunkClobbers destination len) s t) := by
  intro s hready hcode hs
  let i : Fin 4 := ⟨phase, hphase⟩
  have hsrc : (Operand.reg 3#5 : Operand 64).read s +
      (Operand.reg 6#5 : Operand 64).read s + BitVec.ofNat 64 i.val =
      source + BitVec.ofNat 64 (offset + phase) := by
    rw [hs.sourceReg, hs.indexReg, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hdst : (Operand.reg 8#5 : Operand 64).read s +
      (Operand.reg 6#5 : Operand 64).read s + (BitVec.ofNat 64 i.val - 3#64) =
      destination + BitVec.ofNat 64 (offset + phase) := by
    rw [hs.destinationReg, hs.indexReg]
    change destination + 3#64 + BitVec.ofNat 64 offset + (BitVec.ofNat 64 phase - 3#64) = _
    calc
      _ = (destination + BitVec.ofNat 64 offset + BitVec.ofNat 64 phase) + (3#64 - 3#64) := by
        simp only [BitVec.sub_eq_add_neg]
        ac_rfl
      _ = _ := by rw [BitVec.sub_self, BitVec.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hir : s.RIP = p + BitVec.ofNat 64 (chunkPairOffset i.val) := by
    simpa only [show offset < count by omega, ↓reduceIte] using hs.rip
  have hsrcLow : (source + BitVec.ofNat 64 (offset + phase)).toNat + 1 ≤ 2 ^ 32 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hdstLow : (destination + BitVec.ofNat 64 (offset + phase)).toNat + 1 ≤ 2 ^ 32 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hne₁ : p + BitVec.ofNat 64 (chunkPairOffset i.val) +
      BitVec.ofNat 64 (4 + (chunkLoadMode i).tail.length) ≠ boundary.rip := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    apply hne
    exact (by decide +kernel : ∀ j : Fin 4, chunkPairOffset j.val +
      (4 + (chunkLoadMode j).tail.length) ≤ 51) i
  have hne₂ : p + BitVec.ofNat 64 (chunkPairOffset (i.val + 1)) ≠ boundary.rip := by
    apply hne
    exact (by decide +kernel : ∀ j : Fin 4, chunkPairOffset (j.val + 1) ≤ 51) i
  obtain ⟨t, hrun, hready', hcode', hip', hmemory, hframe⟩ :=
    chunk_pair boundary code p i s hready hcode hir hsub
      (by rw [hsrc]; exact (hs.sourceBytes.sub (offset + phase) 1 (by omega)).readable hsrcLow)
      (by rw [hdst]; exact (hs.stateBytes.sub (offset + phase) 1 (by omega)).readable hdstLow)
      (by rw [hdst]; exact htables (offset + phase) (by omega))
      (by rw [hdst]; exact fun byte hb ↦ hseparate byte hb (offset + phase) (by omega)) hne₁ hne₂
  rw [hsrc, hdst, hs.sourceBytes.loadByte (offset + phase) (by omega)] at hmemory
  refine ⟨t, hrun, hready', hcode', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [show offset < count by omega, ↓reduceIte]
    exact hip'
  · exact (hframe.read (by simp)).trans hs.countReg
  · exact (hframe.read (by simp)).trans hs.indexReg
  · exact (hframe.read (by simp)).trans hs.sourceReg
  · exact (hframe.read (by simp)).trans hs.destinationReg
  · rw [hmemory]
    apply hs.sourceBytes.store_disjoint
    intro j hj k hk
    have hj0 : j = 0 := by omega
    subst j
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      hapart (offset + phase) (by omega) k hk
  · rw [hmemory]
    simpa only [Nat.add_assoc] using xor_prefix_byte hs.stateBytes (by omega) (by omega)
  · rw [hdst] at hframe
    apply hframe.widen
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> simp_all [chunkClobbers, Component.isMem]
    · intro x c hc hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact False.elim hx
      · obtain ⟨j, hj, rfl⟩ := hx
        have hj0 : j = 0 := by omega
        subst j
        refine ⟨.mem destination len, by simp [chunkClobbers], offset + phase, by omega, ?_⟩
        simp only [BitVec.add_zero]
      · exact False.elim hx
      · exact False.elim hx

include hspan hsourceLow hdestLow hapart htables hseparate hsub hne in
theorem chunk_four_bytes (offset : Nat) (hoffset : offset + 4 ≤ count) :
    AdvanceTriple boundary 8 (ChunkInvariant p source destination count len initial input offset 0)
      code (fun s t ↦ ChunkInvariant p source destination count len initial input offset 4 t ∧
        AgreesExcept (chunkClobbers destination len) s t) := by
  intro s hready hcode hs
  let invariant := fun i t ↦ ChunkInvariant p source destination count len initial input offset i t ∧
    AgreesExcept (chunkClobbers destination len) s t
  have body : ∀ i, i < 4 → AdvanceTriple boundary 2 (invariant i) code
      (fun _ t ↦ invariant (i + 1) t) := by
    intro i hi u hready' hcode' hu
    obtain ⟨t, hrun, hready'', hcode'', ht, hframe⟩ :=
      chunk_byte_advance boundary code p source destination count len initial input
        hspan hsourceLow hdestLow hapart htables hseparate hsub hne offset i hoffset hi
        u hready' hcode' hu.1
    refine ⟨t, hrun, hready'', hcode'', ht, (hu.2.trans hframe).mono ?_⟩
    intro c hc
    simpa only [List.mem_append, or_self] using hc
  exact AdvanceTriple.iterate 4 2 body s hready hcode ⟨hs, AgreesExcept.refl _ s⟩

include hspan hdestLow hsub hne in
theorem chunk_control (offset : Nat) (hoffset : offset + 4 ≤ count) :
    AdvanceTriple boundary 3 (ChunkInvariant p source destination count len initial input offset 4)
      code (fun s t ↦ ChunkInvariant p source destination count len initial input (offset + 4) 0 t ∧
        AgreesExcept (chunkClobbers destination len) s t) := by
  intro s hready hcode hs
  have hsub₄₂ : ∀ byte ∈ codeRange (p + 42#64) [0x48, 0x83, 0xc6, 0x04], byte ∈ code :=
    fun byte hb ↦ hsub byte (codeRange_mem_of_drop 42 (by decide +kernel) byte hb)
  have hadd : StepEffect (fun s ↦ s.RIP = p + 42#64)
      (codeRange (p + 42#64) [0x48, 0x83, 0xc6, 0x04])
      (addR64Imm8Effect (p + 42#64) 6#5 4#8) :=
    add_r64_imm8_effect_step (p + 42#64) 0x48 0xc6 4#8
      (by unfold RexWPrefix; decide) (by decide) (by decide)
  have hir : s.RIP = p + 42#64 := by
    simpa only [show offset < count by omega, ↓reduceIte, chunkPairOffset, Nat.lt_irrefl] using hs.rip
  have hnext₁ : p + 42#64 + 4#64 = p + 46#64 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨u, hrun₁, hready₁, hu⟩ := hadd.advances hready (hcode.mono hsub₄₂) hir
    (by simpa only [addR64Imm8Effect, BitVec.ofNat_eq_ofNat, hnext₁] using hne 46 (by decide))
  have hc₁ := hu.codeIn (addR64Imm8Effect_avoids _ _ _ s code) hcode
  have huip : u.RIP = BitVec.add p 46#64 := hu.rip.trans hnext₁
  have hcount : (Operand.reg 10#5 : Operand 64).read u = BitVec.ofNat 64 count :=
    (hu.agrees.read (by simp)).trans hs.countReg
  have hindex : (Operand.reg 6#5 : Operand 64).read u = BitVec.ofNat 64 (offset + 4) := by
    have h := hu.writes
    change (Operand.reg 6#5 : Operand 64).read u =
      (Operand.reg 6#5 : Operand 64).read s + 4#64 at h
    simpa only [hs.indexReg, ← BitVec.ofNat_add] using h
  have hsub₄₆ : ∀ byte ∈ codeRange (p + 46#64) [0x49, 0x39, 0xf2], byte ∈ code :=
    fun byte hb ↦ hsub byte (codeRange_mem_of_drop 46 (by decide +kernel) byte hb)
  have hnext₂ : p + 46#64 + 3#64 = p + 49#64 := by rw [BitVec.add_assoc]; rfl
  have hnext₃ : p + 46#64 + 5#64 = p + 51#64 := by rw [BitVec.add_assoc]; rfl
  have hsub₄₉ : ∀ byte ∈ codeRange (p + 46#64 + 3#64) (0x75 :: immBytes 8 0xcd#8),
      byte ∈ code := by
    rw [hnext₂]
    exact fun byte hb ↦ hsub byte (codeRange_mem_of_drop 49 (by decide +kernel) byte hb)
  have htarget : branchTarget (p + 46#64 + 3#64) 2 (BitVec.signExtend 64 0xcd#8) = p := by
    simp only [branchTarget, BitVec.add_assoc]
    change p + 0#64 = p
    exact BitVec.add_zero p
  have hlow : p.toNat < 2 ^ 32 := (hcode _ (hsub _ List.mem_cons_self)).1
  obtain ⟨t, hrun₂, hready₂, hc₂, htip, htframe⟩ :=
    chunk_compare_branch boundary code (p + 46#64) 0xcd#8 u hready₁ hc₁ huip
      hsub₄₆ hsub₄₉ (by rw [htarget]; exact hlow)
      (by rw [hnext₂]; exact hne 49 (by decide))
      (by rw [hnext₃]; exact hne 51 (by decide))
      (by rw [htarget]; simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hne 0 (by decide))
  have hframe : AgreesExcept [.reg 6#5, .flags, .rip] s t := by
    apply (hu.agrees.trans htframe).mono
    simp only [addR64Imm8Effect_components]
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with (rfl | rfl | rfl) | rfl | rfl <;> simp
  have hmemory := hframe.external (by simp [Component.Covers])
  refine ⟨t, hrun₁.trans hrun₂, hready₂, hc₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    hframe.mono (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [chunkClobbers])⟩
  · change t.RIP = (if ((Operand.reg 10#5 : Operand 64).read u -
      (Operand.reg 6#5 : Operand 64).read u == 0#64) then _ else _) at htip
    rw [hcount, hindex, Sha3.Proofs.Update.Tail.sub_ofNat_beq_zero
      (by omega) (by omega), hnext₃, htarget] at htip
    by_cases he : count = offset + 4
    · have hn : ¬ offset + 4 < count := by omega
      simpa only [he, decide_true, ↓reduceIte, hn, Nat.lt_irrefl] using htip
    · have hl : offset + 4 < count := by omega
      simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte] at htip
      simp only [hl, ↓reduceIte, chunkPairOffset, Nat.zero_lt_succ, Nat.mul_zero,
        Nat.zero_sub, BitVec.add_zero]
      exact htip
  · exact (hframe.read (by simp)).trans hs.countReg
  · exact (htframe.read (by simp)).trans hindex
  · exact (hframe.read (by simp)).trans hs.sourceReg
  · exact (hframe.read (by simp)).trans hs.destinationReg
  · simpa only [hmemory] using hs.sourceBytes
  · simpa only [hmemory, Nat.add_zero] using hs.stateBytes

include hspan hsourceLow hdestLow hapart htables hseparate hsub hne in
theorem chunk_iteration (offset : Nat) (hoffset : offset + 4 ≤ count) :
    AdvanceTriple boundary 11 (ChunkInvariant p source destination count len initial input offset 0)
      code (fun s t ↦ ChunkInvariant p source destination count len initial input (offset + 4) 0 t ∧
        AgreesExcept (chunkClobbers destination len) s t) := by
  intro s hready hcode hs
  obtain ⟨u, hrun₁, hready₁, hc₁, hu, hframe₁⟩ :=
    chunk_four_bytes boundary code p source destination count len initial input
      hspan hsourceLow hdestLow hapart htables hseparate hsub hne offset hoffset s hready hcode hs
  obtain ⟨t, hrun₂, hready₂, hc₂, ht, hframe₂⟩ :=
    chunk_control boundary code p source destination count len initial input
      hspan hdestLow hsub hne offset hoffset u hready₁ hc₁ hu
  refine ⟨t, hrun₁.trans hrun₂, hready₂, hc₂, ht, (hframe₁.trans hframe₂).mono ?_⟩
  intro c hc
  simpa only [List.mem_append, or_self] using hc

include hspan hsourceLow hdestLow hapart htables hseparate hsub hne in
theorem chunk_loop (groups : Nat) (hcount : count = 4 * groups) :
    AdvanceTriple boundary (groups * 11)
      (ChunkInvariant p source destination count len initial input 0 0) code
      (fun s t ↦ ChunkInvariant p source destination count len initial input count 0 t ∧
        AgreesExcept (chunkClobbers destination len) s t) := by
  intro s hready hcode hs
  let invariant := fun i t ↦ ChunkInvariant p source destination count len initial input (4 * i) 0 t ∧
    AgreesExcept (chunkClobbers destination len) s t
  have body : ∀ i, i < groups → AdvanceTriple boundary 11 (invariant i) code
      (fun _ t ↦ invariant (i + 1) t) := by
    intro i hi u hready' hcode' hu
    obtain ⟨t, hrun, hready'', hcode'', ht, hframe⟩ :=
      chunk_iteration boundary code p source destination count len initial input
        hspan hsourceLow hdestLow hapart htables hseparate hsub hne (4 * i) (by omega)
        u hready' hcode' hu.1
    refine ⟨t, hrun, hready'', hcode'', ?_, (hu.2.trans hframe).mono ?_⟩
    · simpa only [show 4 * i + 4 = 4 * (i + 1) by omega] using ht
    · intro c hc
      simpa only [List.mem_append, or_self] using hc
  obtain ⟨t, hrun, hready', hcode', ht, hframe⟩ :=
    AdvanceTriple.iterate groups 11 body s hready hcode ⟨hs, AgreesExcept.refl _ s⟩
  exact ⟨t, hrun, hready', hcode', hcount ▸ ht, hframe⟩

end ChunkLoop

end Sha3.Proofs.Update.Partial
