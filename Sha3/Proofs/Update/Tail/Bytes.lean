import Sha3.Proofs.Update.Partial.ByteXor
import Sha3.Proofs.Update.Tail.Compare
import Sha3.Proofs.X86.Instructions.Inc.Triple

namespace Sha3.Proofs.Update.Tail

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha3.Proofs.Update.Partial

theorem tail_byte_pair [Bindings] (boundary : ReturnBoundary) (code : CodeMap)
    (p : BitVec 64) (s : RamState) (hready : ReadyToStep s) (hcode : CodeIn code s)
    (hip : s.RIP = p)
    (hloadCode : ∀ byte ∈ codeRange p [0x0f, 0xb6, 0x14, 0x0b], byte ∈ code)
    (hstoreCode : ∀ byte ∈ codeRange (p + 4#64) [0x41, 0x30, 0x14, 0x0f], byte ∈ code)
    (hsource : MemReadable s (((Operand.reg 3#5 : Operand 64).read s) + ((Operand.reg 1#5 : Operand 64).read s)) 1)
    (hdest : MemReadable s (((Operand.reg 15#5 : Operand 64).read s) + ((Operand.reg 1#5 : Operand 64).read s)) 1)
    (htables : ¬ Spec.Program.InPageTables (((Operand.reg 15#5 : Operand 64).read s) + ((Operand.reg 1#5 : Operand 64).read s)))
    (hseparate : ∀ byte ∈ code, byte.1 ≠ ((Operand.reg 15#5 : Operand 64).read s) + ((Operand.reg 1#5 : Operand 64).read s))
    (hne₁ : p + 4#64 ≠ boundary.rip) (hne₂ : p + 8#64 ≠ boundary.rip) :
    ∃ t : RamState, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn code t ∧ t.RIP = BitVec.add p 8#64 ∧
      t.external = memStore s.external (((Operand.reg 15#5 : Operand 64).read s) + ((Operand.reg 1#5 : Operand 64).read s))
        (memLoad s.external (((Operand.reg 15#5 : Operand 64).read s) + ((Operand.reg 1#5 : Operand 64).read s)) 8 ^^^
          memLoad s.external (((Operand.reg 3#5 : Operand 64).read s) + ((Operand.reg 1#5 : Operand 64).read s)) 8) ∧
      AgreesExcept [.reg 2#5, .mem (((Operand.reg 15#5 : Operand 64).read s) + ((Operand.reg 1#5 : Operand 64).read s)) 1, .flags, .rip] s t := by
  let amLoad : AddrMode := .sib 3 (some 1) 0 .none
  let amStore : AddrMode := .sib 15 (some 1) 0 .none
  have hload : StepEffect (LoadPre p (fun t ↦ amLoad.addr t (p + 4#64)) 1)
      (codeRange p [0x0f, 0xb6, 0x14, 0x0b]) (movzxR32M8Effect p 4 2 amLoad) := by
    have h := movzx_r32_m8_effect_step p 2 amLoad ⟨by decide, by decide⟩ rfl rfl
    simp only [BitVec.ofNat_eq_ofNat] at h
    simpa only [show 3 + amLoad.tail.length = 4 from rfl,
      show amLoad.modrm 2#3 = 0x14 by dsimp [amLoad]; decide +kernel,
      show amLoad.tail = [0x0b] from rfl,
      show gprNumber 0#1 0#1 2#3 = 2#5 from rfl,
      List.length_singleton, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  have hstore : StepEffect (StorePreReadable (p + 4#64) (storeAddrAt (p + 4#64) amStore 4) 1)
      (codeRange (p + 4#64) [0x41, 0x30, 0x14, 0x0f]) (xorMREffect (p + 4#64) 4 8 2 amStore) := by
    have h := xor_m8_r8_rex_effect_step_of_readable (p + 4#64) 0x41
      (by unfold RexPrefix; decide) 2 amStore ⟨by decide, by decide⟩ rfl rfl
    simp only [BitVec.ofNat_eq_ofNat] at h
    simpa only [show 3 + amStore.tail.length = 4 from rfl,
      show amStore.modrm 2#3 = 0x14 by dsimp [amStore]; decide +kernel, show amStore.tail = [0x0f] from rfl,
      show gprNumber 0#1 (rexR (0x41 : UInt8).toBitVec) 2#3 = 2#5 from rfl,
      List.length_singleton, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  have hsrcEq (u : RamState) (next : BitVec 64) : amLoad.addr u next =
      (Operand.reg 3#5 : Operand 64).read u + (Operand.reg 1#5 : Operand 64).read u := by
    change (Operand.reg 3#5 : Operand 64).read u +
      ((Operand.reg 1#5 : Operand 64).read u <<< (0 : Nat)) + 0#64 = _
    simp only [BitVec.shiftLeft_zero, BitVec.add_zero]
  have hdstEq (u : RamState) (next : BitVec 64) : amStore.addr u next =
      (Operand.reg 15#5 : Operand 64).read u + (Operand.reg 1#5 : Operand 64).read u := by
    change (Operand.reg 15#5 : Operand 64).read u +
      ((Operand.reg 1#5 : Operand 64).read u <<< (0 : Nat)) + 0#64 = _
    simp only [BitVec.shiftLeft_zero, BitVec.add_zero]
  have hnext : p + 4#64 + 4#64 = p + 8#64 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨t, hrun, hready', hcode', hip', hmemory, hframe⟩ :=
    load_xor_byte boundary code _ _ p 4 4 2#5 amLoad amStore hload hstore
      hloadCode hstoreCode hne₁ (by simpa only [BitVec.ofNat_eq_ofNat, hnext] using hne₂)
      s hready hcode hip (by simpa only [hsrcEq] using hsource)
      (by simpa only [hdstEq] using hdest)
      (by
        intro u h
        simp only [hdstEq, h.read (r := 15#5) (by simp), h.read (r := 1#5) (by simp)])
      (by simpa only [hdstEq] using htables)
      (by simpa only [hdstEq] using hseparate)
  refine ⟨t, hrun, hready', hcode', hip'.trans hnext, ?_, ?_⟩
  · simpa only [hdstEq, hsrcEq] using hmemory
  · simpa only [hdstEq] using hframe

def tailBytes : List UInt8 :=
  [0x0f, 0xb6, 0x14, 0x0b, 0x41, 0x30, 0x14, 0x0f,
    0x48, 0xff, 0xc1, 0x48, 0x39, 0xc8, 0x75, 0xf0]

theorem tail_iteration [Bindings] (boundary : ReturnBoundary) (code : CodeMap)
    (p : BitVec 64) (s : RamState) (hready : ReadyToStep s) (hcode : CodeIn code s)
    (hip : s.RIP = p)
    (hsub : ∀ byte ∈ codeRange p tailBytes, byte ∈ code)
    (hsource : MemReadable s ((Operand.reg 3#5 : Operand 64).read s +
      (Operand.reg 1#5 : Operand 64).read s) 1)
    (hdest : MemReadable s ((Operand.reg 15#5 : Operand 64).read s +
      (Operand.reg 1#5 : Operand 64).read s) 1)
    (htables : ¬ Spec.Program.InPageTables ((Operand.reg 15#5 : Operand 64).read s +
      (Operand.reg 1#5 : Operand 64).read s))
    (hseparate : ∀ byte ∈ code, byte.1 ≠ (Operand.reg 15#5 : Operand 64).read s +
      (Operand.reg 1#5 : Operand 64).read s)
    (hne : ∀ i ∈ [0, 4, 8, 11, 14, 16], p + BitVec.ofNat 64 i ≠ boundary.rip) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ CodeIn code t ∧
      t.RIP = (if ((Operand.reg 0#5 : Operand 64).read s -
          ((Operand.reg 1#5 : Operand 64).read s + 1#64) == 0#64) then p + 16#64 else p) ∧
      (Operand.reg 1#5 : Operand 64).read t = (Operand.reg 1#5 : Operand 64).read s + 1#64 ∧
      t.external = memStore s.external
        ((Operand.reg 15#5 : Operand 64).read s + (Operand.reg 1#5 : Operand 64).read s)
        (memLoad s.external ((Operand.reg 15#5 : Operand 64).read s +
            (Operand.reg 1#5 : Operand 64).read s) 8 ^^^
          memLoad s.external ((Operand.reg 3#5 : Operand 64).read s +
            (Operand.reg 1#5 : Operand 64).read s) 8) ∧
      AgreesExcept [.reg 2#5, .reg 1#5,
        .mem ((Operand.reg 15#5 : Operand 64).read s +
          (Operand.reg 1#5 : Operand 64).read s) 1, .flags, .rip] s t := by
  have hsub₀ : ∀ byte ∈ codeRange p [0x0f, 0xb6, 0x14, 0x0b], byte ∈ code :=
    fun byte hb ↦ hsub byte (codeRange_mem_of_take (by decide +kernel) byte hb)
  have hsub₄ : ∀ byte ∈ codeRange (p + 4#64) [0x41, 0x30, 0x14, 0x0f], byte ∈ code :=
    fun byte hb ↦ hsub byte (codeRange_mem_of_drop 4 (by decide +kernel) byte hb)
  obtain ⟨u, hrun₁, hready₁, hc₁, huip, humem, huframe⟩ :=
    tail_byte_pair boundary code p s hready hcode hip hsub₀ hsub₄ hsource hdest htables
      hseparate (hne 4 (by simp)) (hne 8 (by simp))
  have hinc : StepEffect (fun s ↦ s.RIP = p + 8#64)
      (codeRange (p + 8#64) [0x48, 0xff, 0xc1]) (incR64Effect (p + 8#64) 1#5) :=
    inc_r64_effect_step (p + 8#64) 0x48 0xc1 (by unfold RexWPrefix; decide)
      (by decide) (by decide)
  have hsub₈ : ∀ byte ∈ codeRange (p + 8#64) [0x48, 0xff, 0xc1], byte ∈ code :=
    fun byte hb ↦ hsub byte (codeRange_mem_of_drop 8 (by decide +kernel) byte hb)
  have hnext₁ : p + 8#64 + 3#64 = p + 11#64 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨v, hrun₂, hready₂, hv⟩ := hinc.advances (boundary := boundary) hready₁ (hc₁.mono hsub₈) huip
    (by simpa only [incR64Effect, BitVec.ofNat_eq_ofNat, hnext₁] using hne 11 (by simp))
  have hc₂ : CodeIn code v := hv.codeIn (incR64Effect_avoids _ _ _ code) hc₁
  have hvip : v.RIP = BitVec.add p 11#64 := hv.rip.trans hnext₁
  have hreg₂u : (Operand.reg 1#5 : Operand 64).read u =
      (Operand.reg 1#5 : Operand 64).read s := huframe.read (by simp)
  have hreg₀v : (Operand.reg 0#5 : Operand 64).read v =
      (Operand.reg 0#5 : Operand 64).read s :=
    (hv.agrees.read (by simp)).trans (huframe.read (by simp))
  have hreg₂v : (Operand.reg 1#5 : Operand 64).read v =
      (Operand.reg 1#5 : Operand 64).read s + 1#64 := by
    have h := hv.writes
    change (Operand.reg 1#5 : Operand 64).read v =
      (Operand.reg 1#5 : Operand 64).read u + 1 at h
    simpa only [hreg₂u, BitVec.ofNat_eq_ofNat] using h
  have hsub₁₁ : ∀ byte ∈ codeRange (p + 11#64) [0x48, 0x39, 0xc8], byte ∈ code :=
    fun byte hb ↦ hsub byte (codeRange_mem_of_drop 11 (by decide +kernel) byte hb)
  have hsub₁₄ : ∀ byte ∈ codeRange (p + 11#64 + 3#64) (0x75 :: immBytes 8 0xf0#8),
      byte ∈ code := by
    have he : p + 11#64 + 3#64 = p + 14#64 := by rw [BitVec.add_assoc]; rfl
    rw [he]
    exact fun byte hb ↦ hsub byte (codeRange_mem_of_drop 14 (by decide +kernel) byte hb)
  have htarget : branchTarget (p + 11#64 + 3#64) 2 (BitVec.signExtend 64 0xf0#8) = p := by
    simp only [branchTarget, BitVec.add_assoc]
    change p + 0#64 = p
    exact BitVec.add_zero p
  have hlow : p.toNat < 2 ^ 32 := (hcode _ (hsub _ (List.mem_cons_self))).1
  have hnext₂ : p + 11#64 + 3#64 = p + 14#64 := by rw [BitVec.add_assoc]; rfl
  have hnext₃ : p + 11#64 + 5#64 = p + 16#64 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨t, hrun₃, hready₃, hc₃, htip, htframe⟩ :=
    compare_register_branch boundary code (p + 11#64) 0#3 1#3 0xf0#8 v hready₂ hc₂ hvip hsub₁₁ hsub₁₄
      (by rw [htarget]; exact hlow) (by rw [hnext₂]; exact hne 14 (by simp))
      (by rw [hnext₃]; exact hne 16 (by simp))
      (by rw [htarget]; simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hne 0 (by simp))
  refine ⟨t, (hrun₁.trans hrun₂).trans hrun₃, hready₃, hc₃, ?_, ?_, ?_, ?_⟩
  · simpa only [show (0#3).setWidth 5 = 0#5 from rfl,
      show (1#3).setWidth 5 = 1#5 from rfl, hreg₀v, hreg₂v, htarget, hnext₃] using htip
  · exact (htframe.read (by simp)).trans hreg₂v
  · rw [htframe.external (by simp [Component.Covers]),
      hv.agrees.external (by simp [Component.Covers]), humem]
  · apply ((huframe.trans hv.agrees).trans htframe).mono
    simp only [incR64Effect_components]
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with ((rfl | rfl | rfl | rfl) | rfl | rfl | rfl) | rfl | rfl <;> simp

structure TailInvariant (p source destination : BitVec 64) (offset count len : Nat)
    (initial input : Nat → UInt8) (i : Nat) (s : RamState) : Prop where
  rip : s.RIP = if i < count then p else p + 16#64
  countReg : (Operand.reg 0#5 : Operand 64).read s = BitVec.ofNat 64 count
  indexReg : (Operand.reg 1#5 : Operand 64).read s = BitVec.ofNat 64 i
  sourceReg : (Operand.reg 3#5 : Operand 64).read s = source
  destinationReg : (Operand.reg 15#5 : Operand 64).read s = destination + BitVec.ofNat 64 offset
  sourceBytes : Bytes s.external source count (fun j ↦ input (offset + j))
  stateBytes : Bytes s.external destination len
    (fun j ↦ initial j ^^^ (if j < offset + i then input j else 0))

def tailClobbers (destination : BitVec 64) (len : Nat) : List Component :=
  [.reg 2#5, .reg 1#5, .mem destination len, .flags, .rip]

section TailLoop

variable [Bindings] (boundary : ReturnBoundary) (code : CodeMap)
    (p source destination : BitVec 64) (offset count len : Nat)
    (initial input : Nat → UInt8)
    (hspan : offset + count ≤ len)
    (hsourceLow : source.toNat + count ≤ 2 ^ 32)
    (hdestLow : destination.toNat + len ≤ 2 ^ 32)
    (hapart : RangeApart destination len source count)
    (htables : ∀ i < len, ¬ Spec.Program.InPageTables (destination + BitVec.ofNat 64 i))
    (hseparate : ∀ byte ∈ code, ∀ i < len, byte.1 ≠ destination + BitVec.ofNat 64 i)
    (hsub : ∀ byte ∈ codeRange p tailBytes, byte ∈ code)
    (hne : ∀ i ∈ [0, 4, 8, 11, 14, 16], p + BitVec.ofNat 64 i ≠ boundary.rip)

include hspan hsourceLow hdestLow hapart htables hseparate hsub hne in
 theorem tail_advance (i : Nat) (hi : i < count) :
    AdvanceTriple boundary 5 (TailInvariant p source destination offset count len initial input i)
      code (fun s t ↦ TailInvariant p source destination offset count len initial input (i + 1) t ∧
        AgreesExcept (tailClobbers destination len) s t) := by
  intro s hready hcode hs
  have hsrc : ((Operand.reg 3#5 : Operand 64).read s +
      (Operand.reg 1#5 : Operand 64).read s) = source + BitVec.ofNat 64 i := by
    rw [hs.sourceReg, hs.indexReg]
  have hdst : ((Operand.reg 15#5 : Operand 64).read s +
      (Operand.reg 1#5 : Operand 64).read s) = destination + BitVec.ofNat 64 (offset + i) := by
    rw [hs.destinationReg, hs.indexReg, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hir : s.RIP = p := by simpa only [hi, ↓reduceIte] using hs.rip
  have hsrcLow : (source + BitVec.ofNat 64 i).toNat + 1 ≤ 2 ^ 32 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hdstLow : (destination + BitVec.ofNat 64 (offset + i)).toNat + 1 ≤ 2 ^ 32 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  obtain ⟨t, hrun, hready', hcode', hip', hindex, hmemory, hframe⟩ :=
    tail_iteration boundary code p s hready hcode hir hsub
      (by rw [hsrc]; exact (hs.sourceBytes.sub i 1 (by omega)).readable hsrcLow)
      (by rw [hdst]; exact (hs.stateBytes.sub (offset + i) 1 (by omega)).readable hdstLow)
      (by rw [hdst]; exact htables (offset + i) (by omega))
      (by rw [hdst]; exact fun byte hb ↦ hseparate byte hb (offset + i) (by omega)) hne
  have hindex' : (Operand.reg 1#5 : Operand 64).read t = BitVec.ofNat 64 (i + 1) := by
    simpa only [hs.indexReg, ← BitVec.ofNat_add] using hindex
  have hip'' : t.RIP = if i + 1 < count then p else p + 16#64 := by
    rw [hs.countReg, hs.indexReg] at hip'
    have heq : (BitVec.ofNat 64 count - (BitVec.ofNat 64 i + 1#64) == 0#64) =
        decide (count = i + 1) := by
      simpa only [← BitVec.ofNat_add] using
        (sub_ofNat_beq_zero (n := 64) (a := count) (b := i + 1) (by omega) (by omega))
    rw [heq] at hip'
    by_cases he : count = i + 1
    · have hnot : ¬ i + 1 < count := by omega
      simpa only [he, decide_true, ↓reduceIte, hnot, Nat.lt_irrefl] using hip'
    · have hlt : i + 1 < count := by omega
      simpa only [he, decide_false, Bool.false_eq_true, ↓reduceIte, hlt] using hip'
  rw [hsrc, hdst, hs.sourceBytes.loadByte i hi] at hmemory
  refine ⟨t, hrun, hready', hcode', ⟨hip'', ?_, hindex', ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (hframe.read (by simp)).trans hs.countReg
  · exact (hframe.read (by simp)).trans hs.sourceReg
  · exact (hframe.read (by simp)).trans hs.destinationReg
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
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp_all [tailClobbers, Component.isMem]
    · intro x c hc hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact False.elim hx
      · exact False.elim hx
      · obtain ⟨j, hj, rfl⟩ := hx
        have hj0 : j = 0 := by omega
        subst j
        refine ⟨.mem destination len, by simp [tailClobbers], offset + i, by omega, ?_⟩
        simp only [BitVec.add_zero]
      · exact False.elim hx
      · exact False.elim hx

include hspan hsourceLow hdestLow hapart htables hseparate hsub hne in
theorem tail_loop :
    AdvanceTriple boundary (count * 5)
      (TailInvariant p source destination offset count len initial input 0) code
      (fun s t ↦ TailInvariant p source destination offset count len initial input count t ∧
        AgreesExcept (tailClobbers destination len) s t) := by
  intro s hready hcode hs
  let invariant := fun i t ↦ TailInvariant p source destination offset count len initial input i t ∧
    AgreesExcept (tailClobbers destination len) s t
  have body : ∀ i, i < count → AdvanceTriple boundary 5 (invariant i) code
      (fun _ t ↦ invariant (i + 1) t) := by
    intro i hi u hready' hcode' hu
    obtain ⟨t, hrun, hready'', hcode'', ht, hframe⟩ :=
      tail_advance boundary code p source destination offset count len initial input
        hspan hsourceLow hdestLow hapart htables hseparate hsub hne i hi u hready' hcode' hu.1
    refine ⟨t, hrun, hready'', hcode'', ht, (hu.2.trans hframe).mono ?_⟩
    intro c hc
    simpa only [List.mem_append, or_self] using hc
  exact AdvanceTriple.iterate count 5 body s hready hcode ⟨hs, AgreesExcept.refl _ s⟩

end TailLoop

end Sha3.Proofs.Update.Tail
