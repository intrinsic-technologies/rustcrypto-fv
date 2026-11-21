import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.LoopConcrete
namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

variable {lengthWritten : Prop}

open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions
open X86Proofs

set_option maxRecDepth 100000 in
 theorem decode_storePre_from_call {routine : Routine} {p : BitVec 64} {initial u : RamState} {input : List UInt8}
    {capacity : Nat} {count : Nat}
    (hvalid : ValidCall routine initial input capacity lengthWritten)
    (hrip : u.RIP = p)
    (hrdx : AddrMode.reg64 1 u = AddrMode.reg64 1 initial)
    (hrsi : AddrMode.reg64 0 u = BitVec.ofNat 64 count)
    (halloc : (outputRegion initial capacity).Allocated u.external)
    (hcount : count < capacity)
    (hprogram : ∀ j : Fin 3, InProgram (p + BitVec.ofNat 64 j.val)) :
    StorePre p 3
      (fun v => lowerStoreAM.addrAt v 3) 1 u := by
  let region := outputRegion initial capacity
  have hb := hvalid.outputInMemory.2.1
  have ha := hvalid.outputInMemory.2.2
  have havoid := hvalid.separation.2.1 (outputRegion initial capacity) (by simp)
  have haddr : lowerStoreAM.addrAt u 3 = BitVec.ofNat 64 (region.start + count) := by
    simp [lowerStoreAM, AddrMode.addr, AddrMode.addrAt, Disp.value]
    have hrdx' : AddrMode.reg64 (1#4) u = AddrMode.reg64 (1#4) initial := by simpa using hrdx
    have hrsi' : AddrMode.reg64 (0#4) u = BitVec.ofNat 64 count := by simpa using hrsi
    change AddrMode.reg64 (1#4) u + AddrMode.reg64 (0#4) u = _
    rw [hrdx', hrsi']
    have hr : AddrMode.reg64 (1#4) initial = initial.regValue .rcx := by rfl
    rw [hr]
    simp [region, outputRegion, registerRegion, BitVec.ofNat_add]
  have hlen : capacity = region.size := by
    change capacity = (outputRegion initial capacity).size
    rfl
  have halloc : region.Allocated u.external := halloc
  have hnat : (BitVec.ofNat 64 (region.start + count)).toNat = region.start + count := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    change region.start + region.size < 2 ^ 32 at hb
    rw [← hlen] at hb
    omega
  have hw : MemWritable u (BitVec.ofNat 64 (region.start + count)) 1 := by
    apply regionWritable hb halloc
    · intro a ha'
      exact (not_or.mp (havoid a ha')).2
    · change region.start ≤ (BitVec.ofNat 64 (region.start + count)).toNat
      rw [hnat]
      omega
    · change (BitVec.ofNat 64 (region.start + count)).toNat + 1 ≤ region.start + region.size
      rw [hnat]
      change region.start + count + 1 ≤ region.start + region.size
      rw [← hlen]
      omega
    · decide
    · rw [hnat]
      have hm := Nat.mod_lt (region.start + count) (by decide : 0 < 4096)
      omega
  refine ⟨hrip, ?_, ?_⟩
  · change MemWritable u (lowerStoreAM.addrAt u 3) 1
    rw [haddr]
    exact hw
  · intro i hi j hj heq
    have hi0 : i = 0 := by omega
    subst i
    rw [BitVec.add_zero, haddr] at heq
    have hreg : region.Contains (BitVec.ofNat 64 (region.start + count)).toNat := by
      rw [hnat]
      change region.start ≤ region.start + count ∧ region.start + count < region.start + region.size
      rw [← hlen]
      omega
    have hnot := havoid (BitVec.ofNat 64 (region.start + count)) hreg
    apply hnot
    left
    rw [heq]
    exact hprogram ⟨j, hj⟩

end Base16ct.Proofs.Base16ctUpperDecodeCorrect

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

variable {lengthWritten : Prop}
open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions
set_option maxRecDepth 100000 in
theorem decode_storeAvoid_from_call {routine : Routine} {p : BitVec 64} {initial u : RamState} {input : List UInt8}
    {capacity count : Nat}
    (hvalid : ValidCall routine initial input capacity lengthWritten)
    (hrdx : AddrMode.reg64 1 u = AddrMode.reg64 1 initial)
    (hrsi : AddrMode.reg64 0 u = BitVec.ofNat 64 count)
    (hcount : count < capacity) :
    (storeEffect p 3
      (fun v => lowerStoreAM.addrAt v 3)
      (fun v => (Operand.reg 5 : Operand 8).read v) u).Avoids programImage := by
  intro x hx c hc
  simp [Effect.components, storeEffect] at hc
  rcases hc with hc | hc
  · subst c
    intro hcover
    obtain ⟨i, hi, hxi⟩ := hcover
    have haddr : lowerStoreAM.addrAt u 3 =
        BitVec.ofNat 64 ((outputRegion initial capacity).start + count) := by
      simp [lowerStoreAM, AddrMode.addr, AddrMode.addrAt, Disp.value]
      have hrdx' : AddrMode.reg64 (1#4) u = AddrMode.reg64 (1#4) initial := by simpa using hrdx
      have hrsi' : AddrMode.reg64 (0#4) u = BitVec.ofNat 64 count := by simpa using hrsi
      change AddrMode.reg64 (1#4) u + AddrMode.reg64 (0#4) u = _
      rw [hrdx', hrsi']
      have hr : AddrMode.reg64 (1#4) initial = initial.regValue .rcx := by rfl
      rw [hr]
      simp [outputRegion, registerRegion, BitVec.ofNat_add]
    have hxi' : x.1 = BitVec.ofNat 64 ((outputRegion initial capacity).start + count) + BitVec.ofNat 64 i := by
      simpa [Component.Covers, haddr] using hxi
    have hout := hvalid.separation.2.1 (outputRegion initial capacity) (by simp)
      (BitVec.ofNat 64 ((outputRegion initial capacity).start + count))
    have hlen : capacity = (outputRegion initial capacity).size := by rfl
    have hb := hvalid.outputInMemory.2.1
    have hnat : (BitVec.ofNat 64 ((outputRegion initial capacity).start + count)).toNat =
        (outputRegion initial capacity).start + count := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      change (outputRegion initial capacity).start + (outputRegion initial capacity).size < 2 ^ 32 at hb
      rw [← hlen] at hb
      omega
    have hcontains : (outputRegion initial capacity).Contains
        (BitVec.ofNat 64 ((outputRegion initial capacity).start + count)).toNat := by
      rw [hnat]
      change (outputRegion initial capacity).start ≤ (outputRegion initial capacity).start + count ∧
        (outputRegion initial capacity).start + count < (outputRegion initial capacity).start + (outputRegion initial capacity).size
      rw [← hlen]
      omega
    have hforbid := hout hcontains
    apply hforbid
    left
    have hi0 : i = 0 := by omega
    subst i
    have hxi0 : x.fst = BitVec.ofNat 64 ((outputRegion initial capacity).start + count) := by
      simpa [BitVec.add_zero] using hxi'
    rw [← hxi0]
    exact ⟨x.2, hx⟩
  · subst c
    simp [Component.Covers]

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
