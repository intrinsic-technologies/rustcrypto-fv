import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def countMemory (mem : Ram) (sp source counter count : BitVec 64) : Ram :=
  let m1 := memStore mem (sp + 240) source
  let m2 := memStore m1 (sp + 320) count
  let m3 := memStore m2 (sp + 232) ((count.setWidth 32 &&& 3).setWidth 64)
  let m4 := memStore m3 (sp + 328) (count >>> 2)
  memStore m4 (sp + 248) counter

theorem countMemory_slots (mem : Ram) (sp source counter count : BitVec 64) :
    memLoad (countMemory mem sp source counter count) (sp + 232) 64 =
      BitVec.ofNat 64 (count.toNat % 4) ∧
    memLoad (countMemory mem sp source counter count) (sp + 240) 64 = source ∧
    memLoad (countMemory mem sp source counter count) (sp + 248) 64 = counter ∧
    memLoad (countMemory mem sp source counter count) (sp + 320) 64 = count ∧
    memLoad (countMemory mem sp source counter count) (sp + 328) 64 =
      BitVec.ofNat 64 (count.toNat / 4) := by
  have hrem : (count.setWidth 32 &&& 3).setWidth 64 = BitVec.ofNat 64 (count.toNat % 4) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_and]
    change (count.setWidth 32).toNat &&& (2 ^ 2 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth,
      Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2 ^ 32), BitVec.toNat_ofNat]
    omega
  have hbatch : count >>> 2 = BitVec.ofNat 64 (count.toNat / 4) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    have := count.isLt
    omega
  have hapart (m : Ram) (a b : BitVec 64) (v : BitVec 64)
      (h : 8 ≤ (b - a).toNat ∧ 8 ≤ (a - b).toNat) :=
    memLoad_memStore_apart m sp a b v 64 h (by decide) (by decide)
  simp (disch := decide) only [countMemory, hapart, memLoad_memStore_same,
    hrem, hbatch, and_self]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem count_split (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp descriptor counter source destination count : BitVec 64)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hdesc : args[3].get 64 = descriptor)
    (hspLow : sp.toNat + 336 ≤ 2 ^ 32)
    (hStack : Writable code mem (sp + 232) 104)
    (hDescriptor : Readable mem descriptor 32)
    (hApart : descriptor.toNat + 32 ≤ (sp + 232).toNat ∨
      (sp + 232).toNat + 104 ≤ descriptor.toNat)
    (hCounter : memLoad mem descriptor 64 = counter)
    (hSource : memLoad mem (descriptor + 8) 64 = source)
    (hDestination : memLoad mem (descriptor + 16) 64 = destination)
    (hCount : memLoad mem (descriptor + 24) 64 = count) :
    ∃ next : LIR.lifted.Location,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l108590 else .l107100), args, mem⟩ = .jump next ∧
      next.label = (if count >>> 2 = 0 then
        (if use256 then .l109509 else .l10805f) else
        (if use256 then .l1085da else .l10714a)) ∧
      next.store = countMemory mem sp source counter count ∧
      next.arguments[1]'(by change 1 < 53; decide) = ⟨64, count >>> 2⟩ ∧
      next.arguments[2]'(by change 2 < 53; decide) = ⟨64, destination⟩ ∧
      next.arguments[9]'(by change 9 < 53; decide) = ⟨64, counter⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame mem next.store [span (sp + 232) 104] := by
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hDescriptorLow := hDescriptor.low
  have hbase : (sp + 232).toNat = sp.toNat + 232 := by bv_omega
  runtime_context [hsp, hdesc, hCount, hCounter, hSource, hDestination]
  have hRange {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) : RangeApart a n
        (if use256 then 0x108590 else 0x107100) 74 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l107100 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l108590 x hx))).apart
  have hCountStored : memLoad (memStore mem (sp + 240) (memLoad mem (descriptor + 8) 64))
      (descriptor + 24) 64 = count := by
    runtime_finish [hCount]
  have hCountStoredSource : memLoad (memStore mem (sp + 240) source)
      (descriptor + 24) 64 = count := by simpa only [hSource] using hCountStored
  runtime_context [hCountStored, hCountStoredSource]
  by_cases hz : count >>> 2 = 0
  all_goals
    cases use256
    all_goals
      have hhelperApart := @hRange
      simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      rotate_left
      · first
        | change LIR.program.runBlock (dialect code) ⟨.l107100, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l108590, args, mem⟩ = _
        cfg_eval [LIR.program, hsp, hdesc]
        runtime_guards branch
        runtime_finish [hCount, hCounter, hSource, hDestination, hz]
        rfl
      · simp only [hz, ↓reduceIte]
        rfl
      · simp only [countMemory, hCountStoredSource, hCounter, hSource]
      · runtime_finish [hCount]
      · runtime_finish [hDestination]
      · runtime_finish [hCounter]
      · rintro ⟨r, hr⟩ hin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
        rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · runtime_typed
      · runtime_finish [span]

end AesGcm.Proofs.Machine.CTR
