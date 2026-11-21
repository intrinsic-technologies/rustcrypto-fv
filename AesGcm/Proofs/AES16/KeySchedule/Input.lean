import AesGcm.Proofs.AES16.KeySchedule.Entry
import AesGcm.Proofs.AES16.Input

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def inputMemory (use256 later : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let src := args[12].get 64 + (if later then 16 else 0)
  let raw := sp + (if use256 then 288 else 200)
  let lo := memLoad mem src 64
  let hi := memLoad mem (src + 8) 64
  let mem := memStore mem (raw + 8) hi
  let mem := memStore mem raw lo
  memStore mem (sp - 8)
    (if later then (0x105856 : BitVec 64) else if use256 then 0x105825 else 0x1043d2)

attribute [local irreducible] memStore memLoad

set_option maxHeartbeats 1200000 in
theorem key_input_call (use256 later : Bool) (hlater : later = true → use256 = true)
    (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram)
    (hbuffer : args[14].get 64 = args[4].get 64 + (if use256 then 12 else 8))
    (hstack : Writable code mem (args[4].get 64 - 8) (if use256 then 312 else 224))
    (hkey : Readable mem (args[12].get 64) (if use256 then 32 else 16)) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if later then .l105825 else if use256 then .l1057f1 else .l1043a4), args, mem⟩ =
          .call callee continuation ∧
      callee.label = .l109ff0 ∧
      continuation.target = (if later then .l105856 else if use256 then .l105825 else .l1043d2) ∧
      continuation.guard = some ⟨64,
        if later then 0x105856 else if use256 then 0x105825 else 0x1043d2⟩ ∧
      callee.store = inputMemory use256 later args mem ∧
      (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = args[4].get 64 - 8 ∧
      (callee.arguments[7]'(by change 7 < 53; decide)).get 64 =
        args[4].get 64 + (if use256 then 12 else 8) + (if later then 16 else 0) ∧
      (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = 8 ∧
      (callee.arguments[2]'(by change 2 < 53; decide)).get 64 =
        args[4].get 64 + (if use256 then 288 else 200) ∧
      callee.arguments[12]'(by change 12 < 53; decide) = args[12] ∧
      callee.arguments[14]'(by change 14 < 53; decide) = args[14] ∧
      (callee.arguments[15]'(by change 15 < 53; decide)).get 64 =
        (if use256 && !later then (8 : BitVec 64) else args[15].get 64) ∧
      callee.arguments[3]'(by change 3 < 53; decide) = args[3] ∧
      callee.arguments[5]'(by change 5 < 53; decide) = args[5] ∧
      callee.arguments[13]'(by change 13 < 53; decide) = args[13] ∧
      callee.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      callee.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      callee.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      callee.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hstackRead := hstack.readable
  cases use256 <;> cases later
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hlater hbuffer hstack hstackRead hkey ⊢
  · have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n 0x1043a4 46 := by
      have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1043a4 x hx))
      have hl : LIR.bytes_l1043a4.length = 46 := by decide +kernel
      rw [hl] at hx
      exact hx.apart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      change LIR.program.runBlock (dialect code) ⟨.l1043a4, args, mem⟩ = _
      cfg_eval [hbuffer]
      refine_norm [hbuffer]
      runtime_guards call
      rfl
    all_goals first | rfl | (intro hTypes; runtime_typed) |
      runtime_finish [inputMemory, hbuffer]
    all_goals simp (config := { bitVecOfNat := false }) only
      [Bool.false_eq_true, ↓reduceIte,
      BitVec.add_assoc, BitVec.reduceAdd]
    all_goals first | rfl | (congr 3; exact (BitVec.add_zero _).symm)
  · exact False.elim (hlater trivial)
  · have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n 0x1057f1 52 := by
      have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1057f1 x hx))
      have hl : LIR.bytes_l1057f1.length = 52 := by decide +kernel
      rw [hl] at hx
      exact hx.apart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      change LIR.program.runBlock (dialect code) ⟨.l1057f1, args, mem⟩ = _
      cfg_eval [hbuffer]
      refine_norm [hbuffer]
      runtime_guards call
      rfl
    all_goals first | rfl | (intro hTypes; runtime_typed) |
      runtime_finish [inputMemory, hbuffer]
    all_goals simp (config := { bitVecOfNat := false }) only
      [Bool.false_eq_true, ↓reduceIte,
      BitVec.add_assoc, BitVec.reduceAdd]
    all_goals first | rfl | (congr 3; exact (BitVec.add_zero _).symm)
  · have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n 0x105825 49 := by
      have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l105825 x hx))
      have hl : LIR.bytes_l105825.length = 49 := by decide +kernel
      rw [hl] at hx
      exact hx.apart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      change LIR.program.runBlock (dialect code) ⟨.l105825, args, mem⟩ = _
      cfg_eval [hbuffer]
      refine_norm [hbuffer]
      runtime_guards call
      rfl
    all_goals first | rfl | (intro hTypes; runtime_typed) |
      runtime_finish [inputMemory, hbuffer]
    all_goals simp (config := { bitVecOfNat := false }) only
      [↓reduceIte,
      BitVec.add_assoc, BitVec.reduceAdd]
    all_goals first | rfl | (congr 3; exact (BitVec.add_zero _).symm)


theorem inputMemory_frame (use256 later : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Readable mem (args[4].get 64 - 8) (if use256 then 312 else 224)) :
    RamWriteFrame mem (inputMemory use256 later args mem)
      [span (args[4].get 64 - 8) 8,
        span (args[4].get 64 + (if use256 then 288 else 200)) 16] := by
  have hlow := hstack.low
  cases use256 <;> cases later
  all_goals simp only [inputMemory, Bool.false_eq_true, ↓reduceIte] at hstack hlow ⊢
  all_goals runtime_finish [span]

theorem inputMemory_load (use256 later : Bool) (args : Values Value Reg.count) (mem : Ram)
    (i : Fin 2) :
    memLoad (inputMemory use256 later args mem)
      (args[4].get 64 + (if use256 then 288 else 200) + BitVec.ofNat 64 (8 * i.val)) 64 =
      memLoad mem (args[12].get 64 + (if later then 16 else 0) +
        BitVec.ofNat 64 (8 * i.val)) 64 := by
  have hi : i = 0 ∨ i = 1 := by have := i.isLt; omega
  rcases hi with rfl | rfl
  all_goals cases use256 <;> cases later
  all_goals simp only [inputMemory, Bool.false_eq_true, ↓reduceIte, Fin.val_zero, Fin.val_one,
    Nat.mul_zero, Nat.mul_one, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    BitVec.add_assoc, BitVec.reduceAdd]
  all_goals
    refine (memLoad_memStore_of_rangeApart _ _ _ _ _ ?_).trans ?_
    · exact RangeApart.of_offsets (x := args[4].get 64) (addr_sub _ 8) rfl (by decide +kernel)
  all_goals first
    | exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    | (refine (memLoad_memStore_of_rangeApart _ _ _ _ _ ?_).trans ?_
       · exact RangeApart.of_offsets (x := args[4].get 64) rfl rfl (by decide +kernel)
       · exact memLoad_memStore_same _ _ _ (by decide) (by decide))

theorem inputMemory_block (use256 later : Bool) (args : Values Value Reg.count) (mem : Ram) :
    Fixslice.memoryBlock (inputMemory use256 later args mem)
      (args[4].get 64 + (if use256 then 288 else 200)) =
      Fixslice.memoryBlock mem (args[12].get 64 + (if later then 16 else 0)) := by
  funext j
  have hb := memByte_of_memLoad_eq
    (inputMemory_load use256 later args mem ⟨j.val / 8, by have := j.isLt; omega⟩)
    (j.val % 8) (by omega)
  have hj : 8 * (j.val / 8) + j.val % 8 = j.val := by omega
  simpa only [Fixslice.memoryBlock, BitVec.add_assoc, ← BitVec.ofNat_add, hj]
    using congrArg UInt8.toBitVec hb

end AesGcm.Proofs.Machine.AES16.KeySchedule
