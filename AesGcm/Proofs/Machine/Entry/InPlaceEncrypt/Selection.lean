import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem capacity_compare (len capacity : BitVec 64) :
    ((cmpSpec len capacity).CF || (cmpSpec len capacity).ZF) =
      decide (len.toNat ≤ capacity.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [Refine.cmpSpec_CF, cmpSpec_ZF, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq, ← BitVec.toNat_inj]
  omega

def selectedPointer (len capacity ptr : BitVec 64) : BitVec 64 :=
  if len.toNat ≤ capacity.toNat then ptr else 1

def selectedLength (len capacity : BitVec 64) : BitVec 64 :=
  if len.toNat ≤ capacity.toNat then len else 0

def descriptorMemory (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let ptr := selectedPointer (args[3].get 64) (args[5].get 64) (args[14].get 64)
  let len := selectedLength (args[3].get 64) (args[5].get 64)
  let mem := memStore mem (sp + 32) ptr
  let mem := memStore mem (sp + 40) ptr
  memStore mem (sp + 48) len

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2048 in
theorem core_call (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 64) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1016a8 else .l1013c8), args, mem⟩ = .call callee continuation ∧
      callee.label = (if use256 then .l102980 else .l102520) ∧
      continuation.target = (if use256 then .l1016e9 else .l101409) ∧
      continuation.guard = some ⟨64, if use256 then 0x1016e9 else 0x101409⟩ ∧
      callee.store = memStore (descriptorMemory args mem) (args[4].get 64 - 8)
        (if use256 then (0x1016e9 : BitVec 64) else 0x101409) ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + 15⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) =
        ⟨64, args[4].get 64 + (if use256 then 0x110 else 0xd0)⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, args[13].get 64⟩ ∧
      callee.arguments[1]'(by change 1 < 53; decide) = ⟨64, args[12].get 64⟩ ∧
      callee.arguments[8]'(by change 8 < 53; decide) = ⟨64, args[15].get 64⟩ ∧
      callee.arguments[9]'(by change 9 < 53; decide) = ⟨64, args[4].get 64 + 32⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] →
        callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x1016a8 else 0x1013c8) 65 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l1013c8 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l1016a8 x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l1013c8, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l1016a8, args, mem⟩ = _
      cfg_eval []
      simp only [capacity_compare, decide_eq_true_eq]
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish [descriptorMemory, selectedPointer, selectedLength]

theorem append_overflow_or_gt (len capacity : BitVec 64) :
    (!(subSpec len 0xfffffffffffffff0).2.CF ||
      !((cmpSpec (len + 16) capacity).CF || (cmpSpec (len + 16) capacity).ZF)) =
      decide (capacity.toNat < len.toNat + 16) := by
  rw [capacity_compare, Bool.eq_iff_iff]
  simp only [Refine.subSpec_CF, BitVec.reduceToNat, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le,
    BitVec.toNat_add, BitVec.reduceToNat]
  have hl := len.isLt
  have hc := capacity.isLt
  omega

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
