import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.GHASHUpdate.ByteReverse
import AesGcm.Proofs.Machine.GHASHUpdate.Memory
import AesGcm.Proofs.Machine.LIR.Fn109980.Frame

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

private theorem tail_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x109a00 157 := by
  have hx := storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l109a00 x hx))
  have hlen : LIR.bytes_l109a00.length = 157 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

def driverTailFrame : StackFrame Value LIR.Label signature Reg.count :=
  { target := .l109a9d, kept := #v[], arity := rfl, guard := some ⟨64, 0x109a9d⟩ }

set_option maxHeartbeats 1000000 in
theorem driver_tail_call_runBlock (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp src offset dst : BitVec 64)
    (hsp : args[4].get 64 = sp) (hsrc : args[3].get 64 = src)
    (hoff : args[12].get 64 = offset) (hdst : args[14].get 64 = dst)
    (hscratch : args[15].get 64 = sp + 8) (hTypes : GPRsTyped args)
    (hr : Readable mem (src + offset) 16)
    (hw : Writable code mem (sp - 8) 32) (hroom : 8 ≤ sp.toNat) :
    ∃ nextArgs : Values Value Reg.count, ∃ outMem : Ram,
      LIR.program.runBlock (dialect code) ⟨.l109a00, args, mem⟩ =
        .call ⟨.l1034c0, nextArgs, outMem⟩ driverTailFrame ∧
      nextArgs[4] = ⟨64, sp - 8⟩ ∧ nextArgs[6] = ⟨64, sp + 8⟩ ∧
      nextArgs[7] = ⟨64, dst⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
        nextArgs[r] = args[r]) ∧ GPRsTyped nextArgs ∧
      RamWriteFrame mem outMem [span (sp - 8) 32] ∧
      memLoad outMem (sp - 8) 64 = 0x109a9d ∧
      (memLoad outMem (sp + 8) 64 = bswapSpec (memLoad mem (src + offset + 8) 64) ∧
        memLoad outMem (sp + 16) 64 = bswapSpec (memLoad mem (src + offset) 64)) := by
  have hhelperApart := @tail_rangeApart code hcode
  have hsr := hw.readable
  have hsl := hsr.low
  have hrl := hr.low
  runtime_context [hsp, hsrc, hoff, hdst, hscratch]
  refine ⟨?nextArgs, ?outMem, ?execution, ?sp, ?src, ?ptr, ?preserved, ?typed, ?frame, ?ret, ?words⟩
  case execution =>
    cfg_eval [hsp, hsrc, hoff, hdst, hscratch]
    runtime_guards call
    rfl
  case sp => runtime_finish []
  case src => runtime_finish []
  case ptr => runtime_finish []
  case preserved =>
    rintro ⟨r,hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case typed =>
    apply GPRsTyped.of_updates hTypes [0, 1, 2, 4, 6, 7]
    · rintro ⟨r,hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rintro ⟨r,hr⟩ hout
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
      have hc : r = 3 ∨ r = 5 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨
          r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case frame => runtime_finish [span]
  case ret => runtime_finish []

  case words =>
    constructor
    all_goals
      apply word64_eq_of_bytes
      intro i
      conv =>
        rhs
        rw [bswap64_extract_byte _ i.val i.isLt]
        rw [extractLsb'_memLoad _ _ (8*(7-i.val)) 8 (by omega) (by decide)
          (by have := i.isLt; omega)]
      rw [extractLsb'_memLoad _ _ (8*i.val) 8 (by omega) (by decide) (by have := i.isLt; omega)]
      rcases i with ⟨i,hi⟩
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      conv =>
        lhs; arg 2
        simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceSub,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      conv =>
        rhs; arg 2
        simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceSub,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    runtime_finish_all [rotate16_extract_low, rotate16_extract_high]
    change (memLoad mem (src + offset) 64).extractLsb' 0 8 = _
    rw [extractLsb'_memLoad _ _ 0 8 (by decide) (by decide) (by decide)]
    simp only [Nat.zero_div, BitVec.add_zero]

end AesGcm.Proofs.Machine.GHASHUpdate
