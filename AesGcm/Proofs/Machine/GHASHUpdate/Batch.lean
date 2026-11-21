import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.GHASHUpdate.ByteReverse
import AesGcm.Proofs.Machine.GHASHUpdate.Memory
import AesGcm.Proofs.Machine.LIR.Fn109ac0.Frame

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

private theorem batch_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x109ac0 705 := by
  have hx := storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l109ac0 x hx))
  have hlen : LIR.bytes_l109ac0.length = 705 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

def batchFrame : StackFrame Value LIR.Label signature Reg.count :=
  { target := .l109d81, kept := #v[], arity := rfl, guard := some ⟨64, 0x109d81⟩ }

set_option maxHeartbeats 1000000 in
theorem batch_runBlock (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (rsp src ptr : BitVec 64)
    (hsp : args[4].get 64 = rsp) (hsrc : args[6].get 64 = src)
    (hptr : args[7].get 64 = ptr) (hTypes : GPRsTyped args)
    (hr : Readable mem src 64) (hp : Readable mem ptr 8)
    (hw : Writable code mem (rsp - 144) 144) (hroom : 144 ≤ rsp.toNat)
    (hApartSrc : rsp.toNat ≤ src.toNat ∨ src.toNat + 64 ≤ rsp.toNat - 144)
    (hApartPtr : rsp.toNat ≤ ptr.toNat ∨ ptr.toNat + 8 ≤ rsp.toNat - 144) :
    ∃ nextArgs : Values Value Reg.count, ∃ outMem : Ram,
      LIR.program.runBlock (dialect code) ⟨.l109ac0, args, mem⟩ =
        .call ⟨.l1034d0, nextArgs, outMem⟩ batchFrame ∧
      nextArgs[4] = ⟨64, rsp - 144⟩ ∧ nextArgs[6] = ⟨64, rsp - 128⟩ ∧
      nextArgs[7] = ⟨64, memLoad mem ptr 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
        nextArgs[r] = args[r]) ∧ GPRsTyped nextArgs ∧
      RamWriteFrame mem outMem [span (rsp - 144) 144] ∧
      memLoad outMem (rsp - 144) 64 = 0x109d81 ∧
      (∀ j : Fin 4,
        memLoad outMem (rsp - 128 + BitVec.ofNat 64 (16*j.val)) 64 =
          bswapSpec (memLoad mem (src + BitVec.ofNat 64 (16*j.val+8)) 64) ∧
        memLoad outMem (rsp - 128 + BitVec.ofNat 64 (16*j.val+8)) 64 =
          bswapSpec (memLoad mem (src + BitVec.ofNat 64 (16*j.val)) 64)) := by
  have hhelperApart := @batch_rangeApart code hcode
  have hsr := hw.readable
  have hsl := hsr.low
  have hrl := hr.low
  have hpl := hp.low
  runtime_context [hsp, hsrc, hptr]
  refine ⟨?nextArgs, ?outMem, ?execution, ?sp, ?src, ?ptr, ?preserved, ?typed, ?frame, ?ret, ?words⟩
  case execution =>
    cfg_eval [hsp, hsrc, hptr]
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
    apply GPRsTyped.of_updates hTypes [0, 1, 4, 6, 7]
    · rintro ⟨r,hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl <;> rfl
    · rintro ⟨r,hr⟩ hout
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
      have hc : r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨
          r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case frame => runtime_finish [span]
  case ret => runtime_finish []

  case words =>
    rintro ⟨j,hj⟩
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl | rfl | rfl
    all_goals constructor
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

end AesGcm.Proofs.Machine.GHASHUpdate
