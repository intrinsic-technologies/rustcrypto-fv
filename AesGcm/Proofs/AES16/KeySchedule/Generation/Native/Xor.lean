import AesGcm.Proofs.AES16.KeySchedule.XorColumns
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Calls
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Memory
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.State

namespace AesGcm.Proofs.Machine.AES16.KeySchedule.Generation.Native

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 800000 in
theorem xor_exec (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (round : Nat) (hr : (variant use256).Nk / 4 ≤ round)
    (hrLast : round ≤ (variant use256).Nr)
    (args : Values Value Reg.count) (mem : Ram) (sp : BitVec 64)
    (hmemory : MemoryReady use256 code mem sp)
    (hsp : args[4] = ⟨64, sp - 8⟩)
    (hdi : args[7] = ⟨64, base use256 sp⟩)
    (hsi : args[6] = ⟨64, if use256 then 120 else 88⟩)
    (hdx : args[2] = ⟨64, BitVec.ofNat 64 (8 * round)⟩)
    (hcx : args[1] = ⟨64, if use256 then 16 else 8⟩)
    (h8 : args[8] = ⟨64, if use256 && oddRound round then 3 else 7⟩)
    (ht : GPRsTyped args) (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) (hDF : args[22] = ⟨1, 0⟩)
    (previous substituted : Fixslice16.Planes16)
    (hprevious : WordsAt mem (base use256 sp + BitVec.ofNat 64 (16 * (round - (variant use256).Nk / 4)))
      16 (Vector.ofFn previous))
    (hsubstituted : WordsAt mem (base use256 sp + BitVec.ofNat 64 (16 * round))
      16 (Vector.ofFn substituted)) :
    ∃ out : Output Value Ram Reg.count,
      LIR.program.Exec (dialect code)
        ⟨⟨.l104010, args, memStore mem (sp - 8) (afterReturn use256 (oddRound round))⟩, []⟩ out ∧
      out.tag = some ⟨64, afterReturn use256 (oddRound round)⟩ ∧
      out.values[4] = ⟨64, sp⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
        out.values[r] = args[r]) ∧ GPRsTyped out.values ∧
      RamWriteFrame mem out.store (roundRegions use256 sp round) ∧
      WordsAt out.store (base use256 sp + BitVec.ofNat 64 (16 * round))
        16 (Vector.ofFn (xorColumns previous substituted
          (if use256 && oddRound round then 3 else 7))) := by
  have hrBound : round ≤ 14 := by cases use256 <;> simp only [variant, Variant.Nr, Bool.false_eq_true, ↓reduceIte] at hrLast <;> omega
  have hs : args[4].get 64 = sp - 8 := by rw [hsp]; rfl
  let ret := afterReturn use256 (oddRound round)
  let pushed := memStore mem (sp - 8) ret
  let fr := activationOfValues pushed args ret (sp - 248)
  have hdi' : fr.rdi = base use256 sp := by change args[7].get 64 = _; rw [hdi]; rfl
  have hsi' : fr.rsi = (if use256 then 120 else 88) := by change args[6].get 64 = _; rw [hsi]; rfl
  have hdxNat : fr.rdx.toNat = 8 * round := by
    change (args[2].get 64).toNat = _
    rw [hdx]
    change (BitVec.ofNat 64 (8 * round)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcxNat : fr.rcx.toNat = (if use256 then 16 else 8) := by
    change (args[1].get 64).toNat = _
    rw [hcx]
    cases use256 <;> rfl
  have h8Nat : fr.r8.toNat = (if use256 && oddRound round then 3 else 7) := by
    change (args[8].get 64).toNat = _
    rw [h8]
    split <;> rfl
  have hlen : 2 * fr.rsi.toNat = (if use256 then 240 else 176) := by
    rw [hsi']; cases use256 <;> decide
  have hpf := push_frame hmemory round ret
  have hpm := memoryReady_of_frame hmemory hpf (round_stack_within hmemory round hrLast)
  have hpre : Writable code pushed fr.rdi (2 * fr.rsi.toNat) ∧
      fr.rsi.toNat ≤ 120 ∧ 8 ≤ fr.rcx.toNat ∧ fr.rcx.toNat ≤ fr.rdx.toNat ∧
      fr.rdx.toNat + 8 ≤ fr.rsi.toNat ∧ fr.r8.toNat < 16 ∧
      (callStack fr).Disjoint (span fr.rdi (2 * fr.rsi.toNat)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdi', hlen]; exact schedule_writable hpm
    · rw [hsi']; cases use256 <;> decide
    · rw [hcxNat]; cases use256 <;> decide
    · rw [hcxNat, hdxNat]
      cases use256 <;> simp only [variant, Variant.Nk, Bool.false_eq_true, ↓reduceIte] at * <;> omega
    · rw [hdxNat, hsi']
      cases use256 <;> simp only [variant, Variant.Nr, Bool.false_eq_true, ↓reduceIte,
        BitVec.reduceToNat] at * <;> omega
    · rw [h8Nat]; split <;> decide
    · rw [hdi']
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, callStack, activationOfValues, fr] using
        callStack_disjoint hmemory args ret hs 0 (2 * fr.rsi.toNat) (by cases use256 <;> decide)
  obtain ⟨out, hexec, htag, hdone, htypes, hframe, hpost⟩ :=
    pushed_call_exec LIR.lifted code .l104010 LIR.Fn104010.frameInfo _ _ _
      (xorColumns_callContract code hcode) mem args sp ret hmemory hs ht h39 h50 h51 hDF
      (by dsimp only [ret]; cases use256 <;> generalize oddRound round = odd <;> cases odd <;> decide)
      (by decide) (by intro x hx; exact hx) hpre
  have hd := pushed_call_done LIR.Fn104010.frameInfo rfl rfl code pushed args sp ret
    (sp - 248) out hs ht h39 h50 h51 hDF hdone
  have hframe' : RamWriteFrame mem out.store (roundRegions use256 sp round) := by
    apply hpf.trans hframe
    change RegionsWithin [fr.region, span (fr.rdi + BitVec.ofNat 64 (2 * fr.rdx.toNat)) 16] _
    rw [hdi', hdxNat, show 2 * (8 * round) = 16 * round by omega]
    exact callee_within hmemory args ret hs round
  refine ⟨out, hexec, htag, hd.1, hd.2, htypes, hframe', ?_⟩
  intro p hp
  have he := hpost ⟨p, hp⟩
  change memLoad out.store (fr.rdi + BitVec.ofNat 64 (2 * (fr.rdx.toNat + p))) 16 =
    xorColumnsWord (memLoad pushed (fr.rdi + BitVec.ofNat 64 (2 * (fr.rdx.toNat - fr.rcx.toNat + p))) 16)
      (memLoad pushed (fr.rdi + BitVec.ofNat 64 (2 * (fr.rdx.toNat + p))) 16) fr.r8.toNat at he
  rw [hdi', hdxNat, hcxNat, h8Nat] at he
  have ha : 2 * (8 * round + p) = 16 * round + 2 * p := by omega
  have hb : 2 * (8 * round - (if use256 then 16 else 8) + p) =
      16 * (round - (variant use256).Nk / 4) + 2 * p := by
    cases use256 <;> simp only [variant, Variant.Nk, Bool.false_eq_true, ↓reduceIte] at * <;> omega
  rw [ha, hb, push_load hmemory ret _ (by
    have := round_bound use256 round hrLast
    omega), push_load hmemory ret _ (by
    have := round_bound use256 round hrLast
    omega)] at he
  have hprev := hprevious p hp
  have hsub := hsubstituted p hp
  simp only [wordAddr, Vector.getElem_ofFn, Nat.reduceDiv, Nat.mul_comm,
    BitVec.add_assoc, ← BitVec.ofNat_add] at hprev hsub he ⊢
  rw [hprev, hsub] at he
  exact he

end AesGcm.Proofs.Machine.AES16.KeySchedule.Generation.Native
