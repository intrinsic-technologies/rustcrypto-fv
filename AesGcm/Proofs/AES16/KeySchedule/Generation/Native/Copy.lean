import AesGcm.Proofs.AES16.KeySchedule.Copy
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Calls
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Memory
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.State

namespace AesGcm.Proofs.Machine.AES16.KeySchedule.Generation.Native

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 800000 in
theorem copy_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (round : Nat) (hr : (variant use256).Nk / 4 ≤ round)
    (hrLast : round ≤ (variant use256).Nr)
    (args : Values Value Reg.count) (mem : Ram) (sp : BitVec 64)
    (hready : Ready use256 round sp args)
    (hmemory : MemoryReady use256 code mem sp) :
    ∃ (nextArgs : Values Value Reg.count) (nextMem : Ram),
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨label use256 round, args, mem⟩, []⟩
        ⟨⟨subLabel use256 (oddRound round), nextArgs, nextMem⟩, []⟩ ∧
      Ready use256 round sp nextArgs ∧ SameFP args nextArgs ∧
      RamWriteFrame mem nextMem (roundRegions use256 sp round) ∧
      (∀ p : Fin 8,
        memLoad nextMem (base use256 sp + BitVec.ofNat 64 (16 * round + 2 * p.val)) 16 =
          memLoad mem (base use256 sp + BitVec.ofNat 64 (16 * (round - 1) + 2 * p.val)) 16) := by
  have hr1 : 1 ≤ round := by cases use256 <;> simp only [variant, Variant.Nk, Bool.false_eq_true, ↓reduceIte] at hr <;> omega
  have hrBound : round ≤ 14 := by cases use256 <;> simp only [variant, Variant.Nr, Bool.false_eq_true, ↓reduceIte] at hrLast <;> omega
  obtain ⟨ca, hcall, hsp, hdi, hsi, hdx, hkeep, ht⟩ :=
    copy_setup use256 (oddRound round) code hcode args mem sp hready.hsp hready.hTypes
      (push_writable hmemory)
  have hs : ca[4].get 64 = sp - 8 := by rw [hsp]; rfl
  have hc39 : ca[39] = args[39] := hkeep 39 (by decide)
  have hc50 : ca[50] = args[50] := hkeep 50 (by decide)
  have hc51 : ca[51] = args[51] := hkeep 51 (by decide)
  have hc22 : ca[22] = args[22] := hkeep 22 (by decide)
  have h39 : ca[39] = ⟨32, ca[39].get 32⟩ := by rw [hc39]; exact hready.h39
  have h50 : ca[50] = ⟨16, ca[50].get 16⟩ := by rw [hc50]; exact hready.h50
  have h51 : ca[51] = ⟨16, ca[51].get 16⟩ := by rw [hc51]; exact hready.h51
  have hDF : ca[22] = ⟨1, 0⟩ := hc22.trans hready.hDF
  let ret := subReturn use256 (oddRound round)
  let pushed := memStore mem (sp - 8) ret
  let fr := activationOfValues pushed ca ret (sp - 248)
  have hdi' : fr.rdi = base use256 sp := by
    change ca[7].get 64 = _
    rw [hdi]
    exact hready.hbuffer
  have hsi' : fr.rsi = (if use256 then 120 else 88) := by
    change ca[6].get 64 = _
    rw [hsi]; rfl
  have hdx' : fr.rdx = BitVec.ofNat 64 (8 * (round - 1)) := by
    change ca[2].get 64 = _
    rw [hdx]
    exact hready.hindex
  have hdxNat : fr.rdx.toNat = 8 * (round - 1) := by
    rw [hdx', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen : 2 * fr.rsi.toNat = (if use256 then 240 else 176) := by
    rw [hsi']; cases use256 <;> decide
  have hpf := push_frame hmemory round ret
  have hpm := memoryReady_of_frame hmemory hpf (round_stack_within hmemory round hrLast)
  have hpre : Writable code pushed fr.rdi (2 * fr.rsi.toNat) ∧
      fr.rsi.toNat ≤ 120 ∧ fr.rdx.toNat + 16 ≤ fr.rsi.toNat ∧
      (callStack fr).Disjoint (span fr.rdi (2 * fr.rsi.toNat)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hdi', hlen]; exact schedule_writable hpm
    · rw [hsi']; cases use256 <;> decide
    · rw [hdxNat, hsi']
      cases use256 <;> simp only [variant, Variant.Nr, Bool.false_eq_true, ↓reduceIte,
        BitVec.reduceToNat] at * <;> omega
    · rw [hdi']
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, callStack, activationOfValues, fr] using
        callStack_disjoint hmemory ca ret hs 0 (2 * fr.rsi.toNat) (by cases use256 <;> decide)
  obtain ⟨out, hexec, htag, hdone, htypes, hframe, hpost⟩ :=
    pushed_call_exec LIR.lifted code .l103f30 LIR.Fn103f30.frameInfo _ _ _
      (copy_callContract code hcode) mem ca sp ret hmemory hs ht h39 h50 h51 hDF
      (by dsimp only [ret]; cases use256 <;> generalize oddRound round = odd <;> cases odd <;> decide)
      (by decide) (by intro x hx; exact hx) hpre
  have hd := pushed_call_done LIR.Fn103f30.frameInfo rfl rfl code pushed ca sp ret
    (sp - 248) out hs ht h39 h50 h51 hDF hdone
  have hkeep' : ∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
      out.values[r] = args[r] := fun r hin ↦ (hd.2 r hin).trans (hkeep r hin)
  have hready' : Ready use256 round sp out.values :=
    ready_of_preserved hready (by rw [hd.1]; rfl) htypes hkeep'
  have hoff : 2 * (fr.rdx.toNat + 8) = 16 * round := by rw [hdxNat]; omega
  have hframe' : RamWriteFrame mem out.store (roundRegions use256 sp round) := by
    apply hpf.trans hframe
    change RegionsWithin [fr.region, span (fr.rdi + BitVec.ofNat 64 (2 * (fr.rdx.toNat + 8))) 16] _
    rw [hdi', hoff]
    exact callee_within hmemory ca ret hs round
  refine ⟨out.values, out.store, ?_, hready',
    ⟨hkeep' 39 (by decide), hkeep' 50 (by decide), hkeep' 51 (by decide)⟩, hframe', ?_⟩
  · rw [copyLabel_eq hrLast]
    exact caller_reaches hcall hexec htag
  · intro p
    have hp := hpost p
    change memLoad out.store (fr.rdi + BitVec.ofNat 64 (2 * (fr.rdx.toNat + 8 + p.val))) 16 =
      memLoad pushed (fr.rdi + BitVec.ofNat 64 (2 * (fr.rdx.toNat + p.val))) 16 at hp
    rw [hdi', hdxNat] at hp
    have ha : 2 * (8 * (round - 1) + 8 + p.val) = 16 * round + 2 * p.val := by omega
    have hb : 2 * (8 * (round - 1) + p.val) = 16 * (round - 1) + 2 * p.val := by omega
    rw [ha, hb] at hp
    exact hp.trans (push_load hmemory ret _ (by
      have := p.isLt
      have := round_bound use256 round hrLast
      omega))

end AesGcm.Proofs.Machine.AES16.KeySchedule.Generation.Native
