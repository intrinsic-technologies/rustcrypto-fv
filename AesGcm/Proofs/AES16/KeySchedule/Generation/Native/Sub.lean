import AesGcm.Proofs.AES16.Sbox
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Calls
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Memory
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.State

namespace AesGcm.Proofs.Machine.AES16.KeySchedule.Generation.Native

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 800000 in
theorem sub_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (round : Nat) (hrLast : round ≤ (variant use256).Nr)
    (args : Values Value Reg.count) (mem : Ram) (sp : BitVec 64)
    (hready : Ready use256 round sp args)
    (hmemory : MemoryReady use256 code mem sp)
    (x : Fixslice16.Planes16)
    (hx : WordsAt mem (base use256 sp + BitVec.ofNat 64 (16 * round)) 16 (Vector.ofFn x)) :
    ∃ (nextArgs : Values Value Reg.count) (nextMem : Ram),
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨subLabel use256 (oddRound round), args, mem⟩, []⟩
        ⟨⟨notLabel use256 (oddRound round), nextArgs, nextMem⟩, []⟩ ∧
      Ready use256 round sp nextArgs ∧ SameFP args nextArgs ∧
      RamWriteFrame mem nextMem (roundRegions use256 sp round) ∧
      WordsAt nextMem (base use256 sp + BitVec.ofNat 64 (16 * round))
        16 (Vector.ofFn (Fixslice16.subBytes x)) := by
  obtain ⟨ca, hcall, hsp, hdi, hsi, hkeep, ht⟩ :=
    sub_setup use256 (oddRound round) code hcode args mem sp hready.hsp hready.hTypes
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
  let ret := notReturn use256 (oddRound round)
  let pushed := memStore mem (sp - 8) ret
  let fr := activationOfValues pushed ca ret (sp - 248)
  have hdi' : fr.rdi = base use256 sp + BitVec.ofNat 64 (16 * round) := by
    change ca[7].get 64 = _
    rw [hdi]
    exact subDestination_eq hready
  have hsi' : fr.rsi = 8 := by change ca[6].get 64 = _; rw [hsi]; rfl
  have hpf := push_frame hmemory round ret
  have hpm := memoryReady_of_frame hmemory hpf (round_stack_within hmemory round hrLast)
  have hpre : fr.rsi = 8 ∧ Writable code pushed fr.rdi 16 ∧
      (callStack fr).Disjoint (span fr.rdi 16) := by
    refine ⟨hsi', ?_, ?_⟩
    · rw [hdi']; exact round_writable hpm round hrLast
    · rw [hdi']
      exact callStack_disjoint hmemory ca ret hs (16 * round) 16
        (by have := round_bound use256 round hrLast; omega)
  obtain ⟨out, hexec, htag, hdone, htypes, hframe, hpost⟩ :=
    pushed_call_exec LIR.lifted code .l100b10 LIR.Fn100b10.frameInfo _ _ _
      (AES16.subBytes_callContract code hcode) mem ca sp ret hmemory hs ht h39 h50 h51 hDF
      (by dsimp only [ret]; cases use256 <;> generalize oddRound round = odd <;> cases odd <;> decide)
      (by decide) (by intro x hx; exact hx) hpre
  have hd := pushed_call_done LIR.Fn100b10.frameInfo rfl rfl code pushed ca sp ret
    (sp - 248) out hs ht h39 h50 h51 hDF hdone
  have hkeep' : ∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
      out.values[r] = args[r] := fun r hin ↦ (hd.2 r hin).trans (hkeep r hin)
  have hready' : Ready use256 round sp out.values :=
    ready_of_preserved hready (by rw [hd.1]; rfl) htypes hkeep'
  have hframe' : RamWriteFrame mem out.store (roundRegions use256 sp round) := by
    apply hpf.trans hframe
    change RegionsWithin [fr.region, span fr.rdi 16] _
    rw [hdi']
    exact callee_within hmemory ca ret hs round
  refine ⟨out.values, out.store, caller_reaches hcall hexec htag, hready',
    ⟨hkeep' 39 (by decide), hkeep' 50 (by decide), hkeep' 51 (by decide)⟩, hframe', ?_⟩
  have hinput : (fun p : Fin 8 ↦ memLoad pushed (fr.rdi + BitVec.ofNat 64 (2 * p.val)) 16) = x := by
    funext p
    rw [hdi', BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [push_load hmemory ret _ (by
      have := p.isLt
      have := round_bound use256 round hrLast
      omega)]
    have hp := hx p.val p.isLt
    simpa only [wordAddr, Vector.getElem_ofFn, Nat.reduceDiv, Nat.mul_comm,
      BitVec.ofNat_add, BitVec.add_assoc] using hp
  change WordsAt out.store fr.rdi 16 (Vector.ofFn (Fixslice16.subBytes
    (fun p ↦ memLoad pushed (fr.rdi + BitVec.ofNat 64 (2 * p.val)) 16))) at hpost
  rw [hinput, hdi'] at hpost
  exact hpost

end AesGcm.Proofs.Machine.AES16.KeySchedule.Generation.Native
