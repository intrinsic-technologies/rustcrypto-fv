import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Blocks
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Memory

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2048 in
theorem finish_exec (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hTypes : GPRsTyped args)
    (hstack : Readable mem (args[4].get 64) (frameBytes use256 + 8))
    (hret : (memLoad mem (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256)) 64).toNat < 2^32)
    (hstatus : memLoad mem (args[4].get 64 + 15) 8 = 0)
    (hwrite : Writable code mem (args[4].get 64 + 32) 16)
    (hbuffer : (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat →
      Writable code mem (args[14].get 64 + args[3].get 64) 16)
    (hapart : (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat →
      (span (args[14].get 64 + args[3].get 64) 16).Disjoint
        (span (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 - 48)) 56)) :
    ∃ output,
      LIR.program.Exec (dialect code)
        ⟨⟨(if use256 then .l1016e9 else .l101409), args, mem⟩, []⟩ output ∧
      output.store = tailMemory args mem ∧
      output.tag = some ⟨64, memLoad mem
        (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256)) 64⟩ ∧
      output.values[4] = ⟨64, args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 + 8)⟩ ∧
      output.values[0] =
        ⟨64, if (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat then 0 else 1⟩ ∧
      output.values[3] = ⟨64, memLoad mem
        (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 - 48)) 64⟩ ∧
      output.values[12] = ⟨64, memLoad mem
        (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 - 40)) 64⟩ ∧
      output.values[13] = ⟨64, memLoad mem
        (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 - 32)) 64⟩ ∧
      output.values[14] = ⟨64, memLoad mem
        (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 - 24)) 64⟩ ∧
      output.values[15] = ⟨64, memLoad mem
        (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 - 16)) 64⟩ ∧
      output.values[5] = ⟨64, memLoad mem
        (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 - 8)) 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [22,39,50,51] → output.values[r] = args[r]) ∧
      GPRsTyped output.values ∧
      RamWriteFrame mem output.store (tailFootprint args) := by
  let sp := args[4].get 64
  let fb := frameBytes use256
  have hfb : 48 ≤ fb := by cases use256 <;> decide
  have hsLow : sp.toNat + fb + 8 ≤ 2^32 := by
    simpa only [Nat.add_assoc] using hstack.low
  have haddr (k : Nat) (hk : k ≤ fb + 8) :
      (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : k < 2^64)]
    exact Nat.mod_eq_of_lt (by omega)
  have hframe : RamWriteFrame mem (tailMemory args mem) (tailFootprint args) :=
    tailMemory_frame args mem (by have := hwrite.readable.low; omega)
      (fun hf => by have := (hbuffer hf).readable.low; omega)
  have hload (k : Nat) (hlo : fb - 48 ≤ k) (hhi : k ≤ fb) :
      memLoad (tailMemory args mem) (sp + BitVec.ofNat 64 k) 64 =
        memLoad mem (sp + BitVec.ofNat 64 k) 64 := by
    apply hframe.memLoad_eq
    refine ⟨?_, ?_⟩
    · rw [haddr k (by omega)]
      omega
    · intro r hr
      simp only [tailFootprint, List.mem_cons] at hr
      rcases hr with rfl | hr
      · right
        change (sp + 32).toNat + 16 ≤ (sp + BitVec.ofNat 64 k).toNat
        have h32 := haddr 32 (by omega)
        rw [haddr k (by omega)]
        change (sp + BitVec.ofNat 64 32).toNat + 16 ≤ sp.toNat + k
        rw [h32]
        cases use256 <;> simp only [fb, frameBytes, Bool.false_eq_true, ↓reduceIte] at hlo <;> omega
      · split at hr
        next hf =>
          rcases List.mem_singleton.mp hr with rfl
          have hd := disjoint_bounds _ 16 _ 56 (by decide) (by decide) (hapart hf)
          change (args[14].get 64 + args[3].get 64).toNat + 16 ≤
              (sp + BitVec.ofNat 64 (fb - 48)).toNat ∨
            (sp + BitVec.ofNat 64 (fb - 48)).toNat + 56 ≤
              (args[14].get 64 + args[3].get 64).toNat at hd
          rw [haddr (fb - 48) (by omega)] at hd
          change (sp + BitVec.ofNat 64 k).toNat + 8 ≤
              (args[14].get 64 + args[3].get 64).toNat ∨
            (args[14].get 64 + args[3].get 64).toNat + 16 ≤
              (sp + BitVec.ofNat 64 k).toNat
          rw [haddr k (by omega)]
          omega
        next => simp only [List.not_mem_nil] at hr
  have hread : Readable mem (args[4].get 64 + 15) 17 := by
    apply hstack.of_offsets rfl (show args[4].get 64 = args[4].get 64 + 0 by simp)
    cases use256 <;> decide
  obtain ⟨target, htail, tl, tm, t0, tk, tt⟩ :=
    tail_reaches_exit use256 code hcode args mem hTypes hread hstatus hwrite hbuffer
  rw [← tailMemory_eq] at tm
  have t4 := tk ⟨4, by decide⟩ (by decide)
  simp only [Fin.getElem_fin] at t4
  obtain ⟨output, hexit, om, otag, o4, o3, o12, o13, o14, o15, o5, ok, otypes⟩ :=
    exit_runBlock use256 code target.arguments target.store
      (by
        rw [t4, tm]
        apply Readable.of_frame (m := tailMemory args mem) ?_ hframe
        apply hstack.of_offsets rfl (show args[4].get 64 = args[4].get 64 + 0 by simp)
        cases use256 <;> decide)
      (by
        rw [t4, tm, hload fb (by omega) (by omega)]
        exact hret)
  have texec : LIR.program.Exec (dialect code) ⟨target, []⟩ output := by
    apply Program.Exec.done
    have htloc : target = ⟨(if use256 then .l101739 else .l101459), target.arguments, target.store⟩ := by
      cases target
      cases tl
      rfl
    rw [htloc]
    simp only [Program.step, hexit, Transfer.next]
  have hoMem : output.store = tailMemory args mem := om.trans tm
  have hoTag : output.tag = some ⟨64, memLoad mem (sp + BitVec.ofNat 64 fb) 64⟩ := by
    rw [t4, tm, hload fb (by omega) (by omega)] at otag
    exact otag
  refine ⟨output, Program.Exec.of_sem (htail.exec texec.sem), hoMem, hoTag, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, otypes tt, ?_⟩
  · simpa only [t4] using o4
  · exact (ok ⟨0, by decide⟩ (by decide)).trans t0
  · rw [t4, tm, hload (fb - 48) (by omega) (by omega)] at o3
    exact o3
  · rw [t4, tm, hload (fb - 40) (by omega) (by omega)] at o12
    exact o12
  · rw [t4, tm, hload (fb - 32) (by omega) (by omega)] at o13
    exact o13
  · rw [t4, tm, hload (fb - 24) (by omega) (by omega)] at o14
    exact o14
  · rw [t4, tm, hload (fb - 16) (by omega) (by omega)] at o15
    exact o15
  · rw [t4, tm, hload (fb - 8) (by omega) (by omega)] at o5
    exact o5
  · intro r hr
    have hk : r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      omega
    have hok : r.val ∈ [0,22,39,50,51] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      omega
    exact (ok r hok).trans (tk r hk)
  · rw [hoMem]
    exact hframe

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
