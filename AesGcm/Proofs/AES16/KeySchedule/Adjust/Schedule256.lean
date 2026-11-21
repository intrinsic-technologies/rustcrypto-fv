import AesGcm.Proofs.AES16.KeySchedule.Adjust.Callees
import AesGcm.Proofs.AES16.KeySchedule.Adjust.Tactics

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem adjust256_schedule_round0 (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ p : Fin 8,
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * 0 + 2 * p.val)) 16 =
        adjustKey .aes256 0 (planes 0) p := by
  adjust_schedule_proof adjust256_callee at 0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem adjust256_schedule_round1 (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ p : Fin 8,
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * 1 + 2 * p.val)) 16 =
        adjustKey .aes256 1 (planes 1) p := by
  adjust_schedule_proof adjust256_callee at 1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem adjust256_schedule_round2 (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ p : Fin 8,
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * 2 + 2 * p.val)) 16 =
        adjustKey .aes256 2 (planes 2) p := by
  adjust_schedule_proof adjust256_callee at 2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem adjust256_schedule_round3 (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ p : Fin 8,
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * 3 + 2 * p.val)) 16 =
        adjustKey .aes256 3 (planes 3) p := by
  adjust_schedule_proof adjust256_callee at 3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem adjust256_schedule_round4 (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ p : Fin 8,
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * 4 + 2 * p.val)) 16 =
        adjustKey .aes256 4 (planes 4) p := by
  adjust_schedule_proof adjust256_callee at 4

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem adjust256_schedule_round5 (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ p : Fin 8,
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * 5 + 2 * p.val)) 16 =
        adjustKey .aes256 5 (planes 5) p := by
  adjust_schedule_proof adjust256_callee at 5

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem adjust256_schedule_round6 (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ p : Fin 8,
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * 6 + 2 * p.val)) 16 =
        adjustKey .aes256 6 (planes 6) p := by
  adjust_schedule_proof adjust256_callee at 6

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem adjust256_schedule_round7 (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ p : Fin 8,
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * 7 + 2 * p.val)) 16 =
        adjustKey .aes256 7 (planes 7) p := by
  adjust_schedule_proof adjust256_callee at 7

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem adjust256_schedule_round8 (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ p : Fin 8,
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * 8 + 2 * p.val)) 16 =
        adjustKey .aes256 8 (planes 8) p := by
  adjust_schedule_proof adjust256_callee at 8

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem adjust256_schedule_round9 (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ p : Fin 8,
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * 9 + 2 * p.val)) 16 =
        adjustKey .aes256 9 (planes 9) p := by
  adjust_schedule_proof adjust256_callee at 9

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem adjust256_schedule_round10 (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ p : Fin 8,
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * 10 + 2 * p.val)) 16 =
        adjustKey .aes256 10 (planes 10) p := by
  adjust_schedule_proof adjust256_callee at 10

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem adjust256_schedule_round11 (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ p : Fin 8,
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * 11 + 2 * p.val)) 16 =
        adjustKey .aes256 11 (planes 11) p := by
  adjust_schedule_proof adjust256_callee at 11

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem adjust256_schedule_round12 (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ p : Fin 8,
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * 12 + 2 * p.val)) 16 =
        adjustKey .aes256 12 (planes 12) p := by
  adjust_schedule_proof adjust256_callee at 12

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem adjust256_schedule_round13 (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ p : Fin 8,
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * 13 + 2 * p.val)) 16 =
        adjustKey .aes256 13 (planes 13) p := by
  adjust_schedule_proof adjust256_callee at 13

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem adjust256_schedule_round14 (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ p : Fin 8,
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * 14 + 2 * p.val)) 16 =
        adjustKey .aes256 14 (planes 14) p := by
  adjust_schedule_proof adjust256_callee at 14

theorem adjust256_schedule (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (planes : Fin 15 → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp)
    (hwords : ∀ (r : Fin 15) (p : Fin 8),
      memLoad mem (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∀ (r : Fin 15) (p : Fin 8),
      memLoad (adjust256_callee code args mem).store
        (sp + 12 + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 =
        adjustKey .aes256 r.val (planes r) p := by
  intro r
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨
      r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 := by
    have := r.isLt
    omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact adjust256_schedule_round0 code args mem sp planes hsp hwords
  · exact adjust256_schedule_round1 code args mem sp planes hsp hwords
  · exact adjust256_schedule_round2 code args mem sp planes hsp hwords
  · exact adjust256_schedule_round3 code args mem sp planes hsp hwords
  · exact adjust256_schedule_round4 code args mem sp planes hsp hwords
  · exact adjust256_schedule_round5 code args mem sp planes hsp hwords
  · exact adjust256_schedule_round6 code args mem sp planes hsp hwords
  · exact adjust256_schedule_round7 code args mem sp planes hsp hwords
  · exact adjust256_schedule_round8 code args mem sp planes hsp hwords
  · exact adjust256_schedule_round9 code args mem sp planes hsp hwords
  · exact adjust256_schedule_round10 code args mem sp planes hsp hwords
  · exact adjust256_schedule_round11 code args mem sp planes hsp hwords
  · exact adjust256_schedule_round12 code args mem sp planes hsp hwords
  · exact adjust256_schedule_round13 code args mem sp planes hsp hwords
  · exact adjust256_schedule_round14 code args mem sp planes hsp hwords

end AesGcm.Proofs.Machine.AES16.KeySchedule
