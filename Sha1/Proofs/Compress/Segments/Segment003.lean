import Sha1.Proofs.Compress.Machine.Cuts
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.AccImm32.Triple

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

set_option maxHeartbeats 800000 in
def effect003 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq ((movR32R32Effect 0x1025a4 2 0 7)) (rolR32Effect 0x1025a6 3 0 5))
    (movR32R32Effect 0x1025a9 2 1 2)) (xorR32R32Effect 0x1025ab 2 1 3)) (andR32R32Effect 0x1025ad 3
    1 11)) (xorR32R32Effect 0x1025b0 2 1 3)) (movM64R64Effect 0x1025b2 3 (.sib 4 none 0 (.d32
    0x90)))) (addR32R32Effect 0x1025ba 3 1 10)) (addR32R32Effect 0x1025bd 3 1 12)) (addR32R32Effect
    0x1025c0 2 0 1)) (addEaxImm32Effect 0x1025c2 0x5a827999)

private def rawBefore003 (stack input : BitVec 64) (v : Vector (BitVec 32) 11) : List Write :=
  [⟨(.reg 2 : Operand 32), (v[1]).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), v[2]⟩,
    ⟨(.reg 5 : Operand 32), v[8]⟩,
    ⟨(.reg 7 : Operand 32), v[5]⟩,
    ⟨(.reg 9 : Operand 32), v[9]⟩,
    ⟨(.reg 10 : Operand 32), v[3]⟩,
    ⟨(.reg 11 : Operand 32), v[0]⟩,
    ⟨(.reg 12 : Operand 32), v[7]⟩,
    ⟨(.reg 14 : Operand 32), v[10]⟩,
    ⟨(.reg 15 : Operand 32), v[6]⟩,
    ⟨(.mem (stack + 8) : Operand 32), v[10]⟩,
    ⟨(.mem (stack + 56) : Operand 32), v[9]⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 88) : Operand 32), v[7]⟩,
    ⟨(.mem (stack + 116) : Operand 32), v[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), v[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), v[4]⟩,
    ⟨(.mem (stack + 152) : Operand 32), v[1]⟩]

private def rawAfter003 (stack input : BitVec 64) (v : Vector (BitVec 32) 11) : List Write :=
  [⟨(.reg 0 : Operand 32), (v[5].rotateLeft 5 + (((v[1].rotateLeft 30 ^^^ v[2]) &&& v[0]) ^^^ v[2])
    + v[3] + v[7] + 0x5a827999)⟩,
    ⟨(.reg 2 : Operand 32), (v[1]).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), v[2]⟩,
    ⟨(.reg 5 : Operand 32), v[8]⟩,
    ⟨(.reg 7 : Operand 32), v[5]⟩,
    ⟨(.reg 9 : Operand 32), v[9]⟩,
    ⟨(.reg 11 : Operand 32), v[0]⟩,
    ⟨(.reg 14 : Operand 32), v[10]⟩,
    ⟨(.reg 15 : Operand 32), v[6]⟩,
    ⟨(.mem (stack + 8) : Operand 32), v[10]⟩,
    ⟨(.mem (stack + 56) : Operand 32), v[9]⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 88) : Operand 32), v[7]⟩,
    ⟨(.mem (stack + 116) : Operand 32), v[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), v[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), v[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), v[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), v[1]⟩]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem effect003_raw_words {stack input : BitVec 64} {v : Vector (BitVec 32) 11}
    {s t : RamState}
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (rawBefore003 stack input v))
    (he : (effect003 s).Holds s t) :
    Write.AllHold t (rawAfter003 stack input v) := by
  have hfull : ∀ wr ∈ (effect003 s).writes, wr.Full := by
    apply Effect.Local.full
    unfold effect003
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [rawBefore003, Write.AllHold] at hw
  obtain ⟨h2,h3,h5,h7,h9,h10,h11,h12,h14,h15,
    hM8,hM56,hM64,hM88,hM116,hM120,hM124,hM152⟩ := hw
  x86_norm at h2 h3 h5 h7 h9 h10 h11 h12 h14 h15
  x86_norm at hM8 hM56 hM64 hM88 hM116 hM120 hM124 hM152
  simp only [rawAfter003, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  x86_norm [effect003,hs,h2,h3,h5,h7,h9,h10,h11,h12,h14,h15,
    hM8,hM56,hM64,hM88,hM116,hM120,hM124,hM152]
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  constructor
  · ac_rfl
  · rw [read32_memStore64_low]
    exact h3

private theorem compiler_choice_order003 (a b c d e w : BitVec 32) :
    a.rotateLeft 5 + (((b ^^^ c) &&& e) ^^^ c) + d + w + 0x5a827999 =
      a.rotateLeft 5 + Standards.NIST.SHA2.SHA256.Ch e b c + 0x5a827999 + w + d := by
  simp only [sha1Ch_eq, BitVec.xor_comm, BitVec.and_comm]
  ac_rfl

private def modelWords003 (H : Vector (BitVec 32) 5)
    (M : Vector (BitVec 32) 16) : Vector (BitVec 32) 11 :=
  #v[H[0],H[1],H[2],H[3],H[4],(workingAfter M H 1).a,
    scheduleWord M 0,scheduleWord M 1,scheduleWord M 2,scheduleWord M 3,scheduleWord M 4]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect003_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut003 stack input H M))
    (he : (effect003 s).Holds s t) :
    Write.AllHold t (cut004 stack input H M) := by
  let v := modelWords003 H M
  have hpre : Write.AllHold s (rawBefore003 stack input v) := by
    change Write.AllHold s (cut003 stack input H M)
    exact hw
  have hraw := effect003_raw_words hf.stackPointer hpre he
  have hWork : (workingAfter M H 2).a =
      (workingAfter M H 1).a.rotateLeft 5 +
        Standards.NIST.SHA2.SHA256.Ch H[0] (H[1].rotateLeft 30) H[2] +
        0x5a827999 + scheduleWord M 1 + H[3] := by
    rw [workingAfter_step M H 1 (by decide +kernel)]
    rw [sha1_step_a_choice ⟨1, by decide⟩ (messageSchedule M)[1]
      (workingAfter M H 1) (by decide)]
    have hSched : (messageSchedule M)[1] = scheduleWord M ⟨1, by decide⟩ := by
      unfold scheduleWord
      rfl
    rw [hSched]
    rw [workingAfter_step_b M H 0 (by decide +kernel),
      workingAfter_step_c M H 0 (by decide +kernel),
      workingAfter_step_d M H 0 (by decide +kernel),
      workingAfter_step_e M H 0 (by decide +kernel),
      workingAfter_zero]
    simp only [WorkingVariables.ofHashValue]
    rw [sha1Rotl_eq_rotateLeft 5 _ (by decide),
      sha1Rotl_eq_rotateLeft 30 _ (by decide)]
    simp [Standards.NIST.SHA1.K]
  have hvalue :
      v[5].rotateLeft 5 + (((v[1].rotateLeft 30 ^^^ v[2]) &&& v[0]) ^^^ v[2]) +
        v[3] + v[7] + 0x5a827999 = (workingAfter M H 2).a := by
    change (workingAfter M H 1).a.rotateLeft 5 +
      (((H[1].rotateLeft 30 ^^^ H[2]) &&& H[0]) ^^^ H[2]) +
        H[3] + scheduleWord M 1 + 0x5a827999 = _
    exact (compiler_choice_order003 _ _ _ _ _ _).trans hWork.symm
  have heq : rawAfter003 stack input v = cut004 stack input H M := by
    simp only [rawAfter003, cut004]
    rw [hvalue]
    rfl
  exact heq ▸ hraw

theorem effect003_rip {s t : RamState} (he : (effect003 s).Holds s t) :
    t.RIP = 0x1025c7 := by
  exact he.rip.trans (by rfl)

end Sha1.Proofs.Compress.Machine
