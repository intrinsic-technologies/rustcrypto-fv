import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Common
import P256.Proofs.Common.Instructions.AddByte.Memory.Stack
import P256.Proofs.Common.Instructions.Carry
import P256.Proofs.Common.Instructions.Sar.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Dec.Generated.R.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions.Carry (adcR64R64Effect adcR64R64Effect_components adc_r64_r64_effect_step)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction

open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def deadComponents (s : RamState) : List Component :=
  [.reg 10, .reg 15, .flags, .rip, .mem (stackPtr s) 112]

theorem dead_wide {s t : RamState} (h : AgreesExcept (deadComponents s) s t) :
    AgreesExcept (scratchComponents s) s t := h.mono (by simp [deadComponents, scratchComponents])

theorem dead_trans {s t u : RamState} (h₁ : AgreesExcept (deadComponents s) s t)
    (h₂ : AgreesExcept (deadComponents t) t u) : AgreesExcept (deadComponents s) s u := by
  have hs : deadComponents t = deadComponents s := by
    simp only [deadComponents, scratch_rsp (dead_wide h₁)]
  rw [hs] at h₂
  exact (h₁.trans h₂).mono (by simp)

theorem dead_memory {s t : RamState} {offset len : Nat} (hlen : offset + len ≤ 112)
    (h : AgreesExcept [.mem (stackPtr s + BitVec.ofNat 64 offset) len, .flags, .rip] s t) :
    AgreesExcept (deadComponents s) s t := by
  apply h.widen
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp_all [Component.isMem, deadComponents]
  · intro a c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨.mem (stackPtr s) 112, by simp [deadComponents], scratch_covered hlen hcov⟩
    · exact hcov.elim
    · exact hcov.elim

theorem dead_step [Bindings] {entry : BitVec 64} {boundary : ReturnBoundary}
    {s : RamState} {P : RamState → Prop} {E : RamState → Effect}
    (he : Entry entry) (hout : ¬ InProgram boundary.rip) (ready : ReadyToStep s)
    (loaded : ProgramLoaded s) (memory : MemoryPre s) (offset finish : Nat) (bytes : List UInt8)
    (hs : offset + bytes.length ≤ 1469) (hf : finish < 1469)
    (hb : Extracted.textBytes.toListFrom (0x145e0 + offset) bytes.length = bytes)
    (step : StepEffect P (codeRange (entry + BitVec.ofNat 64 offset) bytes) E) (pre : P s)
    (next : (E s).rip = entry + BitVec.ofNat 64 finish)
    (frame : ∀ t, (E s).Holds s t → AgreesExcept (deadComponents s) s t) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧ MemoryPre t ∧
      t.RIP = entry + BitVec.ofNat 64 finish ∧ AgreesExcept (deadComponents s) s t := by
  obtain ⟨t, run, ready', effect⟩ := step.advances ready (code_slice he loaded offset bytes hs hb)
    pre (next ▸ instruction_ne_boundary he hout finish hf)
  have fr := frame t effect
  have wide := dead_wide fr
  exact ⟨t, run, ready', memory.loaded (wide.mono (fun _ hc => List.mem_append_left _ hc)) loaded,
    memory.of_scratch wide, effect.rip.trans next, fr⟩

theorem dead_correct [Bindings] {entry : BitVec 64} {boundary : ReturnBoundary} {s : RamState}
    (he : Entry entry) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (memory : MemoryPre s)
    (rip : s.RIP = entry + 0x518#64) :
    ∃ t, Advances boundary 10 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧ MemoryPre t ∧
      t.RIP = entry + 0x543#64 ∧ AgreesExcept (deadComponents s) s t := by
  obtain ⟨s1, a1, r1, l1, m1, ip1, f1⟩ := dead_step he hout ready loaded memory
    0x518 0x51d [0x4c, 0x8d, 0x7c, 0x24, 0x8] (by decide) (by decide) (by decide +kernel)
    (show StepEffect _ _ (leaR64Effect (entry+0x518#64) 15#5 (.sib 4 none 0 (.d8 8))) from lea_r64_effect_step (entry+0x518#64) 0x4c (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
    rip
    (by change (entry+0x518#64)+5#64 = entry+0x51d#64
        rw [BitVec.add_assoc]; rfl)
    (by intro t effect
        apply effect.agrees.mono
        simp [deadComponents])
  obtain ⟨s2, a2, r2, l2, m2, ip2, f2⟩ := dead_step he hout r1 l1 m1
    0x51d 0x523 [0x44, 0xf, 0xb6, 0x7c, 0x24, 0x8] (by decide) (by decide) (by decide +kernel)
    (show StepEffect _ _ (movzxR32M8Effect (entry+0x51d#64) 6 15#5 (.sib 4 none 0 (.d8 8))) from movzx_r_m8_rex_effect_step (entry+0x51d#64) 0x44 (by unfold RexPrefix; decide +kernel) 32 (Or.inr rfl) (fun _ => rfl) 7 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
    (by refine ⟨ip1, ?_⟩
        exact (m1.scratch 8 1 (by decide) (by decide) (by decide)).readable)
    (by change (entry+0x51d#64)+6#64 = entry+0x523#64
        rw [BitVec.add_assoc]; rfl)
    (by intro t effect
        apply effect.agrees.mono
        simp [deadComponents])
  have fAll2 := dead_trans f1 f2
  obtain ⟨s3, a3, r3, l3, m3, ip3, f3⟩ := dead_step he hout r2 l2 m2
    0x523 0x526 [0x49, 0xff, 0xcf] (by decide) (by decide) (by decide +kernel)
    (show StepEffect _ _ (decR64Effect (entry+0x523#64) 15#5) from dec_r64_effect_step (entry+0x523#64) 0x49 0xcf (by unfold RexWPrefix; decide +kernel) rfl rfl)
    ip2
    (by change (entry+0x523#64)+3#64 = entry+0x526#64
        rw [BitVec.add_assoc]; rfl)
    (by intro t effect
        apply effect.agrees.mono
        simp [deadComponents])
  have fAll3 := dead_trans fAll2 f3
  obtain ⟨s4, a4, r4, l4, m4, ip4, f4⟩ := dead_step he hout r3 l3 m3
    0x526 0x529 [0x4d, 0x21, 0xef] (by decide) (by decide) (by decide +kernel)
    (show StepEffect _ _ (andR64R64Effect (entry+0x526#64) 15#5 13#5) from and_r64_r64_effect_step (entry+0x526#64) 0x4d 0xef (by unfold RexWPrefix; decide +kernel) rfl)
    ip3
    (by change (entry+0x526#64)+3#64 = entry+0x529#64
        rw [BitVec.add_assoc]; rfl)
    (by intro t effect
        apply effect.agrees.mono
        simp [deadComponents])
  have fAll4 := dead_trans fAll3 f4
  obtain ⟨s5, a5, r5, l5, m5, ip5, f5⟩ := dead_step he hout r4 l4 m4
    0x529 0x52d [0x49, 0xc1, 0xff, 0x3f] (by decide) (by decide) (by decide +kernel)
    (show StepEffect _ _ (P256.Proofs.Common.Instructions.sarR64Effect (entry+0x529#64) 4 15#5 63) from P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step (entry+0x529#64) 0x49 0xff 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
    ip4
    (by change (entry+0x529#64)+4#64 = entry+0x52d#64
        rw [BitVec.add_assoc]; rfl)
    (by intro t effect
        apply effect.agrees.mono
        simp [deadComponents, P256.Proofs.Common.Instructions.sarR64Effect_components])
  have fAll5 := dead_trans fAll4 f5
  obtain ⟨s6, a6, r6, l6, m6, ip6, f6⟩ := dead_step he hout r5 l5 m5
    0x52d 0x532 [0x80, 0x44, 0x24, 0x10, 0xff] (by decide) (by decide) (by decide +kernel)
    (show StepEffect _ _ (P256.Proofs.Common.Instructions.AddByte.addM8Imm8Effect (entry+0x52d#64) 5 (.sib 4 none 0 (.d8 16)) 255#8) from P256.Proofs.Common.Instructions.AddByte.add_rsp_disp8_imm8_effect_step (entry+0x52d#64) 16 255)
    (by refine ⟨ip5, m5.scratch 16 1 (by decide) (by decide) (by decide), ?_⟩
        exact m5.scratch_apart he 16 1 0x52d 5 (by decide) (by decide))
    (by change (entry+0x52d#64)+5#64 = entry+0x532#64
        rw [BitVec.add_assoc]; rfl)
    (by intro t effect
        apply dead_memory (offset := 16) (len := 1) (by decide)
        have hf := effect.agrees
        rw [P256.Proofs.Common.Instructions.AddByte.addM8Imm8Effect_components] at hf
        exact hf)
  have fAll6 := dead_trans fAll5 f6
  obtain ⟨s7, a7, r7, l7, m7, ip7, f7⟩ := dead_step he hout r6 l6 m6
    0x532 0x535 [0x4d, 0x11, 0xd7] (by decide) (by decide) (by decide +kernel)
    (show StepEffect _ _ (adcR64R64Effect (entry+0x532#64) 15#5 10#5) from adc_r64_r64_effect_step (entry+0x532#64) 0x4d 0xd7 (by unfold RexWPrefix; decide +kernel) rfl)
    ip6
    (by change (entry+0x532#64)+3#64 = entry+0x535#64
        rw [BitVec.add_assoc]; rfl)
    (by intro t effect
        apply effect.agrees.mono
        simp [deadComponents, adcR64R64Effect_components])
  have fAll7 := dead_trans fAll6 f7
  obtain ⟨s8, a8, r8, l8, m8, ip8, f8⟩ := dead_step he hout r7 l7 m7
    0x535 0x539 [0x49, 0xc1, 0xef, 0x3f] (by decide) (by decide) (by decide +kernel)
    (show StepEffect _ _ (shrR64Effect (entry+0x535#64) 4 15#5 63) from shr_r64_imm8_effect_step (entry+0x535#64) 0x49 0xef 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
    ip7
    (by change (entry+0x535#64)+4#64 = entry+0x539#64
        rw [BitVec.add_assoc]; rfl)
    (by intro t effect
        apply effect.agrees.mono
        simp [deadComponents])
  have fAll8 := dead_trans fAll7 f8
  obtain ⟨s9, a9, r9, l9, m9, ip9, f9⟩ := dead_step he hout r8 l8 m8
    0x539 0x53e [0x4c, 0x89, 0x7c, 0x24, 0x8] (by decide) (by decide) (by decide +kernel)
    (show StepEffect _ _ (movM64R64Effect (entry+0x539#64) 15#5 (.sib 4 none 0 (.d8 8))) from mov_m64_r64_effect_step (entry+0x539#64) 0x4c (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
    (by refine ⟨ip8, m8.scratch 8 8 (by decide) (by decide) (by decide), ?_⟩
        exact m8.scratch_apart he 8 8 0x539 5 (by decide) (by decide))
    (by change (entry+0x539#64)+5#64 = entry+0x53e#64
        rw [BitVec.add_assoc]; rfl)
    (by intro t effect
        apply dead_memory (offset := 8) (len := 8) (by decide)
        apply effect.agrees.mono
        simp [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr])
  have fAll9 := dead_trans fAll8 f9
  obtain ⟨s10, a10, r10, l10, m10, ip10, f10⟩ := dead_step he hout r9 l9 m9
    0x53e 0x543 [0x4c, 0x8d, 0x54, 0x24, 0x8] (by decide) (by decide) (by decide +kernel)
    (show StepEffect _ _ (leaR64Effect (entry+0x53e#64) 10#5 (.sib 4 none 0 (.d8 8))) from lea_r64_effect_step (entry+0x53e#64) 0x4c (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
    ip9
    (by change (entry+0x53e#64)+5#64 = entry+0x543#64
        rw [BitVec.add_assoc]; rfl)
    (by intro t effect
        apply effect.agrees.mono
        simp [deadComponents])
  have fAll10 := dead_trans fAll9 f10
  exact ⟨s10, ((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10, r10, l10, m10, ip10, fAll10⟩

end P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction
