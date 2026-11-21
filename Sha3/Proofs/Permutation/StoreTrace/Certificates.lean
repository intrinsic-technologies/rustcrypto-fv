import Sha3.Proofs.Permutation.StoreTrace.Program

namespace Sha3.Proofs.Permutation.StoreTrace

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem TraceStep.of_effect [Bindings] {copy : Copy} {pc next : BitVec 64} {op : Move}
    {bytes : List UInt8} {pre : RamState → Prop} {effect : RamState → Effect}
    (hstep : StepEffect pre (codeRange pc bytes) effect)
    (hpre : ∀ sp pointer s, StepPre copy sp pointer pc op s → pre s)
    (heffect : ∀ sp pointer s, StepPre copy sp pointer pc op s →
      effect s = moveEffect sp pointer next op s) :
    TraceStep copy pc next op bytes := by
  intro sp pointer s hready hcode hp
  obtain ⟨t, hrun, ht, he⟩ := hstep s hready hcode (hpre sp pointer s hp)
  exact ⟨t, hrun, ht, heffect sp pointer s hp ▸ he⟩

theorem StepPre.stackLoadPre {copy : Copy} {sp pointer pc : BitVec 64} {op : Move}
    {s : RamState} (h : StepPre copy sp pointer pc op s) (offset : BitVec 64)
    (ho : offset.toNat + 8 ≤ 272) :
    LoadPre pc
      (fun s ↦ (Operand.reg 4 : Operand 64).read s + offset) 8 s := by
  refine ⟨h.rip, ?_⟩
  rw [h.stack]
  exact Store.readable_offset h.memory.frameRead ho

theorem StepPre.outputStorePre {copy : Copy} {sp pointer pc : BitVec 64}
    {i : Fin 25} {src : Location} {s : RamState}
    (h : StepPre copy sp pointer pc ⟨.output i, src⟩ s) (offset : BitVec 64)
    (ho : offset.toNat + 8 ≤ 200) :
    StorePreReadable pc
      (fun s ↦ (Operand.reg 2 : Operand 64).read s + offset) 8 s := by
  have hp : (Operand.reg 2 : Operand 64).read s = pointer := h.pointerValue
  refine ⟨⟨h.rip, ?_⟩, ?_⟩
  · rw [hp]
    exact Store.readable_offset h.memory.outputRead ho
  · simpa only [hp, BitVec.add_assoc] using Store.tables_offset h.memory.tables ho

theorem dataStep_50b [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 8) ⟨.reg 2, .stack 20⟩
      [0x48, 0x8b, 0x94, 0x24, 0xa0, 0x00, 0x00, 0x00] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 2 (.sib 4 none 0 (.d32 0xa0)) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 160 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 8)
      ⟨.reg 2, .stack 20⟩ s = _
    rw [hp.stack]

theorem dataStep_513 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 5) ⟨.reg 6, .stack 4⟩
      [0x48, 0x8b, 0x74, 0x24, 0x20] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 6 (.sib 4 none 0 (.d8 0x20)) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 32 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 5)
      ⟨.reg 6, .stack 4⟩ s = _
    rw [hp.stack]

theorem dataStep_518 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.output 5, .reg 6⟩
      [0x48, 0x89, 0x72, 0x28] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 6 (.base 2 (.d8 0x28))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 40 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 4)
      ⟨.output 5, .reg 6⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_51c [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 8) ⟨.reg 6, .stack 16⟩
      [0x48, 0x8b, 0xb4, 0x24, 0x80, 0x00, 0x00, 0x00] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 6 (.sib 4 none 0 (.d32 0x80)) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 128 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 8)
      ⟨.reg 6, .stack 16⟩ s = _
    rw [hp.stack]

theorem dataStep_524 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.output 1, .reg 6⟩
      [0x48, 0x89, 0x72, 0x08] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 6 (.base 2 (.d8 0x8))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 8 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 4)
      ⟨.output 1, .reg 6⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_528 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.output 6, .reg 9⟩
      [0x4c, 0x89, 0x4a, 0x30] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 9 (.base 2 (.d8 0x30))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 48 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 4)
      ⟨.output 6, .reg 9⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_52c [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 8) ⟨.reg 6, .stack 17⟩
      [0x48, 0x8b, 0xb4, 0x24, 0x88, 0x00, 0x00, 0x00] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 6 (.sib 4 none 0 (.d32 0x88)) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 136 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 8)
      ⟨.reg 6, .stack 17⟩ s = _
    rw [hp.stack]

theorem dataStep_534 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.output 2, .reg 6⟩
      [0x48, 0x89, 0x72, 0x10] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 6 (.base 2 (.d8 0x10))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 16 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 4)
      ⟨.output 2, .reg 6⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_538 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 5) ⟨.reg 6, .stack 6⟩
      [0x48, 0x8b, 0x74, 0x24, 0x30] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 6 (.sib 4 none 0 (.d8 0x30)) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 48 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 5)
      ⟨.reg 6, .stack 6⟩ s = _
    rw [hp.stack]

theorem dataStep_53d [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.output 7, .reg 6⟩
      [0x48, 0x89, 0x72, 0x38] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 6 (.base 2 (.d8 0x38))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 56 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 4)
      ⟨.output 7, .reg 6⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_541 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 5) ⟨.reg 6, .stack 15⟩
      [0x48, 0x8b, 0x74, 0x24, 0x78] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 6 (.sib 4 none 0 (.d8 0x78)) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 120 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 5)
      ⟨.reg 6, .stack 15⟩ s = _
    rw [hp.stack]

theorem dataStep_546 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.output 3, .reg 6⟩
      [0x48, 0x89, 0x72, 0x18] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 6 (.base 2 (.d8 0x18))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 24 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 4)
      ⟨.output 3, .reg 6⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_54a [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 5) ⟨.reg 6, .stack 14⟩
      [0x48, 0x8b, 0x74, 0x24, 0x70] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 6 (.sib 4 none 0 (.d8 0x70)) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 112 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 5)
      ⟨.reg 6, .stack 14⟩ s = _
    rw [hp.stack]

theorem dataStep_54f [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.output 4, .reg 6⟩
      [0x48, 0x89, 0x72, 0x20] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 6 (.base 2 (.d8 0x20))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 32 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 4)
      ⟨.output 4, .reg 6⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_553 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 5) ⟨.reg 6, .stack 3⟩
      [0x48, 0x8b, 0x74, 0x24, 0x18] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 6 (.sib 4 none 0 (.d8 0x18)) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 24 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 5)
      ⟨.reg 6, .stack 3⟩ s = _
    rw [hp.stack]

theorem dataStep_558 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 3) ⟨.output 0, .reg 6⟩
      [0x48, 0x89, 0x32] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 6 (.base 2 .none)
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 0 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 3)
      ⟨.output 0, .reg 6⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_55b [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 5) ⟨.reg 6, .stack 10⟩
      [0x48, 0x8b, 0x74, 0x24, 0x50] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 6 (.sib 4 none 0 (.d8 0x50)) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 80 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 5)
      ⟨.reg 6, .stack 10⟩ s = _
    rw [hp.stack]

theorem dataStep_560 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 7) ⟨.output 20, .reg 6⟩
      [0x48, 0x89, 0xb2, 0xa0, 0x00, 0x00, 0x00] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 6 (.base 2 (.d32 0xa0))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 160 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 7)
      ⟨.output 20, .reg 6⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_567 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.output 12, .reg 12⟩
      [0x4c, 0x89, 0x62, 0x60] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 12 (.base 2 (.d8 0x60))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 96 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 4)
      ⟨.output 12, .reg 12⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_56b [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 7) ⟨.output 17, .reg 15⟩
      [0x4c, 0x89, 0xba, 0x88, 0x00, 0x00, 0x00] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 15 (.base 2 (.d32 0x88))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 136 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 7)
      ⟨.output 17, .reg 15⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_572 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 5) ⟨.reg 6, .stack 11⟩
      [0x48, 0x8b, 0x74, 0x24, 0x58] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 6 (.sib 4 none 0 (.d8 0x58)) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 88 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 5)
      ⟨.reg 6, .stack 11⟩ s = _
    rw [hp.stack]

theorem dataStep_577 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 7) ⟨.output 22, .reg 6⟩
      [0x48, 0x89, 0xb2, 0xb0, 0x00, 0x00, 0x00] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 6 (.base 2 (.d32 0xb0))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 176 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 7)
      ⟨.output 22, .reg 6⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_57e [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 5) ⟨.reg 6, .stack 7⟩
      [0x48, 0x8b, 0x74, 0x24, 0x38] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 6 (.sib 4 none 0 (.d8 0x38)) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 56 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 5)
      ⟨.reg 6, .stack 7⟩ s = _
    rw [hp.stack]

theorem dataStep_583 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.output 13, .reg 6⟩
      [0x48, 0x89, 0x72, 0x68] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 6 (.base 2 (.d8 0x68))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 104 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 4)
      ⟨.output 13, .reg 6⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_587 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 7) ⟨.output 18, .reg 14⟩
      [0x4c, 0x89, 0xb2, 0x90, 0x00, 0x00, 0x00] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 14 (.base 2 (.d32 0x90))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 144 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 7)
      ⟨.output 18, .reg 14⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_58e [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 5) ⟨.reg 6, .stack 13⟩
      [0x48, 0x8b, 0x74, 0x24, 0x68] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 6 (.sib 4 none 0 (.d8 0x68)) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 104 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 5)
      ⟨.reg 6, .stack 13⟩ s = _
    rw [hp.stack]

theorem dataStep_593 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 7) ⟨.output 23, .reg 6⟩
      [0x48, 0x89, 0xb2, 0xb8, 0x00, 0x00, 0x00] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 6 (.base 2 (.d32 0xb8))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 184 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 7)
      ⟨.output 23, .reg 6⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_59a [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.output 14, .reg 13⟩
      [0x4c, 0x89, 0x6a, 0x70] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 13 (.base 2 (.d8 0x70))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 112 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 4)
      ⟨.output 14, .reg 13⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_59e [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 7) ⟨.output 19, .reg 3⟩
      [0x48, 0x89, 0x9a, 0x98, 0x00, 0x00, 0x00] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 3 (.base 2 (.d32 0x98))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 152 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 7)
      ⟨.output 19, .reg 3⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_5a5 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.reg 6, .stack 0⟩
      [0x48, 0x8b, 0x34, 0x24] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 6 (.sib 4 none 0 .none) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 0 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 4)
      ⟨.reg 6, .stack 0⟩ s = _
    rw [hp.stack]

theorem dataStep_5a9 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 7) ⟨.output 24, .reg 6⟩
      [0x48, 0x89, 0xb2, 0xc0, 0x00, 0x00, 0x00] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 6 (.base 2 (.d32 0xc0))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 192 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 7)
      ⟨.output 24, .reg 6⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_5b0 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.output 10, .reg 0⟩
      [0x48, 0x89, 0x42, 0x50] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 0 (.base 2 (.d8 0x50))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 80 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 4)
      ⟨.output 10, .reg 0⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_5b4 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 5) ⟨.reg 0, .stack 5⟩
      [0x48, 0x8b, 0x44, 0x24, 0x28] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 0 (.sib 4 none 0 (.d8 0x28)) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 40 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 5)
      ⟨.reg 0, .stack 5⟩ s = _
    rw [hp.stack]

theorem dataStep_5b9 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.output 11, .reg 0⟩
      [0x48, 0x89, 0x42, 0x58] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 0 (.base 2 (.d8 0x58))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 88 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 4)
      ⟨.output 11, .reg 0⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_5bd [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 7) ⟨.output 16, .reg 1⟩
      [0x48, 0x89, 0x8a, 0x80, 0x00, 0x00, 0x00] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 1 (.base 2 (.d32 0x80))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 128 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 7)
      ⟨.output 16, .reg 1⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_5c4 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 5) ⟨.reg 0, .stack 12⟩
      [0x48, 0x8b, 0x44, 0x24, 0x60] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 0 (.sib 4 none 0 (.d8 0x60)) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 96 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 5)
      ⟨.reg 0, .stack 12⟩ s = _
    rw [hp.stack]

theorem dataStep_5c9 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 7) ⟨.output 21, .reg 0⟩
      [0x48, 0x89, 0x82, 0xa8, 0x00, 0x00, 0x00] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 0 (.base 2 (.d32 0xa8))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 168 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 7)
      ⟨.output 21, .reg 0⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_5d0 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.output 15, .reg 5⟩
      [0x48, 0x89, 0x6a, 0x78] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 5 (.base 2 (.d8 0x78))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 120 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 4)
      ⟨.output 15, .reg 5⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_5d4 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.output 8, .reg 11⟩
      [0x4c, 0x89, 0x5a, 0x40] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 11 (.base 2 (.d8 0x40))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 64 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 4)
      ⟨.output 8, .reg 11⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataStep_5d8 [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 5) ⟨.reg 0, .stack 2⟩
      [0x48, 0x8b, 0x44, 0x24, 0x10] := by
  apply TraceStep.of_effect
    (Store.mov_load_step pc 0 (.sib 4 none 0 (.d8 0x10)) (by decide +kernel))
  · exact fun _ _ _ h ↦ h.stackLoadPre 16 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect ((Operand.reg 4 : Operand 64).read s) pointer (pc + 5)
      ⟨.reg 0, .stack 2⟩ s = _
    rw [hp.stack]

theorem dataStep_5dd [Bindings] (copy : Copy) (pc : BitVec 64) :
    TraceStep copy pc (pc + 4) ⟨.output 9, .reg 0⟩
      [0x48, 0x89, 0x42, 0x48] := by
  apply TraceStep.of_effect
    (mov_m64_r64_encoded_effect_step_of_readable pc 0 (.base 2 (.d8 0x48))
      (by decide +kernel))
  · exact fun _ _ _ h ↦ h.outputStorePre 72 (by decide +kernel)
  · intro sp pointer s hp
    change moveEffect sp ((Operand.reg 2 : Operand 64).read s) (pc + 4)
      ⟨.output 9, .reg 0⟩ s = _
    have hptr : (Operand.reg 2 : Operand 64).read s = pointer := hp.pointerValue
    rw [hptr]

theorem dataSteps [Bindings] (copy : Copy) (i : Fin 41) :
    TraceStep copy (dataPc copy i.castSucc) (dataPc copy i.succ) (dataOp i) (dataBytes i) := by
  cases copy <;> finite_cases i
  · exact dataStep_50b .absorb _
  · exact dataStep_513 .absorb _
  · exact dataStep_518 .absorb _
  · exact dataStep_51c .absorb _
  · exact dataStep_524 .absorb _
  · exact dataStep_528 .absorb _
  · exact dataStep_52c .absorb _
  · exact dataStep_534 .absorb _
  · exact dataStep_538 .absorb _
  · exact dataStep_53d .absorb _
  · exact dataStep_541 .absorb _
  · exact dataStep_546 .absorb _
  · exact dataStep_54a .absorb _
  · exact dataStep_54f .absorb _
  · exact dataStep_553 .absorb _
  · exact dataStep_558 .absorb _
  · exact dataStep_55b .absorb _
  · exact dataStep_560 .absorb _
  · exact dataStep_567 .absorb _
  · exact dataStep_56b .absorb _
  · exact dataStep_572 .absorb _
  · exact dataStep_577 .absorb _
  · exact dataStep_57e .absorb _
  · exact dataStep_583 .absorb _
  · exact dataStep_587 .absorb _
  · exact dataStep_58e .absorb _
  · exact dataStep_593 .absorb _
  · exact dataStep_59a .absorb _
  · exact dataStep_59e .absorb _
  · exact dataStep_5a5 .absorb _
  · exact dataStep_5a9 .absorb _
  · exact dataStep_5b0 .absorb _
  · exact dataStep_5b4 .absorb _
  · exact dataStep_5b9 .absorb _
  · exact dataStep_5bd .absorb _
  · exact dataStep_5c4 .absorb _
  · exact dataStep_5c9 .absorb _
  · exact dataStep_5d0 .absorb _
  · exact dataStep_5d4 .absorb _
  · exact dataStep_5d8 .absorb _
  · exact dataStep_5dd .absorb _
  · exact dataStep_50b .finalize _
  · exact dataStep_513 .finalize _
  · exact dataStep_518 .finalize _
  · exact dataStep_51c .finalize _
  · exact dataStep_524 .finalize _
  · exact dataStep_528 .finalize _
  · exact dataStep_52c .finalize _
  · exact dataStep_534 .finalize _
  · exact dataStep_538 .finalize _
  · exact dataStep_53d .finalize _
  · exact dataStep_541 .finalize _
  · exact dataStep_546 .finalize _
  · exact dataStep_54a .finalize _
  · exact dataStep_54f .finalize _
  · exact dataStep_553 .finalize _
  · exact dataStep_558 .finalize _
  · exact dataStep_55b .finalize _
  · exact dataStep_560 .finalize _
  · exact dataStep_567 .finalize _
  · exact dataStep_56b .finalize _
  · exact dataStep_572 .finalize _
  · exact dataStep_577 .finalize _
  · exact dataStep_57e .finalize _
  · exact dataStep_583 .finalize _
  · exact dataStep_587 .finalize _
  · exact dataStep_58e .finalize _
  · exact dataStep_593 .finalize _
  · exact dataStep_59a .finalize _
  · exact dataStep_59e .finalize _
  · exact dataStep_5a5 .finalize _
  · exact dataStep_5a9 .finalize _
  · exact dataStep_5b0 .finalize _
  · exact dataStep_5b4 .finalize _
  · exact dataStep_5b9 .finalize _
  · exact dataStep_5bd .finalize _
  · exact dataStep_5c4 .finalize _
  · exact dataStep_5c9 .finalize _
  · exact dataStep_5d0 .finalize _
  · exact dataStep_5d4 .finalize _
  · exact dataStep_5d8 .finalize _
  · exact dataStep_5dd .finalize _

end Sha3.Proofs.Permutation.StoreTrace
