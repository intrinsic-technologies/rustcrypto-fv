import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Steps

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator.Advance

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Instructions.CrossPageStore

def fullEffect (s : RamState) : Effect :=
  let pointer := memLoad s.external (s.regValue .rdi) 64
  let high := memLoad s.external pointer 64
  { rip := 0x118267
    writes := [⟨(Operand.mem (s.regValue .rdi + 32) : Operand 64), high⟩,
      ⟨(Operand.mem (s.regValue .rdi) : Operand 64), pointer + 8⟩,
      ⟨(Operand.mem (s.regValue .rdi + 8) : Operand 64), s.regValue .rcx - 8⟩,
      ⟨(Operand.reg 6 : Operand 64), pointer + 8⟩,
      ⟨(Operand.reg 2 : Operand 64), high⟩,
      ⟨(Operand.reg 1 : Operand 64), s.regValue .rcx - 8⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem full [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x11824e)
    (write : Writable s (s.regValue .rdi) 40)
    (source : MemReadable s (memLoad s.external (s.regValue .rdi) 64) 8)
    (avoid : ∀ i < 40, ¬ InProgram (s.regValue .rdi + BitVec.ofNat 64 i))
    (outer : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧ (fullEffect s).Holds s t := by
  have avoidSlot (o : Nat) (ho : o+8 ≤ 40) :
      ∀ i < 8, ¬ InProgram (s.regValue .rdi + BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact avoid _ (by omega)
  obtain ⟨a, runA, readyA, loadedA, effectA⟩ := load64 (offset := 0x1824e) 6 (.base 7 .none)
    (by decide +kernel) rfl rfl ready loaded rip
    (by change MemReadable s (s.regValue .rdi + 0#64) 8
        exact readable_subrange write.toMemReadable 0 8 (by decide))
    (by decide) (by decide +kernel) outer
  change (movR64M64Effect 0x11824e 6 (.base 7 .none) s).Holds s a at effectA
  have a6 : a.regValue .rsi = memLoad s.external (s.regValue .rdi) 64 := by
    have h : a.regValue .rsi = memLoad s.external (s.regValue .rdi + 0#64) 64 := effectA.writes
    simpa only [BitVec.add_zero] using h
  have agA : AgreesExcept [.reg 6, .rip] s a := effectA.agrees
  obtain ⟨b, runB, readyB, loadedB, effectB⟩ := step_nomem (offset := 0x18251)
    (add_r64_imm8_effect_step 0x118251 0x48 0xc1 0xf8 (by simp [RexWPrefix]) rfl rfl)
    readyA loadedA effectA.rip (by decide) (by decide +kernel)
    (boundary_ne_program outer (inProgram_of_textOffset 0x18255 (by decide)))
    (by simp [Component.Covers])
  change (addR64Imm8Effect 0x118251 1 0xf8 a).Holds a b at effectB
  have agB : AgreesExcept [.reg 6, .reg 1, .flags, .rip] s b :=
    (agA.trans effectB.agrees).mono (by simp)
  have b6 : b.regValue .rsi = memLoad s.external (s.regValue .rdi) 64 :=
    (effectB.agrees.read (n := 64) (r := 6) (by simp)).trans a6
  have b1 : b.regValue .rcx = s.regValue .rcx - 8 := by
    have h : b.regValue .rcx = a.regValue .rcx + (0xf8#8).signExtend 64 := effectB.writes
    have h1 : a.regValue .rcx = s.regValue .rcx := agA.read (n := 64) (r := 1) (by simp)
    rw [h, h1, BitVec.sub_eq_add_neg]
    rfl
  have memB := agB.external (by simp [Component.Covers])
  obtain ⟨c, runC, readyC, loadedC, effectC⟩ := load64 (offset := 0x18255) 2 (.base 6 .none)
    (by decide +kernel) rfl rfl readyB loadedB effectB.rip
    (by change MemReadable b (b.regValue .rsi + 0#64) 8
        rw [BitVec.add_zero, b6]; exact source.of_external_eq memB)
    (by decide) (by decide +kernel) outer
  change (movR64M64Effect 0x118255 2 (.base 6 .none) b).Holds b c at effectC
  have c2 : c.regValue .rdx = memLoad s.external (memLoad s.external (s.regValue .rdi) 64) 64 := by
    have h : c.regValue .rdx = memLoad b.external (b.regValue .rsi + 0#64) 64 := effectC.writes
    simpa only [BitVec.add_zero, memB, b6] using h
  have frameC : AgreesExcept [.reg 2, .rip] b c := effectC.agrees
  have agC := agB.trans frameC
  obtain ⟨d, runD, readyD, loadedD, effectD⟩ := step_nomem (offset := 0x18258)
    (add_r64_imm8_effect_step 0x118258 0x48 0xc6 8 (by simp [RexWPrefix]) rfl rfl)
    readyC loadedC effectC.rip (by decide) (by decide +kernel)
    (boundary_ne_program outer (inProgram_of_textOffset 0x1825c (by decide)))
    (by simp [Component.Covers])
  change (addR64Imm8Effect 0x118258 6 8 c).Holds c d at effectD
  have d6 : d.regValue .rsi = memLoad s.external (s.regValue .rdi) 64 + 8 := by
    have h : d.regValue .rsi = c.regValue .rsi + 8 := effectD.writes
    have h6 : c.regValue .rsi = b.regValue .rsi := frameC.read (n := 64) (r := 6) (by simp)
    rw [h, h6, b6]
  have frameD : AgreesExcept [.reg 6, .flags, .rip] c d := effectD.agrees
  have agD := agC.trans frameD
  have dp : d.regValue .rdi = s.regValue .rdi := agD.read (n := 64) (r := 7) (by simp)
  obtain ⟨e, runE, readyE, loadedE, effectE⟩ := store64 (offset := 0x1825c) 2 (.base 7 (.d8 32))
    (by decide +kernel) rfl rfl readyD loadedD effectD.rip
    (by change Writable d (d.regValue .rdi + 32) 8; rw [dp]
        exact writable_grow (write.add 32 (by decide)) agD.grow)
    (by change ∀ i < 8, ¬ InProgram (d.regValue .rdi + 32 + BitVec.ofNat 64 i)
        rw [dp]; exact avoidSlot 32 (by decide))
    (by decide) (by decide +kernel) outer
  change (movM64R64Effect 0x11825c 2 (.base 7 (.d8 32)) d).Holds d e at effectE
  have frameE : AgreesExcept [.mem (s.regValue .rdi + 32) 8, .rip] d e := by
    have eq : (movM64R64Effect 0x11825c 2 (.base 7 (.d8 32)) d).components =
        [.mem (d.regValue .rdi + 32) 8, .rip] := by
      simp only [movM64R64Effect_components]; congr 2
    simpa only [eq, dp] using effectE.agrees
  have agE := agD.trans frameE
  have ep : e.regValue .rdi = s.regValue .rdi := agE.read (n := 64) (r := 7) (by simp)
  obtain ⟨f, runF, readyF, loadedF, effectF⟩ := store64 (offset := 0x18260) 6 (.base 7 .none)
    (by decide +kernel) rfl rfl readyE loadedE effectE.rip
    (by change Writable e (e.regValue .rdi + 0#64) 8; rw [ep]
        exact writable_grow (write.add 0 (by decide)) agE.grow)
    (by change ∀ i < 8, ¬ InProgram (e.regValue .rdi + 0#64 + BitVec.ofNat 64 i)
        rw [ep]; exact avoidSlot 0 (by decide))
    (by decide) (by decide +kernel) outer
  change (movM64R64Effect 0x118260 6 (.base 7 .none) e).Holds e f at effectF
  have frameF : AgreesExcept [.mem (s.regValue .rdi + 0#64) 8, .rip] e f := by
    have eq : (movM64R64Effect 0x118260 6 (.base 7 .none) e).components =
        [.mem (e.regValue .rdi + 0#64) 8, .rip] := by
      simp only [movM64R64Effect_components]; congr 2
    simpa only [eq, ep] using effectF.agrees
  have agF := agE.trans frameF
  have fp : f.regValue .rdi = s.regValue .rdi := agF.read (n := 64) (r := 7) (by simp)
  obtain ⟨t, runT, readyT, loadedT, effectT⟩ := store64 (offset := 0x18263) 1 (.base 7 (.d8 8))
    (by decide +kernel) rfl rfl readyF loadedF effectF.rip
    (by change Writable f (f.regValue .rdi + 8) 8; rw [fp]
        exact writable_grow (write.add 8 (by decide)) agF.grow)
    (by change ∀ i < 8, ¬ InProgram (f.regValue .rdi + 8 + BitVec.ofNat 64 i)
        rw [fp]; exact avoidSlot 8 (by decide))
    (by decide) (by decide +kernel) outer
  change (movM64R64Effect 0x118263 1 (.base 7 (.d8 8)) f).Holds f t at effectT
  have frameT : AgreesExcept [.mem (s.regValue .rdi + 8) 8, .rip] f t := by
    have eq : (movM64R64Effect 0x118263 1 (.base 7 (.d8 8)) f).components =
        [.mem (f.regValue .rdi + 8) 8, .rip] := by
      simp only [movM64R64Effect_components]; congr 2
    simpa only [eq, fp] using effectT.agrees
  have f1 : f.regValue .rcx = s.regValue .rcx - 8 :=
    ((((frameC.trans frameD).trans frameE).trans frameF).read (n := 64) (r := 1) (by simp)).trans b1
  have d2 : d.regValue .rdx = memLoad s.external (memLoad s.external (s.regValue .rdi) 64) 64 :=
    (frameD.read (n := 64) (r := 2) (by simp)).trans c2
  have e6 : e.regValue .rsi = memLoad s.external (s.regValue .rdi) 64 + 8 :=
    (frameE.read (n := 64) (r := 6) (by simp)).trans d6
  refine ⟨t, (((((runA.trans runB).trans runC).trans runD).trans runE).trans runF).trans runT,
    readyT, loadedT, effectT.rip, ?_, by repeat constructor, ?_⟩
  · change memLoad t.external (s.regValue .rdi + 32) 64 = _ ∧
      memLoad t.external (s.regValue .rdi) 64 = _ ∧
      memLoad t.external (s.regValue .rdi + 8) 64 = _ ∧
      t.regValue .rsi = _ ∧ t.regValue .rdx = _ ∧ t.regValue .rcx = _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [slot_read frameT (by unfold OffsetsApart; decide +kernel),
        slot_read frameF (by unfold OffsetsApart; decide +kernel)]
      have h : memLoad e.external (d.regValue .rdi + 32) 64 = d.regValue .rdx := effectE.writes
      simpa only [dp, d2] using h
    · have h : memLoad f.external (e.regValue .rdi + 0#64) 64 = e.regValue .rsi := effectF.writes
      rw [← BitVec.add_zero (s.regValue .rdi), slot_read frameT (by unfold OffsetsApart; decide +kernel)]
      simpa only [ep, e6, BitVec.add_zero] using h
    · have h : memLoad t.external (f.regValue .rdi + 8) 64 = f.regValue .rcx := effectT.writes
      simpa only [fp, f1] using h
    · exact (((frameE.trans frameF).trans frameT).read (n := 64) (r := 6) (by simp)).trans d6
    · exact ((((frameD.trans frameE).trans frameF).trans frameT).read (n := 64) (r := 2) (by simp)).trans c2
    · exact (frameT.read (n := 64) (r := 1) (by simp)).trans f1
  · apply (agF.trans frameT).mono
    simp [fullEffect, Effect.components]

end P256.Proofs.Verifying.Combination.Naf.Iterator.Advance
