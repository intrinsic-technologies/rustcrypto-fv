import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Steps

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator.Advance

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Instructions.CrossPageStore

def shiftEffect (s : RamState) : Effect :=
  { rip := 0x1181df
    writes := [⟨(Operand.mem (s.regValue .rdi + 16) : Operand 64), s.regValue .rax⟩,
      ⟨(Operand.mem (s.regValue .rdi + 24) : Operand 64), memLoad s.external (s.regValue .rdi + 32) 64⟩,
      ⟨(Operand.reg 1 : Operand 64), memLoad s.external (s.regValue .rdi + 8) 64⟩,
      ⟨(Operand.reg 0 : Operand 64), memLoad s.external (s.regValue .rdi + 32) 64⟩] }

theorem shift [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x1181cf)
    (write : Writable s (s.regValue .rdi) 40)
    (avoid : ∀ i < 40, ¬ InProgram (s.regValue .rdi + BitVec.ofNat 64 i))
    (outer : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧ (shiftEffect s).Holds s t := by
  have avoidSlot (o : Nat) (ho : o+8 ≤ 40) :
      ∀ i < 8, ¬ InProgram (s.regValue .rdi + BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact avoid _ (by omega)
  obtain ⟨a, runA, readyA, loadedA, effectA⟩ := store64 (offset := 0x181cf) 0 (.base 7 (.d8 16))
    (by decide +kernel) rfl rfl ready loaded rip (write.add 16 (by decide))
    (avoidSlot 16 (by decide)) (by decide) (by decide +kernel) outer
  change (movM64R64Effect 0x1181cf 0 (.base 7 (.d8 16)) s).Holds s a at effectA
  have agA : AgreesExcept [.mem (s.regValue .rdi + 16#64) 8, .rip] s a := by
    have eq : (movM64R64Effect 0x1181cf 0 (.base 7 (.d8 16)) s).components =
        [.mem (s.regValue .rdi + 16#64) 8, .rip] := by
      simp only [movM64R64Effect_components]; congr 2
    rw [← eq]; exact effectA.agrees
  have ap : a.regValue .rdi = s.regValue .rdi := agA.read (n := 64) (r := 7) (by simp)
  obtain ⟨b, runB, readyB, loadedB, effectB⟩ := load64 (offset := 0x181d3) 1 (.base 7 (.d8 8))
    (by decide +kernel) rfl rfl readyA loadedA effectA.rip
    (by change MemReadable a (a.regValue .rdi + 8) 8; rw [ap]
        exact (writable_grow (write.add 8 (by decide)) agA.grow).toMemReadable)
    (by decide) (by decide +kernel) outer
  change (movR64M64Effect 0x1181d3 1 (.base 7 (.d8 8)) a).Holds a b at effectB
  have memB : b.external = a.external := effectB.agrees.external (by simp [Component.Covers])
  have bp : b.regValue .rdi = s.regValue .rdi :=
    (effectB.agrees.read (n := 64) (r := 7) (by simp)).trans ap
  have frameB : AgreesExcept [.reg 1, .rip] a b := effectB.agrees
  have agB := agA.trans frameB
  obtain ⟨c, runC, readyC, loadedC, effectC⟩ := load64 (offset := 0x181d7) 0 (.base 7 (.d8 32))
    (by decide +kernel) rfl rfl readyB loadedB effectB.rip
    (by change MemReadable b (b.regValue .rdi + 32) 8; rw [bp]
        exact (writable_grow (write.add 32 (by decide)) agB.grow).toMemReadable)
    (by decide) (by decide +kernel) outer
  change (movR64M64Effect 0x1181d7 0 (.base 7 (.d8 32)) b).Holds b c at effectC
  have frameC : AgreesExcept [.reg 0, .rip] b c := effectC.agrees
  have agC := agB.trans frameC
  have cp : c.regValue .rdi = s.regValue .rdi := agC.read (n := 64) (r := 7) (by simp)
  obtain ⟨t, runT, readyT, loadedT, effectT⟩ := store64 (offset := 0x181db) 0 (.base 7 (.d8 24))
    (by decide +kernel) rfl rfl readyC loadedC effectC.rip
    (by change Writable c (c.regValue .rdi + 24) 8; rw [cp]
        exact writable_grow (write.add 24 (by decide)) agC.grow)
    (by change ∀ i < 8, ¬ InProgram (c.regValue .rdi + 24 + BitVec.ofNat 64 i)
        rw [cp]; exact avoidSlot 24 (by decide))
    (by decide) (by decide +kernel) outer
  change (movM64R64Effect 0x1181db 0 (.base 7 (.d8 24)) c).Holds c t at effectT
  have agT : AgreesExcept [.mem (s.regValue .rdi + 24) 8, .rip] c t := by
    have h' : AgreesExcept [.mem (c.regValue .rdi + 24#64) 8, .rip] c t := by
      have eq : (movM64R64Effect 0x1181db 0 (.base 7 (.d8 24)) c).components =
          [.mem (c.regValue .rdi + 24#64) 8, .rip] := by
        simp only [movM64R64Effect_components]; congr 2
      rw [← eq]; exact effectT.agrees
    simpa only [cp, BitVec.ofNat_eq_ofNat] using h'
  have cx : c.regValue .rax = memLoad s.external (s.regValue .rdi + 32) 64 := by
    have h : c.regValue .rax = memLoad b.external (b.regValue .rdi + 32) 64 := effectC.writes
    rw [h, bp, memB, slot_read agA (by unfold OffsetsApart; decide +kernel)]
  have bc : b.regValue .rcx = memLoad s.external (s.regValue .rdi + 8) 64 := by
    have h : b.regValue .rcx = memLoad a.external (a.regValue .rdi + 8) 64 := effectB.writes
    rw [h, ap, slot_read agA (by unfold OffsetsApart; decide +kernel)]
  refine ⟨t, ((runA.trans runB).trans runC).trans runT, readyT, loadedT, effectT.rip, ?_, trivial, ?_⟩
  · change memLoad t.external (s.regValue .rdi + 16) 64 = s.regValue .rax ∧
      memLoad t.external (s.regValue .rdi + 24) 64 = memLoad s.external (s.regValue .rdi + 32) 64 ∧
      t.regValue .rcx = memLoad s.external (s.regValue .rdi + 8) 64 ∧
      t.regValue .rax = memLoad s.external (s.regValue .rdi + 32) 64
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [slot_read agT (by unfold OffsetsApart; decide +kernel),
        effectC.agrees.external (by simp [Component.Covers]), memB]
      exact effectA.writes
    · have h : memLoad t.external (c.regValue .rdi + 24) 64 = c.regValue .rax := effectT.writes
      simpa only [cp, cx] using h
    · exact ((effectC.agrees.trans agT).read (n := 64) (r := 1) (by simp)).trans bc
    · exact (agT.read (n := 64) (r := 0) (by simp)).trans cx
  · apply (agC.trans agT).mono
    simp [shiftEffect, Effect.components]

theorem cached [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x11822c)
    (readable : MemReadable s (s.regValue .rdi) 40) (outer : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧ t.RIP = 0x118234 ∧
      t.regValue .rax = memLoad s.external (s.regValue .rdi + 24) 64 ∧
      t.regValue .rdx = memLoad s.external (s.regValue .rdi + 32) 64 ∧
      AgreesExcept [.reg 0, .reg 2, .rip] s t := by
  obtain ⟨a, runA, readyA, loadedA, effectA⟩ := load64 (offset := 0x1822c) 0 (.base 7 (.d8 24))
    (by decide +kernel) rfl rfl ready loaded rip (readable_subrange readable 24 8 (by decide))
    (by decide) (by decide +kernel) outer
  change (movR64M64Effect 0x11822c 0 (.base 7 (.d8 24)) s).Holds s a at effectA
  have ap : a.regValue .rdi = s.regValue .rdi := effectA.agrees.read (n := 64) (r := 7) (by simp)
  have memA := effectA.agrees.external (by simp [Component.Covers])
  obtain ⟨t, runT, readyT, loadedT, effectT⟩ := load64 (offset := 0x18230) 2 (.base 7 (.d8 32))
    (by decide +kernel) rfl rfl readyA loadedA effectA.rip
    (by change MemReadable a (a.regValue .rdi + 32) 8; rw [ap]
        exact (readable_subrange readable 32 8 (by decide)).of_external_eq memA)
    (by decide) (by decide +kernel) outer
  change (movR64M64Effect 0x118230 2 (.base 7 (.d8 32)) a).Holds a t at effectT
  refine ⟨t, runA.trans runT, readyT, loadedT, effectT.rip, ?_, ?_, ?_⟩
  · exact (effectT.agrees.read (n := 64) (r := 0) (by simp)).trans effectA.writes
  · have h : t.regValue .rdx = memLoad a.external (a.regValue .rdi + 32) 64 := effectT.writes
    simpa only [ap, memA] using h
  · exact (effectA.agrees.trans effectT.agrees).mono (by simp)

end P256.Proofs.Verifying.Combination.Naf.Iterator.Advance
