import P256.Proofs.ReadBe.Loop.Head
import P256.Proofs.Common.Field.SquareRoot.Exponent.Initialize.Store

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.ReadBe.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem store_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x1190b1)
    (limbs : s.regValue .rcx = 4) (bits : s.regValue .r8 = 256)
    (writable : MemWritable s (stackPtr s + 8) 8)
    (apart : ∀ a, Component.Covers (.mem (stackPtr s + 8) 8) a → ¬ InProgram a)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x1190b9 ∧ t.regValue .rbx = 256 ∧
      t.external = memStore s.external (stackPtr s + 8) (4 : BitVec 64) ∧
      AgreesExcept [.reg 3,.rip,.mem (stackPtr s + 8) 8] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_r32_r32_rex_effect_step 0x1190b1 0x44 0xc3 (by simp [RexNoWPrefix]) rfl).advances ready
      (programText_slice code 0x190b1 _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x190b4 (by decide)))
  change (movR32R32Effect 0x1190b1 3 3 8 s).Holds s s1 at e1
  have f1 : AgreesExcept [.reg 3,.rip] s s1 := e1.agrees
  have m1 := f1.external (by simp [Component.Covers])
  have bx1 : s1.regValue .rbx = 256 := by
    have h : s1.regValue .rbx = ((s.regValue .r8).setWidth 32).setWidth 64 := e1.writes
    rwa [bits] at h
  have cx1 : s1.regValue .rcx = 4 := (f1.read (n := 64) (r := 1) (by simp)).trans limbs
  have sp1 : stackPtr s1 = stackPtr s := f1.read (n := 64) (r := 4) (by simp)
  have writable1 : MemWritable s1 (stackPtr s + 8) 8 := writable.of_external_eq m1
  have codeApart : RangeApart (stackPtr s + 8) 8 0x1190b4 5 := by
    intro i hi j hj he
    apply apart (stackPtr s + 8 + BitVec.ofNat 64 i) ⟨i, hi, rfl⟩
    rw [he]
    have hp := inProgram_of_textOffset (0x190b4+j) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hp
    exact hp
  obtain ⟨t, a2, r2, e2⟩ :=
    (mov_m64_r64_effect_step 0x1190b4 0x48 (by simp [RexWPrefix]) 1
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances r1
      (programText_slice (code.of_external_eq m1) 0x190b4 _ (by decide +kernel) (by decide +kernel))
      ⟨e1.rip, by change MemWritable s1 (stackPtr s1 + 8) 8; rwa [sp1],
        by change RangeApart (stackPtr s1 + 8) 8 0x1190b4 5; rwa [sp1]⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x190b9 (by decide)))
  have f2 : AgreesExcept [.mem (stackPtr s + 8) 8,.rip] s1 t := by
    have h : AgreesExcept [.mem (stackPtr s1 + 8) 8,.rip] s1 t := by
      have address : storeAddrAt 0x1190b4 (.sib 4 none 0 (.d8 8)) 5 s1 = stackPtr s1 + 8 := by rfl
      simpa only [movM64R64Effect_components, show 3 + (AddrMode.sib 4 none 0 (.d8 8)).tail.length = 5 from rfl, address] using e2.agrees
    rwa [sp1] at h
  have value : (Operand.mem (stackPtr s + 8) : Operand 64).read t = 4 := by
    have h : (Operand.mem (stackPtr s1 + 8) : Operand 64).read t = s1.regValue .rcx := e2.writes
    rwa [sp1, cx1] at h
  have memory := P256.Proofs.Common.Field.SquareRoot.ExponentInitialize.external_of_store f2 writable1.mem value
  refine ⟨t, a1.trans a2, r2, ?_, e2.rip,
    (f2.read (n := 64) (r := 3) (by simp)).trans bx1, ?_, (f1.trans f2).mono (by simp)⟩
  · intro a b hb
    apply Eq.trans (f2.byte ?_) (by rw [m1]; exact loaded a b hb)
    intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact apart a ha ⟨b, hb⟩
    · exact ha
  · simpa only [m1] using memory

end P256.Proofs.ReadBe.Entry
