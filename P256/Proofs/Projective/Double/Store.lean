import P256.Proofs.Projective.Double.StoreMemory
import P256.Proofs.Projective.Double.Combinations.Memory

set_option autoImplicit false

namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 2048 in
theorem copy_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (state : FrameState s t 96 1016 728) (rip : t.RIP = 0x106462) (input : OutputAt s t point) :
    ∃ u, Advances boundary 24 t u ∧ FrameState s u 96 1016 728 ∧ u.RIP = 0x1064e5 ∧
      ProjectiveAt u (s.regValue .rdi) point.double := by
  have bx0 := input.rbx
  have memory0 := memoryWriteFrame_refl t #v[registerRegion s .rdi 96]
  obtain ⟨t1, run1, frame1, effect1⟩ := step_registers pre state
    (offset := 0x6462) (mov_r64_m64_effect_step 0x106462 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d32 256)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) ⟨rip, stack_readable (frameOffset := 728) pre state (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x646a (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide)
  have external1 : t1.external = t.external :=
    effect1.agrees.external (by simp [Component.Covers])
  have memory1 : MemoryWriteFrame t t1 #v[registerRegion s .rdi 96] := by
    intro a ha
    exact (congrArg (fun mem : Ram => mem[a]?) external1).trans (memory0 a ha)
  have value1 : (Operand.reg 0 : Operand 64).read t1 =
      memLoad t.external (stackSlot s 256) 64 := by
    have hw : (Operand.reg 0 : Operand 64).read t1 =
        memLoad t.external (stackPtr t + 256) 64 := effect1.writes
    rw [hw, state.rsp]
    exact stackSlot_read_of_point pre memory0 (by decide)
  have bx1 : t1.regValue .rbx = s.regValue .rdi :=
    (effect1.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx0
  obtain ⟨t2, run2, frame2, effect2⟩ := step pre frame1 (by decide)
    (offset := 0x646a) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10646a 0x48
      (by simp [RexWPrefix]) 0 (.base 3 (.d8 24)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨effect1.rip, (by
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable t1 (t1.regValue .rbx + BitVec.ofNat 64 24) 8
      rw [bx1]
      exact point_writable pre frame1 (offset := 24) (by decide) (by decide)),
      (by
        change RangeApart (t1.regValue .rbx + BitVec.ofNat 64 24) 8 0x10646a 4
        rw [bx1]
        exact point_code pre (offset := 24) (codeOffset := 0x646a) (by decide) (by decide))⟩
    (inProgram_of_textOffset 0x646e (by decide))
    (by
      simp only [movM64R64Effect_components]
      change WritesWithin [.mem (t1.regValue .rbx + BitVec.ofNat 64 24) 8, .rip] _
      rw [bx1]
      exact point_write_within pre (offset := 24) (by simp) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have store2 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 24) 8, .rip] t1 t2 := by
    have h : AgreesExcept [.mem (t1.regValue .rbx + BitVec.ofNat 64 24) 8, .rip] t1 t2 := by
      change AgreesExcept [.mem ((Operand.reg 3 : Operand 64).read t1 + BitVec.ofNat 64 24) 8, .rip] t1 t2
      simpa (config := {decide := true}) only [movM64R64Effect_components, x86_compose] using effect2.agrees
    simpa only [bx1, BitVec.add_zero] using h
  have memory2 : MemoryWriteFrame t t2 #v[registerRegion s .rdi 96] :=
    memoryWriteFrame_trans memory1
      (store2.memoryWriteFrame (point_write_within pre (by simp) (by decide)))
  have written2 : memLoad t2.external (s.regValue .rdi + BitVec.ofNat 64 24) 64 =
      memLoad t.external (stackSlot s 256) 64 := by
    have hw : memLoad t2.external (t1.regValue .rbx + BitVec.ofNat 64 24) 64 =
        (Operand.reg 0 : Operand 64).read t1 := effect2.writes
    exact (by
      rw [bx1] at hw
      rw [hw]
      exact value1)
  have bx2 : t2.regValue .rbx = s.regValue .rdi :=
    (effect2.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx1
  obtain ⟨t3, run3, frame3, effect3⟩ := step_registers pre frame2
    (offset := 0x646e) (mov_r64_m64_effect_step 0x10646e 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d32 248)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) ⟨effect2.rip, stack_readable (frameOffset := 728) pre frame2 (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x6476 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide)
  have external3 : t3.external = t2.external :=
    effect3.agrees.external (by simp [Component.Covers])
  have memory3 : MemoryWriteFrame t t3 #v[registerRegion s .rdi 96] := by
    intro a ha
    exact (congrArg (fun mem : Ram => mem[a]?) external3).trans (memory2 a ha)
  have value3 : (Operand.reg 0 : Operand 64).read t3 =
      memLoad t.external (stackSlot s 248) 64 := by
    have hw : (Operand.reg 0 : Operand 64).read t3 =
        memLoad t2.external (stackPtr t2 + 248) 64 := effect3.writes
    rw [hw, frame2.rsp]
    exact stackSlot_read_of_point pre memory2 (by decide)
  have bx3 : t3.regValue .rbx = s.regValue .rdi :=
    (effect3.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx2
  obtain ⟨t4, run4, frame4, effect4⟩ := step pre frame3 (by decide)
    (offset := 0x6476) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106476 0x48
      (by simp [RexWPrefix]) 0 (.base 3 (.d8 16)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨effect3.rip, (by
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable t3 (t3.regValue .rbx + BitVec.ofNat 64 16) 8
      rw [bx3]
      exact point_writable pre frame3 (offset := 16) (by decide) (by decide)),
      (by
        change RangeApart (t3.regValue .rbx + BitVec.ofNat 64 16) 8 0x106476 4
        rw [bx3]
        exact point_code pre (offset := 16) (codeOffset := 0x6476) (by decide) (by decide))⟩
    (inProgram_of_textOffset 0x647a (by decide))
    (by
      simp only [movM64R64Effect_components]
      change WritesWithin [.mem (t3.regValue .rbx + BitVec.ofNat 64 16) 8, .rip] _
      rw [bx3]
      exact point_write_within pre (offset := 16) (by simp) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have store4 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 16) 8, .rip] t3 t4 := by
    have h : AgreesExcept [.mem (t3.regValue .rbx + BitVec.ofNat 64 16) 8, .rip] t3 t4 := by
      change AgreesExcept [.mem ((Operand.reg 3 : Operand 64).read t3 + BitVec.ofNat 64 16) 8, .rip] t3 t4
      simpa (config := {decide := true}) only [movM64R64Effect_components, x86_compose] using effect4.agrees
    simpa only [bx3, BitVec.add_zero] using h
  have memory4 : MemoryWriteFrame t t4 #v[registerRegion s .rdi 96] :=
    memoryWriteFrame_trans memory3
      (store4.memoryWriteFrame (point_write_within pre (by simp) (by decide)))
  have written4 : memLoad t4.external (s.regValue .rdi + BitVec.ofNat 64 16) 64 =
      memLoad t.external (stackSlot s 248) 64 := by
    have hw : memLoad t4.external (t3.regValue .rbx + BitVec.ofNat 64 16) 64 =
        (Operand.reg 0 : Operand 64).read t3 := effect4.writes
    exact (by
      rw [bx3] at hw
      rw [hw]
      exact value3)
  have bx4 : t4.regValue .rbx = s.regValue .rdi :=
    (effect4.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx3
  obtain ⟨t5, run5, frame5, effect5⟩ := step_registers pre frame4
    (offset := 0x647a) (mov_r64_m64_effect_step 0x10647a 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d32 232)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) ⟨effect4.rip, stack_readable (frameOffset := 728) pre frame4 (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x6482 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide)
  have external5 : t5.external = t4.external :=
    effect5.agrees.external (by simp [Component.Covers])
  have memory5 : MemoryWriteFrame t t5 #v[registerRegion s .rdi 96] := by
    intro a ha
    exact (congrArg (fun mem : Ram => mem[a]?) external5).trans (memory4 a ha)
  have value5 : (Operand.reg 0 : Operand 64).read t5 =
      memLoad t.external (stackSlot s 232) 64 := by
    have hw : (Operand.reg 0 : Operand 64).read t5 =
        memLoad t4.external (stackPtr t4 + 232) 64 := effect5.writes
    rw [hw, frame4.rsp]
    exact stackSlot_read_of_point pre memory4 (by decide)
  have bx5 : t5.regValue .rbx = s.regValue .rdi :=
    (effect5.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx4
  obtain ⟨t6, run6, frame6, effect6⟩ := step_registers pre frame5
    (offset := 0x6482) (mov_r64_m64_effect_step 0x106482 0x48 (by simp [RexWPrefix]) 1
      (.sib 4 none 0 (.d32 240)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) ⟨effect5.rip, stack_readable (frameOffset := 728) pre frame5 (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x648a (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 1, .rip]; decide)
  have external6 : t6.external = t5.external :=
    effect6.agrees.external (by simp [Component.Covers])
  have memory6 : MemoryWriteFrame t t6 #v[registerRegion s .rdi 96] := by
    intro a ha
    exact (congrArg (fun mem : Ram => mem[a]?) external6).trans (memory5 a ha)
  have value6 : (Operand.reg 1 : Operand 64).read t6 =
      memLoad t.external (stackSlot s 240) 64 := by
    have hw : (Operand.reg 1 : Operand 64).read t6 =
        memLoad t5.external (stackPtr t5 + 240) 64 := effect6.writes
    rw [hw, frame5.rsp]
    exact stackSlot_read_of_point pre memory5 (by decide)
  have bx6 : t6.regValue .rbx = s.regValue .rdi :=
    (effect6.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx5
  obtain ⟨t7, run7, frame7, effect7⟩ := step pre frame6 (by decide)
    (offset := 0x648a) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10648a 0x48
      (by simp [RexWPrefix]) 1 (.base 3 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨effect6.rip, (by
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable t6 (t6.regValue .rbx + BitVec.ofNat 64 8) 8
      rw [bx6]
      exact point_writable pre frame6 (offset := 8) (by decide) (by decide)),
      (by
        change RangeApart (t6.regValue .rbx + BitVec.ofNat 64 8) 8 0x10648a 4
        rw [bx6]
        exact point_code pre (offset := 8) (codeOffset := 0x648a) (by decide) (by decide))⟩
    (inProgram_of_textOffset 0x648e (by decide))
    (by
      simp only [movM64R64Effect_components]
      change WritesWithin [.mem (t6.regValue .rbx + BitVec.ofNat 64 8) 8, .rip] _
      rw [bx6]
      exact point_write_within pre (offset := 8) (by simp) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have store7 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 8) 8, .rip] t6 t7 := by
    have h : AgreesExcept [.mem (t6.regValue .rbx + BitVec.ofNat 64 8) 8, .rip] t6 t7 := by
      change AgreesExcept [.mem ((Operand.reg 3 : Operand 64).read t6 + BitVec.ofNat 64 8) 8, .rip] t6 t7
      simpa (config := {decide := true}) only [movM64R64Effect_components, x86_compose] using effect7.agrees
    simpa only [bx6, BitVec.add_zero] using h
  have memory7 : MemoryWriteFrame t t7 #v[registerRegion s .rdi 96] :=
    memoryWriteFrame_trans memory6
      (store7.memoryWriteFrame (point_write_within pre (by simp) (by decide)))
  have written7 : memLoad t7.external (s.regValue .rdi + BitVec.ofNat 64 8) 64 =
      memLoad t.external (stackSlot s 240) 64 := by
    have hw : memLoad t7.external (t6.regValue .rbx + BitVec.ofNat 64 8) 64 =
        (Operand.reg 1 : Operand 64).read t6 := effect7.writes
    exact (by
      rw [bx6] at hw
      rw [hw]
      exact value6)
  have bx7 : t7.regValue .rbx = s.regValue .rdi :=
    (effect7.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx6
  obtain ⟨t8, run8, frame8, effect8⟩ := step pre frame7 (by decide)
    (offset := 0x648e) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10648e 0x48
      (by simp [RexWPrefix]) 0 (.base 3 .none) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨effect7.rip, (by
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable t7 (t7.regValue .rbx + BitVec.ofNat 64 0) 8
      rw [bx7]
      exact point_writable pre frame7 (offset := 0) (by decide) (by decide)),
      (by
        change RangeApart (t7.regValue .rbx + BitVec.ofNat 64 0) 8 0x10648e 3
        rw [bx7]
        exact point_code pre (offset := 0) (codeOffset := 0x648e) (by decide) (by decide))⟩
    (inProgram_of_textOffset 0x6491 (by decide))
    (by
      simp only [movM64R64Effect_components]
      change WritesWithin [.mem (t7.regValue .rbx + BitVec.ofNat 64 0) 8, .rip] _
      rw [bx7]
      exact point_write_within pre (offset := 0) (by simp) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have store8 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 0) 8, .rip] t7 t8 := by
    have h : AgreesExcept [.mem (t7.regValue .rbx + BitVec.ofNat 64 0) 8, .rip] t7 t8 := by
      change AgreesExcept [.mem ((Operand.reg 3 : Operand 64).read t7 + BitVec.ofNat 64 0) 8, .rip] t7 t8
      simpa (config := {decide := true}) only [movM64R64Effect_components, x86_compose] using effect8.agrees
    simpa only [bx7, BitVec.add_zero] using h
  have memory8 : MemoryWriteFrame t t8 #v[registerRegion s .rdi 96] :=
    memoryWriteFrame_trans memory7
      (store8.memoryWriteFrame (point_write_within pre (by simp) (by decide)))
  have written8 : memLoad t8.external (s.regValue .rdi + BitVec.ofNat 64 0) 64 =
      memLoad t.external (stackSlot s 232) 64 := by
    have hw : memLoad t8.external (t7.regValue .rbx + BitVec.ofNat 64 0) 64 =
        (Operand.reg 0 : Operand 64).read t7 := effect8.writes
    exact (by
      rw [bx7] at hw
      rw [hw]
      rw [effect7.agrees.read (r := 0) (n := 64) (by simp (config := {decide := true}))]
      rw [effect6.agrees.read (r := 0) (n := 64) (by simp (config := {decide := true}))]
      exact value5)
  have bx8 : t8.regValue .rbx = s.regValue .rdi :=
    (effect8.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx7
  obtain ⟨t9, run9, frame9, effect9⟩ := step_registers pre frame8
    (offset := 0x6491) (mov_r64_m64_effect_step 0x106491 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d32 456)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) ⟨effect8.rip, stack_readable (frameOffset := 728) pre frame8 (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x6499 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide)
  have external9 : t9.external = t8.external :=
    effect9.agrees.external (by simp [Component.Covers])
  have memory9 : MemoryWriteFrame t t9 #v[registerRegion s .rdi 96] := by
    intro a ha
    exact (congrArg (fun mem : Ram => mem[a]?) external9).trans (memory8 a ha)
  have value9 : (Operand.reg 0 : Operand 64).read t9 =
      memLoad t.external (stackSlot s 456) 64 := by
    have hw : (Operand.reg 0 : Operand 64).read t9 =
        memLoad t8.external (stackPtr t8 + 456) 64 := effect9.writes
    rw [hw, frame8.rsp]
    exact stackSlot_read_of_point pre memory8 (by decide)
  have bx9 : t9.regValue .rbx = s.regValue .rdi :=
    (effect9.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx8
  obtain ⟨t10, run10, frame10, effect10⟩ := step_registers pre frame9
    (offset := 0x6499) (mov_r64_m64_effect_step 0x106499 0x48 (by simp [RexWPrefix]) 1
      (.sib 4 none 0 (.d32 464)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) ⟨effect9.rip, stack_readable (frameOffset := 728) pre frame9 (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x64a1 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 1, .rip]; decide)
  have external10 : t10.external = t9.external :=
    effect10.agrees.external (by simp [Component.Covers])
  have memory10 : MemoryWriteFrame t t10 #v[registerRegion s .rdi 96] := by
    intro a ha
    exact (congrArg (fun mem : Ram => mem[a]?) external10).trans (memory9 a ha)
  have value10 : (Operand.reg 1 : Operand 64).read t10 =
      memLoad t.external (stackSlot s 464) 64 := by
    have hw : (Operand.reg 1 : Operand 64).read t10 =
        memLoad t9.external (stackPtr t9 + 464) 64 := effect10.writes
    rw [hw, frame9.rsp]
    exact stackSlot_read_of_point pre memory9 (by decide)
  have bx10 : t10.regValue .rbx = s.regValue .rdi :=
    (effect10.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx9
  obtain ⟨t11, run11, frame11, effect11⟩ := step pre frame10 (by decide)
    (offset := 0x64a1) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1064a1 0x48
      (by simp [RexWPrefix]) 0 (.base 3 (.d8 32)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨effect10.rip, (by
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable t10 (t10.regValue .rbx + BitVec.ofNat 64 32) 8
      rw [bx10]
      exact point_writable pre frame10 (offset := 32) (by decide) (by decide)),
      (by
        change RangeApart (t10.regValue .rbx + BitVec.ofNat 64 32) 8 0x1064a1 4
        rw [bx10]
        exact point_code pre (offset := 32) (codeOffset := 0x64a1) (by decide) (by decide))⟩
    (inProgram_of_textOffset 0x64a5 (by decide))
    (by
      simp only [movM64R64Effect_components]
      change WritesWithin [.mem (t10.regValue .rbx + BitVec.ofNat 64 32) 8, .rip] _
      rw [bx10]
      exact point_write_within pre (offset := 32) (by simp) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have store11 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 32) 8, .rip] t10 t11 := by
    have h : AgreesExcept [.mem (t10.regValue .rbx + BitVec.ofNat 64 32) 8, .rip] t10 t11 := by
      change AgreesExcept [.mem ((Operand.reg 3 : Operand 64).read t10 + BitVec.ofNat 64 32) 8, .rip] t10 t11
      simpa (config := {decide := true}) only [movM64R64Effect_components, x86_compose] using effect11.agrees
    simpa only [bx10, BitVec.add_zero] using h
  have memory11 : MemoryWriteFrame t t11 #v[registerRegion s .rdi 96] :=
    memoryWriteFrame_trans memory10
      (store11.memoryWriteFrame (point_write_within pre (by simp) (by decide)))
  have written11 : memLoad t11.external (s.regValue .rdi + BitVec.ofNat 64 32) 64 =
      memLoad t.external (stackSlot s 456) 64 := by
    have hw : memLoad t11.external (t10.regValue .rbx + BitVec.ofNat 64 32) 64 =
        (Operand.reg 0 : Operand 64).read t10 := effect11.writes
    exact (by
      rw [bx10] at hw
      rw [hw]
      rw [effect10.agrees.read (r := 0) (n := 64) (by simp (config := {decide := true}))]
      exact value9)
  have bx11 : t11.regValue .rbx = s.regValue .rdi :=
    (effect11.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx10
  obtain ⟨t12, run12, frame12, effect12⟩ := step pre frame11 (by decide)
    (offset := 0x64a5) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1064a5 0x48
      (by simp [RexWPrefix]) 1 (.base 3 (.d8 40)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨effect11.rip, (by
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable t11 (t11.regValue .rbx + BitVec.ofNat 64 40) 8
      rw [bx11]
      exact point_writable pre frame11 (offset := 40) (by decide) (by decide)),
      (by
        change RangeApart (t11.regValue .rbx + BitVec.ofNat 64 40) 8 0x1064a5 4
        rw [bx11]
        exact point_code pre (offset := 40) (codeOffset := 0x64a5) (by decide) (by decide))⟩
    (inProgram_of_textOffset 0x64a9 (by decide))
    (by
      simp only [movM64R64Effect_components]
      change WritesWithin [.mem (t11.regValue .rbx + BitVec.ofNat 64 40) 8, .rip] _
      rw [bx11]
      exact point_write_within pre (offset := 40) (by simp) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have store12 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 40) 8, .rip] t11 t12 := by
    have h : AgreesExcept [.mem (t11.regValue .rbx + BitVec.ofNat 64 40) 8, .rip] t11 t12 := by
      change AgreesExcept [.mem ((Operand.reg 3 : Operand 64).read t11 + BitVec.ofNat 64 40) 8, .rip] t11 t12
      simpa (config := {decide := true}) only [movM64R64Effect_components, x86_compose] using effect12.agrees
    simpa only [bx11, BitVec.add_zero] using h
  have memory12 : MemoryWriteFrame t t12 #v[registerRegion s .rdi 96] :=
    memoryWriteFrame_trans memory11
      (store12.memoryWriteFrame (point_write_within pre (by simp) (by decide)))
  have written12 : memLoad t12.external (s.regValue .rdi + BitVec.ofNat 64 40) 64 =
      memLoad t.external (stackSlot s 464) 64 := by
    have hw : memLoad t12.external (t11.regValue .rbx + BitVec.ofNat 64 40) 64 =
        (Operand.reg 1 : Operand 64).read t11 := effect12.writes
    exact (by
      rw [bx11] at hw
      rw [hw]
      rw [effect11.agrees.read (r := 1) (n := 64) (by simp (config := {decide := true}))]
      exact value10)
  have bx12 : t12.regValue .rbx = s.regValue .rdi :=
    (effect12.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx11
  obtain ⟨t13, run13, frame13, effect13⟩ := step_registers pre frame12
    (offset := 0x64a9) (mov_r64_m64_effect_step 0x1064a9 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d32 472)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) ⟨effect12.rip, stack_readable (frameOffset := 728) pre frame12 (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x64b1 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide)
  have external13 : t13.external = t12.external :=
    effect13.agrees.external (by simp [Component.Covers])
  have memory13 : MemoryWriteFrame t t13 #v[registerRegion s .rdi 96] := by
    intro a ha
    exact (congrArg (fun mem : Ram => mem[a]?) external13).trans (memory12 a ha)
  have value13 : (Operand.reg 0 : Operand 64).read t13 =
      memLoad t.external (stackSlot s 472) 64 := by
    have hw : (Operand.reg 0 : Operand 64).read t13 =
        memLoad t12.external (stackPtr t12 + 472) 64 := effect13.writes
    rw [hw, frame12.rsp]
    exact stackSlot_read_of_point pre memory12 (by decide)
  have bx13 : t13.regValue .rbx = s.regValue .rdi :=
    (effect13.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx12
  obtain ⟨t14, run14, frame14, effect14⟩ := step pre frame13 (by decide)
    (offset := 0x64b1) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1064b1 0x48
      (by simp [RexWPrefix]) 0 (.base 3 (.d8 48)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨effect13.rip, (by
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable t13 (t13.regValue .rbx + BitVec.ofNat 64 48) 8
      rw [bx13]
      exact point_writable pre frame13 (offset := 48) (by decide) (by decide)),
      (by
        change RangeApart (t13.regValue .rbx + BitVec.ofNat 64 48) 8 0x1064b1 4
        rw [bx13]
        exact point_code pre (offset := 48) (codeOffset := 0x64b1) (by decide) (by decide))⟩
    (inProgram_of_textOffset 0x64b5 (by decide))
    (by
      simp only [movM64R64Effect_components]
      change WritesWithin [.mem (t13.regValue .rbx + BitVec.ofNat 64 48) 8, .rip] _
      rw [bx13]
      exact point_write_within pre (offset := 48) (by simp) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have store14 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 48) 8, .rip] t13 t14 := by
    have h : AgreesExcept [.mem (t13.regValue .rbx + BitVec.ofNat 64 48) 8, .rip] t13 t14 := by
      change AgreesExcept [.mem ((Operand.reg 3 : Operand 64).read t13 + BitVec.ofNat 64 48) 8, .rip] t13 t14
      simpa (config := {decide := true}) only [movM64R64Effect_components, x86_compose] using effect14.agrees
    simpa only [bx13, BitVec.add_zero] using h
  have memory14 : MemoryWriteFrame t t14 #v[registerRegion s .rdi 96] :=
    memoryWriteFrame_trans memory13
      (store14.memoryWriteFrame (point_write_within pre (by simp) (by decide)))
  have written14 : memLoad t14.external (s.regValue .rdi + BitVec.ofNat 64 48) 64 =
      memLoad t.external (stackSlot s 472) 64 := by
    have hw : memLoad t14.external (t13.regValue .rbx + BitVec.ofNat 64 48) 64 =
        (Operand.reg 0 : Operand 64).read t13 := effect14.writes
    exact (by
      rw [bx13] at hw
      rw [hw]
      exact value13)
  have bx14 : t14.regValue .rbx = s.regValue .rdi :=
    (effect14.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx13
  obtain ⟨t15, run15, frame15, effect15⟩ := step_registers pre frame14
    (offset := 0x64b5) (mov_r64_m64_effect_step 0x1064b5 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d32 480)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) ⟨effect14.rip, stack_readable (frameOffset := 728) pre frame14 (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x64bd (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide)
  have external15 : t15.external = t14.external :=
    effect15.agrees.external (by simp [Component.Covers])
  have memory15 : MemoryWriteFrame t t15 #v[registerRegion s .rdi 96] := by
    intro a ha
    exact (congrArg (fun mem : Ram => mem[a]?) external15).trans (memory14 a ha)
  have value15 : (Operand.reg 0 : Operand 64).read t15 =
      memLoad t.external (stackSlot s 480) 64 := by
    have hw : (Operand.reg 0 : Operand 64).read t15 =
        memLoad t14.external (stackPtr t14 + 480) 64 := effect15.writes
    rw [hw, frame14.rsp]
    exact stackSlot_read_of_point pre memory14 (by decide)
  have bx15 : t15.regValue .rbx = s.regValue .rdi :=
    (effect15.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx14
  obtain ⟨t16, run16, frame16, effect16⟩ := step pre frame15 (by decide)
    (offset := 0x64bd) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1064bd 0x48
      (by simp [RexWPrefix]) 0 (.base 3 (.d8 56)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨effect15.rip, (by
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable t15 (t15.regValue .rbx + BitVec.ofNat 64 56) 8
      rw [bx15]
      exact point_writable pre frame15 (offset := 56) (by decide) (by decide)),
      (by
        change RangeApart (t15.regValue .rbx + BitVec.ofNat 64 56) 8 0x1064bd 4
        rw [bx15]
        exact point_code pre (offset := 56) (codeOffset := 0x64bd) (by decide) (by decide))⟩
    (inProgram_of_textOffset 0x64c1 (by decide))
    (by
      simp only [movM64R64Effect_components]
      change WritesWithin [.mem (t15.regValue .rbx + BitVec.ofNat 64 56) 8, .rip] _
      rw [bx15]
      exact point_write_within pre (offset := 56) (by simp) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have store16 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 56) 8, .rip] t15 t16 := by
    have h : AgreesExcept [.mem (t15.regValue .rbx + BitVec.ofNat 64 56) 8, .rip] t15 t16 := by
      change AgreesExcept [.mem ((Operand.reg 3 : Operand 64).read t15 + BitVec.ofNat 64 56) 8, .rip] t15 t16
      simpa (config := {decide := true}) only [movM64R64Effect_components, x86_compose] using effect16.agrees
    simpa only [bx15, BitVec.add_zero] using h
  have memory16 : MemoryWriteFrame t t16 #v[registerRegion s .rdi 96] :=
    memoryWriteFrame_trans memory15
      (store16.memoryWriteFrame (point_write_within pre (by simp) (by decide)))
  have written16 : memLoad t16.external (s.regValue .rdi + BitVec.ofNat 64 56) 64 =
      memLoad t.external (stackSlot s 480) 64 := by
    have hw : memLoad t16.external (t15.regValue .rbx + BitVec.ofNat 64 56) 64 =
        (Operand.reg 0 : Operand 64).read t15 := effect16.writes
    exact (by
      rw [bx15] at hw
      rw [hw]
      exact value15)
  have bx16 : t16.regValue .rbx = s.regValue .rdi :=
    (effect16.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx15
  obtain ⟨t17, run17, frame17, effect17⟩ := step_registers pre frame16
    (offset := 0x64c1) (mov_r64_m64_effect_step 0x1064c1 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) ⟨effect16.rip, stack_readable (frameOffset := 728) pre frame16 (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x64c6 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide)
  have external17 : t17.external = t16.external :=
    effect17.agrees.external (by simp [Component.Covers])
  have memory17 : MemoryWriteFrame t t17 #v[registerRegion s .rdi 96] := by
    intro a ha
    exact (congrArg (fun mem : Ram => mem[a]?) external17).trans (memory16 a ha)
  have value17 : (Operand.reg 0 : Operand 64).read t17 =
      memLoad t.external (stackSlot s 72) 64 := by
    have hw : (Operand.reg 0 : Operand 64).read t17 =
        memLoad t16.external (stackPtr t16 + 72) 64 := effect17.writes
    rw [hw, frame16.rsp]
    exact stackSlot_read_of_point pre memory16 (by decide)
  have bx17 : t17.regValue .rbx = s.regValue .rdi :=
    (effect17.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx16
  obtain ⟨t18, run18, frame18, effect18⟩ := step_registers pre frame17
    (offset := 0x64c6) (mov_r64_m64_effect_step 0x1064c6 0x48 (by simp [RexWPrefix]) 1
      (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) ⟨effect17.rip, stack_readable (frameOffset := 728) pre frame17 (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x64cb (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 1, .rip]; decide)
  have external18 : t18.external = t17.external :=
    effect18.agrees.external (by simp [Component.Covers])
  have memory18 : MemoryWriteFrame t t18 #v[registerRegion s .rdi 96] := by
    intro a ha
    exact (congrArg (fun mem : Ram => mem[a]?) external18).trans (memory17 a ha)
  have value18 : (Operand.reg 1 : Operand 64).read t18 =
      memLoad t.external (stackSlot s 80) 64 := by
    have hw : (Operand.reg 1 : Operand 64).read t18 =
        memLoad t17.external (stackPtr t17 + 80) 64 := effect18.writes
    rw [hw, frame17.rsp]
    exact stackSlot_read_of_point pre memory17 (by decide)
  have bx18 : t18.regValue .rbx = s.regValue .rdi :=
    (effect18.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx17
  obtain ⟨t19, run19, frame19, effect19⟩ := step pre frame18 (by decide)
    (offset := 0x64cb) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1064cb 0x48
      (by simp [RexWPrefix]) 0 (.base 3 (.d8 64)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨effect18.rip, (by
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable t18 (t18.regValue .rbx + BitVec.ofNat 64 64) 8
      rw [bx18]
      exact point_writable pre frame18 (offset := 64) (by decide) (by decide)),
      (by
        change RangeApart (t18.regValue .rbx + BitVec.ofNat 64 64) 8 0x1064cb 4
        rw [bx18]
        exact point_code pre (offset := 64) (codeOffset := 0x64cb) (by decide) (by decide))⟩
    (inProgram_of_textOffset 0x64cf (by decide))
    (by
      simp only [movM64R64Effect_components]
      change WritesWithin [.mem (t18.regValue .rbx + BitVec.ofNat 64 64) 8, .rip] _
      rw [bx18]
      exact point_write_within pre (offset := 64) (by simp) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have store19 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 64) 8, .rip] t18 t19 := by
    have h : AgreesExcept [.mem (t18.regValue .rbx + BitVec.ofNat 64 64) 8, .rip] t18 t19 := by
      change AgreesExcept [.mem ((Operand.reg 3 : Operand 64).read t18 + BitVec.ofNat 64 64) 8, .rip] t18 t19
      simpa (config := {decide := true}) only [movM64R64Effect_components, x86_compose] using effect19.agrees
    simpa only [bx18, BitVec.add_zero] using h
  have memory19 : MemoryWriteFrame t t19 #v[registerRegion s .rdi 96] :=
    memoryWriteFrame_trans memory18
      (store19.memoryWriteFrame (point_write_within pre (by simp) (by decide)))
  have written19 : memLoad t19.external (s.regValue .rdi + BitVec.ofNat 64 64) 64 =
      memLoad t.external (stackSlot s 72) 64 := by
    have hw : memLoad t19.external (t18.regValue .rbx + BitVec.ofNat 64 64) 64 =
        (Operand.reg 0 : Operand 64).read t18 := effect19.writes
    exact (by
      rw [bx18] at hw
      rw [hw]
      rw [effect18.agrees.read (r := 0) (n := 64) (by simp (config := {decide := true}))]
      exact value17)
  have bx19 : t19.regValue .rbx = s.regValue .rdi :=
    (effect19.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx18
  obtain ⟨t20, run20, frame20, effect20⟩ := step pre frame19 (by decide)
    (offset := 0x64cf) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1064cf 0x48
      (by simp [RexWPrefix]) 1 (.base 3 (.d8 72)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨effect19.rip, (by
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable t19 (t19.regValue .rbx + BitVec.ofNat 64 72) 8
      rw [bx19]
      exact point_writable pre frame19 (offset := 72) (by decide) (by decide)),
      (by
        change RangeApart (t19.regValue .rbx + BitVec.ofNat 64 72) 8 0x1064cf 4
        rw [bx19]
        exact point_code pre (offset := 72) (codeOffset := 0x64cf) (by decide) (by decide))⟩
    (inProgram_of_textOffset 0x64d3 (by decide))
    (by
      simp only [movM64R64Effect_components]
      change WritesWithin [.mem (t19.regValue .rbx + BitVec.ofNat 64 72) 8, .rip] _
      rw [bx19]
      exact point_write_within pre (offset := 72) (by simp) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have store20 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 72) 8, .rip] t19 t20 := by
    have h : AgreesExcept [.mem (t19.regValue .rbx + BitVec.ofNat 64 72) 8, .rip] t19 t20 := by
      change AgreesExcept [.mem ((Operand.reg 3 : Operand 64).read t19 + BitVec.ofNat 64 72) 8, .rip] t19 t20
      simpa (config := {decide := true}) only [movM64R64Effect_components, x86_compose] using effect20.agrees
    simpa only [bx19, BitVec.add_zero] using h
  have memory20 : MemoryWriteFrame t t20 #v[registerRegion s .rdi 96] :=
    memoryWriteFrame_trans memory19
      (store20.memoryWriteFrame (point_write_within pre (by simp) (by decide)))
  have written20 : memLoad t20.external (s.regValue .rdi + BitVec.ofNat 64 72) 64 =
      memLoad t.external (stackSlot s 80) 64 := by
    have hw : memLoad t20.external (t19.regValue .rbx + BitVec.ofNat 64 72) 64 =
        (Operand.reg 1 : Operand 64).read t19 := effect20.writes
    exact (by
      rw [bx19] at hw
      rw [hw]
      rw [effect19.agrees.read (r := 1) (n := 64) (by simp (config := {decide := true}))]
      exact value18)
  have bx20 : t20.regValue .rbx = s.regValue .rdi :=
    (effect20.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx19
  obtain ⟨t21, run21, frame21, effect21⟩ := step_registers pre frame20
    (offset := 0x64d3) (mov_r64_m64_effect_step 0x1064d3 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) ⟨effect20.rip, stack_readable (frameOffset := 728) pre frame20 (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x64d8 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide)
  have external21 : t21.external = t20.external :=
    effect21.agrees.external (by simp [Component.Covers])
  have memory21 : MemoryWriteFrame t t21 #v[registerRegion s .rdi 96] := by
    intro a ha
    exact (congrArg (fun mem : Ram => mem[a]?) external21).trans (memory20 a ha)
  have value21 : (Operand.reg 0 : Operand 64).read t21 =
      memLoad t.external (stackSlot s 88) 64 := by
    have hw : (Operand.reg 0 : Operand 64).read t21 =
        memLoad t20.external (stackPtr t20 + 88) 64 := effect21.writes
    rw [hw, frame20.rsp]
    exact stackSlot_read_of_point pre memory20 (by decide)
  have bx21 : t21.regValue .rbx = s.regValue .rdi :=
    (effect21.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx20
  obtain ⟨t22, run22, frame22, effect22⟩ := step pre frame21 (by decide)
    (offset := 0x64d8) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1064d8 0x48
      (by simp [RexWPrefix]) 0 (.base 3 (.d8 80)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨effect21.rip, (by
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable t21 (t21.regValue .rbx + BitVec.ofNat 64 80) 8
      rw [bx21]
      exact point_writable pre frame21 (offset := 80) (by decide) (by decide)),
      (by
        change RangeApart (t21.regValue .rbx + BitVec.ofNat 64 80) 8 0x1064d8 4
        rw [bx21]
        exact point_code pre (offset := 80) (codeOffset := 0x64d8) (by decide) (by decide))⟩
    (inProgram_of_textOffset 0x64dc (by decide))
    (by
      simp only [movM64R64Effect_components]
      change WritesWithin [.mem (t21.regValue .rbx + BitVec.ofNat 64 80) 8, .rip] _
      rw [bx21]
      exact point_write_within pre (offset := 80) (by simp) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have store22 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 80) 8, .rip] t21 t22 := by
    have h : AgreesExcept [.mem (t21.regValue .rbx + BitVec.ofNat 64 80) 8, .rip] t21 t22 := by
      change AgreesExcept [.mem ((Operand.reg 3 : Operand 64).read t21 + BitVec.ofNat 64 80) 8, .rip] t21 t22
      simpa (config := {decide := true}) only [movM64R64Effect_components, x86_compose] using effect22.agrees
    simpa only [bx21, BitVec.add_zero] using h
  have memory22 : MemoryWriteFrame t t22 #v[registerRegion s .rdi 96] :=
    memoryWriteFrame_trans memory21
      (store22.memoryWriteFrame (point_write_within pre (by simp) (by decide)))
  have written22 : memLoad t22.external (s.regValue .rdi + BitVec.ofNat 64 80) 64 =
      memLoad t.external (stackSlot s 88) 64 := by
    have hw : memLoad t22.external (t21.regValue .rbx + BitVec.ofNat 64 80) 64 =
        (Operand.reg 0 : Operand 64).read t21 := effect22.writes
    exact (by
      rw [bx21] at hw
      rw [hw]
      exact value21)
  have bx22 : t22.regValue .rbx = s.regValue .rdi :=
    (effect22.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx21
  obtain ⟨t23, run23, frame23, effect23⟩ := step_registers pre frame22
    (offset := 0x64dc) (mov_r64_m64_effect_step 0x1064dc 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) ⟨effect22.rip, stack_readable (frameOffset := 728) pre frame22 (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x64e1 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide)
  have external23 : t23.external = t22.external :=
    effect23.agrees.external (by simp [Component.Covers])
  have memory23 : MemoryWriteFrame t t23 #v[registerRegion s .rdi 96] := by
    intro a ha
    exact (congrArg (fun mem : Ram => mem[a]?) external23).trans (memory22 a ha)
  have value23 : (Operand.reg 0 : Operand 64).read t23 =
      memLoad t.external (stackSlot s 96) 64 := by
    have hw : (Operand.reg 0 : Operand 64).read t23 =
        memLoad t22.external (stackPtr t22 + 96) 64 := effect23.writes
    rw [hw, frame22.rsp]
    exact stackSlot_read_of_point pre memory22 (by decide)
  have bx23 : t23.regValue .rbx = s.regValue .rdi :=
    (effect23.agrees.read (n := 64) (r := 3) (by simp (config := {decide := true}))).trans bx22
  obtain ⟨t24, run24, frame24, effect24⟩ := step pre frame23 (by decide)
    (offset := 0x64e1) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1064e1 0x48
      (by simp [RexWPrefix]) 0 (.base 3 (.d8 88)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨effect23.rip, (by
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable t23 (t23.regValue .rbx + BitVec.ofNat 64 88) 8
      rw [bx23]
      exact point_writable pre frame23 (offset := 88) (by decide) (by decide)),
      (by
        change RangeApart (t23.regValue .rbx + BitVec.ofNat 64 88) 8 0x1064e1 4
        rw [bx23]
        exact point_code pre (offset := 88) (codeOffset := 0x64e1) (by decide) (by decide))⟩
    (inProgram_of_textOffset 0x64e5 (by decide))
    (by
      simp only [movM64R64Effect_components]
      change WritesWithin [.mem (t23.regValue .rbx + BitVec.ofNat 64 88) 8, .rip] _
      rw [bx23]
      exact point_write_within pre (offset := 88) (by simp) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have store24 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 88) 8, .rip] t23 t24 := by
    have h : AgreesExcept [.mem (t23.regValue .rbx + BitVec.ofNat 64 88) 8, .rip] t23 t24 := by
      change AgreesExcept [.mem ((Operand.reg 3 : Operand 64).read t23 + BitVec.ofNat 64 88) 8, .rip] t23 t24
      simpa (config := {decide := true}) only [movM64R64Effect_components, x86_compose] using effect24.agrees
    simpa only [bx23, BitVec.add_zero] using h
  have memory24 : MemoryWriteFrame t t24 #v[registerRegion s .rdi 96] :=
    memoryWriteFrame_trans memory23
      (store24.memoryWriteFrame (point_write_within pre (by simp) (by decide)))
  have written24 : memLoad t24.external (s.regValue .rdi + BitVec.ofNat 64 88) 64 =
      memLoad t.external (stackSlot s 96) 64 := by
    have hw : memLoad t24.external (t23.regValue .rbx + BitVec.ofNat 64 88) 64 =
        (Operand.reg 0 : Operand 64).read t23 := effect24.writes
    exact (by
      rw [bx23] at hw
      rw [hw]
      exact value23)
  have word0 : memLoad t24.external (s.regValue .rdi + BitVec.ofNat 64 0) 64 =
      memLoad t.external (stackSlot s 232) 64 := by
    rw [read_of_store store24 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external23]
    rw [read_of_store store22 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external21]
    rw [read_of_store store20 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [read_of_store store19 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external18]
    rw [external17]
    rw [read_of_store store16 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external15]
    rw [read_of_store store14 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external13]
    rw [read_of_store store12 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [read_of_store store11 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external10]
    rw [external9]
    exact written8
  have word8 : memLoad t24.external (s.regValue .rdi + BitVec.ofNat 64 8) 64 =
      memLoad t.external (stackSlot s 240) 64 := by
    rw [read_of_store store24 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external23]
    rw [read_of_store store22 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external21]
    rw [read_of_store store20 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [read_of_store store19 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external18]
    rw [external17]
    rw [read_of_store store16 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external15]
    rw [read_of_store store14 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external13]
    rw [read_of_store store12 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [read_of_store store11 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external10]
    rw [external9]
    rw [read_of_store store8 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    exact written7
  have word16 : memLoad t24.external (s.regValue .rdi + BitVec.ofNat 64 16) 64 =
      memLoad t.external (stackSlot s 248) 64 := by
    rw [read_of_store store24 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external23]
    rw [read_of_store store22 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external21]
    rw [read_of_store store20 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [read_of_store store19 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external18]
    rw [external17]
    rw [read_of_store store16 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external15]
    rw [read_of_store store14 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external13]
    rw [read_of_store store12 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [read_of_store store11 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external10]
    rw [external9]
    rw [read_of_store store8 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [read_of_store store7 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external6]
    rw [external5]
    exact written4
  have word24 : memLoad t24.external (s.regValue .rdi + BitVec.ofNat 64 24) 64 =
      memLoad t.external (stackSlot s 256) 64 := by
    rw [read_of_store store24 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external23]
    rw [read_of_store store22 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external21]
    rw [read_of_store store20 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [read_of_store store19 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external18]
    rw [external17]
    rw [read_of_store store16 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external15]
    rw [read_of_store store14 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external13]
    rw [read_of_store store12 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [read_of_store store11 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external10]
    rw [external9]
    rw [read_of_store store8 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [read_of_store store7 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external6]
    rw [external5]
    rw [read_of_store store4 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external3]
    exact written2
  have word32 : memLoad t24.external (s.regValue .rdi + BitVec.ofNat 64 32) 64 =
      memLoad t.external (stackSlot s 456) 64 := by
    rw [read_of_store store24 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external23]
    rw [read_of_store store22 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external21]
    rw [read_of_store store20 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [read_of_store store19 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external18]
    rw [external17]
    rw [read_of_store store16 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external15]
    rw [read_of_store store14 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external13]
    rw [read_of_store store12 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    exact written11
  have word40 : memLoad t24.external (s.regValue .rdi + BitVec.ofNat 64 40) 64 =
      memLoad t.external (stackSlot s 464) 64 := by
    rw [read_of_store store24 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external23]
    rw [read_of_store store22 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external21]
    rw [read_of_store store20 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [read_of_store store19 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external18]
    rw [external17]
    rw [read_of_store store16 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external15]
    rw [read_of_store store14 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external13]
    exact written12
  have word48 : memLoad t24.external (s.regValue .rdi + BitVec.ofNat 64 48) 64 =
      memLoad t.external (stackSlot s 472) 64 := by
    rw [read_of_store store24 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external23]
    rw [read_of_store store22 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external21]
    rw [read_of_store store20 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [read_of_store store19 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external18]
    rw [external17]
    rw [read_of_store store16 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external15]
    exact written14
  have word56 : memLoad t24.external (s.regValue .rdi + BitVec.ofNat 64 56) 64 =
      memLoad t.external (stackSlot s 480) 64 := by
    rw [read_of_store store24 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external23]
    rw [read_of_store store22 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external21]
    rw [read_of_store store20 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [read_of_store store19 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external18]
    rw [external17]
    exact written16
  have word64 : memLoad t24.external (s.regValue .rdi + BitVec.ofNat 64 64) 64 =
      memLoad t.external (stackSlot s 72) 64 := by
    rw [read_of_store store24 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external23]
    rw [read_of_store store22 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external21]
    rw [read_of_store store20 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    exact written19
  have word72 : memLoad t24.external (s.regValue .rdi + BitVec.ofNat 64 72) 64 =
      memLoad t.external (stackSlot s 80) 64 := by
    rw [read_of_store store24 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external23]
    rw [read_of_store store22 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external21]
    exact written20
  have word80 : memLoad t24.external (s.regValue .rdi + BitVec.ofNat 64 80) 64 =
      memLoad t.external (stackSlot s 88) 64 := by
    rw [read_of_store store24 (RangeApart.offsets _ (by decide) (by decide) (by decide))]
    rw [external23]
    exact written22
  have word88 : memLoad t24.external (s.regValue .rdi + BitVec.ofNat 64 88) 64 =
      memLoad t.external (stackSlot s 96) 64 := by
    exact written24
  have allocated (offset : Nat) (ho : offset < 96) :
      (t24.external[s.regValue .rdi + BitVec.ofNat 64 offset]?).isSome :=
    frame24.allocated _ (Option.isSome_iff_exists.mpr (pre.outputAllocated _
      (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) ho)))
  refine ⟨t24, (((((((((((((((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16).trans run17).trans run18).trans run19).trans run20).trans run21).trans run22).trans run23).trans run24), frame24, effect24.rip, ?_, ?_, ?_⟩
  · apply Field.montgomeryAt_of_memLoad_limbs input.x.1
    · intro i hi
      exact allocated i (by omega)
    · intro j hj
      rw [← input.x.memLoad_limb j hj]
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · simpa (config := {decide := true}) only [stackSlot, BitVec.sub_eq_add_neg,
          BitVec.add_assoc, x86_compose] using word0
      · simpa (config := {decide := true}) only [stackSlot, BitVec.sub_eq_add_neg,
          BitVec.add_assoc, x86_compose] using word8
      · simpa (config := {decide := true}) only [stackSlot, BitVec.sub_eq_add_neg,
          BitVec.add_assoc, x86_compose] using word16
      · simpa (config := {decide := true}) only [stackSlot, BitVec.sub_eq_add_neg,
          BitVec.add_assoc, x86_compose] using word24
  · apply Field.montgomeryAt_of_memLoad_limbs input.y.1
    · intro i hi
      change (t24.external[s.regValue .rdi + BitVec.ofNat 64 32 + BitVec.ofNat 64 i]?).isSome
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact allocated (32 + i) (by omega)
    · intro j hj
      rw [← input.y.memLoad_limb j hj]
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · simpa (config := {decide := true}) only [stackSlot, BitVec.sub_eq_add_neg,
          BitVec.add_assoc, x86_compose] using word32
      · simpa (config := {decide := true}) only [stackSlot, BitVec.sub_eq_add_neg,
          BitVec.add_assoc, x86_compose] using word40
      · simpa (config := {decide := true}) only [stackSlot, BitVec.sub_eq_add_neg,
          BitVec.add_assoc, x86_compose] using word48
      · simpa (config := {decide := true}) only [stackSlot, BitVec.sub_eq_add_neg,
          BitVec.add_assoc, x86_compose] using word56
  · apply Field.montgomeryAt_of_memLoad_limbs input.z.1
    · intro i hi
      change (t24.external[s.regValue .rdi + BitVec.ofNat 64 64 + BitVec.ofNat 64 i]?).isSome
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact allocated (64 + i) (by omega)
    · intro j hj
      rw [← input.z.memLoad_limb j hj]
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · simpa (config := {decide := true}) only [stackSlot, BitVec.sub_eq_add_neg,
          BitVec.add_assoc, x86_compose] using word64
      · simpa (config := {decide := true}) only [stackSlot, BitVec.sub_eq_add_neg,
          BitVec.add_assoc, x86_compose] using word72
      · simpa (config := {decide := true}) only [stackSlot, BitVec.sub_eq_add_neg,
          BitVec.add_assoc, x86_compose] using word80
      · simpa (config := {decide := true}) only [stackSlot, BitVec.sub_eq_add_neg,
          BitVec.add_assoc, x86_compose] using word88

end P256.Proofs.Projective.Double
