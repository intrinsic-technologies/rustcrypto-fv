import P256.Proofs.Sec1Serialize.Tail.Selection.State
import P256.Proofs.Sec1Serialize.Tail.Selection.Memory
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mov_m8_r8_legacy_effect_step)

namespace P256.Proofs.Sec1Serialize.Selection

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame
open Conversion (Stage)

theorem load_byte [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : Nat → UInt8} {infinity : Bool} {index : Nat}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (entry : LoopState s t boundary bytes infinity index) (hi : index < 65) :
    ∃ u, Loaded s u boundary bytes infinity index := by
  have rip : t.RIP = 0x1111a0 := by simpa only [hi, ite_eq_left] using entry.rip
  have addr1 : (AddrMode.sib 4 (some 2) 0 (.d32 199)).addr t 0x1111a8 =
      stackPtr s - 113 + BitVec.ofNat 64 index := by
    change stackPtr t + (t.regValue .rdx <<< 0) + 199 = _
    rw [entry.stage.rsp, entry.counter, BitVec.shiftLeft_zero]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rw [BitVec.add_comm (BitVec.ofNat 64 index) (199 : BitVec 64), ← BitVec.add_assoc (-312 : BitVec 64)]
    rfl
  have readable (v : RamState) (stage : Stage s s v boundary) (offset : Nat)
      (ho : offset ≤ 312) (hn : index ≤ offset) :
      MemReadable v (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 index) 1 := by
    rw [sub_add_index _ hn (by omega)]
    exact readable_of_grow (stack_sub_readable pre.stack (offset := offset-index)
      (by omega) (by omega)) stage.allocated
  have code1 : CodeIn (codeRange 0x1111a0 [0x0f,0xb6,0xb4,0x14,0xc7,0,0,0]) t :=
    programText_slice (programLoaded_codeIn entry.stage.loaded) 0x111a0 _
      (by decide +kernel) (by decide +kernel)
  have read1 : MemReadable t ((AddrMode.sib 4 (some 2) 0 (.d32 199)).addr t 0x1111a8) 1 := by
    rw [addr1]
    exact readable t entry.stage 113 (by decide) (by omega)
  obtain ⟨t1, step1, ready1, effect1⟩ := movzx_r32_m8_effect_step 0x1111a0 6
    (.sib 4 (some 2) 0 (.d32 199)) (by decide) rfl rfl t entry.stage.ready code1 ⟨rip, read1⟩
  change (movzxR32M8Effect 0x1111a0 8 6 (.sib 4 (some 2) 0 (.d32 199)) t).Holds t t1 at effect1
  have stage1 := Conversion.Stage.step_registers pre entry.stage step1 ready1 effect1
    (by simp) (by simp) (inProgram_of_textOffset 0x111a8 (by decide))
  have mem1 : t1.external = t.external := effect1.agrees.external (by simp [Component.Covers])
  have byte1 : t1.regValue .rsi = (bytes index).toBitVec.setWidth 64 := by
    have e : t1.regValue .rsi = ((Operand.mem ((AddrMode.sib 4 (some 2) 0 (.d32 199)).addr t 0x1111a8) : Operand 8).read t).setWidth 64 := effect1.writes
    rw [e, addr1]
    exact congrArg (BitVec.setWidth 64) (entry.source.loadByte index hi)
  have choice1 : (Operand.reg 0 : Operand 8).read t1 = if infinity then 1 else 0 :=
    (effect1.agrees.read (n := 8) (r := 0) (by simp)).trans entry.choice
  have count1 : t1.regValue .rdx = BitVec.ofNat 64 index :=
    (effect1.agrees.read (n := 64) (r := 2) (by simp)).trans entry.counter
  have dest1 : t1.regValue .rbp = s.regValue .rdi :=
    (effect1.agrees.read (n := 64) (r := 5) (by simp)).trans entry.destination
  have addr2 : storeAddrAt 0x1111a8 (.sib 4 none 0 (.d8 11)) 4 t1 = stackPtr s - 301 := by
    change stackPtr t1 + 11 = _
    rw [stage1.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have storepre : StorePre 0x1111a8 4 (storeAddrAt 0x1111a8 (.sib 4 none 0 (.d8 11)) 4) 1 t1 := by
    refine ⟨effect1.rip, ?_, ?_⟩
    · rw [addr2]
      exact (byte_store_pre pre stage1 (offset := 301) (pc := 0x111a8) (len := 4)
        (by decide) (by decide) effect1.rip).write
    · rw [addr2]
      exact (byte_store_pre pre stage1 (offset := 301) (pc := 0x111a8) (len := 4)
        (by decide) (by decide) effect1.rip).code
  have code2 : CodeIn (codeRange 0x1111a8 [0x88,0x44,0x24,0x0b]) t1 :=
    programText_slice (programLoaded_codeIn stage1.loaded) 0x111a8 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, step2, ready2, effect2⟩ := mov_m8_r8_legacy_effect_step 0x1111a8 0
    (by decide) (.sib 4 none 0 (.d8 11)) (by decide) rfl rfl t1 ready1 code2 storepre
  change (storeEffect 0x1111a8 4 (storeAddrAt 0x1111a8 (.sib 4 none 0 (.d8 11)) 4)
    (fun v => (Operand.reg 0 : Operand 8).read v) t1).Holds t1 t2 at effect2
  have agree2 : AgreesExcept [.mem (stackPtr s - 301) 1, .rip] t1 t2 := by
    have a := effect2.agrees
    rw [storeEffect_components, addr2] at a
    exact a
  have stage2 := stage_store pre stage1 (offset := 301) (by decide) (by decide)
    step2 ready2 agree2 (effect2.rip ▸ inProgram_of_textOffset 0x111ac (by decide))
  have flag2 : (Operand.mem (stackPtr s - 301) : Operand 8).read t2 = if infinity then 1 else 0 := by
    have e := effect2.writes
    change (Operand.mem (storeAddrAt 0x1111a8 (.sib 4 none 0 (.d8 11)) 4 t1) : Operand 8).read t2 = _ at e
    rw [addr2] at e
    exact e.trans choice1
  have kept (offset len : Nat) (ho : offset ≤ 296) (hl : len ≤ offset + 8) :
      ∀ i < len, ∀ c ∈ [.mem (stackPtr s - 301) 1, Component.rip],
        ¬ c.Covers (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i) := by
    intro i hin c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, he⟩ := ha
      exact stack_apart pre (a := 301) (b := offset) (by decide) (by omega)
        (by decide) hl (.inl (by omega)) j hj i hin he.symm
    · exact ha
  have source2 : Bytes t2.external (stackPtr s - 113) 65 bytes :=
    (mem1 ▸ entry.source).of_agreesExcept agree2 (kept 113 65 (by decide) (by decide))
  have zeroSource2 : Bytes t2.external (stackPtr s - 184) 65 (fun _ => 0) :=
    (mem1 ▸ entry.zeroSource).of_agreesExcept agree2 (kept 184 65 (by decide) (by decide))
  have selected2 : Bytes t2.external (stackPtr s - 296) index (fun i => if infinity then 0 else bytes i) :=
    (mem1 ▸ entry.selected).of_agreesExcept agree2 (kept 296 index (by decide) (by omega))
  have choice2 : (Operand.reg 0 : Operand 8).read t2 = if infinity then 1 else 0 :=
    (agree2.read (by simp)).trans choice1
  have count2 : t2.regValue .rdx = BitVec.ofNat 64 index :=
    (agree2.read (n := 64) (r := 2) (by simp)).trans count1
  have dest2 : t2.regValue .rbp = s.regValue .rdi :=
    (agree2.read (n := 64) (r := 5) (by simp)).trans dest1
  have byte2 : t2.regValue .rsi = (bytes index).toBitVec.setWidth 64 :=
    (agree2.read (n := 64) (r := 6) (by simp)).trans byte1
  have addr3 : (AddrMode.sib 4 (some 2) 0 (.d32 128)).addr t2 0x1111b4 =
      stackPtr s - 184 + BitVec.ofNat 64 index := by
    change stackPtr t2 + (t2.regValue .rdx <<< 0) + 128 = _
    rw [stage2.rsp, count2, BitVec.shiftLeft_zero]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rw [BitVec.add_comm (BitVec.ofNat 64 index) (128 : BitVec 64), ← BitVec.add_assoc (-312 : BitVec 64)]
    rfl
  have read3 : MemReadable t2 ((AddrMode.sib 4 (some 2) 0 (.d32 128)).addr t2 0x1111b4) 1 := by
    rw [addr3]
    exact readable t2 stage2 184 (by decide) (by omega)
  have code3 : CodeIn (codeRange 0x1111ac [0x0f,0xb6,0xbc,0x14,0x80,0,0,0]) t2 :=
    programText_slice (programLoaded_codeIn stage2.loaded) 0x111ac _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, step3, ready3, effect3⟩ := movzx_r32_m8_effect_step 0x1111ac 7
    (.sib 4 (some 2) 0 (.d32 128)) (by decide) rfl rfl t2 ready2 code3 ⟨effect2.rip, read3⟩
  change (movzxR32M8Effect 0x1111ac 8 7 (.sib 4 (some 2) 0 (.d32 128)) t2).Holds t2 t3 at effect3
  have stage3 := Conversion.Stage.step_registers pre stage2 step3 ready3 effect3
    (by simp) (by simp) (inProgram_of_textOffset 0x111b4 (by decide))
  have zeroByte3 : t3.regValue .rdi = 0 := by
    have e : t3.regValue .rdi = ((Operand.mem ((AddrMode.sib 4 (some 2) 0 (.d32 128)).addr t2 0x1111b4) : Operand 8).read t2).setWidth 64 := effect3.writes
    rw [e, addr3]
    change (memLoad t2.external _ 8).setWidth 64 = 0
    rw [zeroSource2.loadByte index hi]
    rfl
  have mem3 : t3.external = t2.external := effect3.agrees.external (by simp [Component.Covers])
  have addr4 : (AddrMode.sib 4 none 0 (.d8 11)).addr t3 0x1111ba = stackPtr s - 301 := by
    change stackPtr t3 + 11 = _
    rw [stage3.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have read4 : MemReadable t3 ((AddrMode.sib 4 none 0 (.d8 11)).addr t3 0x1111ba) 1 := by
    rw [addr4]
    exact readable_of_grow (stack_sub_readable pre.stack (offset := 301)
      (by decide) (by decide)) stage3.allocated
  have code4 : CodeIn (codeRange 0x1111b4 [0x44,0x0f,0xb6,0x44,0x24,0x0b]) t3 :=
    programText_slice (programLoaded_codeIn stage3.loaded) 0x111b4 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨u, step4, ready4, effect4⟩ := movzx_r_m8_rex_effect_step 0x1111b4 0x44
    (by simp [RexPrefix]) 32 (.inr rfl) (by intro; rfl) 0 (.sib 4 none 0 (.d8 11)) (by decide) rfl rfl
    t3 ready3 code4 ⟨effect3.rip, read4⟩
  change (movzxR32M8Effect 0x1111b4 6 8 (.sib 4 none 0 (.d8 11)) t3).Holds t3 u at effect4
  have stage4 := Conversion.Stage.step_registers pre stage3 step4 ready4 effect4
    (by simp) (by simp) (inProgram_of_textOffset 0x111ba (by decide))
  have mem4 : u.external = t2.external :=
    (effect4.agrees.external (by simp [Component.Covers])).trans mem3
  refine ⟨u, stage4, effect4.rip, ?_, ?_, ?_, mem4 ▸ source2, mem4 ▸ zeroSource2, mem4 ▸ selected2, ?_, ?_, ?_⟩
  · exact (effect4.agrees.read (n := 8) (r := 0) (by simp)).trans
      ((effect3.agrees.read (n := 8) (r := 0) (by simp)).trans choice2)
  · exact (effect4.agrees.read (n := 64) (r := 2) (by simp)).trans
      ((effect3.agrees.read (n := 64) (r := 2) (by simp)).trans count2)
  · exact (effect4.agrees.read (n := 64) (r := 5) (by simp)).trans
      ((effect3.agrees.read (n := 64) (r := 5) (by simp)).trans dest2)
  · exact (effect4.agrees.read (n := 64) (r := 6) (by simp)).trans
      ((effect3.agrees.read (n := 64) (r := 6) (by simp)).trans byte2)
  · exact (effect4.agrees.read (n := 64) (r := 7) (by simp)).trans zeroByte3
  · have e : u.regValue .r8 = ((Operand.mem ((AddrMode.sib 4 none 0 (.d8 11)).addr t3 0x1111ba) : Operand 8).read t3).setWidth 64 := effect4.writes
    rw [e, addr4]
    change (memLoad t3.external (stackPtr s - 301) 8).setWidth 64 = if infinity then 1 else 0
    change memLoad t2.external (stackPtr s - 301) 8 = (if infinity then 1 else 0) at flag2
    rw [mem3, flag2]
    cases infinity <;> rfl

end P256.Proofs.Sec1Serialize.Selection
