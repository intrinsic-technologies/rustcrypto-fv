import P256.Proofs.Sec1.Decode.Frame
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import P256.Proofs.Common.Instructions.CompareByteMemory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Result

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.CompareByteMemory

theorem branch [Bindings] {original s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : DecodePre original boundary bytes) (state : Frame original s)
    (value : BitVec 8) (rip : s.RIP = 0x10e66a)
    (ax : s.regValue .rax = value.setWidth 64) :
    ∃ t, Advances boundary 4 s t ∧ Frame original t ∧
      t.RIP = (if value = 0 then 0x10e6a8 else 0x10e676) ∧
      AgreesExcept [.reg 0, .flags, .mem (stackPtr original - 312) 1, .rip] s t := by
  have size : 2 + (AddrMode.sib 4 none 0 .none).tail.length = 3 := rfl
  have address (v : RamState) :
      storeAddrAt 0x10e66a (.sib 4 none 0 .none) 3 v = stackPtr v + 0 := rfl
  have sp : stackPtr s + 0 = stackPtr original - 312 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  have writable : MemWritable s (stackPtr original - 312) 1 :=
    writable_of_grow (stack_sub_writable pre.stack
      (fun a ha hr ↦ pre.avoids _ (by simp) a ha (.inr hr))
      (offset := 312) (by decide) (by decide) (by decide) (by omega)) state.allocated
  have apart : RangeApart (stackPtr original - 312) 1 0x10e66a 3 := by
    intro i hi j hj he
    apply pre.avoids (Stack.region original 3680) (by simp)
      (stackPtr original - 312 + BitVec.ofNat 64 i)
      (ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) ⟨i, hi, rfl⟩)
    apply Or.inl
    rw [he]
    have h := inProgram_of_textOffset (0xe66a + j) (by omega)
    change InProgram (0x100000#64 + BitVec.ofNat 64 (0xe66a + j)) at h
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
    exact h
  obtain ⟨a, aa, ra, ea⟩ := (mov_m8_r8_legacy_effect_step 0x10e66a 0 (by decide)
    (.sib 4 none 0 .none) (by decide) rfl rfl).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xe66a _
      (by decide) (by decide +kernel)) ⟨rip, by simpa only [size, address, sp] using writable,
        by simpa only [size, address, sp] using apart⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe66d (by decide)))
  have ga : AgreesExcept [.mem (stackPtr original - 312) 1, .rip] s a := by
    simpa only [storeEffect_components, size, address, sp, Nat.reduceDiv] using ea.agrees
  have writes : WritesWithin [.mem (stackPtr original - 312) 1, .rip]
      #v[registerRegion original .rdi 80, ScalarFrame.Work.region original 3680 32] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨ScalarFrame.Work.region original 3680 32, by simp, ScalarFrame.Work.contains pre.toCalleePre (by decide) (by decide) ha⟩
    · exact ha.elim
  have sa := state.after_effect pre ra ga writes (by simp)
  have byte : memLoad a.external (stackPtr original - 312) 8 = value := by
    have h : memLoad a.external (storeAddrAt 0x10e66a (.sib 4 none 0 .none) 3 s) 8 =
      (s.regValue .rax).setWidth 8 := ea.writes
    simpa only [address, sp, ax, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_eq] using h
  obtain ⟨b, ab, rb, eb⟩ := (mov_r64_r64_effect_step 0x10e66d 0x48 0xe0 (by simp [RexWPrefix]) rfl).advances ra
    (programText_slice (programLoaded_codeIn sa.loaded) 0xe66d _
      (by decide) (by decide +kernel)) ea.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe670 (by decide)))
  have gb : AgreesExcept [.reg 0, .rip] a b := eb.agrees
  have sb := sa.after_registers pre rb gb (by simp [Component.Covers]) (by simp)
  have mb := gb.external (by simp [Component.Covers])
  have spb : stackPtr b + 0 = stackPtr original - 312 :=
    ScalarFrame.scalar_stack_address sb.rsp (by decide) (by decide)
  obtain ⟨c, ac, rc, ec⟩ := (CompareByteMemory.cmp_m8_imm8_effect_step 0x10e670
    (.sib 4 none 0 .none) (by decide) rfl rfl 0).advances rb
    (programText_slice (programLoaded_codeIn sb.loaded) 0xe670 _
      (by decide) (by decide +kernel)) ⟨eb.rip, by
        change MemReadable b (stackPtr b + 0) 1
        rw [spb]
        exact readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) sb.allocated⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe674 (by decide)))
  have gc : AgreesExcept [.flags, .rip] b c := ec.agrees
  have sc := sb.after_registers pre rc gc (by simp [Component.Covers]) (by simp)
  have zf : (StatusFlags.ofRFLAGS c.RFLAGS).ZF = decide (value = 0) := by
    have h := CompareByteMemory.cmpM8Imm8Effect_ZF ec
    change (StatusFlags.ofRFLAGS c.RFLAGS).ZF =
      decide (memLoad b.external (stackPtr b + 0) 8 = 0) at h
    rw [h, spb, mb, byte]
  have flag : condHolds 4 (StatusFlags.ofRFLAGS c.RFLAGS) = decide (value = 0) := zf
  have next : (jccEffect 0x10e674 2 4 ((0x32 : BitVec 8).signExtend 64) c).rip =
      if value = 0 then 0x10e6a8 else 0x10e676 := by
    simp only [jccEffect, flag, branchEffect, decide_eq_true_eq]
    rfl
  obtain ⟨t, runT, rt, et⟩ := (jcc_rel8_effect_step 0x10e674 4 0x32).advances rc
    (programText_slice (programLoaded_codeIn sc.loaded) 0xe674 _
      (by decide) (by decide +kernel)) ⟨ec.rip, by intro; decide⟩
    (by rw [next]; split
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe6a8 (by decide))
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe676 (by decide)))
  have gt : AgreesExcept [.rip] c t := et.agrees
  exact ⟨t, ((aa.trans ab).trans ac).trans runT,
    sc.after_registers pre rt gt (by simp [Component.Covers]) (by simp), et.rip.trans next,
    (((ga.trans gb).trans gc).trans gt).mono (by simp)⟩

end P256.Proofs.Sec1.Decode.Result
