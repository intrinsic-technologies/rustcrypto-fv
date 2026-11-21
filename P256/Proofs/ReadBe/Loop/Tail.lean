import P256.Proofs.ReadBe.Memory
import P256.Proofs.Common.Instructions.Bswap
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (bswap64 bswap_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.ReadBe

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure LoopTailPre (s : RamState) (k : Nat) : Prop where
  rip : s.RIP = 0x119131
  size : s.regValue .rbp = 32
  offset : s.regValue .r15 = BitVec.ofNat 64 (8*k)
  readable : MemReadable s (stackPtr s + 16) 8
  writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable s (s.regValue .r14 + s.regValue .r15) 8
  avoids : ∀ a, Component.Covers (.mem (s.regValue .r14 + s.regValue .r15) 8) a → ¬ InProgram a

def loopTailComponents (s : RamState) : List Component :=
  [.reg 0, .reg 12, .reg 13, .reg 15, .flags, .rip,
   .mem (s.regValue .r14 + s.regValue .r15) 8]

structure LoopTailResult [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (k : Nat) : Prop where
  execution : Advances boundary 8 s t
  ready : ReadyToStep t
  rip : t.RIP = if k+1 < 4 then 0x11914e else 0x119170
  remaining : t.regValue .r13 = s.regValue .r13 - 8
  source : t.regValue .r12 = s.regValue .r12 - 8
  offset : t.regValue .r15 = s.regValue .r15 + 8
  word : memLoad t.external (s.regValue .r14 + s.regValue .r15) 64 =
    bswap64 (memLoad s.external (stackPtr s + 16) 64)
  agrees : AgreesExcept (loopTailComponents s) s t

theorem loop_tail [Bindings] {s : RamState} {boundary : ReturnBoundary} {k : Nat}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (pre : LoopTailPre s k)
    (hk : k < 4) (outside : ¬ InProgram boundary.rip) :
    ∃ t, LoopTailResult s t boundary k := by
  have code := programLoaded_codeIn loaded
  obtain ⟨s1, ha1, hr1, he1⟩ :=
    (mov_r64_m64_effect_step 0x119131 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid]) rfl rfl).advances ready
      (programText_slice code 0x19131 _ (by decide +kernel) (by decide +kernel))
      ⟨pre.rip, pre.readable⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x19136 (by decide +kernel)))
  have f1 : AgreesExcept [.reg 0, .rip] s s1 := he1.agrees
  have ext1 := f1.external (by simp [Component.Covers])
  have ax1 : s1.regValue .rax = memLoad s.external (stackPtr s + 16) 64 := he1.writes
  obtain ⟨s2, ha2, hr2, he2⟩ := (bswap_r64_effect_step 0x119136 0).advances hr1
    (programText_slice (code.of_external_eq ext1) 0x19136 _
      (by decide +kernel) (by decide +kernel)) he1.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x19139 (by decide +kernel)))
  have f2 : AgreesExcept [.reg 0, .rip] s1 s2 := he2.agrees
  have ext2 := (f2.external (by simp [Component.Covers])).trans ext1
  have ax2 : s2.regValue .rax = bswap64 (memLoad s.external (stackPtr s + 16) 64) :=
    he2.writes.trans (congrArg bswap64 ax1)
  have f02 := f1.trans f2
  have out2 : s2.regValue .r14 = s.regValue .r14 := f02.read (n := 64) (r := 14) (by simp)
  have off2 : s2.regValue .r15 = s.regValue .r15 := f02.read (n := 64) (r := 15) (by simp)
  have addr2 (next : BitVec 64) :
      (AddrMode.sib 14 (some 15) 0 .none).addr s2 next = s.regValue .r14 + s.regValue .r15 := by
    change s2.regValue .r14 + (s2.regValue .r15 <<< (0 : Nat)) + 0 = _
    simp only [BitVec.shiftLeft_zero, out2, off2]
    exact BitVec.add_zero _
  have apart : RangeApart (s.regValue .r14 + s.regValue .r15) 8 0x119139 4 := by
    intro i hi j hj he
    apply pre.avoids _ ⟨i, hi, rfl⟩
    rw [he]
    have hp := inProgram_of_textOffset (0x19139+j) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hp
    exact hp
  obtain ⟨s3, ha3, hr3, he3⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x119139 0x4b (by simp [RexWPrefix]) 0
      (.sib 14 (some 15) 0 .none) (by decide +kernel) rfl rfl).advances hr2
      (programText_slice (code.of_external_eq ext2) 0x19139 _
        (by decide +kernel) (by decide +kernel))
      ⟨he2.rip, by
         change P256.Proofs.Common.Instructions.CrossPageStore.Writable s2 ((AddrMode.sib 14 (some 15) 0 .none).addr s2 _) 8
         rw [addr2]
         exact pre.writable.of_external_eq ext2,
       by
         change RangeApart ((AddrMode.sib 14 (some 15) 0 .none).addr s2 _) 8 0x119139 4
         rw [addr2]
         exact apart⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x1913d (by decide +kernel)))
  have f3 : AgreesExcept [.mem (s.regValue .r14 + s.regValue .r15) 8, .rip] s2 s3 := by
    have hf := he3.agrees
    simpa only [movM64R64Effect_components, storeAddrAt, addr2] using hf
  have word3 : memLoad s3.external (s.regValue .r14 + s.regValue .r15) 64 =
      bswap64 (memLoad s.external (stackPtr s + 16) 64) := by
    have hw := he3.writes
    change memLoad s3.external ((AddrMode.sib 14 (some 15) 0 .none).addr s2 _) 64 =
      s2.regValue .rax at hw
    rw [addr2] at hw
    exact hw.trans ax2
  have loaded3 : ProgramLoaded s3 := by
    intro a b hb
    apply Eq.trans (f3.byte ?_) (by rw [ext2]; exact loaded a b hb)
    intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact pre.avoids a ha ⟨b, hb⟩
    · exact ha
  have code3 := programLoaded_codeIn loaded3
  obtain ⟨s4, ha4, hr4, he4⟩ :=
    (add_r64_imm8_effect_step 0x11913d 0x49 0xc7 8
      (by simp [RexWPrefix]) rfl rfl).advances hr3
      (programText_slice code3 0x1913d _ (by decide +kernel) (by decide +kernel)) he3.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x19141 (by decide +kernel)))
  have f4 : AgreesExcept [.reg 15, .flags, .rip] s3 s4 := he4.agrees
  have ext4 := f4.external (by simp [Component.Covers])
  have off4 : s4.regValue .r15 = s.regValue .r15 + 8 := by
    have hw : s4.regValue .r15 = s3.regValue .r15 + 8 := he4.writes
    have hp : s3.regValue .r15 = s2.regValue .r15 := f3.read (n := 64) (r := 15) (by simp)
    rw [hw, hp, off2]
  obtain ⟨s5, ha5, hr5, he5⟩ :=
    (add_r64_imm8_effect_step 0x119141 0x49 0xc5 0xf8
      (by simp [RexWPrefix]) rfl rfl).advances hr4
      (programText_slice (code3.of_external_eq ext4) 0x19141 _
        (by decide +kernel) (by decide +kernel)) he4.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x19145 (by decide +kernel)))
  have f5 : AgreesExcept [.reg 13, .flags, .rip] s4 s5 := he5.agrees
  have ext5 := (f5.external (by simp [Component.Covers])).trans ext4
  have rem5 : s5.regValue .r13 = s.regValue .r13 - 8 := by
    have hw : s5.regValue .r13 = s4.regValue .r13 + (-8 : BitVec 64) := he5.writes
    have hp : s4.regValue .r13 = s.regValue .r13 :=
      ((f02.trans f3).trans f4).read (n := 64) (r := 13) (by simp)
    rw [hw, hp, BitVec.sub_eq_add_neg]
  obtain ⟨s6, ha6, hr6, he6⟩ :=
    (add_r64_imm8_effect_step 0x119145 0x49 0xc4 0xf8
      (by simp [RexWPrefix]) rfl rfl).advances hr5
      (programText_slice (code3.of_external_eq ext5) 0x19145 _
        (by decide +kernel) (by decide +kernel)) he5.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x19149 (by decide +kernel)))
  have f6 : AgreesExcept [.reg 12, .flags, .rip] s5 s6 := he6.agrees
  have ext6 := (f6.external (by simp [Component.Covers])).trans ext5
  have src6 : s6.regValue .r12 = s.regValue .r12 - 8 := by
    have hw : s6.regValue .r12 = s5.regValue .r12 + (-8 : BitVec 64) := he6.writes
    have hp : s5.regValue .r12 = s.regValue .r12 :=
      (((f02.trans f3).trans f4).trans f5).read (n := 64) (r := 12) (by simp)
    rw [hw, hp, BitVec.sub_eq_add_neg]
  have off6 : s6.regValue .r15 = s.regValue .r15 + 8 :=
    ((f5.trans f6).read (n := 64) (r := 15) (by simp)).trans off4
  have size6 : s6.regValue .rbp = 32 :=
    (((((f02.trans f3).trans f4).trans f5).trans f6).read
      (n := 64) (r := 5) (by simp)).trans pre.size
  obtain ⟨s7, ha7, hr7, he7⟩ :=
    (cmp_r64_r64_effect_step 0x119149 0x4c 0xfd (by simp [RexWPrefix]) rfl).advances hr6
      (programText_slice (code3.of_external_eq ext6) 0x19149 _
        (by decide +kernel) (by decide +kernel)) he6.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x1914c (by decide +kernel)))
  have f7 : AgreesExcept [.flags, .rip] s6 s7 := he7.agrees
  have ext7 := (f7.external (by simp [Component.Covers])).trans ext6
  have zf7 : (StatusFlags.ofRFLAGS s7.RFLAGS).ZF = decide (k+1 = 4) := by
    have hz := he7.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s7.RFLAGS).ZF =
      ((s6.regValue .rbp - s6.regValue .r15) == 0) at hz
    rw [size6, off6, pre.offset] at hz
    have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> exact hz
  have branch : (jccEffect 0x11914c 2 4 ((0x22 : BitVec 8).signExtend 64) s7).rip =
      if k+1 < 4 then 0x11914e else 0x119170 := by
    have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [jccEffect, branchEffect, condHolds, zf7, branchTarget]
  obtain ⟨t, ha8, hr8, he8⟩ := (jcc_rel8_effect_step 0x11914c 4 0x22).advances hr7
    (programText_slice (code3.of_external_eq ext7) 0x1914c _
      (by decide +kernel) (by decide +kernel)) ⟨he7.rip, by intro _; decide +kernel⟩
    (by
      rw [branch]
      split
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x1914e (by decide +kernel))
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x19170 (by decide +kernel)))
  have f8 : AgreesExcept [.rip] s7 t := he8.agrees
  have ext8 := (f8.external (by simp [Component.Covers])).trans ext7
  refine ⟨t, ⟨ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans (ha6.trans
    (ha7.trans ha8)))))), hr8, he8.rip.trans branch, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (((f6.trans f7).trans f8).read (n := 64) (r := 13) (by simp)).trans rem5
  · exact ((f7.trans f8).read (n := 64) (r := 12) (by simp)).trans src6
  · exact ((((f5.trans f6).trans f7).trans f8).read (n := 64) (r := 15) (by simp)).trans off4
  · rw [ext8]
    exact word3
  · exact ((((((f02.trans f3).trans f4).trans f5).trans f6).trans f7).trans f8).mono
      (by simp [loopTailComponents])

end P256.Proofs.ReadBe
