import Sha2.Proofs.Common.Encoding.Serialize.Push
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple

set_option autoImplicit false

open Sha2.Proofs.Common.Machine (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice supportedMachine_readyToStep)

namespace Sha2.Proofs.Common.Encoding.Serialize

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def saveMemory (s : RamState) : Ram :=
  memStore (memStore (memStore (memStore (memStore (memStore s.external
    (stackPtr s - 8) (s.regValue .rbp))
    (stackPtr s - 16) (s.regValue .r15))
    (stackPtr s - 24) (s.regValue .r14))
    (stackPtr s - 32) (s.regValue .r13))
    (stackPtr s - 40) (s.regValue .r12))
    (stackPtr s - 48) (s.regValue .rbx)

def saveFrame (s : RamState) : List Component :=
  [.reg 4, .rip, .mem (stackPtr s - 8) 8, .mem (stackPtr s - 16) 8,
    .mem (stackPtr s - 24) 8, .mem (stackPtr s - 32) 8,
    .mem (stackPtr s - 40) 8, .mem (stackPtr s - 48) 8]

structure SaveCode (offset : Nat) : Prop where
  bounded : offset + 10 < 71757
  rbp : Extracted.textBytes.toListFrom offset 1 = [0x55]
  r15 : Extracted.textBytes.toListFrom (offset + 1) 2 = [0x41, 0x57]
  r14 : Extracted.textBytes.toListFrom (offset + 3) 2 = [0x41, 0x56]
  r13 : Extracted.textBytes.toListFrom (offset + 5) 2 = [0x41, 0x55]
  r12 : Extracted.textBytes.toListFrom (offset + 7) 2 = [0x41, 0x54]
  rbx : Extracted.textBytes.toListFrom (offset + 9) 1 = [0x53]

structure PushSteps [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop where
  run : ∀ {t : RamState}, ReadyToStep t → ProgramLoaded t →
    (∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) →
    ∀ (src : BitVec 4) (offset codeOffset : Nat),
      stackPtr t = stackPtr s - BitVec.ofNat 64 offset →
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset →
      offset + 8 ≤ 48 → (offset + 8) % 8 = 0 →
      codeOffset + (encodePushR64 src).length < 71757 →
      Extracted.textBytes.toListFrom codeOffset (encodePushR64 src).length = encodePushR64 src →
      ∃ u, Advances boundary 1 t u ∧ ReadyToStep u ∧ ProgramLoaded u ∧
        u.RIP = Extracted.textAddress +
          BitVec.ofNat 64 (codeOffset + (encodePushR64 src).length) ∧
        stackPtr u = stackPtr s - BitVec.ofNat 64 (offset + 8) ∧
        AgreesExcept [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 (offset + 8)) 8, .rip] t u ∧
        u.external = memStore t.external (stackPtr s - BitVec.ofNat 64 (offset + 8))
          ((Operand.reg (src.setWidth 5) : Operand 64).read t)

theorem save_registers_of_push [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {codeOffset : Nat} (push : PushSteps s boundary)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (code : SaveCode codeOffset) :
    ∃ t, Advances boundary 6 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 10) ∧ stackPtr t = stackPtr s - 48 ∧
      t.external = saveMemory s ∧ AgreesExcept (saveFrame s) s t := by
  obtain ⟨s1, ha1, hr1, hl1, hip1, hsp1, hfstep1, hm1⟩ :=
    push.run ready loaded (fun _ h => h) 5 0 codeOffset
      (by simp only [BitVec.sub_zero]) rip (by omega) (by decide +kernel)
      (by have h := code.bounded; change codeOffset + 1 < 71757; omega) code.rbp
  have hf1 := hfstep1
  obtain ⟨s2, ha2, hr2, hl2, hip2, hsp2, hfstep2, hm2⟩ :=
    push.run hr1 hl1 hf1.grow 15 8 (codeOffset + 1)
      hsp1 hip1 (by omega) (by decide +kernel)
      (by have h := code.bounded; change codeOffset + 3 < 71757; omega) code.r15
  have hf2 := hf1.trans hfstep2
  obtain ⟨s3, ha3, hr3, hl3, hip3, hsp3, hfstep3, hm3⟩ :=
    push.run hr2 hl2 hf2.grow 14 16 (codeOffset + 3)
      hsp2 hip2 (by omega) (by decide +kernel)
      (by have h := code.bounded; change codeOffset + 5 < 71757; omega) code.r14
  have hf3 := hf2.trans hfstep3
  obtain ⟨s4, ha4, hr4, hl4, hip4, hsp4, hfstep4, hm4⟩ :=
    push.run hr3 hl3 hf3.grow 13 24 (codeOffset + 5)
      hsp3 hip3 (by omega) (by decide +kernel)
      (by have h := code.bounded; change codeOffset + 7 < 71757; omega) code.r13
  have hf4 := hf3.trans hfstep4
  obtain ⟨s5, ha5, hr5, hl5, hip5, hsp5, hfstep5, hm5⟩ :=
    push.run hr4 hl4 hf4.grow 12 32 (codeOffset + 7)
      hsp4 hip4 (by omega) (by decide +kernel)
      (by have h := code.bounded; change codeOffset + 9 < 71757; omega) code.r12
  have hf5 := hf4.trans hfstep5
  obtain ⟨s6, ha6, hr6, hl6, hip6, hsp6, hfstep6, hm6⟩ :=
    push.run hr5 hl5 hf5.grow 3 40 (codeOffset + 9)
      hsp5 hip5 (by omega) (by decide +kernel)
      (by have h := code.bounded; change codeOffset + 10 < 71757; omega) code.rbx
  have hf6 := hf5.trans hfstep6
  refine ⟨s6, (((((ha1.trans ha2).trans ha3).trans ha4).trans ha5).trans ha6),
    hr6, hl6, hip6, hsp6, ?_, ?_⟩
  · have hv1 : (Operand.reg 5 : Operand 64).read s = s.regValue .rbp := rfl
    have hv2 : (Operand.reg 15 : Operand 64).read s1 = s.regValue .r15 := by
      exact hf1.read (by simp)
    have hv3 : (Operand.reg 14 : Operand 64).read s2 = s.regValue .r14 := by
      exact hf2.read (by simp)
    have hv4 : (Operand.reg 13 : Operand 64).read s3 = s.regValue .r13 := by
      exact hf3.read (by simp)
    have hv5 : (Operand.reg 12 : Operand 64).read s4 = s.regValue .r12 := by
      exact hf4.read (by simp)
    have hv6 : (Operand.reg 3 : Operand 64).read s5 = s.regValue .rbx := by
      exact hf5.read (by simp)
    rw [hm6, hm5, hm4, hm3, hm2, hm1]
    simp only [show BitVec.setWidth 5 (5 : BitVec 4) = (5 : BitVec 5) from rfl,
      show BitVec.setWidth 5 (15 : BitVec 4) = (15 : BitVec 5) from rfl,
      show BitVec.setWidth 5 (14 : BitVec 4) = (14 : BitVec 5) from rfl,
      show BitVec.setWidth 5 (13 : BitVec 4) = (13 : BitVec 5) from rfl,
      show BitVec.setWidth 5 (12 : BitVec 4) = (12 : BitVec 5) from rfl,
      show BitVec.setWidth 5 (3 : BitVec 4) = (3 : BitVec 5) from rfl,
      hv1, hv2, hv3, hv4, hv5, hv6]
    rfl
  · apply hf6.mono
    simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with (((((h | h) | h) | h) | h) | h) <;>
      rcases h with rfl | rfl | rfl <;> simp

theorem save_registers [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes reserve codeOffset : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    (hreserve : 48 ≤ reserve)
    (hentry : entry = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (code : SaveCode codeOffset) :
    ∃ t, Advances boundary 6 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 10) ∧ stackPtr t = stackPtr s - 48 ∧
      t.external = saveMemory s ∧ AgreesExcept (saveFrame s) s t := by
  apply save_registers_of_push (ready := supportedMachine_readyToStep pre.machine)
    (loaded := pre.loaded) (rip := pre.rip.trans hentry) (code := code)
  constructor
  intro t ready loaded grow src offset codeOffset sp ip bound align size bytes
  exact push_exists pre ready loaded grow src offset codeOffset sp ip (by omega) align size bytes

theorem saveMemory_saved (s : RamState) (entry : Syntax.Reg × Nat)
    (hentry : entry ∈ savedRegisters) :
    memLoad (saveMemory s) (stackPtr s - BitVec.ofNat 64 entry.2) 64 =
      s.regValue entry.1 := by
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hentry
  rcases hentry with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [saveMemory, BitVec.sub_eq_add_neg]
    repeat first
      | rw [memLoad_memStore_apart _ _ _ _ _ 64
          (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
      | exact memLoad_memStore _ _ (by decide) (by decide) _

end Sha2.Proofs.Common.Encoding.Serialize
