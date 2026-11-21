import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps
import P256.Proofs.Sec1Serialize.Tail.Selection.State
import P256.Proofs.Common.Encoding.Serialize.Tail.Selection.Cmov
import P256.Proofs.Sec1Serialize.Tail.Selection.Memory
import P256.Proofs.Common.Encoding.Parser.ByteStore

set_option autoImplicit false

open P256.Proofs.Common.Instructions (cmovR32R32Effect cmovR32R32Value cmov_r32_r32_effect_step mov_m8_r8_effect_step testR8R8Effect test_r8_r8_effect_step)

namespace P256.Proofs.Sec1Serialize.Selection

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame
open Conversion (Stage)

theorem store_selected [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : Nat → UInt8} {infinity : Bool} {index : Nat}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (entry : Loaded s t boundary bytes infinity index) (hi : index < 65) :
    ∃ u, Stored s u boundary bytes infinity index := by
  have hc1 : CodeIn (codeRange 0x1111ba [0x45, 0x84, 0xc0]) t :=
    programText_slice (programLoaded_codeIn entry.stage.loaded) 0x111ba _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, hs1, hr1, he1⟩ := test_r8_r8_effect_step 0x1111ba 0x45 0xc0
    (by simp [RexPrefix]) (by decide) t entry.stage.ready hc1 entry.rip
  change (testR8R8Effect 0x1111ba 8 8 t).Holds t t1 at he1
  have stage1 := Conversion.Stage.step_registers pre entry.stage hs1 hr1 he1
    (by simp [Effect.components, testR8R8Effect]) (by simp [Effect.components, testR8R8Effect])
    (inProgram_of_textOffset 0x111bd (by decide))
  have hz : (StatusFlags.ofRFLAGS t1.RFLAGS).ZF = !infinity := by
    have h := he1.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS t1.RFLAGS).ZF =
      (((t.regValue .r8).setWidth 8 &&& (t.regValue .r8).setWidth 8) == 0) at h
    rw [entry.flag] at h
    cases infinity <;> simpa using h
  have hm1 : t1.external = t.external := he1.agrees.external (by simp [testR8R8Effect, Effect.components, Component.Covers])
  have hb1 : t1.regValue .rsi = (bytes index).toBitVec.setWidth 64 :=
    (he1.agrees.read (n := 64) (r := 6) (by simp [testR8R8Effect, Effect.components])).trans entry.byte
  have hz1 : t1.regValue .rdi = 0 :=
    (he1.agrees.read (n := 64) (r := 7) (by simp [testR8R8Effect, Effect.components])).trans entry.zeroByte
  have hc2 : CodeIn (codeRange 0x1111bd [0x0f, 0x45, 0xf7]) t1 :=
    programText_slice (programLoaded_codeIn stage1.loaded) 0x111bd _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, hs2, hr2, he2⟩ := cmov_r32_r32_effect_step 0x1111bd 0x45 0xf7
    (by simp) (by decide) t1 hr1 hc2 he1.rip
  change (cmovR32R32Effect 0x1111bd 5 6 7 t1).Holds t1 t2 at he2
  have stage2 := Conversion.Stage.step_registers pre stage1 hs2 hr2 he2
    (by simp [Effect.components, cmovR32R32Effect, Write.component, Operand.component])
    (by simp [cmovR32R32Effect, Effect.components, Write.component, Operand.component]) (inProgram_of_textOffset 0x111c0 (by decide))
  have hb2 : (t2.regValue .rsi).setWidth 8 =
      (if infinity then 0 else bytes index).toBitVec := by
    have hw : t2.regValue .rsi = (cmovR32R32Value 5 6 7 t1).setWidth 64 := he2.writes
    rw [hw]
    simp only [cmovR32R32Value, condHolds, hz]
    change ((if !(!infinity) then (t1.regValue .rdi).setWidth 32
      else (t1.regValue .rsi).setWidth 32).setWidth 64).setWidth 8 = _
    rw [hb1, hz1]
    cases infinity <;> simp
  have hm2 : t2.external = t.external :=
    (he2.agrees.external (by simp [cmovR32R32Effect, Effect.components, Write.component, Operand.component, Component.Covers])).trans hm1
  have ha : AgreesExcept [.reg 6, .flags, .rip] t t2 :=
    (he1.agrees.trans he2.agrees).mono
      (by simp [Effect.components, testR8R8Effect, cmovR32R32Effect,
        Write.component, Operand.component])
  have hn2 : t2.regValue .rdx = BitVec.ofNat 64 index :=
    (ha.read (n := 64) (r := 2) (by simp)).trans entry.counter
  let am : AddrMode := .sib 4 (some 2) 0 (.d8 16)
  have haddr : storeAddrAt 0x1111c0 am 5 t2 =
      stackPtr s - BitVec.ofNat 64 (296-index) := by
    change stackPtr t2 + (t2.regValue .rdx <<< 0) + 16 = _
    rw [stage2.rsp, hn2, BitVec.shiftLeft_zero]
    rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 index), ← BitVec.add_assoc]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc (stackPtr s),
      show -(312 : BitVec 64) + 16 = -(296 : BitVec 64) from by decide,
      ← BitVec.sub_eq_add_neg]
    exact sub_add_index _ (offset := 296) (i := index) (by omega) (by decide)
  have hpre : StorePre 0x1111c0 5 (storeAddrAt 0x1111c0 am 5) 1 t2 := by
    have hp := byte_store_pre pre stage2 (offset := 296-index) (pc := 0x111c0) (len := 5)
      (by omega) (by decide) he2.rip
    exact ⟨hp.rip, haddr.symm ▸ hp.write, haddr.symm ▸ hp.code⟩
  have hc3 : CodeIn (codeRange 0x1111c0 [0x40, 0x88, 0x74, 0x14, 0x10]) t2 :=
    programText_slice (programLoaded_codeIn stage2.loaded) 0x111c0 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨u, hs3, hr3, he3⟩ := mov_m8_r8_effect_step 0x1111c0 0x40
    (by simp [RexPrefix]) 6 am (by decide) (by decide) (by decide) t2 hr2 (by rw [show 0x40 :: 0x88 :: am.modrm 6 :: am.tail = [0x40, 0x88, 0x74, 0x14, 0x10] from by decide +kernel]; exact hc3) hpre
  have hagree : AgreesExcept [.mem (stackPtr s - BitVec.ofNat 64 (296-index)) 1, .rip]
      t2 u := by
    simpa only [storeEffect_components, show 3 + am.tail.length = 5 from rfl, haddr] using he3.agrees
  have stage3 := stage_store pre stage2 (by omega) (by omega) hs3 hr3 hagree (by
    rw [he3.rip]
    exact inProgram_of_textOffset 0x111c5 (by decide))
  have hb3 : (Operand.mem (stackPtr s - BitVec.ofNat 64 (296-index)) : Operand 8).read u =
      (if infinity then 0 else bytes index).toBitVec := by
    have hw : (Operand.mem (storeAddrAt 0x1111c0 am 5 t2) : Operand 8).read u =
        (t2.regValue .rsi).setWidth 8 := he3.writes
    simpa only [haddr, hb2] using hw
  have hsingle : u.external[stackPtr s - BitVec.ofNat 64 (296-index)]? =
      some (if infinity then 0 else bytes index) := by
    apply byte_of_read _ hb3
    apply hagree.grow
    have hp := hpre.write.mem 0 (by decide)
    simpa only [BitVec.add_zero, haddr] using hp
  refine ⟨u, stage3, he3.rip, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hagree.read (n := 8) (r := 0) (by simp)).trans
      ((ha.read (n := 8) (r := 0) (by simp)).trans entry.choice)
  · exact (hagree.read (n := 64) (r := 2) (by simp)).trans hn2
  · exact (hagree.read (n := 64) (r := 5) (by simp)).trans
      ((ha.read (n := 64) (r := 5) (by simp)).trans entry.destination)
  · apply Bytes.of_agreesExcept (hm2 ▸ entry.source) hagree
    intro i hi c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j,hj,he⟩ := hcov
      exact stack_apart pre (a := 296-index) (b := 113) (n := 1) (m := 65) (by omega) (by decide) (by omega) (by decide)
        (.inl (by omega)) j hj i hi he.symm
    · exact hcov
  · apply Bytes.of_agreesExcept (hm2 ▸ entry.zeroSource) hagree
    intro i hi c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, he⟩ := hcov
      exact stack_apart pre (a := 296-index) (b := 184) (n := 1) (m := 65)
        (by omega) (by decide) (by omega) (by decide)
        (.inl (by omega)) j hj i hi he.symm
    · exact hcov
  · intro i hilt
    by_cases hil : i < index
    · rw [hagree.byte]
      · rw [hm2]
        exact entry.selected i hil
      · intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · obtain ⟨j,hj,he⟩ := hcov
          have hbase := sub_add_index (stackPtr s) (offset := 296) (i := index)
            (by omega) (by decide)
          rw [← hbase] at he
          have ha : RangeApart (stackPtr s - 296 + BitVec.ofNat 64 index) 1
              (stackPtr s - 296) index := by
            simpa only [BitVec.add_zero] using RangeApart.offsets (stackPtr s - 296)
              (a := index) (b := 0) (len := 1) (count := index)
              (by omega) (by omega) (.inr (by omega))
          exact ha j hj i hil he.symm
        · exact hcov
    · have he : i = index := by omega
      rw [he]
      change u.external[stackPtr s - BitVec.ofNat 64 296 + BitVec.ofNat 64 index]? = _
      rw [sub_add_index _ (by omega) (by decide)]
      exact hsingle

end P256.Proofs.Sec1Serialize.Selection
