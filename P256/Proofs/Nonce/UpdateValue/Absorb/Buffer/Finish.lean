import P256.Proofs.Nonce.UpdateValue.Absorb.Buffer.Memory
import P256.Proofs.Nonce.UpdateValue.Absorb.OrByte
import P256.Proofs.Common.Encoding.Parser.ByteStore
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Absorb.Buffer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {state : State}

theorem finish (pre : UpdateValuePre initial boundary state) (frame : FrameState initial s)
    (rip : s.RIP = 0x10ab28) (position : s.regValue .r15 = 0) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ t.RIP = 0x10ab96 ∧
      AgreesExcept [.reg 15, .flags, .mem (stackPtr s + 231) 1, .rip] s t ∧
      t.external[stackPtr s + 231]? = some 32 := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (OrByte.or_r8_imm8_effect_step 0x10ab28 0x41 0xcf 32
      (by simp [RexPrefix]) rfl rfl).advances
      (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) 0xab28
        [0x41,0x80,0xcf,0x20] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xab2c (by decide)))
  have agreesA : AgreesExcept [.reg 15, .flags, .rip] s a := effectA.agrees
  have memoryA := agreesA.external (by simp [Component.Covers])
  have rspA : stackPtr a = stackPtr s := agreesA.read (n := 64) (r := 4) (by simp)
  have valueA : a.regValue .r15 = 32 := by
    have h := effectA.writes
    change a.regValue .r15 = mergeGPR 8 ((s.regValue .r15).setWidth 8 ||| 32) (s.regValue .r15) at h
    rw [position] at h
    exact h
  have writable := ScalarFrame.stack_writable pre.callee frame (by decide) (offset := 231) (len := 1)
    (by decide) (by decide)
  have writableOne : MemWritable s (stackPtr s + 231) 1 :=
    ⟨writable.low, writable.mem, writable.tables⟩
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (P256.Proofs.Common.Instructions.mov_m8_r8_effect_step 0x10ab2c 0x44
      (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d32 231))
      (by decide +kernel) rfl rfl).advances readyA
      (programText_slice (agreesA.codeIn (by simp [Component.Covers])
        (programLoaded_codeIn frame.loaded)) 0xab2c
        [0x44,0x88,0xbc,0x24,0xe7,0,0,0] (by decide) (by decide +kernel))
      ⟨effectA.rip, by
        change MemWritable a (stackPtr a + 231) 1
        rw [rspA]
        exact writableOne.of_external_eq memoryA, by
        change RangeApart (stackPtr a + 231) 1 0x10ab2c 8
        rw [rspA]
        exact ScalarFrame.stack_code pre.callee frame (by decide) (by decide)
          (codeOffset := 0xab2c) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xab34 (by decide)))
  have agreesB : AgreesExcept [.mem (stackPtr s + 231) 1, .rip] a b := by
    rw [← rspA]
    refine (congrArg (fun cs => AgreesExcept cs a b) ?_).mp effectB.agrees
    simp only [storeEffect_components]
    congr 2
  have codeB : CodeIn (codeRange 0x10ab34 [0xeb,0x60]) b := by
    apply CodeIn.of_agreesExcept agreesB ?_
      (programText_slice (agreesA.codeIn (by simp [Component.Covers])
        (programLoaded_codeIn frame.loaded)) 0xab34
        [0xeb,0x60] (by decide) (by decide +kernel))
    intro x hx c hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, eq⟩ := covered
      obtain ⟨j, hj, eqj⟩ := exists_of_mem_codeRange hx
      exact ScalarFrame.stack_code pre.callee frame (by decide) (offset := 231) (len := 1)
        (by decide) (codeOffset := 0xab34) (by decide) i hi j hj (eq.symm.trans eqj)
    · exact covered
  obtain ⟨t, runT, readyT, effectT⟩ :=
    (jmp_rel8_effect_step 0x10ab34 0x60 (by decide)).advances readyB codeB effectB.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xab96 (by decide)))
  have agreesT : AgreesExcept [.rip] b t := effectT.agrees
  have valueB : memLoad b.external (stackPtr s + 231) 8 = 32 := by
    have h := effectB.writes
    change memLoad b.external (stackPtr a + 231) 8 = (a.regValue .r15).setWidth 8 at h
    rw [rspA, valueA] at h
    exact h
  have readableB := readable_of_grow
    (writableOne.readable.of_external_eq memoryA) agreesB.grow
  have bytesB := Bytes.of_memLoad (n := 8) readableB.mem
  rw [valueB] at bytesB
  have byteB : b.external[stackPtr s + 231]? = some 32 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      show storedByte (32#8) 0 = (32 : UInt8) from rfl] using bytesB 0 (by decide)
  refine ⟨t, runA.trans (runB.trans runT), readyT, effectT.rip, ?_, ?_⟩
  · exact (agreesA.trans (agreesB.trans agreesT)).mono (by simp)
  · rw [agreesT.external (by simp [Component.Covers])]
    exact byteB

end P256.Proofs.Nonce.UpdateValue.Absorb.Buffer
