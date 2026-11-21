import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Memory
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Preserve
import P256.Proofs.Common.Encoding.Parser.ByteStore
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open NextNonce (scalarFrame coreFrame)

structure Stored [Bindings] (s t u : RamState) (offset : Nat) (value : BitVec 8) : Prop where
  frame : Frame s u
  byte : u.external[frameBase s+BitVec.ofNat 64 offset]? = some (UInt8.ofBitVec value)
  agrees : AgreesExcept [.mem (frameBase s+BitVec.ofNat 64 offset) 1,.rip] t u

theorem stored [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {offset : Nat} {value : BitVec 8}
    (pre : SignPre s boundary) (frame : Frame s t) (ready : ReadyToStep u)
    (bound : offset+1 ≤ 2232)
    (agrees : AgreesExcept [.mem (frameBase s+BitVec.ofNat 64 offset) 1,.rip] t u)
    (word : memLoad u.external (frameBase s+BitVec.ofNat 64 offset) 8 = value) : Stored s t u offset value := by
  have fu : Frame s u := by
    apply after_agrees pre frame ready agrees
    · intro c hc a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl
      · exact ⟨ScalarFrame.workRegion s 4584,by simp,
          local_work pre.toCalleePre (scalarFrame frame) bound (by rwa [frame.rsp])⟩
      · exact ha.elim
    · exact agrees.read (n := 64) (r := 4) (by simp)
    · simp
    · simp
    · simp
  refine ⟨fu,?_,agrees⟩
  have b := Bytes.of_memLoad (n := 8) (local_readable pre fu (offset := offset) (len := 1) (by omega)).mem
  rw [word] at b
  simpa [storedByte,UInt8.ofBitVec] using b 0 (by decide)

theorem Stored.unchanged [Bindings] {s t u : RamState} {offset i : Nat} {value : BitVec 8}
    (result : Stored s t u offset value) (bound : offset+1 < 2^64)
    (small : i < 2^64) (apart : i < offset ∨ offset+1 ≤ i) :
    u.external[frameBase s+BitVec.ofNat 64 i]? = t.external[frameBase s+BitVec.ofNat 64 i]? := by
  apply region_byte result.agrees (offset := offset) (len := 1) ?_ bound small apart
  intro c hc a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl
  · exact ha
  · exact ha.elim

set_option maxRecDepth 2048 in
theorem zero [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d095) :
    ∃ u, Advances boundary 1 t u ∧ u.RIP = 0x10d09d ∧ Stored s t u 1392 0 := by
  obtain ⟨u,run,ready,ef⟩ :=
    (mov_m8_imm8_effect_step 0x10d095 (.sib 4 none 0 (.d32 1392)) (by decide +kernel) rfl rfl 0).advances
      (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) 0xd095 _ (by decide) (by decide +kernel))
      ⟨rip,(by change MemWritable t (stackPtr t+1392) 1; exact local_byte_writable pre.toCalleePre (scalarFrame frame) (offset := 1392) (by decide)),
        by change RangeApart (stackPtr t+1392) 1 _ 8
           rw [frame.rsp]; exact local_code_apart pre frame (offset := 1392) (len := 1) (codeOffset := 0xd095) (codeLen := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd09d (by decide)))
  have ag : AgreesExcept [.mem (frameBase s+1392) 1,.rip] t u := by
    have h := ef.agrees
    simp only [movM8Imm8Effect,storeEffect_components] at h
    change AgreesExcept [.mem (stackPtr t+1392) 1,.rip] t u at h
    rwa [frame.rsp] at h
  have word : memLoad u.external (frameBase s+1392) 8 = 0 := by
    have h := ef.writes
    change memLoad u.external (stackPtr t+1392) 8 = 0 at h
    rwa [frame.rsp] at h
  exact ⟨u,run,ef.rip,stored pre frame ready (by decide) ag word⟩

set_option maxRecDepth 2048 in
theorem flag [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d0ab) :
    ∃ u, Advances boundary 1 t u ∧ u.RIP = 0x10d0b3 ∧
      Stored s t u 600 ((t.regValue .r12).setWidth 8) := by
  obtain ⟨u,run,ready,ef⟩ :=
    (Common.Instructions.mov_m8_r8_effect_step 0x10d0ab 0x44 (by simp [RexPrefix]) 4
      (.sib 4 none 0 (.d32 600)) (by decide +kernel) rfl rfl).advances
      (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) 0xd0ab _ (by decide) (by decide +kernel))
      ⟨rip,(by change MemWritable t (stackPtr t+600) 1; exact local_byte_writable pre.toCalleePre (scalarFrame frame) (offset := 600) (by decide)),
        by change RangeApart (stackPtr t+600) 1 _ 8
           rw [frame.rsp]; exact local_code_apart pre frame (offset := 600) (len := 1) (codeOffset := 0xd0ab) (codeLen := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd0b3 (by decide)))
  have ag : AgreesExcept [.mem (frameBase s+600) 1,.rip] t u := by
    have h := ef.agrees
    simp only [storeEffect_components] at h
    change AgreesExcept [.mem (stackPtr t+600) 1,.rip] t u at h
    rwa [frame.rsp] at h
  have word : memLoad u.external (frameBase s+600) 8 = (t.regValue .r12).setWidth 8 := by
    have h := ef.writes
    change memLoad u.external (stackPtr t+600) 8 = (t.regValue .r12).setWidth 8 at h
    rwa [frame.rsp] at h
  exact ⟨u,run,ef.rip,stored pre frame ready (by decide) ag word⟩

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish
