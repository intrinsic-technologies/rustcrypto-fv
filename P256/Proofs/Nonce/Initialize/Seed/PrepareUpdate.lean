import P256.Proofs.Nonce.Initialize.Seed.Ready
import P256.Proofs.Nonce.Initialize.Seed.InitializeRun
import P256.Proofs.Nonce.Initialize.Seed.WriteFrames
import P256.Proofs.Nonce.UpdateValue.Bytes

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Nonce.Initialize.Reduce.Blocks

theorem prepare_update [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {value : Nat}
    (pre : Nonce.InitializePre initial boundary orderAddress)
    (serialized : Serialized initial s boundary orderAddress value) :
    ∃ t, UpdateReady initial t boundary orderAddress value := by
  obtain ⟨u, stage, initEffect, drbg⟩ := initialize_stage pre serialized.stage serialized.rip
  have spu : stackPtr u = stackPtr s :=
    initEffect.agrees.read (n := 64) (r := 4) (by simp [initializeEffect, Effect.components])
  have kept (offset count : Nat) (lo : 72 ≤ offset) (hi : offset + count < 2^64) :=
    copied_of_offsets initEffect.agrees (initialize_writes s) (by decide) hi (.inl lo)
  have word (offset : Nat) (lo : 72 ≤ offset) (hi : offset + 8 < 2^64) :
      memLoad u.external (stackPtr u + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr s + BitVec.ofNat 64 offset) 64 := by
    rw [spu]
    exact word_of_copied (kept offset 8 lo hi)
  have blockPre : DescriptorsPre u := by
    refine ⟨initEffect.rip, ?_, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact ScalarFrame.stack_readable pre.toCalleePre stage.toFrameState (offset := 184) (by decide) (by decide)
      · exact ScalarFrame.stack_readable pre.toCalleePre stage.toFrameState (offset := 168) (by decide) (by decide)
      · exact entropy_readable pre stage
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact Prepare.stack_writable8 pre stage (by decide) (by decide)
    · intro i hi codeOffset codeLen bound
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact (block_pre pre stage initEffect.rip).apart _ 8 (by decide) codeOffset codeLen bound
  obtain ⟨fuel, t, run, ready, _, effect⟩ := descriptors_run boundary pre.outerBoundary u
    (readyToStep stage.machine stage.bindingsSupported)
    (programText_slice (programLoaded_codeIn stage.loaded) 0x7bc7 descriptorsBytes
      (by decide +kernel) (by decide +kernel)) blockPre
  have spt : stackPtr t = stackPtr u :=
    effect.agrees.read (n := 64) (r := 4) (by simp [descriptorsEffect, Effect.components])
  have stage' : Stage initial t boundary := Reduce.Blocks.Stage.of_local pre stage run ready effect.agrees (by
    intro c hc a ha
    exact local_covers (offset := 104) (len := 48) (by decide) (descriptors_writes u c hc a ha))
    (by simp [descriptorsEffect, Effect.components]) (by simp [descriptorsEffect, Effect.components])
    (by simp [descriptorsEffect, Effect.components]) (by simp [descriptorsEffect, Effect.components])
  have copied (offset count : Nat) (hi : offset + count < 2^64)
      (apart : 152 ≤ offset ∨ offset + count ≤ 104) :=
    copied_of_offsets effect.agrees (descriptors_writes u) (by decide) hi apart
  have input : memLoad u.external (stackPtr u + 184) 64 = initial.regValue .rsi :=
    (word 184 (by decide) (by decide)).trans serialized.secret
  have length : u.regValue .rbx = 32 :=
    (initEffect.agrees.read (n := 64) (r := 3)
      (by simp [initializeEffect, Effect.components])).trans serialized.length
  have buffer : u.regValue .r12 = stackPtr u + 200 := by
    rw [spu]
    exact (initEffect.agrees.read (n := 64) (r := 12)
      (by simp [initializeEffect, Effect.components])).trans serialized.buffer
  have octets : (MemoryRegion.mk (stackPtr u + 200).toNat 32).HasBytes u.external
      (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n value) := by
    rw [spu]
    exact hasBytes_copy serialized.octets (kept 200 32 (by decide) (by decide))
  obtain ⟨rax, destination, descriptors, count, secretPointer, secretLength,
    reducedPointer, reducedLength, entropyPointer, entropyLength⟩ := effect.writes
  change t.regValue .rdi = (Operand.reg 4 : Operand 64).read u + 8 at destination
  change t.regValue .rsi = (Operand.reg 4 : Operand 64).read u + 104 at descriptors
  change t.regValue .rdx = 3 at count
  change memLoad t.external ((Operand.reg 4 : Operand 64).read u + 104) 64 =
    memLoad u.external ((Operand.reg 4 : Operand 64).read u + 184) 64 at secretPointer
  change memLoad t.external ((Operand.reg 4 : Operand 64).read u + 112) 64 =
    (Operand.reg 3 : Operand 64).read u at secretLength
  change memLoad t.external ((Operand.reg 4 : Operand 64).read u + 120) 64 =
    (Operand.reg 12 : Operand 64).read u at reducedPointer
  change memLoad t.external ((Operand.reg 4 : Operand 64).read u + 128) 64 =
    (Operand.reg 3 : Operand 64).read u at reducedLength
  change memLoad t.external ((Operand.reg 4 : Operand 64).read u + 144) 64 =
    memLoad u.external ((Operand.reg 4 : Operand 64).read u + 288) 64 at entropyLength
  have readsp : (Operand.reg 4 : Operand 64).read u = stackPtr u := Operand.read_reg64 u 4
  have read14 : (Operand.reg 3 : Operand 64).read u = u.regValue .rbx := Operand.read_reg64 u 3
  have read12 : (Operand.reg 12 : Operand 64).read u = u.regValue .r12 := Operand.read_reg64 u 12
  simp only [readsp, read14, read12] at destination descriptors secretPointer secretLength reducedPointer reducedLength entropyLength
  refine ⟨t, stage', effect.rip, ?_, ?_, ?_, ?_, count, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (effect.agrees.read (n := 64) (r := 15)
      (by simp [descriptorsEffect, Effect.components])).trans
      ((initEffect.agrees.read (n := 64) (r := 15)
        (by simp [initializeEffect, Effect.components])).trans serialized.order)
  · rw [spt]
    exact (word_of_copied (copied 192 8 (by decide) (.inl (by decide)))).trans
      ((word 192 (by decide) (by decide)).trans serialized.output)
  · simpa only [spt] using destination
  · simpa only [spt] using descriptors
  · simpa only [spt] using secretPointer.trans input
  · simpa only [spt] using secretLength.trans length
  · simpa only [spt] using reducedPointer.trans buffer
  · simpa only [spt] using reducedLength.trans length
  · simpa only [spt] using entropyLength.trans (entropy_length pre stage)
  · rw [spt]
    exact hasBytes_copy octets (copied 200 32 (by decide) (.inl (by decide)))
  · rw [spt]
    apply DrbgAt.copy (a := stackPtr u + 8) (by simpa only [spu] using drbg)
    exact copied 8 64 (by decide) (.inr (by decide))

  · exact (effect.agrees.read (n := 64) (r := 14)
      (by simp [descriptorsEffect, Effect.components])).trans
      ((initEffect.agrees.read (n := 64) (r := 14)
        (by simp [initializeEffect, Effect.components])).trans serialized.outputPointer)

end P256.Proofs.Nonce.Initialize.Seed
