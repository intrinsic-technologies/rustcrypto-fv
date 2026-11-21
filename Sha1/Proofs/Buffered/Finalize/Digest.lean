import Sha1.Proofs.Buffered.DigestContracts
import Sha1.Proofs.Compress.Blocks
import Sha1.Proofs.Buffered.Finalize.Digest.Pad
import Sha1.Proofs.Buffered.Finalize.Digest.Branch
import Sha1.Proofs.Buffered.Finalize.Digest.LongPath
import Sha1.Proofs.Buffered.Finalize.Digest.BlocksDigest

namespace Sha1.Proofs.Buffered.Finalize

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Buffered.Finalize.Digest
open Sha1.Proofs.Buffered.DigestPrepare.Long (CompressionCall)

theorem digest_finalize_of_compression [bindings : Bindings] (hBridge : CompressionCall)
    {initial s : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (hp : DigestPrepared initial boundary input s) :
    ∃ t, Post .digestCopy boundary input s t := by
  have hpre := hp.pre
  obtain ⟨v, hv⟩ := Digest.prepare hpre hp.statePointer
  obtain ⟨w, hw⟩ := Digest.pad hpre.stride hpre.boundaryOutside hv
  have hn : input.size % 64 < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨x, hxa, hxr, hxc, hxip, hxag⟩ :=
    padding_branch hw.ready hw.code hpre.boundaryOutside hw.rip hn hw.remaining
  have hxsp : stackPtr x = stackPtr w := hxag.read (n := 64) (r := 4) (by simp)
  have hxm : x.external = w.external := hxag.external (by simp [Component.Covers])
  have hxs := hw.storage.of_agrees hxag hxsp
  have hxdf : DirectionFlagClear x.RFLAGS := (hxag.directionFlagClear (by simp) ⟨hw.df⟩).df
  have hx15 : (Operand.reg 15 : Operand 64).read x = BitVec.ofNat 64 (input.size % 64) :=
    (hxag.read (by simp)).trans hw.position
  have hx12 : (Operand.reg 12 : Operand 64).read x = BitVec.ofNat 64 (input.size / 64) :=
    (hxag.read (by simp)).trans hw.blocks
  have hxpadded : Bytes x.external (stackPtr x + 24) 64 (fun i ↦ (firstBlock input)[i]!) := by
    rw [hxsp, hxm]
    exact hw.padded
  have hxstate : (⟨(stackPtr x).toNat, 20⟩ : MemoryRegion).HasBytes x.external
      (absorbedStateBytes input) := by
    rw [hxsp, hxm]
    exact hw.state
  have hxag' : AgreesExcept (Kind.digestCopy.changes s) s x := by
    apply (hw.agrees.trans hxag).mono
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | rfl | rfl
    · exact hc
    all_goals simp [Kind.changes]
  have hxsp' : stackPtr x = stackPtr s := hxsp.trans hw.rsp
  obtain ⟨nw, hnw⟩ := hw.advances
  have finish : ∀ (H : Vector (BitVec 32) 5) (y : RamState),
      (∃ fuel, Advances boundary fuel s y) → LastPre boundary input H y →
      stackPtr y = stackPtr s → AgreesExcept (Kind.digestCopy.changes s) s y →
      Kind.digestCopy.resultBytes input = Wrapper.Hash.Serialize.stateBytes
        (Wrapper.Absorb.compressBlocks H (lastBlock input)) →
      ∃ t, Post .digestCopy boundary input s t := by
    intro H y hadv hl hsp hag hres
    obtain ⟨z, hz⟩ := last_block hBridge hpre.stride hl
    obtain ⟨n1, h1⟩ := hadv
    obtain ⟨n2, h2⟩ := hz.advances
    have hag2 := hz.agrees
    rw [Kind.changes_eq_of_rsp _ hsp (by decide)] at hag2
    refine ⟨z, ⟨⟨n1 + n2, h1.trans h2⟩, hz.ready, hz.code, hz.rip, ?_,
      (hag.trans hag2).mono (by simp)⟩⟩
    change (⟨(stackPtr s).toNat, 20⟩ : MemoryRegion).HasBytes z.external _
    rw [hres, ← hsp]
    exact hz.state
  by_cases hshort : input.size % 64 < 56
  · have hxip' : x.RIP = 0x1001f2 := by rw [hxip]; simp [hshort]
    apply finish (absorbedHash input) x ⟨nw + 2, hnw.trans hxa⟩ _ hxsp' hxag'
      (resultBytes_short input hshort)
    refine ⟨hxs, hxr, hxc, hxip', hpre.boundaryOutside, hxdf, hx15, hx12, ?_, hxstate⟩
    intro i hi
    simp only [hshort, ite_true]
    have := hxpadded i (by omega)
    change x.external[stackPtr x + BitVec.ofNat 64 24 + BitVec.ofNat 64 i]? = _ at this
    rwa [stack_offset] at this
  · have hxip' : x.RIP = 0x10013c := by rw [hxip]; simp [hshort]
    obtain ⟨y, hyadv, hyl, hysp, hyag⟩ := long_path hBridge hpre.stride
      ⟨hxs, hxr, hxc, hxip', hpre.boundaryOutside, hxdf, by omega, hx15, hx12, hxpadded,
        hxstate⟩
    obtain ⟨ny, hny⟩ := hyadv
    rw [Kind.changes_eq_of_rsp _ hxsp' (by decide)] at hyag
    exact finish _ y ⟨nw + 2 + ny, (hnw.trans hxa).trans hny⟩ hyl (hysp.trans hxsp')
      ((hxag'.trans hyag).mono (by simp)) (resultBytes_long input (by omega))

theorem digest_finalize [bindings : Bindings] {initial s : RamState}
    {boundary : ReturnBoundary} {input : ByteArray}
    (hp : DigestPrepared initial boundary input s) :
    ∃ t, Post .digestCopy boundary input s t := by
  exact digest_finalize_of_compression
    (Sha1.Proofs.Common.CompressCall.compression_call
      Sha1.Proofs.Compress.block_correct)
    hp

end Sha1.Proofs.Buffered.Finalize
