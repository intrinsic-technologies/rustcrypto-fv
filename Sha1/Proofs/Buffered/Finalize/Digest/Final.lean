import Sha1.Proofs.Buffered.Finalize.Digest.CompressSite
import Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy.Composition
import Sha1.Proofs.Buffered.Finalize.Digest.LengthBytes

namespace Sha1.Proofs.Buffered.Finalize.Digest

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine
open Sha1.Proofs.Buffered.DigestPrepare.Long (CompressionCall)

theorem hasBytes_of_bytes_size {m : Ram} {base : BitVec 64} {n : Nat} {bytes : ByteArray}
    (h : Bytes m base n (fun i ↦ bytes[i]!)) (hn : bytes.size = n) :
    (⟨base.toNat, n⟩ : MemoryRegion).HasBytes m bytes := by
  subst hn
  exact hasBytes_of_bytes h

theorem stack_offset (base : BitVec 64) (a j : Nat) :
    base + BitVec.ofNat 64 a + BitVec.ofNat 64 j = base + BitVec.ofNat 64 (a + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

structure LastPre [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (H : Vector (BitVec 32) 5) (y : RamState) : Prop extends Storage .digestCopy y where
  ready : ReadyToStep y
  code : CodeIn Extracted.programImage y
  rip : y.RIP = 0x1001f2
  boundaryOutside : ¬ InProgram boundary.rip
  df : DirectionFlagClear y.RFLAGS
  position : (Operand.reg 15 : Operand 64).read y = BitVec.ofNat 64 (message.size % 64)
  blocks : (Operand.reg 12 : Operand 64).read y = BitVec.ofNat 64 (message.size / 64)
  pre56 : ∀ i < 56, y.external[stackPtr y + BitVec.ofNat 64 (24 + i)]? =
    some (if message.size % 64 < 56 then (firstBlock message)[i]! else 0)
  state : (⟨(stackPtr y).toNat, 20⟩ : MemoryRegion).HasBytes y.external
    (Wrapper.Hash.Serialize.stateBytes H)

structure LastPost [Bindings] (boundary : ReturnBoundary) (H : Vector (BitVec 32) 5)
    (block : ByteArray) (y z : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel y z
  ready : ReadyToStep z
  code : CodeIn Extracted.programImage z
  rip : z.RIP = 0x100277
  rsp : stackPtr z = stackPtr y
  state : (⟨(stackPtr y).toNat, 20⟩ : MemoryRegion).HasBytes z.external
    (Wrapper.Hash.Serialize.stateBytes (Wrapper.Absorb.compressBlocks H block))
  agrees : AgreesExcept (Kind.digestCopy.changes y) y z

theorem last_block [bindings : Bindings] (hBridge : CompressionCall)
    (hStride : UnitStringStride bindings) {boundary : ReturnBoundary} {message : ByteArray}
    {H : Vector (BitVec 32) 5} {y : RamState} (h : LastPre boundary message H y) :
    ∃ z, LastPost boundary H (lastBlock message) y z := by
  obtain ⟨y', hy'⟩ := BlockCopy.final_copy h.ready h.code h.boundaryOutside ⟨h.toStorage, h.rip⟩
  have hsp := hy'.rsp
  have hs' := h.toStorage.of_agrees hy'.agrees hsp
  have hbytes : Bytes y'.external (stackPtr y' + BitVec.ofNat 64 120) 64
      (fun i ↦ (lastBlock message)[i]!) := by
    apply lastBlock_bytes
    · intro i hi
      rw [hsp, stack_offset, hy'.copy i hi]
      exact h.pre56 i hi
    · intro k hk
      rw [hsp, stack_offset, show 120 + (56 + k) = 176 + k by omega, hy'.length k hk,
        lengthValue_bytes h.position h.blocks k hk]
  have hblock := hasBytes_of_bytes_size hbytes (size_lastBlock message)
  have hstate' : (⟨(stackPtr y').toNat, 20⟩ : MemoryRegion).HasBytes y'.external
      (Wrapper.Hash.Serialize.stateBytes H) := by
    apply hasBytes_resize' _ (Wrapper.Hash.Serialize.stateBytes_size H)
    apply hasBytes_of_copy (src := stackPtr y) (dst := stackPtr y') _
      (hasBytes_resize h.state (Wrapper.Hash.Serialize.stateBytes_size H).symm)
    intro i hi
    rw [Wrapper.Hash.Serialize.stateBytes_size] at hi
    rw [hsp]
    apply hy'.agrees.byte
    intro c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    · exact covers_apart (base := stackPtr y) (a := 80) (len := 8) (b := i) (count := 1) (i := 0)
        (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) (.inr (by omega)) hcov
    · exact covers_apart (base := stackPtr y) (a := 120) (len := 64) (b := i) (count := 1) (i := 0)
        (by rw [BitVec.add_zero]) (by decide) (by omega) (by omega) (.inr (by omega)) hcov
  have hdf' : DirectionFlagClear y'.RFLAGS :=
    (hy'.agrees.directionFlagClear (by simp) ⟨h.df⟩).df
  have hsite : SitePre boundary 0x100272 H (lastBlock message) y' := by
    refine ⟨hs', hy'.ready, hy'.code, hy'.rip, h.boundaryOutside, hdf', ?_, ?_, hy'.rdx,
      size_lastBlock message, hblock, hstate'⟩
    · exact hy'.rdi.trans hsp.symm
    · rw [hsp]
      exact hy'.rsi
  obtain ⟨z, hz⟩ := compress_site (disp := 0x2269) (off := 0x272) hBridge hStride hsite rfl
    (by decide +kernel) (by decide)
    (Sha1.Proofs.Compress.Machine.program_text_slice hy'.code 0x272 5 (by decide +kernel))
    (by decide) (text_address_ne_return h.boundaryOutside 0x277 (by decide +kernel))
  have hag1 : AgreesExcept (Kind.digestCopy.changes y) y y' := by
    apply agrees_changes hy'.agrees
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters]
    · intro x c hc hcov
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcov.elim
      · exact h.toStorage.localWithin (offset := 80) (len := 8) (by decide) hcov
      · exact h.toStorage.localWithin (offset := 120) (len := 64) (by decide) hcov
  have hag2 := hz.agrees
  rw [Kind.changes_eq_of_rsp _ hsp (by decide)] at hag2
  obtain ⟨n1, h1⟩ := hy'.advances
  obtain ⟨n2, h2⟩ := hz.advances
  refine ⟨z, ⟨⟨n1 + n2, h1.trans h2⟩, hz.ready, hz.code, hz.rip.trans (by decide),
    hz.rsp.trans hsp, ?_, (hag1.trans hag2).mono (by simp)⟩⟩
  have := hz.state
  rwa [hsp] at this

end Sha1.Proofs.Buffered.Finalize.Digest
