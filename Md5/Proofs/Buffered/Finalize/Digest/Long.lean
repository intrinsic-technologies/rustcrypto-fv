import Md5.Proofs.Buffered.Finalize.Digest.Long.Finish
import Md5.Proofs.Buffered.Finalize.Digest.Long.Copy

namespace Md5.Proofs.Buffered.Finalize.Digest.Long

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_agrees {s t : RamState} (h : (Copy.effect s).Holds s t) :
    AgreesExcept (changes s) s t := by
  apply (Copy.effect_agrees h).widen
  · intro c hc hm
    simp only [Copy.changes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [changes, Component.isMem]
  · intro a c hc ha
    simp only [Copy.changes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    refine ⟨.mem (stackPtr s + 8) 168, by simp [changes], ?_⟩
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨104 + i, by omega, ?_⟩
    simp only [BitVec.ofNat_add, ← BitVec.add_assoc]
    congr 1
    rw [BitVec.add_assoc]
    rfl

theorem run [Bindings] {boundary : ReturnBoundary} {message : ByteArray} {s : RamState}
    (hp : Pre boundary message s) : ∃ t, Post boundary message s t := by
  obtain ⟨n, u, ha, hr, hc, he⟩ :=
    Copy.run hp.ready hp.code hp.toStorage hp.boundaryOutside hp.rip
  have hsp := Copy.effect_rsp he
  have hsu := hp.toStorage.of_agrees he.agrees hsp
  obtain ⟨hdi, hsi, hdx⟩ := Copy.effect_arguments he
  have hdi' : u.regValue .rdi = stackPtr u + 8 := by rw [hsp]; exact hdi
  have hsi' : u.regValue .rsi = stackPtr u + 112 := by rw [hsp]; exact hsi
  have hinput : (⟨(stackPtr u + 112).toNat, (firstBlock message).size⟩ : MemoryRegion).HasBytes
      u.external (firstBlock message) := by
    rw [hsp]
    exact Copy.effect_bytes hp.toStorage he (size_firstBlock message)
      (by simpa only [size_firstBlock] using hp.input)
  have hbuffer := Copy.effect_buffer he hp.buffer
  obtain ⟨v, hv⟩ := Compression.run hr hc hsu hp.boundaryOutside he.rip
    (size_firstBlock message) hdi' hsi' hdx hinput hbuffer
  have hCopy := copy_agrees he
  obtain ⟨t, ht⟩ := finish_call hsu hp.boundaryOutside hdi'
    ((hCopy.read (n := 64) (r := 12) (by simp [changes])).trans hp.position)
    ((hCopy.read (n := 64) (r := 15) (by simp [changes])).trans hp.blocks) hv
  obtain ⟨m, hm⟩ := ht.advances
  refine ⟨t, ⟨⟨n + m, ha.trans hm⟩, ht.ready, ht.code, ht.rip,
    ht.storage, ht.rsp.trans hsp, ht.zeroPrefix, ht.buffer, ht.position, ht.blocks, ?_⟩⟩
  have hh := ht.agrees
  have heq : Kind.digest.changes u = Kind.digest.changes s := by
    simp only [Kind.changes, Kind.localChanges, hsp]
  rw [heq] at hh
  exact ((agrees_digest hCopy).trans hh).mono (by simp)

end Md5.Proofs.Buffered.Finalize.Digest.Long
