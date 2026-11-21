import Md5.Proofs.Buffered.FinalizeReset.CompressCall.Pre

namespace Md5.Proofs.Buffered.FinalizeReset.CompressCall

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def changes (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip, .mem (s.regValue .rdi) 16, .mem (stackPtr s - 320) 320]

structure Post [Bindings] (boundary : ReturnBoundary) (ret : BitVec 64)
    (buffer : Standards.RFC.MD5.Buffer) (input : ByteArray) (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = ret
  rsp : stackPtr t = stackPtr s
  output : (Compress.outputRegion s).HasBytes t.external
    ⟨(Standards.RFC.MD5.processBlocks buffer (Standards.RFC.MD5.wordsOfBytes input)).toBytes.toArray⟩
  agrees : AgreesExcept (changes s) s t

set_option maxRecDepth 2048 in
theorem call_return_agrees {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    {s u t : RamState} {target : RamState → BitVec 64} {ret : BitVec 64}
    (h : Pre buffer input s) (he : (callEffect target ret s).Holds s u)
    (hb : AgreesExcept (Block.compressionComponents u) u t)
    (hrsp : stackPtr t = stackPtr s) : AgreesExcept (changes s) s t := by
  have hdi : u.regValue .rdi = s.regValue .rdi := callEffect_read he (r := 7) (by decide)
  have hstart : BitVec.ofNat 64 (scratchRegion s).start = stackPtr s - 320 := by
    rw [show (scratchRegion s).start = (stackPtr s - 320).toNat from h.scratchAddress.symm,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hcomponents : Block.compressionComponents u =
      [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
        .flags, .rip, .mem (s.regValue .rdi) 16, .mem (stackPtr s - 320) 320] := by
    unfold Block.compressionComponents
    rw [hdi, h.calleeStackRegion he, hstart]
    rfl
  rw [hcomponents] at hb
  have hw : AgreesExcept (.reg 4 :: changes s) s t := by
    apply (he.agrees.trans hb).widen
    · intro c hc hm
      simp only [pushEffect_components, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl | rfl) |
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals simp_all [changes, Component.isMem]
    · intro address c hc hcover
      simp only [pushEffect_components, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl | rfl) |
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals try exact hcover.elim
      · refine ⟨.mem (stackPtr s - 320) 320, by simp [changes], ?_⟩
        obtain ⟨i, hi, rfl⟩ := hcover
        refine ⟨312 + i, by omega, ?_⟩
        rw [h.pushAddress, BitVec.add_assoc, BitVec.ofNat_add]
        rfl
      · exact ⟨.mem (s.regValue .rdi) 16, by simp [changes], hcover⟩
      · exact ⟨.mem (stackPtr s - 320) 320, by simp [changes], hcover⟩
  apply hw.narrow
  intro c hc hn
  have heq : c = .reg 4 := by simpa only [List.mem_cons, hn, or_false] using hc
  subst c
  exact hrsp

end Md5.Proofs.Buffered.FinalizeReset.CompressCall
