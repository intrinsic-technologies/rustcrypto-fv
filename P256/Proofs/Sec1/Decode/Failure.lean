import P256.Proofs.Sec1.Decode.Epilogue
import P256.Proofs.Sec1.Decode.Length
import P256.Proofs.Sec1.Decode.Reject
import P256.Proofs.Sec1.Model
import P256.Proofs.Program.ScalarFrame.Output

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem failure [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : DecodePre s boundary bytes) (state : Frame s t) (rip : t.RIP = 0x10e68e)
    (output : t.regValue .rdi = s.regValue .rdi)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 80 3680 ∧ PublicKeyResultAt u (s.regValue .rdi) none := by
  have writable := (ScalarFrame.output_writable pre.toCalleePre (by decide) state.allocated).add
    0 (len := 8) (by decide)
  have apart := P256.Proofs.Common.Instructions.RangeApart.add_left
    (ScalarFrame.output_code pre.toCalleePre (offset := 0xe693) (len := 3) (by decide))
    0 (len := 8) (by decide)
  change RangeApart (s.regValue .rdi + 0#64) 8 0x10e693 3 at apart
  obtain ⟨v, av, rv, iv, tag, gv⟩ := reject_tag
    (readyToStep state.machine state.bindingsSupported) state.loaded pre.outerBoundary rip
    (by simpa only [output, BitVec.add_zero] using writable)
    (by simpa only [output, BitVec.add_zero] using apart)
  rw [output] at tag gv
  have writes : WritesWithin [.reg 0, .mem (s.regValue .rdi) 8, .rip]
      #v[registerRegion s .rdi 80, ScalarFrame.Work.region s 3680 32] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · refine ⟨registerRegion s .rdi 80, by simp, ?_⟩
      exact ScalarFrame.output_contains pre.toCalleePre (offset := 0) (len := 8)
        (by decide) (by simpa only [BitVec.add_zero] using ha)
    · exact ha.elim
  have sv := state.after_effect pre rv gv writes (by simp)
  obtain ⟨u, result, memory⟩ := finish pre sv iv (by
    obtain ⟨fuel, before⟩ := execution
    exact ⟨fuel + 2, before.trans av⟩)
  exact ⟨u, result, by simpa only [PublicKeyResultAt, memory] using tag⟩

theorem decode_empty [Bindings] {s : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : DecodePre s boundary bytes) (empty : bytes.size = 0) :
    ∃ t, CalleeResult s t boundary 80 3680 ∧
      PublicKeyResultAt t (s.regValue .rdi) (P256.Spec.Points.decodePublicKey bytes) := by
  obtain ⟨a, entry⟩ := prologue pre
  have sa := entry.frame pre
  obtain ⟨b, ab, rb, ib, gb⟩ := length_branch entry.ready entry.loaded pre.outerBoundary entry.rip
  have length : a.regValue .rdx = 0 := by
    have ha : a.regValue .rdx = s.regValue .rdx := entry.agrees.read (n := 64) (r := 2)
      (by simp [saveComponents, savedRegisters, pushSequenceFrame])
    exact ha.trans (by rw [pre.length, empty]; rfl)
  have sb := sa.after_registers pre rb gb (by simp [Component.Covers]) (by simp)
  have output : b.regValue .rdi = s.regValue .rdi :=
    (gb.read (n := 64) (r := 7) (by simp)).trans
      (entry.agrees.read (n := 64) (r := 7)
        (by simp [saveComponents, savedRegisters, pushSequenceFrame]))
  obtain ⟨t, result, tag⟩ := failure pre sb (by simpa only [length, ite_true] using ib)
    output ⟨7, entry.execution.trans ab⟩
  refine ⟨t, result, ?_⟩
  rw [decodePublicKey_invalid_size (by omega) (by omega) (by omega)]
  exact tag

end P256.Proofs.Sec1.Decode
