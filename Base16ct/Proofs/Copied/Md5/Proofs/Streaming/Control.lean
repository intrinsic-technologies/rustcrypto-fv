import Base16ct.Proofs.Copied.Md5.Proofs.Block.Entry
import Base16ct.Proofs.Copied.Md5.Proofs.Block.Execution
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple

namespace Base16ct.Proofs.Copied.Md5.Proofs.Streaming

open Base16ct.Proofs.Copied.Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

structure CounterPre [Bindings] (boundary : ReturnBoundary) (pc : BitVec 64)
    (index count : BitVec 4) (s : RamState) : Prop where
  ready : ReadyToStep s
  code : CodeIn (codeRange pc (encodeIncR64 index ++ encodeCmpR64R64 count index)) s
  rip : s.RIP = pc
  different : index.setWidth 5 ≠ count.setWidth 5
  incrementContinues : pc + 3#64 ≠ boundary.rip
  compareContinues : pc + 6#64 ≠ boundary.rip

structure CounterPost [Bindings] (boundary : ReturnBoundary) (pc : BitVec 64)
    (index count : BitVec 4) (s t : RamState) : Prop where
  advances : Advances boundary 2 s t
  ready : ReadyToStep t
  rip : t.RIP = pc + 6#64
  indexValue : (Operand.reg (index.setWidth 5) : Operand 64).read t =
    (Operand.reg (index.setWidth 5) : Operand 64).read s + 1
  zero : (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
    ((Operand.reg (count.setWidth 5) : Operand 64).read s ==
      (Operand.reg (index.setWidth 5) : Operand 64).read s + 1)
  agrees : AgreesExcept [.reg (index.setWidth 5), .flags, .rip] s t

theorem counter_increment_compare [Bindings] {boundary : ReturnBoundary} {pc : BitVec 64}
    {index count : BitVec 4} {s : RamState} (h : CounterPre boundary pc index count s) :
    ∃ t, CounterPost boundary pc index count s t := by
  have hInc : StepEffect (fun s ↦ s.RIP = pc) (codeRange pc (encodeIncR64 index))
      (incR64Effect pc (index.setWidth 5)) := by
    obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeIncR64_spec index
    rw [hbytes, ← hdst]
    exact inc_r64_effect_step pc rex modrm hrex hmod hreg
  have hCmp : StepEffect (fun s ↦ s.RIP = pc + 3#64)
      (codeRange (pc + 3#64) (encodeCmpR64R64 count index))
      (cmpR64R64Effect (pc + 3#64) (count.setWidth 5) (index.setWidth 5)) := by
    obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeCmpR64R64_spec count index
    rw [hbytes, ← hdst, ← hsrc]
    exact cmp_r64_r64_effect_step (pc + 3#64) rex modrm hrex hmod
  have hCode : CodeIn (codeRange pc (encodeIncR64 index) ++
      codeRange (pc + 3#64) (encodeCmpR64R64 count index)) s := by
    simpa only [codeRange_append, encodeIncR64, List.length_cons, List.length_nil, Nat.reduceAdd] using h.code
  obtain ⟨hIncCode, hCmpCode⟩ := CodeIn.append_iff.mp hCode
  obtain ⟨u, hRun, hReady, hEffect⟩ := hInc.advances h.ready hIncCode h.rip h.incrementContinues
  have hCmpCode' := hEffect.codeIn (incR64Effect_avoids pc (index.setWidth 5) s _) hCmpCode
  obtain ⟨t, hRun', hReady', hEffect'⟩ := hCmp.advances (boundary := boundary)
    hReady hCmpCode' hEffect.rip (by
      simpa only [cmpR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd] using h.compareContinues)
  have hIndex : (Operand.reg (index.setWidth 5) : Operand 64).read u =
      (Operand.reg (index.setWidth 5) : Operand 64).read s + 1 := hEffect.writes
  have hCount : (Operand.reg (count.setWidth 5) : Operand 64).read u =
      (Operand.reg (count.setWidth 5) : Operand 64).read s :=
    hEffect.agrees.read (by simpa using Ne.symm h.different)
  refine ⟨t, hRun.trans hRun', hReady', ?_, ?_, ?_, ?_⟩
  · simpa only [cmpR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd] using hEffect'.rip
  · exact (hEffect'.agrees.read (n := 64) (r := index.setWidth 5) (by simp)).trans hIndex
  · have hz := hEffect'.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
      (((Operand.reg (count.setWidth 5) : Operand 64).read u -
        (Operand.reg (index.setWidth 5) : Operand 64).read u) == 0) at hz
    rw [hz, hCount, hIndex]
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.sub_eq_iff_eq_add]
  · apply (hEffect.agrees.trans hEffect'.agrees).mono
    intro c hc
    simpa only [incR64Effect_components, cmpR64R64Effect_components, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, or_self, or_assoc] using hc

inductive RegisterCounterKind where
  | slicesPartial
  | slicesFull
  | resetFirstPartial
  | resetFirstFull

namespace RegisterCounterKind

def pc : RegisterCounterKind → BitVec 64
  | .slicesPartial => 0x100f71
  | .slicesFull => 0x10104f
  | .resetFirstPartial => 0x1012ec
  | .resetFirstFull => 0x1013ab

def count : RegisterCounterKind → BitVec 4
  | .slicesPartial | .slicesFull => 12
  | .resetFirstPartial | .resetFirstFull => 5

end RegisterCounterKind

end Base16ct.Proofs.Copied.Md5.Proofs.Streaming
