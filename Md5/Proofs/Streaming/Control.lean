import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple

namespace Md5.Proofs.Streaming

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

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
  | updateFinalizeIntoPartial
  | updateFinalizeIntoFull
  | finalizeResetFirstPartial
  | finalizeResetFirstFull
  | resetDiscardFirstPartial
  | resetDiscardFirstFull

namespace RegisterCounterKind

def pc : RegisterCounterKind → BitVec 64
  | .slicesPartial => 0x100331
  | .slicesFull => 0x10040f
  | .resetFirstPartial => 0x1006ac
  | .resetFirstFull => 0x10076b
  | .updateFinalizeIntoPartial => 0x1018e1
  | .updateFinalizeIntoFull => 0x1019bf
  | .finalizeResetFirstPartial => 0x100d5c
  | .finalizeResetFirstFull => 0x100e1b
  | .resetDiscardFirstPartial => 0x1013ec
  | .resetDiscardFirstFull => 0x1014a6

def count : RegisterCounterKind → BitVec 4
  | .slicesPartial | .slicesFull => 12
  | .resetFirstPartial | .resetFirstFull => 5
  | .updateFinalizeIntoPartial | .updateFinalizeIntoFull => 12
  | .finalizeResetFirstPartial | .finalizeResetFirstFull => 5
  | .resetDiscardFirstPartial | .resetDiscardFirstFull => 12

def cc : RegisterCounterKind → BitVec 4
  | .slicesPartial | .resetFirstPartial => 4
  | .slicesFull | .resetFirstFull => 5
  | .updateFinalizeIntoPartial => 4
  | .updateFinalizeIntoFull => 5
  | .finalizeResetFirstPartial => 4
  | .finalizeResetFirstFull => 5
  | .resetDiscardFirstPartial => 4
  | .resetDiscardFirstFull => 5

def displacement : RegisterCounterKind → BitVec 32
  | .slicesPartial => 0xee
  | .slicesFull => 0xffffff22
  | .resetFirstPartial => 0xd8
  | .resetFirstFull => 0xffffff41
  | .updateFinalizeIntoPartial => 0xee
  | .updateFinalizeIntoFull => 0xffffff22
  | .finalizeResetFirstPartial => 0xd8
  | .finalizeResetFirstFull => 0xffffff41
  | .resetDiscardFirstPartial => 0xcf
  | .resetDiscardFirstFull => 0xffffff46

def donePC : RegisterCounterKind → BitVec 64
  | .slicesPartial => 0x10042b
  | .slicesFull => 0x10041b
  | .resetFirstPartial => 0x100790
  | .resetFirstFull => 0x100777
  | .updateFinalizeIntoPartial => 0x1019db
  | .updateFinalizeIntoFull => 0x1019cb
  | .finalizeResetFirstPartial => 0x100e40
  | .finalizeResetFirstFull => 0x100e27
  | .resetDiscardFirstPartial => 0x1014c7
  | .resetDiscardFirstFull => 0x1014b2

def loopPC : RegisterCounterKind → BitVec 64
  | .slicesPartial | .slicesFull => 0x10033d
  | .resetFirstPartial | .resetFirstFull => 0x1006b8
  | .updateFinalizeIntoPartial | .updateFinalizeIntoFull => 0x1018ed
  | .finalizeResetFirstPartial | .finalizeResetFirstFull => 0x100d68
  | .resetDiscardFirstPartial | .resetDiscardFirstFull => 0x1013f8

def effect (kind : RegisterCounterKind) (s : RamState) : Effect where
  rip := if (Operand.reg (kind.count.setWidth 5) : Operand 64).read s =
      (Operand.reg 15 : Operand 64).read s + 1 then kind.donePC else kind.loopPC
  writes := [⟨(.reg 15 : Operand 64), (Operand.reg 15 : Operand 64).read s + 1⟩]
  flags := some ⟨none, none, none, none, none, none⟩

end RegisterCounterKind

theorem register_counter_branch [Bindings] (kind : RegisterCounterKind)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = kind.pc) Extracted.programImage kind.effect := by
  intro s hReady hCode hRip
  have hPre : CounterPre boundary kind.pc 15 kind.count s := by
    refine ⟨hReady, ?_, hRip, ?_, ?_, ?_⟩
    · cases kind
      · exact program_text_slice hCode 0x331 6 (by decide +kernel)
      · exact program_text_slice hCode 0x40f 6 (by decide +kernel)
      · exact program_text_slice hCode 0x6ac 6 (by decide +kernel)
      · exact program_text_slice hCode 0x76b 6 (by decide +kernel)
      · exact program_text_slice hCode 0x18e1 6 (by decide +kernel)
      · exact program_text_slice hCode 0x19bf 6 (by decide +kernel)
      · exact program_text_slice hCode 0xd5c 6 (by decide +kernel)
      · exact program_text_slice hCode 0xe1b 6 (by decide +kernel)
      · exact program_text_slice hCode 0x13ec 6 (by decide +kernel)
      · exact program_text_slice hCode 0x14a6 6 (by decide +kernel)
    · cases kind <;> decide
    · cases kind
      · exact text_address_ne_return hOutside 0x334 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x412 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x6af (by decide +kernel)
      · exact text_address_ne_return hOutside 0x76e (by decide +kernel)
      · exact text_address_ne_return hOutside 0x18e4 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x19c2 (by decide +kernel)
      · exact text_address_ne_return hOutside 0xd5f (by decide +kernel)
      · exact text_address_ne_return hOutside 0xe1e (by decide +kernel)
      · exact text_address_ne_return hOutside 0x13ef (by decide +kernel)
      · exact text_address_ne_return hOutside 0x14a9 (by decide +kernel)
    · cases kind
      · exact text_address_ne_return hOutside 0x337 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x415 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x6b2 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x771 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x18e7 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x19c5 (by decide +kernel)
      · exact text_address_ne_return hOutside 0xd62 (by decide +kernel)
      · exact text_address_ne_return hOutside 0xe21 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x13f2 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x14ac (by decide +kernel)
  obtain ⟨u, hCounter⟩ := counter_increment_compare hPre
  have hCode' := hCounter.agrees.codeIn (by simp [Component.Covers]) hCode
  have hNext :
      (jccEffect (kind.pc + 6) 6 kind.cc (kind.displacement.signExtend 64) u).rip =
        (kind.effect s).rip := by
    cases kind <;>
      simp [RegisterCounterKind.pc, RegisterCounterKind.cc,
        RegisterCounterKind.displacement, RegisterCounterKind.effect, RegisterCounterKind.count,
        RegisterCounterKind.donePC, RegisterCounterKind.loopPC, jccEffect, branchEffect,
        condHolds, hCounter.zero, branchTarget]
  have hNe : (kind.effect s).rip ≠ boundary.rip := by
    cases kind <;> unfold RegisterCounterKind.effect
    all_goals split
    · exact text_address_ne_return hOutside 0x42b (by decide +kernel)
    · exact text_address_ne_return hOutside 0x33d (by decide +kernel)
    · exact text_address_ne_return hOutside 0x41b (by decide +kernel)
    · exact text_address_ne_return hOutside 0x33d (by decide +kernel)
    · exact text_address_ne_return hOutside 0x790 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x6b8 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x777 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x6b8 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x19db (by decide +kernel)
    · exact text_address_ne_return hOutside 0x18ed (by decide +kernel)
    · exact text_address_ne_return hOutside 0x19cb (by decide +kernel)
    · exact text_address_ne_return hOutside 0x18ed (by decide +kernel)
    · exact text_address_ne_return hOutside 0xe40 (by decide +kernel)
    · exact text_address_ne_return hOutside 0xd68 (by decide +kernel)
    · exact text_address_ne_return hOutside 0xe27 (by decide +kernel)
    · exact text_address_ne_return hOutside 0xd68 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x14c7 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x13f8 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x14b2 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x13f8 (by decide +kernel)
  have hBranchCode : CodeIn (codeRange (kind.pc + 6)
      (0x0f :: jccOpcode32 kind.cc :: immBytes 32 kind.displacement)) u := by
    cases kind
    · exact program_text_slice hCode' 0x337 6 (by decide +kernel)
    · exact program_text_slice hCode' 0x415 6 (by decide +kernel)
    · exact program_text_slice hCode' 0x6b2 6 (by decide +kernel)
    · exact program_text_slice hCode' 0x771 6 (by decide +kernel)
    · exact program_text_slice hCode' 0x18e7 6 (by decide +kernel)
    · exact program_text_slice hCode' 0x19c5 6 (by decide +kernel)
    · exact program_text_slice hCode' 0xd62 6 (by decide +kernel)
    · exact program_text_slice hCode' 0xe21 6 (by decide +kernel)
    · exact program_text_slice hCode' 0x13f2 6 (by decide +kernel)
    · exact program_text_slice hCode' 0x14ac 6 (by decide +kernel)
  obtain ⟨t, hAdvance, hReady', hEffect⟩ :=
    (jcc_rel32_effect_step (kind.pc + 6) kind.cc kind.displacement).advances
      hCounter.ready hBranchCode ⟨hCounter.rip, fun _ ↦ by cases kind <;> decide +kernel⟩
      (hNext ▸ hNe)
  have hAgrees : AgreesExcept [.rip] u t := hEffect.agrees
  refine ⟨3, t, hCounter.advances.trans hAdvance, hReady',
    hAgrees.codeIn (by simp [Component.Covers]) hCode',
    hEffect.rip.trans hNext, ?_, by trivial, ?_⟩
  · exact (hAgrees.read (n := 64) (r := 15) (by simp)).trans hCounter.indexValue
  · apply (hCounter.agrees.trans hAgrees).mono
    simp [RegisterCounterKind.effect, Effect.components]

end Md5.Proofs.Streaming
