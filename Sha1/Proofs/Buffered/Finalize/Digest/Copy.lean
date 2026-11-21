import Sha1.Proofs.Buffered.Finalize.Copy
import Sha1.Proofs.Compress.Machine.Execution
import Sha1.Proofs.Compress.Machine.Code

namespace Sha1.Proofs.Buffered.Finalize.Digest

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

namespace Entry

def bytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x18, 0x48, 0x8d, 0xb4, 0x24, 0xb8, 0, 0, 0,
    0xb9, 0x0c, 0, 0, 0]

def effect (s : RamState) : Effect :=
  { rip := 0x1000ec
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 24⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 184⟩,
      ⟨(.reg 1 : Operand 64), 12⟩] }

theorem execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1000da) (codeRange 0x1000da bytes) effect := by
  unfold bytes
  md5_run_begin lea_r64_effect_step 0x1000da 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 24)) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xdf (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x1000df 0x48 (by unfold RexWPrefix; decide)
    6 (.sib 4 none 0 (.d32 184)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1000da) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe7 (by decide +kernel)
  md5_run_then mov_r32_imm32_effect_step 0x1000e7 0xb9 (by decide) 12
  case sub => exact codeRange_mem_of_drop (p := 0x1000da) 13 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xec (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [effect]
  · x86_norm [effect, stackPtr]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

theorem run [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (h : Pre .digestCopy boundary message s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect s).Holds s t := by
  have hc : CodeIn (codeRange 0x1000da bytes) s :=
    program_text_slice h.code 0xda 18 (by decide +kernel)
  obtain ⟨fuel, t, ha, hr, _, he⟩ := execution boundary h.boundaryOutside s h.ready hc h.rip
  refine ⟨fuel, t, ha, hr, he.codeIn ?_ h.code, he⟩
  apply Effect.Avoids.of_noMem
  simp [effect, Effect.components, Component.Covers]

end Entry

def copyChanges (s : RamState) : List Component :=
  [.reg 1, .reg 6, .reg 7, .mem (stackPtr s + 24) 96, .rip]

structure Copied [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = 0x1000ef
  storage : Storage .digestCopy t
  absorbed : Absorbed (stackPtr t + 24) message t
  source : Absorbed (stackPtr t + 184) message t
  agrees : AgreesExcept (copyChanges s) s t

theorem copy_context [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hp : Pre .digestCopy boundary message s) :
    ∃ t, Copied boundary message s t := by
  obtain ⟨fuel, u, hu, hur, huc, he⟩ := Entry.run hp
  have hsp : stackPtr u = stackPtr s := he.agrees.read (n := 64) (r := 4) (by
    simp [Entry.effect, Effect.components])
  have hmem (a : BitVec 64) : u.external[a]? = s.external[a]? := by
    apply he.agrees.byte
    intro c hc hcover
    simp only [Entry.effect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact hcover
  have habs : Absorbed (stackPtr u + 184) message u := by
    rw [hsp]
    exact absorbed_of_copy hp.absorbed (fun i _ ↦ hmem _)
  have hcp : Streams.CopyPre .digestCopy 0xec 184 24 u := by
    refine ⟨hp.toStorage.of_agrees he.agrees hsp, hur, huc, ?_, ?_, he.rip, ?_, ?_, ?_,
      by decide, by decide, by decide, by decide, by decide +kernel⟩
    · exact program_text_slice huc 0xec 3 (by decide +kernel)
    · exact (he.agrees.directionFlagClear (by simp [Entry.effect, Effect.components]) hp.df).df
    · rw [hsp]
      exact he.writes.2.1
    · rw [hsp]
      exact he.writes.1
    · exact he.writes.2.2
  obtain ⟨t, ht⟩ := Streams.copy_context hp.stride boundary hp.boundaryOutside hcp
  have hsp' : stackPtr t = stackPtr s := ht.rsp.trans hsp
  have hag : AgreesExcept (copyChanges s) s t := by
    have ha := he.agrees.trans ht.agrees
    rw [hsp] at ha
    apply ha.mono
    intro c hc
    simp only [Entry.effect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [copyChanges]
  exact ⟨t, ⟨⟨fuel + 12, hu.trans ht.advances⟩, ht.ready, ht.code, ht.rip,
    hp.toStorage.of_agrees hag hsp', ht.absorbed habs, ht.sourceAbsorbed hcp habs, hag⟩⟩

theorem Copied.rsp [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (h : Copied boundary message s t) : stackPtr t = stackPtr s :=
  h.agrees.read (n := 64) (r := 4) (by simp [copyChanges])

theorem Copied.agreesDigest [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (h : Copied boundary message s t) (hs : Storage .digestCopy s) :
    AgreesExcept (Kind.digestCopy.changes s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [copyChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
  · intro a c hc hcover
    simp only [copyChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    refine ⟨.mem (stackPtr s - Finalize.Kind.frameBytes) (Finalize.Kind.frameBytes + Kind.digestCopy.stackBytes),
      by simp [Kind.changes, Kind.localChanges], ?_⟩
    exact hs.localWithin (offset := 24) (len := 96) (by decide) hcover

end Sha1.Proofs.Buffered.Finalize.Digest
