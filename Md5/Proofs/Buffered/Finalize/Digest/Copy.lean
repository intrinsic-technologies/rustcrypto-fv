import Md5.Proofs.Buffered.Finalize.Digest.Entry
import Md5.Proofs.Buffered.Finalize.Streams.Copy

namespace Md5.Proofs.Buffered.Finalize.Digest

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

def copyChanges (s : RamState) : List Component :=
  [.reg 1, .reg 6, .reg 7, .mem (stackPtr s + 24) 88, .rip]

structure Copied [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = 0x1000e4
  storage : Storage .digest t
  absorbed : Absorbed (stackPtr t + 24) message t
  source : Absorbed (stackPtr t + 176) message t
  state : (Operand.reg 14 : Operand 64).read t = stackPtr t + 240
  agrees : AgreesExcept (copyChanges s) s t

theorem copy_context [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hp : Pre .digest boundary message s) : ∃ t, Copied boundary message s t := by
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
  have habs : Absorbed (stackPtr u + 176) message u := by
    rw [hsp]
    exact absorbed_of_copy hp.absorbed (fun i _ ↦ hmem _)
  have hcp : Streams.CopyPre .digest 0xe1 176 24 u := by
    refine ⟨hp.toStorage.of_agrees he.agrees hsp, hur, huc, ?_, ?_, he.rip, ?_, ?_, ?_,
      by decide, by decide, by decide, by decide, by decide +kernel⟩
    · exact program_text_slice huc 0xe1 3 (by decide +kernel)
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
  refine ⟨t, ⟨⟨fuel + 11, hu.trans ht.advances⟩, ht.ready, ht.code, ht.rip,
    hp.toStorage.of_agrees hag hsp', ht.absorbed habs, ht.sourceAbsorbed hcp habs, ?_, hag⟩⟩
  rw [hag.read (n := 64) (r := 14) (by simp [copyChanges]), hp.digestState rfl, hsp']

end Md5.Proofs.Buffered.Finalize.Digest
