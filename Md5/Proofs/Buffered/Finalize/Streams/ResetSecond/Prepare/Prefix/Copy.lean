import Md5.Proofs.Buffered.Finalize.Streams.Copy
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare.Prefix.Entry

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

def copyChanges (s : RamState) (variant : Variant := .original) : List Component :=
  [.reg 1, .reg 6, .reg 7, .mem (stackPtr s + BitVec.ofNat 64 variant.tailOffset) 88, .rip]

structure Copied [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s t : RamState) (variant : Variant := .original) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = match variant with
    | .original => 0x100aa2 | .finalize => 0x101132 | .discard => 0x101612
  storage : Storage variant.toKind t
  source : Absorbed (stackPtr t + BitVec.ofNat 64 variant.toKind.contextOffset) message t
  destination : Absorbed (stackPtr t + BitVec.ofNat 64 variant.tailOffset) message t
  rsp : stackPtr t = stackPtr s
  agrees : AgreesExcept (copyChanges s variant) s t

theorem copy [Bindings] {variant : Variant} {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (h : Pre variant.toKind boundary message s) : ∃ t, Copied boundary message s t variant := by
  cases variant with
  | original =>
      obtain ⟨fuel, u, hrun, hready, hcode, he⟩ := entry_state (variant := .original) h
      have hsp : stackPtr u = stackPtr s := he.agrees.read (n := 64) (r := 4)
        (by simp [entryEffect, Variant.toKind, Variant.tailOffset, Kind.contextOffset, Effect.components])
      have hm : u.external = s.external := he.agrees.external
        (by simp [entryEffect, Variant.toKind, Variant.tailOffset, Kind.contextOffset, Effect.components, Component.Covers])
      have ha : Absorbed (stackPtr u + 8) message u := by
        apply absorbed_of_copy h.absorbed
        intro i _
        simp only [hsp, hm, Kind.context, Kind.contextOffset]
        rfl
      have hp : Streams.CopyPre .resetSecond 0xa9f 8 96 u := by
        refine ⟨h.toStorage.of_agrees he.agrees hsp, hready, hcode, ?_,
          (he.agrees.directionFlagClear (by simp [entryEffect, Variant.toKind, Variant.tailOffset, Kind.contextOffset, Effect.components]) h.df).df,
          he.rip, ?_, ?_, ?_,
          by decide, by decide, by decide, by decide, by decide +kernel⟩
        · exact program_text_slice hcode 0xa9f 3 (by decide +kernel)
        · rw [hsp]
          exact he.writes.2.1
        · rw [hsp]
          exact he.writes.1
        · exact he.writes.2.2
      obtain ⟨t, ht⟩ := copy_context h.stride boundary h.boundaryOutside hp
      refine ⟨t, ⟨⟨fuel + 11, hrun.trans ht.advances⟩, ht.ready, ht.code, ht.rip,
        hp.toStorage.of_agrees ht.agrees ht.rsp, ht.sourceAbsorbed hp ha, ht.absorbed ha,
        ht.rsp.trans hsp, ?_⟩⟩
      have hAg := he.agrees.trans ht.agrees
      rw [hsp] at hAg
      apply hAg.mono
      intro c hc
      simp only [entryEffect, Variant.toKind, Variant.tailOffset, Kind.contextOffset, Effect.components, List.map_cons, List.map_nil, List.append_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [copyChanges, Variant.tailOffset]
  | finalize =>
      obtain ⟨fuel, u, hrun, hready, hcode, he⟩ := entry_state (variant := .finalize) h
      have hsp : stackPtr u = stackPtr s := he.agrees.read (n := 64) (r := 4)
        (by simp [entryEffect, Variant.toKind, Variant.tailOffset, Kind.contextOffset, Effect.components])
      have hm : u.external = s.external := he.agrees.external
        (by simp [entryEffect, Variant.toKind, Variant.tailOffset, Kind.contextOffset, Effect.components, Component.Covers])
      have ha : Absorbed (stackPtr u + 8) message u := by
        apply absorbed_of_copy h.absorbed
        intro i _
        simp only [hsp, hm, Kind.context, Kind.contextOffset]
        rfl
      have hp : Streams.CopyPre .finalizeResetSecond 0x112f 8 96 u := by
        refine ⟨h.toStorage.of_agrees he.agrees hsp, hready, hcode, ?_,
          (he.agrees.directionFlagClear (by simp [entryEffect, Variant.toKind, Variant.tailOffset, Kind.contextOffset, Effect.components]) h.df).df,
          he.rip, ?_, ?_, ?_,
          by decide, by decide, by decide, by decide, by decide +kernel⟩
        · exact program_text_slice hcode 0x112f 3 (by decide +kernel)
        · rw [hsp]
          exact he.writes.2.1
        · rw [hsp]
          exact he.writes.1
        · exact he.writes.2.2
      obtain ⟨t, ht⟩ := copy_context h.stride boundary h.boundaryOutside hp
      refine ⟨t, ⟨⟨fuel + 11, hrun.trans ht.advances⟩, ht.ready, ht.code, ht.rip,
        hp.toStorage.of_agrees ht.agrees ht.rsp, ht.sourceAbsorbed hp ha, ht.absorbed ha,
        ht.rsp.trans hsp, ?_⟩⟩
      have hAg := he.agrees.trans ht.agrees
      rw [hsp] at hAg
      apply hAg.mono
      intro c hc
      simp only [entryEffect, Variant.toKind, Variant.tailOffset, Kind.contextOffset, Effect.components, List.map_cons, List.map_nil, List.append_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [copyChanges, Variant.tailOffset]
  | discard =>
      obtain ⟨fuel, u, hrun, hready, hcode, he⟩ := entry_state (variant := .discard) h
      have hsp : stackPtr u = stackPtr s := he.agrees.read (n := 64) (r := 4)
        (by simp [entryEffect, Variant.toKind, Variant.tailOffset, Kind.contextOffset, Effect.components])
      have hm : u.external = s.external := he.agrees.external
        (by simp [entryEffect, Variant.toKind, Variant.tailOffset, Kind.contextOffset, Effect.components, Component.Covers])
      have ha : Absorbed (stackPtr u + 32) message u := by
        apply absorbed_of_copy h.absorbed
        intro i _
        simp only [hsp, hm, Kind.context, Kind.contextOffset]
        rfl
      have hp : Streams.CopyPre .resetDiscardSecond 0x160f 32 136 u := by
        refine ⟨h.toStorage.of_agrees he.agrees hsp, hready, hcode, ?_,
          (he.agrees.directionFlagClear (by simp [entryEffect, Variant.toKind, Variant.tailOffset, Kind.contextOffset, Effect.components]) h.df).df,
          he.rip, ?_, ?_, ?_,
          by decide, by decide, by decide, by decide, by decide +kernel⟩
        · exact program_text_slice hcode 0x160f 3 (by decide +kernel)
        · rw [hsp]
          exact he.writes.2.1
        · rw [hsp]
          exact he.writes.1
        · exact he.writes.2.2
      obtain ⟨t, ht⟩ := copy_context h.stride boundary h.boundaryOutside hp
      refine ⟨t, ⟨⟨fuel + 11, hrun.trans ht.advances⟩, ht.ready, ht.code, ht.rip,
        hp.toStorage.of_agrees ht.agrees ht.rsp, ht.sourceAbsorbed hp ha, ht.absorbed ha,
        ht.rsp.trans hsp, ?_⟩⟩
      have hAg := he.agrees.trans ht.agrees
      rw [hsp] at hAg
      apply hAg.mono
      intro c hc
      simp only [entryEffect, Variant.toKind, Variant.tailOffset, Kind.contextOffset, Effect.components, List.map_cons, List.map_nil, List.append_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [copyChanges, Variant.tailOffset]

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare
