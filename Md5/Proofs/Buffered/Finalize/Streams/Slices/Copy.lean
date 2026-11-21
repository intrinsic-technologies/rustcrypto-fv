import Md5.Proofs.Buffered.Finalize.Streams.Copy
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Entry

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

def copyChanges (s : RamState) : List Component :=
  [.reg 1, .reg 6, .reg 7, .mem (stackPtr s + 16) 88, .rip]

structure Copied [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s t : RamState) (update : Bool := false) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = (BitVec.ofNat 64 (relocated update 0x100440))
  storage : Storage (streamKind update) t
  source : Absorbed (stackPtr t + 192) message t
  destination : Absorbed (stackPtr t + 16) message t
  rsp : stackPtr t = stackPtr s
  agrees : AgreesExcept (copyChanges s) s t

theorem copy {update : Bool} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (h : Pre (streamKind update) boundary message s) : ∃ t, Copied (update := update) boundary message s t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    obtain ⟨fuel, u, hrun, hready, hcode, he⟩ := prepare (update := update) h
    have hsp : stackPtr u = stackPtr s := he.agrees.read (n := 64) (r := 4)
      (by simp [entryEffect, Effect.components])
    have hm : u.external = s.external := he.agrees.external
      (by simp [entryEffect, Effect.components, Component.Covers])
    have ha : Absorbed (stackPtr u + 192) message u := by
      apply absorbed_of_copy h.absorbed
      intro i _
      simp only [hsp, hm, Kind.context, Kind.contextOffset]
      rfl
    have hp : Streams.CopyPre (streamKind update) (relocated update 0x43d) 192 16 u := by
      refine ⟨h.toStorage.of_agrees he.agrees hsp, hready, hcode, ?_,
        (he.agrees.directionFlagClear (by simp [entryEffect, Effect.components]) h.df).df,
        he.rip, ?_, ?_, ?_,
        by decide, by decide, by decide, by decide, by decide +kernel⟩
      · have hc := program_text_slice hcode (relocated update 0x43d) 3 (by decide +kernel)
        have hb : Extracted.textBytes.toListFrom (relocated update 0x43d) 3 =
            [0xf3, 0x48, 0xa5] := by decide +kernel
        rw [hb] at hc
        exact hc
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
    simp only [entryEffect, Effect.components, List.map_cons, List.map_nil, List.append_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [copyChanges]

end Md5.Proofs.Buffered.Finalize.Streams.Slices
