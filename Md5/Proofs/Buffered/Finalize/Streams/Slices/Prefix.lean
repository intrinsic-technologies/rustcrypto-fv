import Md5.Proofs.Buffered.Finalize.Streams.Slices.Copy
import Md5.Proofs.Buffered.Finalize.Streams.Slices.PrepareBytes

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

structure Prepared [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s t : RamState) (update : Bool := false) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = (BitVec.ofNat 64 (relocated update 0x100463))
  storage : Storage (streamKind update) t
  absorbed : Absorbed (stackPtr t + 16) message t
  result : (⟨(stackPtr t).toNat, 16⟩ : MemoryRegion).HasBytes t.external
    ⟨(absorbedBuffer message).toBytes.toArray⟩
  blocks : (Operand.reg 14 : Operand 64).read t = BitVec.ofNat 64 (message.size / 64)
  position : (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 (message.size % 64)
  df : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS
  rsp : stackPtr t = stackPtr s
  agrees : AgreesExcept ((streamKind update).changes s) s t

theorem prepare_code {update : Bool} {s t : RamState} (hs : Storage (streamKind update) s)
    (h : (prepareEffect (update := update) s).Holds s t) (hc : CodeIn Extracted.programImage s) :
    CodeIn Extracted.programImage t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    apply CodeIn.of_agreesExcept h.agrees _ hc
    intro x hx c hc hcover
    simp only [prepareEffect, Effect.components, List.map_cons, List.map_nil, List.append_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    · obtain ⟨i, hi, he⟩ := hcover
      exact (hs.stackRange 8 8 (by decide)).code i hi ⟨x.2, he ▸ hx⟩
    · obtain ⟨i, hi, he⟩ := hcover
      exact (hs.stackRange 0 8 (by decide)).code i hi
        ⟨x.2, by simpa using he ▸ hx⟩

theorem prepare_state {update : Bool} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (h : Pre (streamKind update) boundary message s) : ∃ t, Prepared (update := update) boundary message s t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    obtain ⟨u, hu⟩ := copy (update := update) h
    have hbytes : CodeIn (codeRange (BitVec.ofNat 64 (relocated update 0x100440)) prepareBytes) u :=
      by
        have hc := program_text_slice hu.code (relocated update 0x440) 35 (by decide +kernel)
        have hb : Extracted.textBytes.toListFrom (relocated update 0x440) 35 =
            prepareBytes := by decide +kernel
        rw [hb] at hc
        exact hc
    obtain ⟨fuel, t, hrun, hready, _, he⟩ := prepare_execution (update := update) boundary h.boundaryOutside u
      hu.ready hbytes ⟨hu.storage, hu.rip⟩
    have hsp : stackPtr t = stackPtr u := he.agrees.read (n := 64) (r := 4)
      (by simp [prepareEffect, Effect.components])
    have hlength := prepare_length he hu.destination
    obtain ⟨firstFuel, hfirst⟩ := hu.advances
    have hag := hu.agrees.trans he.agrees
    refine ⟨t, ⟨⟨firstFuel + fuel, hfirst.trans hrun⟩, hready, prepare_code (update := update) hu.storage he hu.code,
      he.rip, hu.storage.of_agrees he.agrees hsp, prepare_preserves_context he hu.destination,
      ?_, hlength.1, hlength.2,
      hag.directionFlagClear (by simp [copyChanges, prepareEffect, Effect.components]) h.df,
      hsp.trans hu.rsp, ?_⟩⟩
    · rw [hsp]
      exact prepare_result (update := update) hu.storage he hu.source
    · have heffect : (prepareEffect (update := update) u).components = (prepareEffect (update := update) s).components := by
        simp only [prepareEffect, Effect.components, List.map_cons, List.map_nil,
          List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
          hu.rsp]
      rw [heffect] at hag
      apply hag.widen
      · intro c hc hm
        simp only [copyChanges, prepareEffect, Effect.components, List.map_cons, List.map_nil,
          List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [update, streamKind, Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
      · intro address c hc hcover
        refine ⟨.mem (stackPtr s) 168, by simp [streamKind, Kind.changes, Kind.localChanges], ?_⟩
        simp only [copyChanges, prepareEffect, Effect.components, List.map_cons, List.map_nil,
          List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcover.elim
        · exact FinalizeReset.Export.covers_shift (offset := 16) hcover (by decide)
        · exact FinalizeReset.Export.covers_shift (offset := 8) hcover (by decide)
        · obtain ⟨i, hi, he⟩ := hcover
          exact ⟨i, by omega, he⟩

end Md5.Proofs.Buffered.Finalize.Streams.Slices
