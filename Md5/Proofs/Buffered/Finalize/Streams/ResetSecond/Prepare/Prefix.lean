import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare.Contracts
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare.Prefix.Copy
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare.Prefix.Bytes

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem prepare_code {variant : Variant} {s t : RamState} (hs : Storage variant.toKind s)
    (h : (prepareEffect s variant).Holds s t) (hc : CodeIn Extracted.programImage s) :
    CodeIn Extracted.programImage t := by
  cases variant with
  | original =>
      apply CodeIn.of_agreesExcept h.agrees _ hc
      intro x hx c hc hcover
      simp only [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Effect.components, List.map_cons, List.map_nil, List.append_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      · obtain ⟨i, hi, he⟩ := hcover
        exact (hs.stackRange 224 8 (by decide)).code i hi ⟨x.2, he ▸ hx⟩
      · obtain ⟨i, hi, he⟩ := hcover
        exact (hs.stackRange 216 8 (by decide)).code i hi ⟨x.2, he ▸ hx⟩
  | finalize =>
      apply CodeIn.of_agreesExcept h.agrees _ hc
      intro x hx c hc hcover
      simp only [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Effect.components, List.map_cons, List.map_nil, List.append_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      · obtain ⟨i, hi, he⟩ := hcover
        exact (hs.stackRange 224 8 (by decide)).code i hi ⟨x.2, he ▸ hx⟩
      · obtain ⟨i, hi, he⟩ := hcover
        exact (hs.stackRange 216 8 (by decide)).code i hi ⟨x.2, he ▸ hx⟩
  | discard =>
      apply CodeIn.of_agreesExcept h.agrees _ hc
      intro x hx c hc hcover
      simp only [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Effect.components, List.map_cons, List.map_nil, List.append_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      · obtain ⟨i, hi, he⟩ := hcover
        exact (hs.stackRange 128 8 (by decide)).code i hi ⟨x.2, he ▸ hx⟩
      · obtain ⟨i, hi, he⟩ := hcover
        exact (hs.stackRange 120 8 (by decide)).code i hi ⟨x.2, he ▸ hx⟩

theorem «prefix» [Bindings] {variant : Variant} {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (h : Finalize.Pre variant.toKind boundary message s) :
    ∃ t, ResetSecond.Transition boundary s t variant ∧ Prefix message t variant := by
  cases variant with
  | original =>
      obtain ⟨u, hu⟩ := copy (variant := .original) h
      have hbytes : CodeIn (codeRange 0x100aa2 (prepareBytes .original)) u :=
        program_text_slice hu.code 0xaa2 45 (by decide +kernel)
      obtain ⟨fuel, t, hrun, hready, _, he⟩ := prepare_execution (variant := .original) boundary h.boundaryOutside u
        hu.ready hbytes ⟨hu.storage, hu.rip⟩
      have hsp : stackPtr t = stackPtr u := he.agrees.read (n := 64) (r := 4)
        (by simp [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Effect.components])
      have hlength := prepare_length he hu.destination
      obtain ⟨firstFuel, hfirst⟩ := hu.advances
      have hag := hu.agrees.trans he.agrees
      refine ⟨t, ⟨⟨firstFuel + fuel, hfirst.trans hrun⟩, ?_⟩,
        ⟨hu.storage.of_agrees he.agrees hsp, hready, prepare_code hu.storage he hu.code,
          he.rip, prepare_preserves_context he hu.destination, ?_, hlength.1, hlength.2,
          (hag.directionFlagClear (by simp [copyChanges, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, prepareEffect, Effect.components])
            h.df).df⟩⟩
      · have heffect : (prepareEffect u .original).components = (prepareEffect s .original).components := by
          simp only [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Effect.components, List.map_cons, List.map_nil,
            List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
            hu.rsp]
        rw [heffect] at hag
        apply hag.widen
        · intro c hc hm
          simp only [copyChanges, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, prepareEffect, Effect.components, List.map_cons, List.map_nil,
            List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
            List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals simp_all [Component.isMem, Variant.toKind, Kind.changes, Kind.workRegisters, Kind.localChanges]
        · intro address c hc hcover
          simp only [copyChanges, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, prepareEffect, Effect.components, List.map_cons, List.map_nil,
            List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
            List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals try exact hcover.elim
          · exact ⟨.mem (stackPtr s + 96) 88, by simp [Variant.toKind, Kind.changes, Kind.localChanges], hcover⟩
          · refine ⟨.mem (stackPtr s + 216) 80, by simp [Variant.toKind, Kind.changes, Kind.localChanges], ?_⟩
            apply FinalizeReset.Export.covers_shift (offset := 8) (len := 8) (by
              simpa [BitVec.add_assoc] using hcover) (by decide)
          · refine ⟨.mem (stackPtr s + 216) 80, by simp [Variant.toKind, Kind.changes, Kind.localChanges], ?_⟩
            obtain ⟨i, hi, he⟩ := hcover
            exact ⟨i, by omega, he⟩
      · rw [hsp]
        exact prepare_result hu.storage he hu.source
  | finalize =>
      obtain ⟨u, hu⟩ := copy (variant := .finalize) h
      have hbytes : CodeIn (codeRange 0x101132 (prepareBytes .finalize)) u :=
        program_text_slice hu.code 0x1132 45 (by decide +kernel)
      obtain ⟨fuel, t, hrun, hready, _, he⟩ := prepare_execution (variant := .finalize) boundary h.boundaryOutside u
        hu.ready hbytes ⟨hu.storage, hu.rip⟩
      have hsp : stackPtr t = stackPtr u := he.agrees.read (n := 64) (r := 4)
        (by simp [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Effect.components])
      have hlength := prepare_length he hu.destination
      obtain ⟨firstFuel, hfirst⟩ := hu.advances
      have hag := hu.agrees.trans he.agrees
      refine ⟨t, ⟨⟨firstFuel + fuel, hfirst.trans hrun⟩, ?_⟩,
        ⟨hu.storage.of_agrees he.agrees hsp, hready, prepare_code hu.storage he hu.code,
          he.rip, prepare_preserves_context he hu.destination, ?_, hlength.1, hlength.2,
          (hag.directionFlagClear (by simp [copyChanges, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, prepareEffect, Effect.components])
            h.df).df⟩⟩
      · have heffect : (prepareEffect u .finalize).components = (prepareEffect s .finalize).components := by
          simp only [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Effect.components, List.map_cons, List.map_nil,
            List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
            hu.rsp]
        rw [heffect] at hag
        apply hag.widen
        · intro c hc hm
          simp only [copyChanges, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, prepareEffect, Effect.components, List.map_cons, List.map_nil,
            List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
            List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals simp_all [Component.isMem, Variant.toKind, Kind.changes, Kind.workRegisters, Kind.localChanges]
        · intro address c hc hcover
          simp only [copyChanges, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, prepareEffect, Effect.components, List.map_cons, List.map_nil,
            List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
            List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals try exact hcover.elim
          · exact ⟨.mem (stackPtr s + 96) 88, by simp [Variant.toKind, Kind.changes, Kind.localChanges], hcover⟩
          · refine ⟨.mem (stackPtr s + 216) 80, by simp [Variant.toKind, Kind.changes, Kind.localChanges], ?_⟩
            apply FinalizeReset.Export.covers_shift (offset := 8) (len := 8) (by
              simpa [BitVec.add_assoc] using hcover) (by decide)
          · refine ⟨.mem (stackPtr s + 216) 80, by simp [Variant.toKind, Kind.changes, Kind.localChanges], ?_⟩
            obtain ⟨i, hi, he⟩ := hcover
            exact ⟨i, by omega, he⟩
      · rw [hsp]
        exact prepare_result hu.storage he hu.source
  | discard =>
      obtain ⟨u, hu⟩ := copy (variant := .discard) h
      have hbytes : CodeIn (codeRange 0x101612 (prepareBytes .discard)) u :=
        program_text_slice hu.code 0x1612 42 (by decide +kernel)
      obtain ⟨fuel, t, hrun, hready, _, he⟩ := prepare_execution (variant := .discard) boundary h.boundaryOutside u
        hu.ready hbytes ⟨hu.storage, hu.rip⟩
      have hsp : stackPtr t = stackPtr u := he.agrees.read (n := 64) (r := 4)
        (by simp [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Effect.components])
      have hlength := prepare_length he hu.destination
      obtain ⟨firstFuel, hfirst⟩ := hu.advances
      have hag := hu.agrees.trans he.agrees
      refine ⟨t, ⟨⟨firstFuel + fuel, hfirst.trans hrun⟩, ?_⟩,
        ⟨hu.storage.of_agrees he.agrees hsp, hready, prepare_code hu.storage he hu.code,
          he.rip, prepare_preserves_context he hu.destination, ?_, hlength.1, hlength.2,
          (hag.directionFlagClear (by simp [copyChanges, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, prepareEffect, Effect.components])
            h.df).df⟩⟩
      · have heffect : (prepareEffect u .discard).components = (prepareEffect s .discard).components := by
          simp only [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, Effect.components, List.map_cons, List.map_nil,
            List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
            hu.rsp]
        rw [heffect] at hag
        apply hag.widen
        · intro c hc hm
          simp only [copyChanges, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, prepareEffect, Effect.components, List.map_cons, List.map_nil,
            List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
            List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals simp_all [Component.isMem, Variant.toKind, Kind.changes, Kind.workRegisters, Kind.localChanges]
        · intro address c hc hcover
          simp only [copyChanges, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, prepareEffect, Effect.components, List.map_cons, List.map_nil,
            List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
            List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals try exact hcover.elim
          · refine ⟨.mem (stackPtr s + 120) 168, by simp [Variant.toKind, Kind.changes, Kind.localChanges], ?_⟩
            apply FinalizeReset.Export.covers_shift (offset := 16) (len := 88) (by
              simpa [BitVec.add_assoc] using hcover) (by decide)
          · refine ⟨.mem (stackPtr s + 120) 168, by simp [Variant.toKind, Kind.changes, Kind.localChanges], ?_⟩
            apply FinalizeReset.Export.covers_shift (offset := 8) (len := 8) (by
              simpa [BitVec.add_assoc] using hcover) (by decide)
          · refine ⟨.mem (stackPtr s + 120) 168, by simp [Variant.toKind, Kind.changes, Kind.localChanges], ?_⟩
            obtain ⟨i, hi, he⟩ := hcover
            exact ⟨i, by omega, he⟩
      · rw [hsp]
        exact prepare_result hu.storage he hu.source


end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare
