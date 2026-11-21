import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Additions.Call
import K256.Proofs.Generate.Generator.Multiply.Prepare.Frame

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

local macro "call_widths" h:ident " using " numbers:Lean.Parser.Tactic.simpLemma : tactic =>
  `(tactic| (
    rintro ⟨i, hi⟩ hm
    have w := $h ⟨i, hi⟩ hm
    simp only [$numbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm|hm|hm|hm|hm|hm <;> change i = _ at hm <;> subst i <;> first | rfl | exact w))

local macro "call_preserves" : tactic =>
  `(tactic| (
    rintro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    repeat' (guard_hyp hm : _ ∨ _; rcases hm with hm|hm)
    all_goals change i = _ at hm
    all_goals subst i; rfl))

theorem firstCopyBlock {fr : Activation} {a : Registers} {m : Ram} {table : BitVec 64}
    (rsp : a[4].get 64 = sp fr)
    (slot : Writable Extracted.programImage m (sp fr - 8) 8)
    (widths : ParseSignature.ArgumentWidths a) (saved : SavedWidths a)
    (r13 : a[13].get 64 = table) :
    ∃ b, WindowCall fr .l11d6a6 .l12a820 .l11d6c2 0x11d6c2 a b m ∧
      b[3].get 64 = 0x12a820 ∧ b[14].get 64 = sp fr + 0x850 ∧ b[7].get 64 = sp fr + 0x850 ∧
      b[6].get 64 = table ∧ b[2].get 64 = 960 ∧
      ∀ i : Fin Reg.count, i.val ∈ [5,12,13,15] → b[i] = a[i] := by
  have push : StoreOk Extracted.programImage m (sp fr - 8) 8 0x11d6c0 2 := by
    slot_guard using code_l11d6a6
  refine ⟨?_, ⟨?run, ?widths, ?saved, ?rsp, ?control⟩, ?post⟩
  case run =>
    change program.runBlock (dialect Extracted.programImage) ⟨.l11d6a6,a,m⟩ =
      .call ⟨.l12a820,_,memStore m (sp fr - 8) (0x11d6c2 : BitVec 64)⟩ (callFrame .l11d6c2 0x11d6c2)
    arithmetic_segment using code_l11d6a6 [rsp, push, r13]
  case widths => call_widths widths using Activation.argumentNumbers
  case saved => call_widths saved using Activation.calleeSavedNumbers
  case rsp => rfl
  case control => call_preserves
  case post =>
    exact ⟨rfl, rfl, rfl, rfl, rfl, by call_preserves⟩

theorem secondCopyBlock {fr : Activation} {a : Registers} {m : Ram} {table : BitVec 64}
    (rsp : a[4].get 64 = sp fr)
    (slot : Writable Extracted.programImage m (sp fr - 8) 8)
    (widths : ParseSignature.ArgumentWidths a) (saved : SavedWidths a)
    (r13 : a[13].get 64 = table)
    (r15 : a[15].get 64 = sp fr + 0x490)
    (r3 : a[3].get 64 = 0x12a820) :
    ∃ b, WindowCall fr .l11d6c2 .l12a820 .l11d6d3 0x11d6d3 a b m ∧
      b[7].get 64 = sp fr + 0x490 ∧ b[6].get 64 = table + 960 ∧ b[2].get 64 = 960 ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → b[i] = a[i] := by
  have push : StoreOk Extracted.programImage m (sp fr - 8) 8 0x11d6d1 2 := by
    slot_guard using code_l11d6c2
  refine ⟨?_, ⟨?run, ?widths, ?saved, ?rsp, ?control⟩, ?post⟩
  case run =>
    change program.runBlock (dialect Extracted.programImage) ⟨.l11d6c2,a,m⟩ =
      .call ⟨.l12a820,_,memStore m (sp fr - 8) (0x11d6d3 : BitVec 64)⟩ (callFrame .l11d6d3 0x11d6d3)
    arithmetic_segment using code_l11d6c2 [rsp, push, r13, r15, r3]
  case widths => call_widths widths using Activation.argumentNumbers
  case saved => call_widths saved using Activation.calleeSavedNumbers
  case rsp => rfl
  case control => call_preserves
  case post =>
    exact ⟨rfl, rfl, rfl, by call_preserves⟩

theorem firstLookupBlock {fr : Activation} {a : Registers} {m : Ram} {ptr : BitVec 64} {digit : BitVec 8}
    (rsp : a[4].get 64 = sp fr)
    (slot : Writable Extracted.programImage m (sp fr - 8) 8)
    (widths : ParseSignature.ArgumentWidths a) (saved : SavedWidths a)
    (r5 : a[5].get 64 = 0)
    (r12 : a[12].get 64 = sp fr + 0x1d0)
    (r14 : a[14].get 64 = sp fr + 0x850)
    (ptrLoad : memLoad m (sp fr + 0xf0) 64 = ptr) (localRead : Readable m (sp fr + 0xf0) 8)
    (byteLoad : memLoad m (ptr + 32) 8 = digit) (byteRead : Readable m (ptr + 32) 1) :
    ∃ b, WindowCall fr .l11d6d3 .l11c510 .l11d6eb 0x11d6eb a b m ∧
      b[3].get 64 = ptr ∧ b[7].get 64 = sp fr + 0x1d0 ∧ b[6].get 64 = sp fr + 0x850 ∧
      b[2].get 64 = digit.setWidth 64 ∧
      ∀ i : Fin Reg.count, i.val ∈ [5,12,13,14,15] → b[i] = a[i] := by
  have push : StoreOk Extracted.programImage m (sp fr - 8) 8 0x11d6e6 5 := by
    slot_guard using code_l11d6d3
  refine ⟨?_, ⟨?run, ?widths, ?saved, ?rsp, ?control⟩, ?post⟩
  case run =>
    change program.runBlock (dialect Extracted.programImage) ⟨.l11d6d3,a,m⟩ =
      .call ⟨.l11c510,_,memStore m (sp fr - 8) (0x11d6eb : BitVec 64)⟩ (callFrame .l11d6eb 0x11d6eb)
    arithmetic_segment using code_l11d6d3 [rsp, push, r5, r12, r14, byteLoad, BitVec.add_zero, BitVec.zero_add, ptrLoad]
  case widths => call_widths widths using Activation.argumentNumbers
  case saved => call_widths saved using Activation.calleeSavedNumbers
  case rsp => rfl
  case control => call_preserves
  case post =>
    exact ⟨rfl, rfl, rfl, rfl, by call_preserves⟩

theorem firstAddBlock {fr : Activation} {a : Registers} {m : Ram}
    (rsp : a[4].get 64 = sp fr)
    (slot : Writable Extracted.programImage m (sp fr - 8) 8)
    (widths : ParseSignature.ArgumentWidths a) (saved : SavedWidths a)
    (r12 : a[12].get 64 = sp fr + 0x1d0) :
    ∃ b, WindowCall fr .l11d6eb .l10a410 .l11d6fe 0x11d6fe a b m ∧
      b[14].get 64 = sp fr + 0x128 ∧ b[7].get 64 = sp fr + 0x128 ∧ b[6].get 64 = sp fr + 0x1d0 ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,15] → b[i] = a[i] := by
  have push : StoreOk Extracted.programImage m (sp fr - 8) 8 0x11d6f9 5 := by
    slot_guard using code_l11d6eb
  refine ⟨?_, ⟨?run, ?widths, ?saved, ?rsp, ?control⟩, ?post⟩
  case run =>
    change program.runBlock (dialect Extracted.programImage) ⟨.l11d6eb,a,m⟩ =
      .call ⟨.l10a410,_,memStore m (sp fr - 8) (0x11d6fe : BitVec 64)⟩ (callFrame .l11d6fe 0x11d6fe)
    arithmetic_segment using code_l11d6eb [rsp, push, r12]
  case widths => call_widths widths using Activation.argumentNumbers
  case saved => call_widths saved using Activation.calleeSavedNumbers
  case rsp => rfl
  case control => call_preserves
  case post =>
    exact ⟨rfl, rfl, rfl, by call_preserves⟩

theorem secondLookupBlock {fr : Activation} {a : Registers} {m : Ram} {ptr : BitVec 64} {digit : BitVec 8}
    (rsp : a[4].get 64 = sp fr)
    (slot : Writable Extracted.programImage m (sp fr - 8) 8)
    (widths : ParseSignature.ArgumentWidths a) (saved : SavedWidths a)
    (r5 : a[5].get 64 = 0)
    (r12 : a[12].get 64 = sp fr + 0x1d0)
    (r15 : a[15].get 64 = sp fr + 0x490)
    (r3 : a[3].get 64 = ptr)
    (byteLoad : memLoad m (ptr + 65) 8 = digit) (byteRead : Readable m (ptr + 65) 1) :
    ∃ b, WindowCall fr .l11d6fe .l11c510 .l11d70e 0x11d70e a b m ∧
      b[7].get 64 = sp fr + 0x1d0 ∧ b[6].get 64 = sp fr + 0x490 ∧ b[2].get 64 = digit.setWidth 64 ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → b[i] = a[i] := by
  have push : StoreOk Extracted.programImage m (sp fr - 8) 8 0x11d709 5 := by
    slot_guard using code_l11d6fe
  refine ⟨?_, ⟨?run, ?widths, ?saved, ?rsp, ?control⟩, ?post⟩
  case run =>
    change program.runBlock (dialect Extracted.programImage) ⟨.l11d6fe,a,m⟩ =
      .call ⟨.l11c510,_,memStore m (sp fr - 8) (0x11d70e : BitVec 64)⟩ (callFrame .l11d70e 0x11d70e)
    arithmetic_segment using code_l11d6fe [rsp, push, r5, r12, r15, r3, byteLoad, BitVec.add_zero, BitVec.zero_add]
  case widths => call_widths widths using Activation.argumentNumbers
  case saved => call_widths saved using Activation.calleeSavedNumbers
  case rsp => rfl
  case control => call_preserves
  case post =>
    exact ⟨rfl, rfl, rfl, by call_preserves⟩

theorem secondAddBlock {fr : Activation} {a : Registers} {m : Ram}
    (rsp : a[4].get 64 = sp fr)
    (slot : Writable Extracted.programImage m (sp fr - 8) 8)
    (widths : ParseSignature.ArgumentWidths a) (saved : SavedWidths a)
    (r12 : a[12].get 64 = sp fr + 0x1d0)
    (r14 : a[14].get 64 = sp fr + 0x128) :
    ∃ b, WindowCall fr .l11d70e .l10a410 .l11d719 0x11d719 a b m ∧
      b[7].get 64 = sp fr + 0x128 ∧ b[6].get 64 = sp fr + 0x1d0 ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → b[i] = a[i] := by
  have push : StoreOk Extracted.programImage m (sp fr - 8) 8 0x11d714 5 := by
    slot_guard using code_l11d70e
  refine ⟨?_, ⟨?run, ?widths, ?saved, ?rsp, ?control⟩, ?post⟩
  case run =>
    change program.runBlock (dialect Extracted.programImage) ⟨.l11d70e,a,m⟩ =
      .call ⟨.l10a410,_,memStore m (sp fr - 8) (0x11d719 : BitVec 64)⟩ (callFrame .l11d719 0x11d719)
    arithmetic_segment using code_l11d70e [rsp, push, r12, r14]
  case widths => call_widths widths using Activation.argumentNumbers
  case saved => call_widths saved using Activation.calleeSavedNumbers
  case rsp => rfl
  case control => call_preserves
  case post =>
    exact ⟨rfl, rfl, by call_preserves⟩

end K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator
