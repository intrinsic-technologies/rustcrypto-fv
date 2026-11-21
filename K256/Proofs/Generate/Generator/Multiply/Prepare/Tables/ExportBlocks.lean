import K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator.TableCopy
import K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator.Frame

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Tactic K256.Proofs.Generate.LIR

abbrev copySite (first : Bool) : Label := if first then .l11d514 else .l11d535
abbrev copyResume (first : Bool) : Label := if first then .l11d535 else .l11d546
abbrev copyTag (first : Bool) : BitVec 64 := if first then 0x11d535 else 0x11d546
abbrev copySrc (first : Bool) (fr : Activation) := sp fr + (if first then 0x850 else 0x490)
abbrev copyDst (first : Bool) (fr : Activation) := if first then fr.rcx else fr.rcx+960

local macro "export_widths " h:ident " using " nums:Lean.Parser.Tactic.simpLemma : tactic =>
  `(tactic| (
    rintro ⟨j,hj⟩ hm
    have w := $h ⟨j,hj⟩ hm
    simp only [$nums,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with eq|eq|eq|eq|eq|eq <;> change j = _ at eq <;> subst j <;> first | rfl | exact w))

set_option maxRecDepth 8192 in
theorem exportBlock (first : Bool) {fr : Activation} {a : Registers} {m : Ram}
    (rsp : a[4].get 64 = sp fr) (slot : Writable Extracted.programImage m (sp fr-8) 8)
    (widths : ParseSignature.ArgumentWidths a) (saved : SavedWidths a)
    (read : Readable m (sp fr+0xd8) 8) (pointer : memLoad m (sp fr+0xd8) 64 = fr.rcx)
    (fnPtr : first = false → a[3].get 64 = 0x12a820) (tabPtr : first = false → a[5] = ⟨64,fr.rcx⟩)
    (srcPtr : first = false → a[13].get 64 = sp fr+0x490) :
    ∃ b, WindowCall fr (copySite first) .l12a820 (copyResume first) (copyTag first) a b m ∧
      b[3].get 64 = 0x12a820 ∧ b[5] = ⟨64,fr.rcx⟩ ∧ b[2].get 64 = 960 ∧
      b[7].get 64 = copyDst first fr ∧ b[6].get 64 = copySrc first fr ∧
      ∀ j : Fin Reg.count, j.val ∈ [12,13,14,15] → b[j] = a[j] := by
  cases first
  · have target := fnPtr rfl
    have start := congrArg (Value.get 64) (tabPtr rfl)
    change a[5].get 64 = fr.rcx at start
    have src := srcPtr rfl
    have push : StoreOk Extracted.programImage m (sp fr-8) 8 0x11d544 2 := by slot_guard using code_l11d535
    refine ⟨?b,⟨?run,?w,?s,?r,?ctrl⟩,?fnptr,?tab,?cnt,?dst,?src,?keep⟩
    case run =>
      change program.runBlock (dialect Extracted.programImage) ⟨.l11d535,a,m⟩ =
        .call ⟨.l12a820,?b,memStore m (sp fr-8) (0x11d546 : BitVec 64)⟩ (callFrame .l11d546 0x11d546)
      arithmetic_segment using code_l11d535 [rsp,start,src,target,push]
    case r => rfl
    case fnptr => exact target
    case tab => exact tabPtr rfl
    case cnt => rfl
    case dst => rfl
    case src => first | rfl | exact src
    case w => export_widths widths using Activation.argumentNumbers
    case s => export_widths saved using Activation.calleeSavedNumbers
    all_goals
      rintro ⟨j,hj⟩ hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl <;> rfl
  · have push : StoreOk Extracted.programImage m (sp fr-8) 8 0x11d533 2 := by slot_guard using code_l11d514
    have load : LoadOk m (sp fr+0xd8) 8 := LoadOk.of_region read (Nat.le_refl _) (Nat.le_refl _)
    refine ⟨?bTrue,⟨?runTrue,?wTrue,?sTrue,?rTrue,?ctrlTrue⟩,?fnptrTrue,?tabTrue,?cntTrue,?dstTrue,?srcTrue,?keepTrue⟩
    case runTrue =>
      change program.runBlock (dialect Extracted.programImage) ⟨.l11d514,a,m⟩ =
        .call ⟨.l12a820,?bTrue,memStore m (sp fr-8) (0x11d535 : BitVec 64)⟩ (callFrame .l11d535 0x11d535)
      arithmetic_segment using code_l11d514 [rsp,load,pointer,push]
    case rTrue => rfl
    case fnptrTrue => rfl
    case tabTrue => rfl
    case cntTrue => rfl
    case dstTrue => rfl
    case srcTrue => rfl
    case wTrue => export_widths widths using Activation.argumentNumbers
    case sTrue => export_widths saved using Activation.calleeSavedNumbers
    all_goals
      rintro ⟨j,hj⟩ hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
