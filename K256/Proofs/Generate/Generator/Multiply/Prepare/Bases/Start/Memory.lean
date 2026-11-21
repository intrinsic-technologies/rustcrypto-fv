import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Frame
import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Dispatch

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

namespace Start

theorem initialContext {fr : Activation} {a initial : Registers} {m : Ram} {d : Nat}
    (e : CoreEntry fr initial d) (s : SplitState fr a m d) : Context fr a m := by
  refine ⟨s.atoms,s.widths,s.savedWidths,s.frame,?_⟩
  intro kv hk
  change kv ∈ [(0x8,0),(0x38,fr.rsi),(0x60,66),(0x68,152),(0x88,152),(0xb0,fr.rsi),(0xc0,0),(0xd8,fr.rcx),(0xf0,fr.r9),(0x100,1),(0x1a0,1),(0x1c0,fr.rcx),(0x248,fr.rdi)] ++ [(0xcc0,1)] at hk
  rcases List.mem_append.mp hk with h | h
  · exact s.locals kv h
  · obtain rfl := List.mem_singleton.mp h
    have addr : sp fr + 0xcc0 = fr.rsp + 8 := by unfold sp; bv_omega
    change memLoad m (sp fr + 0xcc0) 64 = 1
    rw [addr]
    apply (s.frame.memLoad_eq ?_).trans e.digitCount
    have high := e.high
    have h := Split.Caller.lowNat e
    have := e.room
    refine ⟨by bv_omega,?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right; dsimp only [Activation.region]; bv_omega

abbrev memory (fr : Activation) (m : Ram) (d : Nat) :=
  stageEndomorphism m (sp fr) (v d)

abbrev callee (fr : Activation) (b : Registers) (m : Ram) (d : Nat) :=
  child fr b (memory fr m d) 0x11ca7f

abbrev spans : Spans := [(0x1f0,32),(0x40,8),(0x10,8),(0x28,8),(0x2b0,120)]

set_option maxRecDepth 4096 in
theorem stagedFrame {fr : Activation} {initial : Registers} {d : Nat} (e : CoreEntry fr initial d)
    (m : Ram) (v : Vector (BitVec 64) 4) :
    RamWriteFrame m (stageEndomorphism m (sp fr) v) (writes fr spans) := by
  unfold stageEndomorphism
  refine RamWriteFrame.memStore ?_ _ (inBelow e spans (i := 8) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := spans) (i := 40) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := spans) (i := 16) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := spans) (i := 64) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := spans) (i := 496) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := spans) (i := 504) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := spans) (i := 512) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (inSlot e (xs := spans) (i := 520) (size := 8) (by decide) (by decide))
  exact RamWriteFrame.refl _ _

private theorem stagedSlotValues (m : Ram) (fr : Activation) (d : Nat) :
    Locals fr (stageEndomorphism m (sp fr) (v d)) [(0x40,(v d)[1]),(0x10,(v d)[2]),(0x28,(v d)[3])] := by
  intro kv hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl
  all_goals segment_words [stageEndomorphism]

theorem restoredSlots {fr : Activation} {initial : Registers} {m n : Ram} {d : Nat}
    (e : CoreEntry fr initial d)
    (post : RamWriteFrame (stageEndomorphism m (sp fr) (v d)) n
      [⟨(sp fr-8).toNat-128,128⟩,⟨(sp fr+0x2b0).toNat,120⟩]) :
    Locals fr n [(0x40,(v d)[1]),(0x10,(v d)[2]),(0x28,(v d)[3])] := by
  let xs : Spans := [(0x2b0,120)]
  have rel : RamWriteFrame (stageEndomorphism m (sp fr) (v d)) n (writes fr xs) :=
    (RamWriteFrame.refl _ _).trans post (childWithin e (i := 0x2b0) (size := 120) (depth := 128)
      (by decide) (by decide) (by decide))
  apply (stagedSlotValues m fr d).of_frame rel
  intro kv hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl
  · exact outside e xs (i := 64) (n := 8) (by decide) (by decide)
  · exact outside e xs (i := 16) (n := 8) (by decide) (by decide)
  · exact outside e xs (i := 40) (n := 8) (by decide) (by decide)

theorem callerWindow {fr : Activation} {initial : Registers} {d : Nat} {m : Ram}
    (e : CoreEntry fr initial d) (frame : RamWriteFrame fr.original m [fr.region]) :
    Writable Extracted.programImage m (sp fr - 8) 0x440 := by
  have window := (Split.Caller.stackAccess e frame).stack
  have := e.room
  have lo := Split.Caller.lowNat e
  have top := Split.Caller.spNat e
  change (sp fr).toNat = fr.rsp.toNat - 3256 at top
  have push := Split.Caller.pushNat e
  change (sp fr - 8).toNat = (sp fr).toNat - 8 at push
  rw [← e.low] at window
  exact window.sub (by omega) (by omega)

theorem memoryFrame {fr : Activation} {initial : Registers} {d : Nat} {m : Ram}
    (e : CoreEntry fr initial d) (frame : RamWriteFrame fr.original m [fr.region]) :
    RamWriteFrame fr.original (memory fr m d) [fr.region] :=
  frame.trans (stagedFrame e m (v d)) (within e (by decide))

end Start

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
