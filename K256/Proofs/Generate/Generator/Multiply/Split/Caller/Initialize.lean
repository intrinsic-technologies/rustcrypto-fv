import K256.Proofs.Generate.Generator.Multiply.Split.Caller.Sites
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Resume.Flag

namespace K256.Proofs.Generate.Generator.Multiply.Split.Caller

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem enterFirstCall {fr : Activation} {a b : Registers} {m : Ram} {d : Nat}
    (entry : CoreEntry fr a d) (atoms : Atom.All Extracted.programImage b m (Fn11c880.frameAt .l11c8d2 fr))
    (count : b[6] = ⟨64, 1⟩) (frame : RamWriteFrame fr.original m [fr.region]) :
    ∃ a₁ m₁ a₂ m₂, Reaches .l11c8d2 b m .l11c920 a₁ m₁ ∧
      program.runBlock (dialect Extracted.programImage) ⟨.l11c920,a₁,m₁⟩ =
        .call ⟨.l11b8f0,a₂,m₂⟩ (callFrame .l11c95d 0x11c95d) ∧
      CallRegisters (Site.roundFirst.child fr b) a₂ ∧
      memLoad m₂ (sp fr - 8) 64 = 0x11c95d ∧
      RamWriteFrame fr.original m₂ [fr.region] ∧ LocalsAt fr m₂ := by
  simp only [Fn11c880.frameAt, Fn11c880.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨rs, df, cx, dx, bx, _, _, r8, r9, _, r13, r14, _, mx, ftw, fcw,
    pair, digits, tables, pairs, table, output, savedBx, saved12, saved13, saved14,
    saved15, savedBp, _, _, _, writable, _, _, _, _, _, _, _, _⟩ := atoms
  have g4 : b[4].get 64 = fr.rsp - 0xcb8 := congrArg (Value.get 64) rs
  have g1 : b[1].get 64 = fr.rcx := congrArg (Value.get 64) cx
  have g2 : b[2].get 64 = 1 := (congrArg (Value.get 64) dx).trans entry.pairCount
  have g6 : b[6].get 64 = 1 := congrArg (Value.get 64) count
  have g8 : b[8].get 64 = 1 := (congrArg (Value.get 64) r8).trans entry.tableCount
  have g14 : b[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have pairCount := entry.pairCount
  have tableCount := entry.tableCount
  have high := entry.high
  have room := entry.room
  have regionLow := entry.low
  refine ⟨?_, ?_, ?_, ?_, ?jump, ?call, ?regs, ?returnWord, ?frameAfter, ?locals⟩
  case jump =>
    have run : program.runBlock (dialect Extracted.programImage) ⟨.l11c8d2, b, m⟩ =
        .jump ⟨.l11c920, ?_, ?_⟩ := by
      arithmetic_segment using code_l11c8d2 [g4, g1, g2, g6, g8, g14,
        Lift.reduceAddOffset, Lift.reduceSubOffset, Lift.reduceAddNeg, Lift.reduceSubNeg,
        BitVec.reduceAdd, BitVec.reduceSub]
    refine .step (b := ⟨⟨.l11c920, _, _⟩, []⟩) ?_ (Star.refl _)
    simp only [Program.sem, Program.step, run, Transfer.next] <;> rfl
  case call =>
    arithmetic_segment using code_l11c920 [g4, g1, g2, g6, g8, g14, pair,
      Lift.reduceAddOffset, Lift.reduceSubOffset, Lift.reduceAddNeg, Lift.reduceSubNeg,
      BitVec.reduceAdd, BitVec.reduceSub]
  case regs =>
    have dest : Value.mk 64 (fr.rsp - 2960) = Value.mk 64 (sp fr + 0x128) := by
      apply congrArg (Value.mk 64)
      dsimp only [sp]
      bv_omega
    have wide {v : Value} {x : BitVec 64} (h : v = ⟨64, x⟩) : v = ⟨64, v.get 64⟩ :=
      h.trans (congrArg (fun w : Value => Value.mk 64 (w.get 64)) h).symm
    refine ⟨?_, df, rfl, rfl, bx, rfl, rfl, dest, wide r8, wide r9, dest, r13, rfl, ?_, mx, ftw, fcw⟩
    · change Value.mk 64 (fr.rsp - 3264) = Value.mk 64 (sp fr - 8)
      apply congrArg (Value.mk 64)
      dsimp only [sp]
      bv_omega
    · change Value.mk 64 (fr.rsp - 2792) = Value.mk 64 (sp fr + 0x1d0)
      apply congrArg (Value.mk 64)
      dsimp only [sp]
      bv_omega
  case returnWord =>
    refine_norm [sp]
  case frameAfter =>
    refine frame.trans (regions' := [fr.region]) ?_ (fun r h => ⟨r, h, Nat.le_refl _, Nat.le_refl _⟩)
    simp only [Activation.region, regionLow]
    slot_state region
  case locals =>
    intro kv h
    simp only [locals, savedSlots, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine_norm [sp, pair, digits, tables, pairs, table, output, savedBx, saved12, saved13,
        saved14, saved15, savedBp, pairCount, tableCount]

end K256.Proofs.Generate.Generator.Multiply.Split.Caller
