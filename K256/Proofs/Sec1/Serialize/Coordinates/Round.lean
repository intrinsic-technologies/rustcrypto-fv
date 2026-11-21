import K256.Proofs.Sec1.Serialize.Coordinates.NormalizeSetup
import K256.Proofs.Sec1.Serialize.Coordinates.Normalize
import K256.Proofs.Sec1.Serialize.Coordinates.Pack

namespace K256.Proofs.Sec1.Serialize.Coordinates

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR
open K256.Proofs.Common.Field

theorem appendFrames {o m n : Ram} {a b : List MemoryRegion}
    (ha : RamWriteFrame o m a) (hb : RamWriteFrame m n b) :
    RamWriteFrame o n (a ++ b) where
  present i h := hb.present i (ha.present i h)
  outside i hi := (hb.outside i ⟨hi.1, fun r hr => hi.2 r (List.mem_append_right a hr)⟩).trans
    (ha.outside i ⟨hi.1, fun r hr => hi.2 r (List.mem_append_left b hr)⟩)

theorem canonicalValue {v : Value} (h : v.width = 64) : v = ⟨64, v.get 64⟩ := by
  rcases v with ⟨_, v⟩
  cases h
  rfl

theorem round (k : Axis) {code : CodeMap} (cover : ∀ x ∈ fnCode, x ∈ code)
    {args child : Values Value Reg.count} {m written : Ram} {base point dest flag : Word}
    {a : Limbs} (setup : NormalizeSetup k code args m base point dest flag a child written)
    (win : Writable code m (base - 121) 433) (aligned : base.toNat % 16 = 0)
    (textApart : base.toNat + 312 ≤ 0x100000 ∨ 0x12a9bf ≤ (base - 121).toNat)
    (df : args[22] = ⟨1, 0⟩) (w12 : args[12].width = 64) (w13 : args[13].width = 64) :
    ∃ (b : Values Value Reg.count) (m' : Ram), (program.sem (dialect code)).Reaches
        ⟨⟨k.normalizeSite, args, m⟩, []⟩ ⟨⟨k.afterPack, b, m'⟩, []⟩ ∧
      b[4] = ⟨64, base⟩ ∧ b[3] = ⟨64, dest⟩ ∧ b[5] = ⟨64, flag⟩ ∧ b[14] = ⟨64, point⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [12,13,22,39,50,51] → b[i] = args[i]) ∧
      RamWriteFrame written m' (normalizeWrites base ++ packWrites base k) ∧
      WordsAt m' (base + k.offset) 64 (packWords (Normalize.normalize a)) := by
  have writable := win.of_frame setup.frame
  have canonical (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) :
      child[i] = ⟨64, child[i].get 64⟩ := by
    apply canonicalValue
    rcases i with ⟨i, hi'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · exact congrArg Value.width setup.out
    · exact congrArg Value.width setup.flag
    · exact (congrArg Value.width (setup.keeps 12 (by decide))).trans w12
    · exact (congrArg Value.width (setup.keeps 13 (by decide))).trans w13
    · exact congrArg Value.width setup.point
    · exact congrArg Value.width setup.scratch
  obtain ⟨out, run, tag, pop, regs, nf, nw⟩ :=
    normalize setup.rsp setup.src setup.dst ((setup.keeps 22 (by decide)).trans df) canonical
      writable aligned textApart (by cases k <;> decide) setup.slot setup.words
  have pwin : Writable code out.store (base - 8) 320 :=
    (writable.of_frame nf).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  obtain ⟨b, m', packed, h4, kept, pf, words⟩ :=
    pack k cover pop ((regs 15 (by decide)).trans setup.scratch) pwin nw
  have same (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :
      b[i] = child[i] := (kept i hi).trans (regs i hi)
  refine ⟨b, m', (reaches_call setup.run run tag).trans packed, h4,
    (same 3 (by decide)).trans setup.out, (same 5 (by decide)).trans setup.flag,
    (same 14 (by decide)).trans setup.point, ?_, appendFrames nf pf, words⟩
  intro i hi
  apply Eq.trans (same i ?_) (setup.keeps i ?_) <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢ <;> omega

end K256.Proofs.Sec1.Serialize.Coordinates
