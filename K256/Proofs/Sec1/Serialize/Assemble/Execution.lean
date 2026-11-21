import K256.Proofs.Sec1.Serialize.Assemble.Stage
import K256.Proofs.Sec1.Serialize.Assemble.Call
import K256.Proofs.Sec1.Serialize.AssembleChoice
import K256.Proofs.Sec1.Serialize.Control

namespace K256.Proofs.Sec1.Serialize.Assemble

open Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field LIR
open Standards.SECG.ECC Standards.SECG.DomainParameters

theorem uncompressedExecution {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {sp dst point : BitVec 64} {a b : Limbs} {x y : Fin modulus}
    (cover : ∀ entry ∈ fnCode, entry ∈ code)
    (rsp : args[4] = ⟨64, sp⟩) (rbx : args[3] = ⟨64, dst⟩)
    (r14 : args[14] = ⟨64, point⟩) (compress : args[5].get 64 = 0)
    (xs : WordsAt mem (sp + 151) 64 (packWords (Normalize.normalize a)))
    (ys : WordsAt mem (sp + 183) 64 (packWords (Normalize.normalize b)))
    (hx : FieldRepr a x 8) (hy : FieldRepr b y 8)
    (flag : memLoad mem (point + 80) 8 = 0) (pointRead : Readable mem point 88)
    (stack : Writable code mem (sp - 9) 289)
    (room : 9 ≤ sp.toNat) (apart : sp.toNat + 280 ≤ point.toNat) :
    ∃ (regs : Values Value Reg.count) (final : Ram),
      (program.sem (dialect code)).Reaches ⟨⟨.l121692, args, mem⟩, []⟩
        ⟨⟨.l121831, regs, final⟩, []⟩ ∧
      (⟨(sp + 215).toNat, 65⟩ : MemoryRegion).HasBytes final
        (Points.encodePoint Secp256k1.domain false (.affine x.val y.val)) ∧
      regs[0].get 8 = 0 ∧ regs[4] = ⟨64, sp⟩ ∧ regs[3] = ⟨64, dst⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [12,13,22,39,50,51] → regs[i] = args[i]) ∧
      RamWriteFrame mem final [⟨(sp - 9).toNat, 289⟩] := by
  let entry := args.set 19 (.ofBool true)
  let regions : List MemoryRegion := [⟨(sp - 9).toNat, 289⟩]
  have entryKeeps (i : Fin Reg.count) (hi : i.val ≠ 19) : entry[i] = args[i] := by
    change entry[i.val] = args[i.val]
    simp only [entry, Vector.getElem_set, Ne.symm hi, ↓reduceIte]
  have slot {m : Ram} {p offset : BitVec 64} {n : Nat} (h : Writable code m (sp - 9) 289)
      (hp : p = sp + offset) (bound : (offset - (0 - 9)).toNat + n ≤ 289) :
      Writable code m p n :=
    h.of_offsets hp (addr_sub sp 9) bound
  have within {p offset : BitVec 64} {n : Nat} (hp : p = sp + offset)
      (bound : (offset - (0 - 9)).toNat + n ≤ 289) :
      ∃ r ∈ regions, r.start ≤ p.toNat ∧ p.toNat + n ≤ r.start + r.size := by
    have he := toNat_of_offsets hp (addr_sub sp 9) stack.readable.low bound
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change (sp - 9).toNat ≤ p.toNat ∧ p.toNat + n ≤ (sp - 9).toNat + 289
    omega
  have stageWithin : RegionsWithin [⟨(sp + 80).toNat, 32⟩, ⟨(sp + 8).toNat, 32⟩] regions := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact within (n := 32) rfl (by decide)
    · exact within (n := 32) rfl (by decide)
  have buffersWithin : RegionsWithin (assemblyBuffers sp) regions := by
    intro r hr
    simp only [assemblyBuffers, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact within (n := 65) rfl (by decide)
    · exact within (n := 65) rfl (by decide)
  have writesWithin : RegionsWithin (assemblyWrites sp) regions := by
    intro r hr
    rcases List.mem_cons.mp hr with h | h
    · subst r
      exact within (n := 8) (addr_sub sp 8) (by decide)
    · exact buffersWithin r h
  have pointSlot : Readable mem (point + 80) 4 :=
    pointRead.of_offsets rfl (addr_self point) (by decide)
  have pointAddress : (point + 80).toNat = point.toNat + 80 :=
    toNat_of_offsets (n := 4) rfl (addr_self point) pointRead.low (by decide)
  have start : (sp - 9).toNat = sp.toNat - 9 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact room)]
    rfl
  have pointOutside {small : List MemoryRegion} (fit : RegionsWithin small regions)
      {n : Nat} (hn : n ≤ 4) : Outside small (point + 80) n := by
    have hl := pointSlot.low
    refine ⟨by omega, ?_⟩
    intro r hr
    obtain ⟨large, hlarge, _, hend⟩ := fit r hr
    have eq : large = ⟨(sp - 9).toNat, 289⟩ := List.mem_singleton.mp hlarge
    subst large
    change r.start + r.size ≤ (sp - 9).toNat + 289 at hend
    right
    omega
  have branch := uncompressedBranch (code := code) (mem := mem) compress
  have entrySp : entry[4].get 64 = sp := by
    have h : entry[4] = args[4] := entryKeeps 4 (by decide)
    rw [h, rsp, Value.get_mk]
  obtain ⟨staged, m₁, stage, tag, stagedSp, stageKeeps, x₁, y₁, stageFrame⟩ :=
    stageCoordinates cover entrySp (slot stack (addr_sub sp 8) (by decide)) xs ys
  have sp₁ : staged[4].get 64 = sp := by rw [stagedSp, entrySp]
  have point₁ : staged[14].get 64 = point := by
    have h : staged[14] = ⟨64, point⟩ :=
      (stageKeeps 14 (by decide)).trans ((entryKeeps 14 (by decide)).trans r14)
    rw [h, Value.get_mk]
  have stack₁ := stack.of_frame stageFrame
  have flag₁ : memLoad m₁ (point + 80) 8 = 0 :=
    (stageFrame.memLoad_eq (pointOutside stageWithin (n := 1) (by decide))).trans flag
  obtain ⟨next, m₂, call, sp₂, arg, assemblyKeeps, assemblyFrame, ret, tagByte, x₂, y₂, _⟩ :=
    assembleCoordinates cover sp₁ point₁ tag (slot stack₁ (addr_sub sp 8) (by decide))
      (pointSlot.of_frame stageFrame) (pointOutside buffersWithin (by decide)) flag₁ x₁ y₁
  have stack₂ := stack₁.of_frame assemblyFrame
  have scratch : Writable code m₂ (sp - 9) 1 := slot stack₂ (addr_sub sp 9) (by decide)
  have retSlot : Readable m₂ (sp - 8) 8 := (slot stack₂ (addr_sub sp 8) (by decide)).readable
  have encoding : Readable m₂ (sp + 215) 65 := (slot stack₂ rfl (by decide)).readable
  obtain ⟨regs, final, choice, finalSp, zero, choiceKeeps, choiceFrame, bytes⟩ :=
    assembleChoice cover call sp₂ arg scratch retSlot ret hx hy (by decide) tagByte x₂ y₂ encoding
  have choiceWithin : RegionsWithin [⟨(sp - 9).toNat, 1⟩] regions := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact within (n := 1) (addr_sub sp 9) (by decide)
  have frame₁ := (RamWriteFrame.refl mem regions).trans stageFrame stageWithin
  have frame₂ := frame₁.trans assemblyFrame writesWithin
  have frame := frame₂.trans choiceFrame choiceWithin
  refine ⟨regs, final, ?_, bytes, zero, finalSp, ?_, ?_, frame⟩
  · refine .step (b := ⟨⟨.l121702, entry, mem⟩, []⟩) ?_ (.step (b := ⟨⟨.l12176c, staged, m₁⟩, []⟩) ?_ choice)
    · simp only [Program.sem, Program.step, branch, Transfer.next, entry]
    · simp only [Program.sem, Program.step, stage, Transfer.next]
  · exact (choiceKeeps 3 (by decide)).trans ((assemblyKeeps 3 (by decide)).trans
      ((stageKeeps 3 (by decide)).trans ((entryKeeps 3 (by decide)).trans rbx)))
  · intro i hi
    have hs : i.val ∈ [2,3,5,6,8,9,10,11,12,13,14,15,22,39,50,51] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    have hc : i.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    have he : i.val ≠ 19 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
    exact (choiceKeeps i hc).trans ((assemblyKeeps i hs).trans ((stageKeeps i hs).trans (entryKeeps i he)))

end K256.Proofs.Sec1.Serialize.Assemble
