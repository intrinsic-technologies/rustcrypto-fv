import K256.Proofs.ParseSignature.Pair.Frame
import K256.Proofs.ParseSignature.Scalar
import K256.Proofs.ParseSignature.Wrapper.Discriminant

namespace K256.Proofs.ParseSignature.Pair

open Standards.SECG.DomainParameters K256.Proofs.Common X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

theorem runScalar {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (entry resume ok : Label) (ret src : BitVec 64) (regs : Values Value Reg.count) (start : Ram)
    (site : (resume, ok, ret) ∈ [(.l103b07, .l103b12, 0x103b07), (.l103b75, .l103b80, 0x103b75)])
    (call : program.runBlock (dialect code) ⟨entry, args, mem⟩ =
      .call ⟨.l107730, regs, start⟩ (resumeAt resume ret))
    (prepared : ScalarEntry code fr ret src regs start) :
    let valid := scalarValue fr.original src < Secp256k1.domain.n
    ∃ next after, reaches code entry args mem (if valid then ok else .l103c4d) next after ∧
      Active code fr true next after ∧
      (valid → scalarLimbsAt after (sp fr + 16) fr.original src) ∧
      (scalarLimbsAt start (sp fr + 104) fr.original fr.rsi →
        scalarLimbsAt after (sp fr + 104) fr.original fr.rsi) := by
  dsimp only
  let child := scalarChild fr ret regs start
  obtain ⟨_, caller⟩ := prepared.caller
  simp only [Fn103ac0.frameAt, Fn103ac0.frameAtG0, Atom.All, Atom.Holds] at caller
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, savedBx, saved14, retRead, retWord, retLow,
    stackWrite, room, aligned, slotRead₁, slotWord₁, slotRead₂, slotWord₂,
    slotRead₃, slotWord₃, apart, _⟩ := caller
  change fr.low.toNat + 560 ≤ fr.rsp.toNat at room
  have limit := retRead.low
  have spNat : (sp fr).toNat = fr.rsp.toNat - 184 := stackSub_toNat room 184 (by decide)
  have addrNat (k : Nat) (hk : k ≤ 184) :
      (sp fr + BitVec.ofNat 64 k).toNat = fr.rsp.toNat - 184 + k := by
    rw [BitVec.toNat_add, spNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have bottom : (fr.rsp - 560).toNat = fr.rsp.toNat - 560 := stackSub_toNat room 560 (by decide)
  have childRsp : (fr.rsp - 192).toNat = fr.rsp.toNat - 192 := stackSub_toNat room 192 (by decide)
  have destNat : (sp fr + 8).toNat = fr.rsp.toNat - 184 + 8 := addrNat 8 (by decide)
  have blockWrite (k n : Nat) (hk : k + n ≤ 184) :
      Writable code start (sp fr + BitVec.ofNat 64 k) n :=
    stackWrite.sub (by rw [bottom, addrNat k (by omega)]; omega)
      (by rw [bottom, addrNat k (by omega)]; omega)
  have aboveChild (k n : Nat) (hk : k + n ≤ 184) :
      Outside [callStack child] (sp fr + BitVec.ofNat 64 k) n := by
    simp only [Outside, List.mem_singleton, forall_eq, callStack, child,
      bottom, childRsp, addrNat k (by omega)]
    omega
  obtain ⟨out, run, tag, doneAtoms, writes, widths, post⟩ :=
    decode_call hcode child rfl (blockWrite 72 32 (by decide)).readable
      (blockWrite 8 40 (by decide)) (aboveChild 72 32 (by decide))
      (aboveChild 8 40 (by decide)) regs prepared.atoms
  change RamWriteFrame start out.store [child.region, buffer (sp fr + 8) 40] at writes
  have withinFrame : RegionsWithin [child.region, buffer (sp fr + 8) 40] [fr.region] := by
    intro r hr
    refine ⟨fr.region, .head _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      simp only [child, Activation.region, buffer, bottom, childRsp, destNat] <;> omega
  have unchanged {addr : BitVec 64}
      (hapart : addr.toNat + 8 ≤ fr.rsp.toNat - 560 ∨
        fr.rsp.toNat - 184 + 48 ≤ addr.toNat) (hlim : addr.toNat + 8 ≤ 2^64) :
      memLoad out.store addr 64 = memLoad start addr 64 := by
    apply writes.memLoad_eq
    simp only [Outside, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Nat.reduceDiv, child, Activation.region, bottom, childRsp, buffer, destNat]
    omega
  have saved (k : Nat) (hk : k ≤ 16) :
      memLoad out.store (fr.rsp - BitVec.ofNat 64 k) 64 =
        memLoad start (fr.rsp - BitVec.ofNat 64 k) 64 :=
    unchanged (by rw [stackSub_toNat room k (by omega)]; omega) (by rw [stackSub_toNat room k (by omega)]; omega)
  have slot {a : BitVec 64} (hl : 0x203dd0 ≤ a.toNat) (hh : a.toNat + 8 ≤ 0x203e28) :
      memLoad out.store a 64 = memLoad start a 64 := unchanged (by omega) (by omega)
  have oldRet : memLoad out.store fr.rsp 64 = fr.ret :=
    (unchanged (by omega) (by omega)).trans retWord
  have valueEq : scalarValue start (sp fr + 72) = scalarValue fr.original src := by
    simp only [scalarValue, prepared.words 0 (by decide), prepared.words 1 (by decide),
      prepared.words 2 (by decide), prepared.words 3 (by decide)]
  change (if scalarValue start (sp fr + 72) < Secp256k1.domain.n then
    memLoad out.store (sp fr + 8) 64 = 0 ∧ scalarLimbsAt out.store (sp fr + 8 + 8) start (sp fr + 72)
    else memLoad out.store (sp fr + 8) 64 = 1) at post
  rw [valueEq] at post
  change Atom.All code out.values out.store (Fn107730.doneAt child) at doneAtoms
  simp only [Fn107730.doneAt, Atom.All, Atom.Holds] at doneAtoms
  obtain ⟨rsp, df, bx, bp, r12, r13, r14, r15, mx, ftw, fcw, _⟩ := doneAtoms
  have hsp : out.values[4] = ⟨64, sp fr⟩ := by
    change out.values[4] = ⟨64, fr.rsp - 192 + 8⟩ at rsp
    rwa [show fr.rsp - 192 + 8 = sp fr by unfold sp; bv_omega] at rsp
  have toBranch : reaches code entry args mem resume out.values out.store :=
    reachesOfCall call run tag
  let flag := Value.ofBool ((memLoad out.store (sp fr + 8) 64).setWidth 32 == 1)
  let next := out.values.set 19 flag
  have reg (i : Fin Reg.count) (hi : 19 ≠ i.val) : next[i.val] = out.values[i.val] :=
    Vector.getElem_set_ne _ _ hi
  have site' : (resume, ok, Label.l103c4d) ∈ [(.l102468, .l10246f, .l1024df),
      (.l103b07, .l103b12, .l103c4d), (.l103b75, .l103b80, .l103c4d)] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at site ⊢
    grind
  have bread : LoadOk out.store (sp fr + 8) 4 := by
    apply LoadOk.of_region ((blockWrite 8 40 (by decide)).of_frame writes).readable (Nat.le_refl _)
    exact Nat.add_le_add_left (by decide : 4 ≤ 40) _
  have jump := resultBranch (code := code) site' hsp bread
  dsimp only at jump
  have target :
      (if (memLoad out.store (sp fr + 8) 64).setWidth 32 = 1 then Label.l103c4d else ok) =
        (if scalarValue fr.original src < Secp256k1.domain.n then ok else .l103c4d) := by
    split at post
    next h => rw [post.1, ite_eq_left h]; rfl
    next h => rw [post, ite_eq_right h]; rfl
  rw [target] at jump
  refine ⟨next, out.store, toBranch.tail ?_, ⟨?_, prepared.writes.trans writes withinFrame, ?_⟩, ?_, ?_⟩
  · change program.step (dialect code) _ = _
    simp only [Program.step, jump, Transfer.next, next, flag]
  · change Atom.All code next out.store (Fn103ac0.frameAt .l103b07 fr)
    simp only [Fn103ac0.frameAt, Fn103ac0.frameAtG0, Atom.All, Atom.Holds]
    exact ⟨(reg 4 (by decide)).trans hsp,
      (reg 22 (by decide)).trans df,
      (reg 3 (by decide)).trans bx,
      (reg 5 (by decide)).trans bp,
      (reg 12 (by decide)).trans r12,
      (reg 13 (by decide)).trans r13,
      (reg 14 (by decide)).trans r14,
      (reg 15 (by decide)).trans r15,
      (reg 39 (by decide)).trans mx,
      (reg 50 (by decide)).trans ftw,
      (reg 51 (by decide)).trans fcw, (saved 16 (by decide)).trans savedBx,
      (saved 8 (by decide)).trans saved14, retRead.of_frame writes, oldRet, retLow,
      stackWrite.of_frame writes, room, aligned, slotRead₁.of_frame writes,
      (slot (by decide) (by decide)).trans slotWord₁, slotRead₂.of_frame writes,
      (slot (by decide) (by decide)).trans slotWord₂, slotRead₃.of_frame writes,
      (slot (by decide) (by decide)).trans slotWord₃, apart, trivial⟩
  · intro i hi
    have ne : i.val ≠ 19 := by
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
    exact (congrArg Value.width (reg i ne.symm)).trans (widths i hi)
  · intro h i hi
    rw [ite_eq_left h] at post
    rw [← prepared.words i hi]
    have offset : sp fr + 8 + 8 = sp fr + 16 := by rw [BitVec.add_assoc]; rfl
    rw [← offset]
    exact post.2 i hi
  · intro h i hi
    have nat : (wordAddr (sp fr + 104) 64 i).toNat = fr.rsp.toNat - 184 + (104 + 8 * i) := by
      unfold wordAddr
      rw [show 64 / 8 = 8 by decide, BitVec.add_assoc]
      have eqn := addrNat (104 + 8 * i) (by omega)
      rw [BitVec.ofNat_add] at eqn
      exact eqn
    exact (unchanged (by rw [nat]; omega) (by rw [nat]; omega)).trans (h i hi)

end K256.Proofs.ParseSignature.Pair
