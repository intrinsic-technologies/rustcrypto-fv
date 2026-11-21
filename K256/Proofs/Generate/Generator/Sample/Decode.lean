import K256.Proofs.Generate.Generator.Sample.Decode.Prepare
import K256.Proofs.Generate.Generator.Sample.Decode.Scalar
import K256.Proofs.Generate.Generator.Sample.Memory
import K256.Proofs.Generate.Generator.Activation
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

theorem decode {s : RamState} {random : ByteArray} {fr : Activation} {a : Registers}
    (call : ValidCall signingKeyGenerateFromRng s [random]) (entry : Entry s fr a) {i : Nat}
    {b : Registers} {mem : Ram} (bound : i < random.size / 32)
    (current : AtBlock s random fr i b mem) (stack : List (StackFrame Value Label signature Reg.count)) :
    ∃ c m, Run.Reaches ⟨⟨.l106020, b, mem⟩, stack⟩ ⟨⟨.l10605d, c, m⟩, stack⟩ ∧
      AfterDecode s random fr i c m := by
  obtain ⟨c, m, push, atoms, prep, words⟩ := prepareDecode call entry bound current
  let child := decodeActivation fr s random i c m
  have caller := current.atoms
  simp only [Fn105f30.frameAt, Fn105f30.frameAtG0, Atom.All, Atom.Holds] at caller
  obtain ⟨_, _, _, _, _, _, savedOut, savedBx, saved12, saved13, saved14, saved15, savedBp,
    readRet, callerRet, retLow, window, room, align, _, _, _, _, apart, _⟩ := caller
  have top := readRet.low
  have off (k : Nat) (hk : k ≤ 10168) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have reduced : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, reduced]; omega), reduced]
  have off10168 : (fr.rsp - 10168).toNat = fr.rsp.toNat - 10168 := off 10168 (by decide)
  have off465 : (fr.rsp - 465).toNat = fr.rsp.toNat - 465 := off 465 (by decide)
  have off400 : (fr.rsp - 400).toNat = fr.rsp.toNat - 400 := off 400 (by decide)
  have off288 : (fr.rsp - 288).toNat = fr.rsp.toNat - 288 := off 288 (by decide)
  have off168 : (fr.rsp - 168).toNat = fr.rsp.toNat - 168 := off 168 (by decide)
  have subwindow (k n : Nat) (hk : k ≤ 10168) (hn : n ≤ k) :
      Writable Extracted.programImage m (fr.rsp - BitVec.ofNat 64 k) n := by
    apply (window.of_frame prep).sub
    · rw [off10168, off k hk]; omega
    · rw [off10168, off k hk]; omega
  have aboveChild (k n : Nat) (hk : k ≤ 392) (hn : n ≤ k) :
      Outside [ParseSignature.callStack child] (fr.rsp - BitVec.ofNat 64 k) n := by
    simp only [Outside, ParseSignature.callStack, child, decodeActivation, List.mem_singleton,
      forall_eq, off465, off400, off k (by omega)]
    omega
  obtain ⟨out, run, tag, doneAtoms, callee, widths, limbs, flag⟩ :=
    decodeScalar child (subwindow 288 32 (by decide) (by decide)).readable
      (subwindow 168 33 (by decide) (by decide)) (aboveChild 288 32 (by decide) (by decide))
      (aboveChild 168 33 (by decide) (by decide)) c atoms
  let postRegions := [child.region, ⟨child.rdi.toNat,33⟩]
  have lowEnough : fr.low.toNat + 10168 ≤ fr.rsp.toNat := room
  have inFrame (k n : Nat) (hk : k ≤ 10168) (hn : n ≤ k) :
      fr.region.start ≤ (fr.rsp - BitVec.ofNat 64 k).toNat ∧
      (fr.rsp - BitVec.ofNat 64 k).toNat + n ≤ fr.region.start + fr.region.size := by
    simp only [Activation.region, off k hk]; omega
  have prepWithin : RegionsWithin (prepareRegions fr) (regions fr) := by
    intro r hr
    simp only [prepareRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, .head _, inFrame 400 8 (by decide) (by decide)⟩
    · exact ⟨_, .head _, inFrame 288 32 (by decide) (by decide)⟩
    · exact ⟨_, .tail _ (.head _), Nat.le_refl _, Nat.le_refl _⟩
  have childWithin : RegionsWithin postRegions (regions fr) := by
    intro r hr
    simp only [postRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨_, .head _, ?_⟩
      simp only [Activation.region, child, decodeActivation, off465, off400]
      omega
    · exact ⟨_, .head _, inFrame 168 33 (by decide) (by decide)⟩
  have writes := (current.writes.trans prep prepWithin).trans callee childWithin
  have descriptor : fr.rsp.toNat + 80 = fr.rsi.toNat := by
    rw [entry.rsp, entry.descriptor]
    change (stackPtr s - 288).toNat + 80 = (stackPtr s - 208).toNat
    have sp : (stackPtr s - 288).toNat = (stackPtr s).toNat - 288 := stackOffset (off := 288) call (by decide)
    have desc : (stackPtr s - 208).toNat = (stackPtr s).toNat - 208 := stackOffset (off := 208) call (by decide)
    rw [sp, desc]
    have : 10584 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
    omega
  have saved (k : Nat) (hk : k ≤ 48 ∨ k = 360) :
      memLoad out.store (fr.rsp - BitVec.ofNat 64 k) 64 =
        memLoad mem (fr.rsp - BitVec.ofNat 64 k) 64 := by
    change RamWriteFrame m out.store postRegions at callee
    rw [callee.memLoad_eq, prep.memLoad_eq]
    all_goals
      simp only [prepareRegions, postRegions, Outside, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, child, decodeActivation, Activation.region,
        off465, off400, off288,
        off168, off k (by omega), Nat.reduceDiv]
      omega
  have slot := Fn105f30.callSlots_loaded
    (show rodataSection ∈ Extracted.programSections by simp [rodataSection, Extracted.programSections])
    (loaded_of_stackFrame call (stackFrame call entry writes))
  obtain ⟨read1, val1⟩ := slot (0x203de0, 0x129770) (by decide)
  obtain ⟨read2, val2⟩ := slot (0x203e20, 0x100a20) (by decide)
  change Atom.All _ _ _ (Fn109e60.doneAt child) at doneAtoms
  simp only [Fn109e60.doneAt, child, decodeActivation, Atom.All, Atom.Holds] at doneAtoms
  obtain ⟨osp, df, bx, bp, r12, r13, r14, r15, mx, ftw, fcw, _⟩ := doneAtoms
  refine ⟨out.values, out.store, ?_, ⟨⟨?_, writes⟩, widths 2 (by decide),
    widths 8 (by decide), widths 9 (by decide), bp, r13, bx, r12, r15, ?_, ?_⟩⟩
  · let resume := callFrame .l10605d 0x10605d
    refine .step (b := ⟨⟨.l109e60, c, m⟩, resume :: stack⟩) ?_ ?_
    · change (program.runBlock (dialect Extracted.programImage) _).next _ _ = _
      rw [push]
      rfl
    · have accepts : resume.Accepts (dialect Extracted.programImage) out.tag = true := by
        rw [tag]
        rfl
      have back := ParseSignature.exec_reaches_resume run resume stack accepts
      have ar := ParseSignature.resume_arguments resume out
      have resumed : resume.resume out = ⟨.l10605d, out.values, out.store⟩ := by
        change Location.mk Label.l10605d (resume.resume out).arguments out.store = _
        rw [ar]
      rw [resumed] at back
      exact back
  · simp only [Fn105f30.frameAt, Fn105f30.frameAtG0, Atom.All, Atom.Holds]
    have oldRet := saved 0 (by decide)
    change memLoad out.store (fr.rsp - 0) 64 = memLoad mem (fr.rsp - 0) 64 at oldRet
    rw [show fr.rsp - 0 = fr.rsp by bv_omega] at oldRet
    refine ⟨?_, df, r14, mx, ftw, fcw, (saved 360 (by decide)).trans savedOut,
      (saved 48 (by decide)).trans savedBx, (saved 40 (by decide)).trans saved12,
      (saved 32 (by decide)).trans saved13, (saved 24 (by decide)).trans saved14,
      (saved 16 (by decide)).trans saved15, (saved 8 (by decide)).trans savedBp,
      (readRet.of_frame prep).of_frame callee, oldRet.trans callerRet, retLow,
      (window.of_frame prep).of_frame callee, room, align, read1, val1, read2, val2, apart, trivial⟩
    rw [osp, show fr.rsp - 400 + 8 = fr.rsp - 392 by bv_omega]
  · intro j hj
    have value := limbs j hj
    simp only [Vector.getElem_ofFn] at value ⊢
    exact value.trans (words j hj)
  · change memLoad out.store (fr.rsp - 168 + 32) 8 = _ at flag
    rw [show fr.rsp - 168 + 32 = fr.rsp - 136 by bv_omega] at flag
    simpa only [child, decodeActivation, words 0 (by decide), words 1 (by decide),
      words 2 (by decide), words 3 (by decide)] using flag

end K256.Proofs.Generate.Generator.Sample
