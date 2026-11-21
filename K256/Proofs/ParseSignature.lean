import K256.Proofs.ParseSignature.Pair
import K256.Proofs.ParseSignature.Serialize
import K256.Proofs.ParseSignature.Wrapper.Entry
import K256.Proofs.ParseSignature.Wrapper.Memory
import K256.Proofs.ParseSignature.Wrapper.Return
import K256.Proofs.ParseSignature.Wrapper.Output
import K256.Proofs.ParseSignature.Wrapper.Words
import K256.Proofs.ParseSignature.Wrapper.Discriminant
import K256.Proofs.Common.SignatureScalars
import K256.Proofs.RejectLength.ErrorPayload

namespace K256.Proofs

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR ParseSignature ParseSignature.Wrapper
open Standards.SECG.DomainParameters

theorem parseSignature
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {bytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signatureFromSlice initial [bytes])
    (hLength : bytes.size = 64) : SignatureSliceResult initial bytes := by
  let fr := pairFrame initial
  let sp := initial.regValue .rsp
  let src := initial.regValue .rsi
  let dst := initial.regValue .rdi
  let base := sp - 88
  obtain ⟨args, entry, resume⟩ := enterPair hCall hLength
  obtain ⟨hr, hw, hi, ho, words⟩ := pairBuffers hCall hLength
  obtain ⟨pair, run, tag, atoms, written, _, post⟩ :=
    decodePair_call Common.fnCode_subset_programImage fr hr hw hi ho args entry
  obtain ⟨stackWrites, saved, ret⟩ := pairWrites hCall written
  have main (final : Output Value Ram Reg.count)
      (cont : program.Exec (dialect Extracted.programImage)
        ⟨⟨.l102468, pair.values, pair.store⟩, []⟩ final) :=
    resume pair final run tag cont
  let r := scalarValue fr.original src
  let s := scalarValue fr.original (src + 32)
  let n := Secp256k1.domain.n
  have er : scalarValue fr.original (src + (0 : BitVec 64)) = scalarValue initial.external (src + 0) :=
    scalarValue_of_inputWords words 0
  have es : s = scalarValue initial.external (src + 32) := scalarValue_of_inputWords words 1
  have er0 : r = scalarValue initial.external src := by
    calc
      r = scalarValue fr.original (src + 0) := congrArg (scalarValue fr.original) (BitVec.add_zero src).symm
      _ = _ := er.trans (congrArg (scalarValue initial.external) (BitVec.add_zero src))
  have model := Common.signatureScalars_of_words hCall hLength
  change Ecdsa.signatureScalars bytes =
    (if 0 < scalarValue initial.external src ∧ scalarValue initial.external src < n ∧
      0 < scalarValue initial.external (src + 32) ∧ scalarValue initial.external (src + 32) < n
      then some (scalarValue initial.external src, scalarValue initial.external (src + 32)) else none) at model
  rw [← er0, ← es] at model
  change Ecdsa.signatureScalars bytes = if 0 < r ∧ r < n ∧ 0 < s ∧ s < n then some (r,s) else none at model
  have dest : fr.rdi = base + 8 := by change sp - 80 = sp - 88 + 8; bv_omega
  change (if 0 < r ∧ r < n ∧ 0 < s ∧ s < n then
    memLoad pair.store fr.rdi 64 = 0 ∧ scalarLimbsAt pair.store (fr.rdi+8) fr.original src ∧
    scalarLimbsAt pair.store (fr.rdi+40) fr.original (src+32)
    else memLoad pair.store fr.rdi 64 = 1 ∧ memLoad pair.store (fr.rdi+8) 64 = 0) at post
  rw [dest] at post
  have h16 : base + 8 + 8 = base + 16 := by rw [BitVec.add_assoc]; rfl
  have h48 : base + 8 + 40 = base + 48 := by rw [BitVec.add_assoc]; rfl
  simp only [h16, h48] at post
  have readBuf : Readable pair.store (base + 8) 72 := by
    rw [← dest]
    exact hw.readable.of_frame written
  have readTag : LoadOk pair.store (base + 8) 4 :=
    LoadOk.of_offsets readBuf (addr_self _) (addr_self _) (by decide)
  let disc := (memLoad pair.store (base + 8) 64).setWidth 32
  let next := pair.values.set 19 (.ofBool (disc == 1))
  change Atom.All _ _ _ (Fn103ac0.doneAt fr) at atoms
  simp only [Fn103ac0.doneAt, Atom.All, Atom.Holds] at atoms
  obtain ⟨csp, cdf, cbx, cbp, c12, c13, c14, c15, _⟩ := atoms
  have spEq : fr.rsp + 8 = base := by change sp - 96 + 8 = sp - 88; bv_omega
  have spNext : next[4] = ⟨64, base⟩ := by
    change (pair.values.set 19 _)[4] = _
    rw [Vector.getElem_set_ne (by decide) (by decide) (by decide : 19 ≠ 4), ← spEq]
    exact csp
  have dstNext : next[3] = ⟨64, dst⟩ := by
    change (pair.values.set 19 _)[3] = _
    rw [Vector.getElem_set_ne (by decide) (by decide) (by decide : 19 ≠ 3)]
    exact cbx
  have kept (i : Fin 53) (hm : i.val ∈ [5, 12, 13, 14, 15, 22]) :
      next[i] = (Reg.ofIndex i).read initial := by
    obtain ⟨i, bound⟩ := i
    change i ∈ [5,12,13,14,15,22] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals change (pair.values.set 19 _)[(_ : Nat)] = _
    all_goals rw [Vector.getElem_set_ne (by decide) (by decide +revert) (by decide +revert)]
    all_goals first | exact cbp | exact c12 | exact c13 | exact c14 | exact c15 |
      exact cdf.trans (Reg.read_df_iff.mpr hCall.directionFlagUnset).symm
  have branch : program.runBlock (dialect Extracted.programImage) ⟨.l102468, pair.values, pair.store⟩ =
      .jump ⟨if disc = 1 then .l1024df else .l10246f, next, pair.store⟩ :=
    resultBranch List.mem_cons_self (spEq ▸ csp) readTag
  by_cases valid : 0 < r ∧ r < n ∧ 0 < s ∧ s < n
  · rw [ite_eq_left valid] at post model
    obtain ⟨htag, first, second⟩ := post
    have hd : disc ≠ 1 := by dsimp only [disc]; rw [htag]; decide
    rw [ite_eq_right hd] at branch
    obtain ⟨_, dstWrite, _, _, _⟩ := Common.signatureBuffers hCall hLength
    have srcRead : Readable pair.store (base + 16) 64 :=
      readBuf.of_offsets (show base + 16 = base + 16 by rfl) rfl (by decide)
    obtain ⟨regs, mem, step, eax, same, stores, copy⟩ :=
      serializeBlock Common.fnCode_subset_programImage spNext dstNext srcRead (dstWrite.of_frame stackWrites)
    obtain ⟨frame, saved', ret'⟩ := afterSerialize hCall hLength stackWrites stores
    let regions := #v[outputRegion signatureFromSlice initial, Stack.region initial signatureFromSlice.minStackBytes]
    obtain ⟨out, doneExec, returned, status, memEq⟩ := finishWrapper (regions := regions) hCall
      ((same 4 (by decide)).trans spNext) eax (fun i h => (same i (.tail 4 h)).trans (kept i h))
      frame (saved'.trans saved) (ret'.trans ret)
    have input : (registerRegion initial .rsi bytes.size).HasBytes initial.external bytes :=
      hCall.inputsInMemory.1.2.2
    have hbytes := Common.hasBytes_of_word_copy (n := 8) input hLength
      ((dstWrite.readable.of_frame stackWrites).of_frame stores) (fun i hi => by
        rw [copy i hi, serializedWords first second hi]
        apply Eq.trans (words i hi)
        change memLoad initial.external (wordAddr src 64 i) 64 =
          memLoad initial.external (wordAddr (BitVec.ofNat 64 src.toNat) 64 i) 64
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    apply Common.signatureSliceAccepted hBindings hMachine hCall (main out ?_) returned status _ model
    · exact .next (congrArg (Transfer.next _ []) branch) (.next (congrArg (Transfer.next _ []) step) doneExec)
    · rw [memEq]
      change (⟨dst.toNat,64⟩ : MemoryRegion).HasBytes mem bytes
      simpa only [hLength] using hbytes
  · rw [ite_eq_right valid] at post model
    have hd : disc = 1 := by dsimp only [disc]; rw [post.1]; rfl
    rw [ite_eq_left hd] at branch
    have readPayload : LoadOk pair.store (base + 16) 8 :=
      LoadOk.of_offsets readBuf (show base + 16 = base + 16 by rfl) rfl (by decide)
    obtain ⟨regs, step, eax, same⟩ :=
      SignatureSlice.emptyErrorBlock (code := Extracted.programImage) spNext readPayload post.2
    let regions := #v[Stack.region initial signatureFromSlice.minStackBytes]
    obtain ⟨out, doneExec, returned, status, _⟩ := finishWrapper (regions := regions) hCall
      ((same 4 (by decide)).trans spNext) eax (fun i h => (same i (.tail 4 h)).trans (kept i h))
      stackWrites saved ret
    apply Common.signatureSliceRejected hBindings hMachine hCall (main out ?_) returned status model
    exact .next (congrArg (Transfer.next _ []) branch) (.next (congrArg (Transfer.next _ []) step) doneExec)

end K256.Proofs
