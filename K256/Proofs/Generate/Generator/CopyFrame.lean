import K256.Proofs.Generate.Generator.Multiply.Execution
import K256.Proofs.Generate.Generator.Affine.Execution
import K256.Proofs.Generate.Generator.CopyFrame.Memory
import K256.Proofs.Common.Tactic
import K256.Proofs.Common.Encoding
import K256.Proofs.ParseSignature.Call
import K256.Proofs.Generate.Generator.Child
import K256.Proofs.Generate.Generator.Copy

namespace K256.Proofs.Generate.Generator

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

open CopyFrame Standards.SECG.ECC Standards.SECG.DomainParameters

private theorem decodedDraw {random : ByteArray} {d : Nat}
    (draw : K256.Spec.Secp256k1.randomSecret random = some d) :
    0 < d ∧ d < Secp256k1.domain.n ∧
    Keys.publicKey Secp256k1.domain (Encoding.natToOctets 32 d) = some (Curve.generatorWindow d) := by
  obtain ⟨i, _, ok, _⟩ := Sampling.randomSecret_eq_some_iff.mp draw
  let input := random.extract (32 * i) (32 * i + 32)
  change Keys.decodeSecret Secp256k1.domain input = some d at ok
  have h := ok
  dsimp only [Keys.decodeSecret] at h
  split at h
  next good =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at good
    obtain ⟨⟨len, pos⟩, bound⟩ := good
    obtain rfl := Option.some.inj h
    change input.size = 32 at len
    have encoded := Common.Encoding.natToOctets_octetsToNat input
    rw [len] at encoded
    rw [encoded]
    exact ⟨pos, bound, Curve.publicKey_eq_generatorWindow input _ ok⟩
  next => contradiction

private theorem runCall {caller callee : lifted.Location} {resume : Label} {ret : BitVec 64}
    {out : Output Value Ram Reg.count}
    (step : program.runBlock (dialect Extracted.programImage) caller = .call callee (callFrame resume ret))
    (exec : program.Exec (dialect Extracted.programImage) ⟨callee, []⟩ out)
    (tag : out.tag = some ⟨64, ret⟩) (stack : List lifted.StackFrame) :
    Run.Reaches ⟨caller, stack⟩ ⟨⟨resume, out.values, out.store⟩, stack⟩ := by
  apply Star.step (b := ⟨callee, callFrame resume ret :: stack⟩)
  · change program.step _ _ = _
    simp only [Program.step, step, Transfer.next]
  · exact ParseSignature.exec_reaches_resume exec (callFrame resume ret) stack (by
      rw [tag]
      change decide ((⟨64, ret⟩ : Value) = ⟨64, ret⟩) = true
      simp)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 700000 in
theorem copyReady_of_calls
    (multiply : type_of% @Multiply.execution) (affine : type_of% @Affine.execution)
    {s : RamState} {random : ByteArray} {args : Sample.Registers} {mem : Ram} {d : Nat}
    (call : ValidCall signingKeyGenerateFromRng s [random])
    (draw : K256.Spec.Secp256k1.randomSecret random = some d)
    (accepted : Sample.Accepted (activation s) d args mem) :
    let stack := [callFrame .l102539 0x102539]
    ∃ b m, Run.Reaches ⟨⟨.l10607d, args, mem⟩, stack⟩ ⟨⟨.l1060c7, b, m⟩, stack⟩ ∧
      CopyReady s random b m d (Curve.generatorWindow d) := by
  intro stack
  obtain ⟨pos, bound, pub⟩ := decodedDraw draw
  let sp := atDepth s 680
  let mm := mulInput s mem d
  have w0 := Sample.stackFrame call (sampleEntry call) accepted.writes
  obtain ⟨wm, limbs, saved⟩ := mulInput_memory call w0 d
  have ptr : sp - 8 = atDepth s 688 := by dsimp [sp, atDepth]; bv_omega
  have projPtr : sp + 224 = atDepth s 456 := by dsimp [sp, atDepth]; bv_omega
  have affPtr : sp + 136 = atDepth s 544 := by dsimp [sp, atDepth]; bv_omega
  have win : Writable Extracted.programImage mem (sp - 8) 80 := by
    rw [ptr]
    exact (stackWritable (off := 688) call (by decide) (by decide) (by decide)).of_frame w0
  have atoms := accepted.atoms
  simp only [Fn105f30.frameAt, Fn105f30.frameAtG0, Atom.All, Atom.Holds, Fin.getElem_fin] at atoms
  obtain ⟨rsp, df, _, mx, ft, fc, _⟩ := atoms
  have hsp : args[4].get 64 = sp := by
    apply (congrArg (Value.get 64) rsp).trans
    change (s.regValue .rsp - 288) - 392 = s.regValue .rsp - 680
    bv_omega
  have srcWords : WordsAt mem (sp + 40) 64 (scalarWords d) := by
    rw [show sp + 40 = (activation s).rsp - 352 by change (s.regValue .rsp - 680) + 40 = _ - 288 - 352; bv_omega]
    exact accepted.limbs
  obtain ⟨b, step, _, b1, b4, b6, b7, b14, same⟩ := multiplyCall hsp win srcWords
  have regs : ChildRegisters s b := by
    refine ⟨b4.trans (congrArg (Value.mk 64) ptr), (same 22 (by decide)).trans df, ?_, ?_, ?_, ?_⟩
    · rintro ⟨i, hi⟩ hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact congrArg Value.width b1
        | exact congrArg Value.width b6
        | exact congrArg Value.width b7
        | exact congrArg Value.width b14
        | exact (congrArg Value.width (same _ (by simp))).trans (accepted.widths _ (by simp))
    · exact congrArg Value.width ((same 39 (by decide)).trans mx)
    · exact congrArg Value.width ((same 50 (by decide)).trans ft)
    · exact congrArg Value.width ((same 51 (by decide)).trans fc)
  let fr := childActivation s mm b 9768 0x1060b7
  have src : fr.rsi = sp := congrArg (Value.get 64) b6
  have dst : fr.rdi = atDepth s 456 := (congrArg (Value.get 64) b7).trans projPtr
  have saved14 : fr.r14 = sp + 224 := congrArg (Value.get 64) b14
  have hroom : 10584 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  have hlim := call.stackAvailable.1
  change (s.regValue .rsp).toNat - 10584 + ((s.regValue .rsp).toNat + 8 -
    ((s.regValue .rsp).toNat - 10584)) < 2^32 at hlim
  have offset : (atDepth s 688).toNat = (s.regValue .rsp).toNat - 688 := stackOffset (off := 688) call (by decide)
  have high : (atDepth s 688).toNat + 352 ≤ 2^32 := by omega
  obtain ⟨out, run, tag, done_, widths, mulWrites, proj⟩ := multiply (fr := fr) (d := d)
    (childEntryAtoms call wm Fn10ee80.frameInfo rfl (by decide) (by decide) regs (by decide) saved)
    (loaded_of_stackFrame call wm) (by change 9768 ≤ (atDepth s 688).toNat; omega)
    (by change s.regValue .rsp - 10456 = _ - 688 - 9768; bv_omega) high
    (by rw [src]; change _ - 680 = _ - 688 + 8; bv_omega)
    (by rw [dst]; change _ - 456 = _ - 688 + 232; bv_omega)
    (src ▸ ((stackWritable (off := 680) (len := 32) call (by decide) (by decide) (by decide)).of_frame wm).readable)
    (dst ▸ (stackWritable (off := 456) (len := 120) call (by decide) (by decide) (by decide)).of_frame wm)
    (src ▸ limbs) pos bound
  rw [dst] at mulWrites proj
  obtain ⟨wo, wa, affineProj, resume⟩ := affineInput_memory call wm mulWrites proj
  simp only [Fn10ee80.doneAt, Atom.All, Atom.Holds, Fin.getElem_fin] at done_
  obtain ⟨os, odf, o3, o5, o12, o13, o14, o15, omx, oft, ofc, _⟩ := done_
  have os' : (out.values[4]'(by decide)).get 64 = sp := by
    apply (congrArg (Value.get 64) os).trans
    change (s.regValue .rsp - 688) + 8 = _ - 680
    bv_omega
  have o14' : (out.values[14]'(by decide)).get 64 = sp + 224 := (congrArg (Value.get 64) o14).trans saved14
  obtain ⟨c, affineStep, c4, c6, c7, kept⟩ := affineCall os' o14' (by
    rw [ptr]
    exact (stackWritable (off := 688) (len := 8) call (by decide) (by decide) (by decide)).of_frame wo)
  rw [ptr] at affineStep
  let fa := childActivation s (affineInput s out.store) c 976 0x1060c7
  have srcA : fa.rsi = atDepth s 456 := (congrArg (Value.get 64) c6).trans projPtr
  have dstA : fa.rdi = atDepth s 544 := (congrArg (Value.get 64) c7).trans affPtr
  have cregs : ChildRegisters s c := by
    refine ⟨c4.trans (congrArg (Value.mk 64) ptr), (kept 22 (by decide)).trans odf, ?_, ?_, ?_, ?_⟩
    · rintro ⟨i, hi⟩ hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (congrArg Value.width (kept 1 (by decide))).trans (widths 1 (by decide))
      · exact (congrArg Value.width (kept 2 (by decide))).trans (widths 2 (by decide))
      · exact congrArg Value.width ((kept 3 (by decide)).trans o3)
      · exact congrArg Value.width ((kept 5 (by decide)).trans o5)
      · exact congrArg Value.width c6
      · exact congrArg Value.width c7
      · exact (congrArg Value.width (kept 8 (by decide))).trans (widths 8 (by decide))
      · exact (congrArg Value.width (kept 9 (by decide))).trans (widths 9 (by decide))
      · exact congrArg Value.width ((kept 12 (by decide)).trans o12)
      · exact congrArg Value.width ((kept 13 (by decide)).trans o13)
      · exact congrArg Value.width ((kept 14 (by decide)).trans o14)
      · exact congrArg Value.width ((kept 15 (by decide)).trans o15)
    · exact congrArg Value.width ((kept 39 (by decide)).trans omx)
    · exact congrArg Value.width ((kept 50 (by decide)).trans oft)
    · exact congrArg Value.width ((kept 51 (by decide)).trans ofc)
  have affineFrame : RamWriteFrame (affineInput s out.store) (affineInput s out.store) (Affine.writes fa) := by
    slot_state region
  have st : Affine.State .l10fe50 fa c (affineInput s out.store) := by
    refine ⟨childEntryAtoms call wa Fn10fe50.frameInfo rfl (by decide) (by decide) cregs (by decide) resume,
      loaded_of_stackFrame call wa, ?_, ?_, ?_, ?_, high, affineFrame⟩
    · rw [srcA]
      exact ((stackWritable (off := 456) (len := 120) call (by decide) (by decide) (by decide)).of_frame wa).readable
    · rw [dstA]
      exact (stackWritable (off := 544) (len := 88) call (by decide) (by decide) (by decide)).of_frame wa
    · rw [srcA]; change _ - 456 = _ - 688 + 232; bv_omega
    · rw [dstA]; change _ - 544 = _ - 688 + 144; bv_omega
  obtain ⟨final, affineRun, affineTag, affineDone, write, pk⟩ := affine st (srcA ▸ affineProj)
    (Curve.generatorWindow_ne_infinity d pos bound)
  change RamWriteFrame _ _ [fa.region, ⟨fa.rdi.toNat, 88⟩] at write
  rw [dstA] at pk write
  simp only [Fn10fe50.doneAt, Atom.All, Atom.Holds, Fin.getElem_fin] at affineDone
  refine ⟨final.values, final.store, (runCall step run tag stack).trans (runCall affineStep affineRun affineTag stack),
    copyReady call accepted mulWrites write draw pub pk ?_ affineDone.2.1⟩
  exact affineDone.1.trans (congrArg (Value.mk 64) (by change _ - 688 + 8 = _ - 680; bv_omega))

end K256.Proofs.Generate.Generator
