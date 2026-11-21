import K256.Proofs.ParseSignature.Pair.Nonzero.Frame
import X86Proofs.Program.Compose

namespace K256.Proofs.ParseSignature.Pair

open K256.Proofs.Common Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

private theorem callWithZeroMask {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    {args : Values Value Reg.count} {mem : Ram} {stack : BitVec 64} (second zero : Bool)
    (rsp : args[4] = ⟨64, stack⟩) (writable : Writable code mem (stack - 8) 8)
    (widths : ArgumentWidths args) (value : args[0].get 8 = if zero then 1 else 0) :
    let ret : BitVec 64 := if second then 0x103c49 else 0x103bfb
    ∃ regs, program.runBlock (dialect code) ⟨if second then .l103c3f else .l103bf1, args, mem⟩ =
        .call ⟨.l127d50, regs, memStore mem (stack - 8) ret⟩
          (resumeAt (if second then .l103c49 else .l103bfb) ret) ∧
      regs[7] = ⟨64, if zero then 1 else 0⟩ ∧ regs[4] = ⟨64, stack - 8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] → regs[i] = args[i]) ∧
      ArgumentWidths regs := by
  have stackBits : args[4].get 64 = stack := congrArg (Value.get 64) rsp
  have lowByte : (args[0].get 64).setWidth 8 = args[0].get 8 := by
    exact BitVec.setWidth_setWidth_of_le _ (by decide)
  have mask : ((args[0].get 64).setWidth 8 &&& 1).setWidth 64 = if zero then 1 else 0 := by
    rw [lowByte, value]
    cases zero <;> rfl
  have pushFirst : StoreOk code mem (stack - 8) 8 0x103bf6 5 :=
    storeOk_of_codeRange (off := 5) writable (fun x hx => hcode x (code_l103bf1 x hx)) (by decide)
  have pushSecond : StoreOk code mem (stack - 8) 8 0x103c44 5 :=
    storeOk_of_codeRange (off := 5) writable (fun x hx => hcode x (code_l103c3f x hx)) (by decide)
  cases second
  all_goals
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · cfg_eval [stackBits, pushFirst, pushSecond]
      rfl
    · refine ⟨?_, rfl, ?_, ?_⟩
      · change Value.mk 64 ((mergeGPR 8 ((args[0].get 64).setWidth 8 &&& 1)
          (args[0].get 64)).setWidth 8 |>.setWidth 64) = _
        rw [setWidth_mergeGPR8, mask]
      · intro ⟨i, bound⟩ hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · intro ⟨i, bound⟩ hi
        have width := widths ⟨i, bound⟩ hi
        simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact width

private theorem jumpOnZeroMask {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    (second zero : Bool) (mask : args[0] = ⟨64, if zero then 1 else 0⟩) :
    program.runBlock (dialect code) ⟨if second then .l103c49 else .l103bfb, args, mem⟩ =
      .jump ⟨if zero then .l103c4d else if second then .l103c6a else .l103bff,
        args.set 19 (.ofBool (!zero)), mem⟩ := by
  let al := (args[0].get 64).setWidth 8
  have flag : (testFlags (al &&& al)).ZF.getD false = !zero := by
    dsimp only [al]
    rw [mask]
    cases zero <;> rfl
  cases second <;> cfg_eval <;> rw [flag] <;> cases zero <;>
    simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;>
    congr 2 <;>
    apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
      fun h => Vector.ext fun i hi => h ⟨i, hi⟩) <;>
    intro i <;> finite_cases i <;> simp only [Vector.getElem_set] <;> rfl

theorem branchOnZero {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (second zero : Bool)
    (active : Active code fr false args mem) (limbs : pairLimbs fr mem)
    (value : args[0].get 8 = if zero then 1 else 0) :
    ∃ next after, reaches code (if second then .l103c3f else .l103bf1) args mem
        (if zero then .l103c4d else if second then .l103c6a else .l103bff) next after ∧
      Active code fr false next after ∧ pairLimbs fr after := by
  have caller := active.atoms
  change Atom.All code args mem (Fn103ac0.frameAt .l103b80 fr) at caller
  simp only [Fn103ac0.frameAt, Fn103ac0.frameAtG0, Atom.All, Atom.Holds] at caller
  obtain ⟨rsp, df, bx, bp, r12, r13, r14, r15, mx, ftw, fcw, _, _, _, _, _, stack,
    room, aligned, _⟩ := caller
  let ret : BitVec 64 := if second then 0x103c49 else 0x103bfb
  let slot := sp fr - 8
  let byte := sp fr - 9
  let pushed := memStore mem slot ret
  let scratch : MemoryRegion := buffer byte 9
  have slotNat : slot.toNat = fr.rsp.toNat - 192 := by
    rw [show slot = fr.rsp - 192 by dsimp only [slot, sp]; bv_omega]
    exact stackSub_toNat room 192 (by decide)
  have byteNat : byte.toNat = fr.rsp.toNat - 193 := by
    rw [show byte = fr.rsp - 193 by dsimp only [byte, sp]; bv_omega]
    exact stackSub_toNat room 193 (by decide)
  have bottom : (fr.rsp - 560).toNat = fr.rsp.toNat - 560 :=
    stackSub_toNat room 560 (by decide)
  have slotWrite : Writable code mem slot 8 :=
    stack.sub (by rw [bottom, slotNat]; omega) (by rw [bottom, slotNat]; omega)
  have byteWrite : Writable code mem byte 1 :=
    stack.sub (by rw [bottom, byteNat]; omega) (by rw [bottom, byteNat]; omega)
  obtain ⟨regs, call, boxInput, pushedSp, keep, widths⟩ :=
    callWithZeroMask hcode second zero rsp slotWrite active.widths value
  let child := zeroChild fr regs pushed ret
  have callSlot : Readable pushed child.rsp 8 := slotWrite.readable.memStore slot ret
  have retWord : memLoad pushed child.rsp 64 = child.ret :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have retLow : child.ret.toNat < 2 ^ 32 := by
    change ret.toNat < 2 ^ 32
    cases second <;> decide
  have writable : Writable code pushed (child.rsp - 1) 1 := by
    rw [show child.rsp - 1 = byte by dsimp only [child, zeroChild, withArguments, byte]; bv_omega]
    exact byteWrite.memStore slot ret
  have childRoom : child.low.toNat + 1 ≤ child.rsp.toNat := by
    change byte.toNat + 1 ≤ slot.toNat
    rw [byteNat, slotNat]
    omega
  have childAligned : child.rsp.toNat % 16 = 8 := by
    change slot.toNat % 16 = 8
    rw [slotNat]
    omega
  have entry : Atom.All code regs pushed (Fn127d50.frameInfo.entryAtoms child) := by
    change Atom.All code regs pushed (Fn127d50.frameAt .l127d50 child)
    simp only [Fn127d50.frameAt, Fn127d50.frameAtG0, Atom.All, Atom.Holds]
    refine ⟨pushedSp, (keep 22 (by decide)).trans df,
      entryArgument widths _ 1 (by decide), entryArgument widths _ 2 (by decide),
      (keep 3 (by decide)).trans bx, (keep 5 (by decide)).trans bp,
      entryArgument widths _ 6 (by decide), entryArgument widths _ 7 (by decide),
      entryArgument widths _ 8 (by decide), entryArgument widths _ 9 (by decide),
      (keep 12 (by decide)).trans r12, (keep 13 (by decide)).trans r13,
      (keep 14 (by decide)).trans r14, (keep 15 (by decide)).trans r15,
      (keep 39 (by decide)).trans mx, (keep 50 (by decide)).trans ftw,
      (keep 51 (by decide)).trans fcw, callSlot, retWord, retLow, writable, childRoom,
      childAligned, trivial⟩
  obtain ⟨out, exec, tag, done, calleeWrites, widthsOut, mask⟩ :=
    blackBox_call hcode child regs entry
  have branchMask : out.values[0] = ⟨64, if zero then 1 else 0⟩ := by
    have arg : child.rdi = if zero then 1 else 0 :=
      congrArg (Value.get 64) boxInput
    rw [mask, arg]
    cases zero <;> rfl
  have scratchEnd : scratch.start + scratch.size = fr.rsp.toNat - 184 := by
    change byte.toNat + 9 = _
    rw [byteNat]
    omega
  have pushWrites : RamWriteFrame mem pushed [scratch] := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨scratch, List.mem_singleton_self _, ?_⟩
    change byte.toNat ≤ slot.toNat ∧ slot.toNat + 8 ≤ scratch.start + scratch.size ∧
      slot.toNat + 8 ≤ 2^64
    rw [byteNat, slotNat, scratchEnd]
    have := fr.rsp.isLt
    omega
  have writes : RamWriteFrame mem out.store [scratch] := by
    apply pushWrites.trans calleeWrites
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    refine ⟨scratch, List.mem_singleton_self _, Nat.le_refl _, ?_⟩
    change byte.toNat + (slot.toNat - byte.toNat) ≤ scratch.start + scratch.size
    rw [slotNat, byteNat, scratchEnd]
    omega
  have current := active.ofScratchFrame writes (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    change fr.low.toNat ≤ byte.toNat ∧ scratch.start + scratch.size ≤ (fr.rsp - 16).toNat
    have savedStart : (fr.rsp - 16).toNat = fr.rsp.toNat - 16 :=
      stackSub_toNat room 16 (by decide)
    rw [byteNat, scratchEnd, savedStart]
    omega)
  have saved := pairLimbs_of_frame active limbs writes (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    have limbsStart : (sp fr + 104).toNat = fr.rsp.toNat - 80 := by
      rw [show sp fr + 104 = fr.rsp - 80 by unfold sp; bv_omega]
      exact stackSub_toNat room 80 (by decide)
    rw [scratchEnd, limbsStart]
    omega)
  let next : Values Value Reg.count := out.values.set 19 (.ofBool (!zero))
  have keepAfter (i : Fin Reg.count) (hi : 19 ≠ i.val) : next[i] = out.values[i] :=
    Vector.getElem_set_ne _ _ hi
  have widthsNext : ArgumentWidths next := by
    intro i hi
    have unchanged := keepAfter i (by
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega)
    exact (congrArg Value.width unchanged).trans (widthsOut i hi)
  have doneNext : Atom.All code next out.store (Fn127f50.frameInfo.doneAtoms child) := by
    change Atom.All code next out.store (Fn127d50.doneAt child)
    change Atom.All code out.values out.store (Fn127d50.doneAt child) at done
    simp only [Fn127d50.doneAt, Atom.All, Atom.Holds] at done ⊢
    simpa only [keepAfter 4 (by decide), keepAfter 22 (by decide), keepAfter 3 (by decide),
      keepAfter 5 (by decide), keepAfter 12 (by decide), keepAfter 13 (by decide),
      keepAfter 14 (by decide), keepAfter 15 (by decide), keepAfter 39 (by decide),
      keepAfter 50 (by decide), keepAfter 51 (by decide)] using done
  refine ⟨next, out.store, (reachesOfCall call exec tag).tail ?_,
    activeOfZeroReturn current doneNext widthsNext, saved⟩
  change program.step (dialect code) _ = _
  rw [Program.step, jumpOnZeroMask second zero branchMask]
  rfl

end K256.Proofs.ParseSignature.Pair
