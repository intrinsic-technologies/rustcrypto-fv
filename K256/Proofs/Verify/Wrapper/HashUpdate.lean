import K256.Proofs.Verify.Hash.Update.Long
import K256.Proofs.Verify.Wrapper.Copy.Signature
import K256.Proofs.Verify.Wrapper.OperandFrame

namespace K256.Proofs.Verify.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Standards.SECG.ECC Standards.NIST.SHA2

variable {initial : RamState} {key msg sig : ByteArray} {p : Curve.Point} {r s : Nat}
    {a : Core.Registers} {m : Ram}

private theorem initializeHash (call : ValidCall verifyingKeyVerify initial [key,msg,sig])
    (input : HashInput initial a m p r s) :
    let sp := localSp initial
    let stored := signatureMemory m sp
    Memory initial stored ∧ AffineInputs initial stored p r s 352 ∧
      Verify.Hash.Compression.StateAt stored (sp + 312) Verify.Hash.initialHash ∧
      memLoad stored (sp+344) 64 = 0 := by
  let sp := localSp initial
  let stored := signatureMemory m sp
  obtain ⟨depth,limit⟩ := Verify.Hash.Update.stackBounds call
  have base : sp.toNat = (stackPtr initial).toNat - 536 := Common.stackOffset call.stackAvailable (by decide)
  have addr (off : Nat) (bound : off ≤ 504) : (sp+BitVec.ofNat 64 off).toNat = sp.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have start : (sp+311).toNat = sp.toNat + 311 := addr 311 (by decide)
  have wrote := signatureMemory_frame m sp (by omega)
  have mem := input.memory.advance call wrote (by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    change _ ≤ (sp+311).toNat ∧ (sp+311).toNat + 105 ≤ _
    omega)
  obtain ⟨hr,hs⟩ := signatureMemory_scalars input.operands.rAt input.operands.sAt
  refine ⟨mem, ⟨input.operands.point.of_copy ?_, hr, hs⟩, ⟨by decide +kernel, ?_⟩,
    (signatureMemory_hash m sp).2.2.2.2.1⟩
  · intro off width fit
    apply wrote.memLoad_eq
    change Outside _ (sp + 416 + BitVec.ofNat 64 off) _
    have address : (sp + 416 + BitVec.ofNat 64 off).toNat = sp.toNat + (416+off) := by
      rw [show sp + 416 + BitVec.ofNat 64 off = sp + BitVec.ofNat 64 (416+off) by
        rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl]
      exact addr _ (by omega)
    refine ⟨by omega, fun reg hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (by change (sp+311).toNat + 105 ≤ _; omega)
  · have words : (Vector.ofFn fun i : Fin 8 => Verify.Hash.initialHash[i.val]!.toBitVec) = SHA256.«H⁽⁰⁾» := by
      decide +kernel
    rw [words]
    exact signatureMemory_initialHash m sp

theorem hashUpdate (compress : Verify.Hash.Update.Compresses)
    (call : ValidCall verifyingKeyVerify initial [key,msg,sig]) (input : HashInput initial a m p r s) :
    ∃ b t, Core.Reaches .l103037 a m .l103170 b t ∧ HashBuffer initial b t p r s msg := by
  let sp := localSp initial
  let n := initial.regValue .rdx
  let start := signatureArguments a m sp n
  let stored := signatureMemory m sp
  obtain ⟨mem, inputs, hs, zero⟩ := initializeHash call input
  have win := Verify.Hash.Update.writable (p := sp) (off := 536) (len := 416)
    call input.memory rfl (by decide) (by decide) (by decide)
  have block := signatureCopyBlock (congrArg (Value.get 64) input.rsp)
    (congrArg (Value.get 64) input.length) win
  change program.runBlock (dialect Extracted.programImage) ⟨.l103037,a,m⟩ =
    .jump ⟨if 63 < n.toNat then .l10311e else .l103101, start, stored⟩ at block
  have unchanged (i : Fin 53) (hi : i.val ∈ [3,4,5,12,13,14,22,39,50,51]) : start[i] = a[i] := by
    rcases i with ⟨i,lt⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [start, signatureArguments, Fin.getElem_fin, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
  have bsp := congrArg (Value.get 64) ((unchanged 4 (by decide)).trans input.rsp)
  have bn := congrArg (Value.get 64) ((unchanged 3 (by decide)).trans input.length)
  have bsrc := congrArg (Value.get 64) ((unchanged 14 (by decide)).trans input.source)
  have df := congrArg (Value.get 1) ((unchanged 22 (by decide)).trans input.df)
  have count : n.toNat = msg.size := call.lengthArgumentsMatchInputs.2.1
  have route : ∃ b t, Core.Reaches .l103037 a m .l103170 b t ∧
      Verify.Hash.Update.Updated initial msg Verify.Hash.initialHash start stored b t := by
    by_cases h : 63 < n.toNat
    · rw [ite_eq_left h] at block
      have widths (i : Fin 53) (hi : i.val ∈ [5,13,14]) : start[i].width = 64 := by
        rcases i with ⟨i,lt⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl|rfl|rfl
        · exact congrArg Value.width ((unchanged 5 (by decide)).trans input.rbp)
        · exact congrArg Value.width ((unchanged 13 (by decide)).trans input.r13)
        · exact congrArg Value.width ((unchanged 14 (by decide)).trans input.source)
      obtain ⟨b,t,run,ready⟩ := Verify.Hash.Update.long compress call mem bsp bn bsrc widths df hs (by omega)
      exact ⟨b,t,.step (congrArg (Transfer.next _ []) block) run,ready⟩
    · rw [ite_eq_right h] at block
      obtain ⟨b,t,run,ready⟩ := Verify.Hash.Update.short call mem bsp bn bsrc
        ((congrArg Value.width (unchanged 12 (by decide))).trans input.r12Width) df hs zero (by omega)
      exact ⟨b,t,.step (congrArg (Transfer.next _ []) block) run,ready⟩
  obtain ⟨b,t,reach,ready⟩ := route
  have keep (i : Fin 53) (hi : i.val ∈ [5,13,22,39,50,51]) : b[i] = a[i] :=
    (ready.kept i hi).trans (unchanged i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega))
  obtain ⟨depth,limit⟩ := Verify.Hash.Update.stackBounds call
  have base : sp.toNat = (stackPtr initial).toNat - 536 := Common.stackOffset call.stackAvailable (by decide)
  refine ⟨b,t,reach,⟨⟨Verify.Hash.Update.advance call mem ready.writes, ready.rsp,
    (keep 5 (by decide)).trans input.rbp, (keep 13 (by decide)).trans input.r13,
    (keep 22 (by decide)).trans input.df, ready.r12width,
    (congrArg Value.width (keep 39 (by decide))).trans input.mxcsr,
    (congrArg Value.width (keep 50 (by decide))).trans input.ftw,
    (congrArg Value.width (keep 51 (by decide))).trans input.fcw⟩,
    inputs.afterHashWrites call ready.writes ?_,ready.state,ready.bytes,ready.len,ready.blocks⟩⟩
  intro reg hr
  obtain rfl := List.mem_singleton.mp hr
  change (stackPtr initial).toNat - 880 + 696 ≤ sp.toNat + 352
  omega

end K256.Proofs.Verify.Wrapper
