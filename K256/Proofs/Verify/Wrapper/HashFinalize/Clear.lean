import K256.Proofs.Verify.Wrapper.HashFinalize.State

namespace K256.Proofs.Verify.Wrapper.HashFinalize

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Standards.SECG.ECC Hash.FinalBlocks

variable {initial : RamState} {key msg sig : ByteArray} {p : Curve.Point} {r s : Nat}
    {a : Core.Registers} {m : Ram}

theorem clear {hash : Array UInt32} (call : ValidCall verifyingKeyVerify initial [key,msg,sig])
    (h : State initial a m p r s msg hash) (long : ¬ msg.size % 64 < 56) :
    ∃ b t, Core.Reaches .l10324a a m .l103289 b t ∧ State initial b t p r s msg hash ∧
      (⟨(localSp initial+8).toNat,56⟩ : MemoryRegion).HasBytes t (Hash.finalPrefix msg) := by
  let sp := localSp initial
  obtain ⟨depth,low⟩ := Hash.Update.stackBounds call
  have base : sp.toNat = (stackPtr initial).toNat - 536 :=
    Common.stackOffset call.stackAvailable (by decide)
  have addr : sp+8 = stackPtr initial - (528 : Word) := by dsimp [sp, localSp]; bv_omega
  have natAddr : (sp+8).toNat = (stackPtr initial).toNat - 528 := by
    rw [addr]; exact Common.stackOffset call.stackAvailable (by decide)
  have stack := Hash.Update.writable (off := 528) (len := 56) call h.memory addr
    (by decide) (by decide) (by decide)
  obtain ⟨b,step,keep⟩ := clearBlock a m sp (congrArg (Value.get 64) h.rsp) stack
  have writes := clearPrefix_frame m sp (by omega)
  have mem := h.memory.advance call writes (by
    intro reg hr; obtain rfl := List.mem_singleton.mp hr
    change _ ≤ (sp+8).toNat ∧ (sp+8).toNat + 56 ≤ _; omega)
  have ops := h.operands.afterHashWrites call writes (by
    intro reg hr; obtain rfl := List.mem_singleton.mp hr
    change (sp+8).toNat + 56 ≤ sp.toNat + 352; omega)
  have st := stateOutside h.state writes (by change sp.toNat + 224 ≤ _; omega) (by
    intro reg hr; obtain rfl := List.mem_singleton.mp hr
    left; change (sp+8).toNat + 56 ≤ sp.toNat + 72; omega)
  refine ⟨b, _, .step (congrArg (Transfer.next _ []) step) (.refl _), ?_,
    clearedPrefix m sp msg long stack.readable⟩
  refine ⟨⟨mem, (keep 4 (by decide)).trans h.rsp, (keep 5 (by decide)).trans h.rbp,
    (keep 13 (by decide)).trans h.r13, (keep 22 (by decide)).trans h.df, ?_, ?_, ?_, ?_⟩,
    ops, st, (keep 3 (by decide)).trans h.rbx, ?_, (keep 15 (by decide)).trans h.length⟩
  all_goals first
    | exact (congrArg Value.width (keep 12 (by decide))).trans h.r12Width
    | exact (congrArg Value.width (keep 39 (by decide))).trans h.mxcsr
    | exact (congrArg Value.width (keep 50 (by decide))).trans h.ftw
    | exact (congrArg Value.width (keep 51 (by decide))).trans h.fcw
    | exact (congrArg Value.width (keep 14 (by decide))).trans h.r14Width

end K256.Proofs.Verify.Wrapper.HashFinalize
