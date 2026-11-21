import K256.Proofs.Ecdh.Scalar.Calls
import K256.Proofs.Ecdh.Scalar.Stage
import K256.Proofs.Ecdh.Scalar.Select
import K256.Proofs.Common.SignatureRun

namespace K256.Proofs.Ecdh.Scalar

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Wrapper Ecdh.LIR

set_option maxRecDepth 4096 in
theorem selectPrefix {s : RamState} {secret peer : ByteArray} {a : Values Value Reg.count} {m : Ram}
    {w : Vector (BitVec 64) 4} (call : ValidCall ecdhDiffieHellman s [secret, peer])
    (regs : Registers s a) (mem : Memory s m) (r15 : a[15] = ⟨64, localSp s + 0x158⟩)
    (src : WordsAt m (localSp s + 0x158) 64 w) (bit : memLoad m (localSp s + 0x178) 8 = 1) :
    ∃ b n, Reaches ⟨.l1016be, a, m⟩ ⟨.l101712, b, n⟩ ∧ Registers s b ∧ Memory s n ∧
      b[12] = ⟨64, localSp s + 0xc98⟩ ∧ b[5].get 8 = 1 ∧ WordsAt n (localSp s + 0xc98) 64 w := by
  let sp := localSp s
  let flag := memLoad m (sp + 0x178) 32
  let args := selectArgs a sp flag
  let tmp := prepareMemory m sp 0x8d8 0x101712
  let fr := childActivation s tmp args 1 0x101712
  have code : ∀ x ∈ fnCode, x ∈ Extracted.programImage := Common.fnCode_subset_programImage
  have win := mem.window call
  obtain ⟨push, flagBit⟩ := prepareSelect code (congrArg (Value.get 64) regs.rsp)
    (congrArg (Value.get 64) r15) (win.of_offsets (addr_sub _ 8) (addr_sub _ 3936) (by decide)) bit
  have prev (i : Fin Reg.count) (h : i.val ∈ [3,13,14,22,39,50,51]) : args[i] = a[i] := by
    obtain ⟨i, bound⟩ := i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    change args[i] = a[i]
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [args, selectArgs]
  have pre : Wrapper.ChildRegisters s args :=
    childRegisters regs (by simp [args, selectArgs, sp]) (selectArgs_width sp flag) (fun i hi => prev i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      grind))
  obtain ⟨tmpMem, ret⟩ := stageMemory call mem 0x8d8 0x101712 (.inl rfl)
  have entry := childEntry call tmpMem.frame pre Fn10a220.frameInfo rfl (by decide)
    (by decide) (by decide +kernel) ret
  have window := tmpMem.window call
  have rsi : fr.rsi = sp + 0x8d8 := by
    have h : (selectArgs a sp flag)[(6 : Nat)] = ⟨64, sp + 0x8d8⟩ := by
      simp only [selectArgs, Vector.getElem_set]; rfl
    exact congrArg (Value.get 64) h
  have rdx : fr.rdx = sp + 0x158 := by
    have h : (selectArgs a sp flag)[(2 : Nat)] = ⟨64, sp + 0x158⟩ := by
      simp only [selectArgs, Vector.getElem_set]; rfl
    exact congrArg (Value.get 64) h
  have rdi : fr.rdi = sp + 0xc98 := by
    have h : (selectArgs a sp flag)[(7 : Nat)] = ⟨64, sp + 0xc98⟩ := by
      simp only [selectArgs, Vector.getElem_set]; rfl
    exact congrArg (Value.get 64) h
  have rcx : fr.rcx = flag.setWidth 64 := by
    have h : (selectArgs a sp flag)[(1 : Nat)] = ⟨64, flag.setWidth 64⟩ := by
      simp only [selectArgs, Vector.getElem_set]; rfl
    exact congrArg (Value.get 64) h
  have readL : Readable tmp fr.rsi 32 := by
    rw [rsi]
    exact window.readable.of_offsets rfl (addr_sub _ _) (by decide)
  have readR : Readable tmp fr.rdx 32 := by
    rw [rdx]
    exact window.readable.of_offsets rfl (addr_sub _ _) (by decide)
  have dst : Writable Extracted.programImage tmp fr.rdi 32 := by
    rw [rdi]
    exact window.of_offsets rfl (addr_sub _ _) (by decide)
  have choice : fr.rcx.setWidth 8 = 1 := by
    rw [rcx]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]
    exact flagBit
  have ⟨room, bound, base⟩ := stack_geometry call
  change sp.toNat = _ at base
  have lo : fr.low.toNat = (stackPtr s).toNat - 6161 :=
    Common.stackOffset call.stackAvailable (off := 6161) (by decide)
  have top : fr.rsp.toNat = (stackPtr s).toNat - 6160 :=
    Common.stackOffset call.stackAvailable (off := 6160) (by decide)
  have apart : Outside [fr.region] fr.rdx 32 := by
    simp only [Outside, List.mem_singleton, forall_eq, Activation.region, lo, top, rdx]
    change (sp + 0x158).toNat + 32 ≤ _ ∧ _
    constructor
    · bv_omega
    · right
      change _ ≤ (sp + 0x158).toNat
      bv_omega
  have apartDst : Outside [ParseSignature.callStack fr] fr.rdi 32 := by
    simp only [Outside, List.mem_singleton, forall_eq, ParseSignature.callStack, lo, top, rdi]
    change (sp + 0xc98).toNat + 32 ≤ _ ∧ _
    constructor
    · bv_omega
    · right
      change _ ≤ (sp + 0xc98).toNat
      bv_omega
  obtain ⟨out, run, tag, done, writes, widths, result⟩ :=
    select_call code fr choice readL readR dst apart apartDst args entry
  have ⟨rsp, kept⟩ := childReturn pre (win := 1) (ret := 0x101712) (m := tmp) done
  refine ⟨out.values, out.store, resumeCall push run tag,
    returnedRegisters regs pre rsp widths kept prev, ?_, (kept 12 (by decide)).trans (by change (selectArgs a sp flag)[(12 : Nat)] = _; simp [selectArgs, sp]), ?_, ?_⟩
  · apply tmpMem.advance call writes
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only [Activation.region, lo, top]
      omega
    · obtain rfl := List.mem_singleton.mp hr
      simp only [ParseSignature.buffer, rdi]
      change _ ≤ (sp + 0xc98).toNat ∧ (sp + 0xc98).toNat + 32 ≤ _
      bv_omega
  · refine (congrArg (Value.get 8) (kept 5 (by decide))).trans ?_
    have hb : args[(5 : Nat)] = ⟨64, flag.setWidth 64⟩ := by simp only [args, selectArgs, Vector.getElem_set]; rfl
    exact (congrArg (Value.get 8) hb).trans ((congrArg (BitVec.setWidth 8) rcx.symm).trans choice)
  · have src' : WordsAt tmp (sp + 0x158) 64 w := by
      apply preparedWords src (win.of_offsets (addr_sub _ 8) (addr_sub _ 3936) (by decide))
      change Outside [⟨(sp - 8).toNat, 8⟩, ⟨(sp + 0x8d8).toNat, 32⟩] (sp + 0x158) 32
      simp only [Outside, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · bv_omega
      · intro r hr
        rcases hr with rfl | rfl <;> dsimp only <;> bv_omega
    intro i hi
    have result' := result i hi
    simp only [rdi, rdx, Vector.getElem_ofFn] at result'
    exact result'.trans (src' i hi)

end K256.Proofs.Ecdh.Scalar
