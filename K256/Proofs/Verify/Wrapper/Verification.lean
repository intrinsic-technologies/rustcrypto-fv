import K256.Proofs.Verify.Transfer.SignatureWords
import K256.Proofs.Verify.Wrapper.State
import K256.Proofs.Verify.Wrapper.Copy.Prepare
import K256.Proofs.Verify.Wrapper.Copy.Operands
import K256.Proofs.Verify.Wrapper.Finish
import K256.Proofs.Verify.Core.Execution

namespace K256.Proofs.Verify.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

private abbrev coreArgs (i : RamState) (a : Core.Registers) :=
  verificationCallArgs a (localSp i)

private abbrev coreActivation (i : RamState) (a : Core.Registers) (m : Ram) :=
  childActivation i m (coreArgs i a) 12456 0x1033c7

local macro "core_regs" : tactic =>
  `(tactic| simp only [coreArgs, verificationCallArgs, Vector.getElem_set, Fin.getElem_fin,
    Nat.reduceEqDiff, ↓reduceIte, Value.get, BitVec.setWidth_eq])

private theorem coreRegisters {i : RamState} {a : Core.Registers} {m : Ram}
    {p : Curve.Point} {r s : Nat} {digest : ByteArray} (v : VerificationInput i a m p r s digest) :
    ChildRegisters i (coreArgs i a) := by
  have bp : a[5].width = 64 := by rw [v.rbp]; rfl
  have r13 : a[13].width = 64 := by rw [v.r13]; rfl
  have rbx : a[3].width = 64 := by rw [v.keyPtr]
  refine ⟨?_, by core_regs; exact v.df, ?_, by core_regs; exact v.mxcsr,
    by core_regs; exact v.ftw, by core_regs; exact v.fcw⟩
  · core_regs
    change (⟨64, localSp i - 8⟩ : Value) = ⟨64, i.regValue .rsp - 544⟩
    congr 1
    change stackPtr i - 536 - 8 = stackPtr i - 544
    bv_omega
  · rintro ⟨j,hj⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> core_regs <;>
      first | rfl | exact bp | exact r13 | exact rbx | exact v.r9Width | exact v.r12Width |
        exact v.r14Width | exact v.r15Width

private theorem verificationOperands (i : RamState) (a : Core.Registers) (m : Ram)
    (key : a[3] = ⟨64,localSp i + 8⟩) :
    let fr := coreActivation i a m
    fr.rdi = localSp i + 160 ∧ fr.rsi = localSp i + 8 ∧ fr.rdx = localSp i + 128 ∧
      fr.r8 = localSp i + 352 ∧ fr.rcx = 32 := by
  let b := coreArgs i a
  have dst : b[7] = ⟨64,localSp i + 160⟩ := by simp only [b]; core_regs
  have src : b[6] = ⟨64,localSp i + 8⟩ := by simp only [b]; core_regs; rw [key]; rfl
  have hash : b[2] = ⟨64,localSp i + 128⟩ := by simp only [b]; core_regs
  have sig : b[8] = ⟨64,localSp i + 352⟩ := by simp only [b]; core_regs
  have len : b[1] = ⟨64,32⟩ := by simp only [b]; core_regs
  exact ⟨congrArg (Value.get 64) dst, congrArg (Value.get 64) src, congrArg (Value.get 64) hash,
    congrArg (Value.get 64) sig, congrArg (Value.get 64) len⟩

set_option maxRecDepth 4096 in
private theorem prepareCore {i : RamState} {key msg sig digest : ByteArray} {p : Curve.Point}
    {r s : Nat} {a : Core.Registers} {m : Ram}
    (call : ValidCall verifyingKeyVerify i [key,msg,sig])
    (dk : Secp256k1.decodePublicKey key = some p) (ds : Ecdsa.signatureScalars sig = some (r,s))
    (v : VerificationInput i a m p r s digest) :
    let pushed := memStore m (localSp i - 8) (0x1033c7 : BitVec 64)
    let fr := coreActivation i a pushed
    program.runBlock (dialect Extracted.programImage) ⟨.l1033a2, a, m⟩ =
      .call ⟨.l104f20, coreArgs i a, pushed⟩ (resumeAt .l1033c7 0x1033c7) ∧
      Memory i pushed ∧ Core.Entry fr (coreArgs i a) p digest r s := by
  let sp := localSp i
  let pushed := memStore m (sp - 8) (0x1033c7 : BitVec 64)
  let fr := coreActivation i a pushed
  obtain ⟨block, memory, ret⟩ := prepareVerification call v.memory (congrArg (Value.get 64) v.rsp)
  have slot : sp - 8 = stackPtr i - 544 := by dsimp only [sp, localSp]; bv_omega
  have bottom : fr.low = stackPtr i - 13000 := rfl
  have top : fr.rsp.toNat = (stackPtr i).toNat - 544 := Common.stackOffset call.stackAvailable (by decide)
  have base : sp.toNat = (stackPtr i).toNat - 536 := Common.stackOffset call.stackAvailable (by decide)
  have depth : 13000 ≤ (stackPtr i).toNat := call.stackAvailable.2.2.1
  have lim := call.stackAvailable.1
  change (stackPtr i).toNat - 13000 + ((stackPtr i).toNat + 8 - ((stackPtr i).toNat - 13000)) < 2^32 at lim
  obtain ⟨q, stored, valid, val⟩ := v.peer
  obtain ⟨peer, hash, rAt, sAt⟩ := verificationCallOperands (by omega : 8 ≤ sp.toNat)
    (by omega : sp.toNat + 416 ≤ 2^32) stored v.hash v.rAt v.sAt
  have frsp : fr.rsp = sp - 8 := slot.symm
  obtain ⟨dst, keyPtr, dig, sigPtr, size⟩ := verificationOperands i a pushed v.keyPtr
  change fr.rdi = sp + 160 at dst
  change fr.rsi = sp + 8 at keyPtr
  change fr.rdx = sp + 128 at dig
  change fr.r8 = sp + 352 at sigPtr
  change fr.rcx = 32 at size
  have keyInput : ValidInput i (registerRegion i .rdi 65) key := call.inputsInMemory.1
  have sigInput : ValidInput i (registerRegion i .rcx 64) sig := call.inputsInMemory.2.2.1
  have bits := (Verify.Transfer.signatureValues (src := i.regValue .rcx) sigInput.2.2 ds).2.2
  refine ⟨block, memory, ?_⟩
  change Core.Entry fr (coreArgs i a) p digest r s
  refine ⟨?_, (inputMemory call memory.frame).2.2.2, ?_, ?_, ?_, size, ?_, (show 12456 ≤ fr.rsp.toNat by omega), ?_,
    ?_, ?_, (show fr.rsp.toNat + 512 ≤ 2^32 by omega), ?_, Verify.Transfer.PublicKey.uncompressedOnCurve keyInput.2.2.1 dk, ?_, ?_, ?_, bits⟩
  · change Atom.All _ _ _ (Fn104f20.frameInfo.entryAtoms fr)
    have ret' : memLoad pushed (stackPtr i - 544) 64 = 0x1033c7 := slot ▸ ret
    exact childEntry call memory (coreRegisters v) Fn104f20.frameInfo (room := 12456)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide) ret'
  · rw [dst, frsp]; bv_omega
  · rw [keyPtr, frsp]; bv_omega
  · rw [dig, frsp]; bv_omega
  · rw [sigPtr, frsp]; bv_omega
  · change stackPtr i - 13000 = stackPtr i - 544 - 12456
    bv_omega
  · exact (Common.stackWritable (off := 13000) (len := 12456) call (by decide)
      (by decide) (by decide)).of_frame memory.frame
  · rw [frsp, BitVec.sub_add_cancel]
    exact (Common.stackWritable (off := 536) (len := 504) call (by decide)
      (by decide) (by decide)).of_frame memory.frame
  · rw [keyPtr]
    exact ⟨q, peer, valid, val⟩
  · rw [dig]; exact hash
  · rw [sigPtr]; exact rAt
  · rw [sigPtr, BitVec.add_assoc]
    exact sAt

theorem verificationSuffix {i : RamState} {key msg sig digest : ByteArray} {p : Curve.Point}
    {r s : Nat} {a : Core.Registers} {m : Ram}
    (call : ValidCall verifyingKeyVerify i [key,msg,sig])
    (dk : Secp256k1.decodePublicKey key = some p) (ds : Ecdsa.signatureScalars sig = some (r,s))
    (v : VerificationInput i a m p r s digest) :
    let ok := decide (s ≤ domain.n / 2) && (Nat.mod (affineX (verificationPoint p digest r s)) domain.n == r)
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1033a2, a, m⟩, []⟩ out ∧
      Common.Returned i #v[stack i] out ∧ out.values[0] = ⟨64, if ok then 0 else 1⟩ := by
  let pushed := memStore m (localSp i - 8) (0x1033c7 : BitVec 64)
  let fr := coreActivation i a pushed
  obtain ⟨block, memory, pre⟩ := prepareCore call dk ds v
  obtain ⟨o, run, res⟩ := Core.execution pre
  have reach := Verify.reachesOfCall (resume := .l1033c7) block run res.tag
  have top : fr.rsp.toNat = (stackPtr i).toNat - 544 := Common.stackOffset call.stackAvailable (by decide)
  have floor : fr.low.toNat = (stackPtr i).toNat - 13000 := Common.stackOffset call.stackAvailable (by decide)
  have room : 13000 ≤ (stackPtr i).toNat := call.stackAvailable.2.2.1
  have dst : fr.rdi = localSp i + 160 := by
    rw [pre.dst]
    change stackPtr i - 544 + 168 = stackPtr i - 536 + 160
    bv_omega
  have natDst : fr.rdi.toNat = (stackPtr i).toNat - 376 := by
    rw [dst, show localSp i + 160 = stackPtr i - 376 by unfold localSp; bv_omega]
    exact Common.stackOffset call.stackAvailable (by decide)
  have memory' := memory.advance call res.writes (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · change _ ≤ fr.low.toNat ∧ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ _
      omega
    · change _ ≤ fr.rdi.toNat ∧ fr.rdi.toNat + 16 ≤ _
      omega)
  have atoms := res.atoms
  simp only [Fn104f20.doneAt, Atom.All, Atom.Holds, Fin.getElem_fin] at atoms
  obtain ⟨rsp, df, _, bp, _, r13, _⟩ := atoms
  have stackEq : o.values[4].get 64 = localSp i := by
    calc
      _ = fr.rsp + 8 := congrArg (Value.get 64) rsp
      _ = _ := by
        change stackPtr i - 544 + 8 = stackPtr i - 536
        bv_omega
  have bpEq : o.values[5] = (Reg.ofIndex 5).read i := by
    apply bp.trans
    change (⟨64,(coreArgs i a)[5].get 64⟩ : Value) = _
    have reg : (coreArgs i a)[5] = a[5] := by core_regs
    rw [reg, v.rbp]
    rfl
  have r13Eq : o.values[13] = (Reg.ofIndex 13).read i := by
    apply r13.trans
    change (⟨64,(coreArgs i a)[13].get 64⟩ : Value) = _
    have reg : (coreArgs i a)[13] = a[13] := by core_regs
    rw [reg, v.r13]
    rfl
  let ok := decide (s ≤ domain.n / 2) && (Nat.mod (affineX (verificationPoint p digest r s)) domain.n == r)
  have status : memLoad o.store (localSp i + 160) 64 = if ok then 0 else 1 := dst ▸ res.status
  have null : (if ok then 0 else 1 : BitVec 64) ≠ 0 →
      memLoad o.store (localSp i + 168) 64 = 0 := by
    intro h
    have no : ok = false := by cases eq : ok <;> simp_all
    have z := res.null no
    rw [dst, BitVec.add_assoc] at z
    exact z
  obtain ⟨out, tailRun, returned, value⟩ := finish call memory' stackEq status null bpEq r13Eq df
  exact ⟨out, Program.Exec.of_sem (reach.exec tailRun.sem), returned, value⟩

end K256.Proofs.Verify.Wrapper
