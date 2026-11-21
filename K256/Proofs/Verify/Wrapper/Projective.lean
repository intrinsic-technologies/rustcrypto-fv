import K256.Proofs.Verify.Wrapper.Projective.Memory
import K256.Proofs.Verify.Transfer.Projective
import K256.Proofs.Verify.Transfer.PublicKey.Uncompressed

namespace K256.Proofs.Verify.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Standards.SECG.ECC Standards.NIST.SHA2

variable {initial : RamState} {key msg sig : ByteArray} {p : Curve.Point} {r s : Nat}
    {a : Core.Registers} {m : Ram}

set_option maxRecDepth 4096 in
theorem makeProjective (call : ValidCall verifyingKeyVerify initial [key,msg,sig])
    (decoded : Secp256k1.decodePublicKey key = some p)
    (hash : HashOutput initial a m p r s msg) :
    ∃ b t, Core.Reaches .l103306 a m .l1033a2 b t ∧
      VerificationInput initial b t p r s (SHA256.hashBytes msg) := by
  let sp := localSp initial
  let h := Hash.compressBlocks Hash.initialHash (Hash.bytePadding msg)
  let pushed := Hash.coreMemory m sp h
  obtain ⟨memory, operands, point, window⟩ := projectiveCallMemory call hash
  have ⟨rep, push⟩ := conversionGuards window
  have df : a[22].get 1 = 0 := congrArg (Value.get 1) hash.df
  obtain ⟨b, block, bx, bp, si, di, keep, widths⟩ := Hash.serializeCall (hash := h)
    (congrArg (Value.get 64) hash.rsp)
    ((Hash.Update.writable call hash.memory (off := 464) (len := 32)
      (by change localSp initial + 72 = stackPtr initial - 464; unfold localSp; bv_omega)
      (by decide) (by decide) (by decide)).readable)
    (Hash.Update.writable call hash.memory (off := 408)
      (by change localSp initial + 128 = stackPtr initial - 408; unfold localSp; bv_omega)
      (by decide) (by decide) (by decide))
    hash.state.2 (df ▸ rep) push
  let fr := childActivation initial pushed b 97 0x1033a2
  have slot : sp - 8 = stackPtr initial - 544 := by dsimp only [sp,localSp]; bv_omega
  have si' : fr.rsi = sp + 160 := congrArg (Value.get 64) si
  have di' : fr.rdi = sp + 8 := congrArg (Value.get 64) di
  have rbp := (keep 5 (by decide)).trans hash.rbp
  have r13 := (keep 13 (by decide)).trans hash.r13
  have regs : ChildRegisters initial b := by
    refine ⟨by rw [bp]; exact congrArg (Value.mk 64) slot, (keep 22 (by decide)).trans hash.df, ?_,
      (congrArg Value.width (keep 39 (by decide))).trans hash.mxcsr,
      (congrArg Value.width (keep 50 (by decide))).trans hash.ftw,
      (congrArg Value.width (keep 51 (by decide))).trans hash.fcw⟩
    rintro ⟨j,hj⟩ mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | exact widths 1 (by decide) | exact widths 2 (by decide) | exact widths 8 (by decide) | exact widths 9 (by decide) | exact congrArg Value.width bx | exact congrArg Value.width rbp |
        exact congrArg Value.width si | exact congrArg Value.width di | exact congrArg Value.width r13 |
        exact (congrArg Value.width (keep 12 (by decide))).trans hash.r12Width |
        exact (congrArg Value.width (keep 14 (by decide))).trans hash.r14Width |
        exact (congrArg Value.width (keep 15 (by decide))).trans hash.r15Width
  have ret : memLoad pushed (stackPtr initial - 544) 64 = 0x1033a2 := by
    rw [←slot]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have atoms := childEntry call memory regs Fn10fa10.frameInfo (room := 97)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide : (0x1033a2 : BitVec 64).toNat < 2^32) ret
  obtain ⟨depth, limit⟩ := Hash.Update.stackBounds call
  have top : fr.rsp.toNat = (stackPtr initial).toNat - 544 := Common.stackOffset call.stackAvailable (by decide)
  have floor : fr.low.toNat = (stackPtr initial).toNat - 641 := Common.stackOffset call.stackAvailable (by decide)
  have base : sp.toNat = (stackPtr initial).toNat - 536 := Common.stackOffset call.stackAvailable (by decide)
  have atOff (off : BitVec 64) (bound : off.toNat ≤ 504) : (sp + off).toNat = sp.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have srcNat : fr.rsi.toNat = sp.toNat + 160 := si' ▸ atOff 160 (by decide)
  have dstNat : fr.rdi.toNat = sp.toNat + 8 := di' ▸ atOff 8 (by decide)
  have win : Writable Extracted.programImage pushed sp 504 :=
    (Common.stackWritable call (off := 536) (by decide) (by decide) (by decide)).of_frame memory.frame
  have read : Readable pushed fr.rsi 84 := win.readable.sub (by omega) (by omega)
  have write : Writable Extracted.programImage pushed fr.rdi 120 := win.sub (by omega) (by omega)
  have above {addr : BitVec 64} {n : Nat} (lo : sp.toNat ≤ addr.toNat) (hi : addr.toNat+n ≤ 2^64) :
      Outside [ParseSignature.callStack fr] addr n := by
    refine ⟨hi, fun reg member => ?_⟩
    obtain rfl := List.mem_singleton.mp member
    exact Or.inr (by change fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ addr.toNat; omega)
  have keyInput : ValidInput initial (registerRegion initial .rdi 65) key := call.inputsInMemory.1
  obtain ⟨out, run, tag, done_, writes, argWidths, peer, stored, valid, value⟩ :=
    Verify.Transfer.projectiveExecution fr b atoms read (above (by omega) (by omega))
      write (above (by omega) (by omega)) (si' ▸ point)
      (Verify.Transfer.PublicKey.uncompressedOnCurve keyInput.2.2.1 decoded)
  have reach := Verify.reachesOfCall (resume := .l1033a2) block run tag
  have regionBounds (reg : MemoryRegion) (hr : reg ∈ [fr.region, ⟨fr.rdi.toNat,120⟩]) :
      (stackPtr initial).toNat - 13000 ≤ reg.start ∧ reg.start + reg.size ≤ sp.toNat + 128 := by
    rcases List.mem_cons.mp hr with rfl | hr
    · change _ ≤ fr.low.toNat ∧ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ _
      omega
    · obtain rfl := List.mem_singleton.mp hr
      change _ ≤ fr.rdi.toNat ∧ fr.rdi.toNat + 120 ≤ _
      omega
  have finalMemory := memory.advance call writes (fun reg hr =>
    ⟨(regionBounds reg hr).1, by have := (regionBounds reg hr).2; omega⟩)
  have finalOps := operands.afterHashWrites call writes (fun reg hr => by
    have := (regionBounds reg hr).2
    change _ ≤ sp.toNat + 352
    omega)
  have digest : (⟨(sp + 128).toNat,32⟩ : MemoryRegion).HasBytes pushed (SHA256.hashBytes msg) := by
    rw [← Hash.serializeHash_compressBlocks_bytePadding]
    exact Hash.coreMemory_digest m sp hash.state.1
  have digest' : (⟨(sp + 128).toNat,32⟩ : MemoryRegion).HasBytes out.store (SHA256.hashBytes msg) := by
    refine ⟨digest.1,fun i => (writes.outside _ ?_).trans (digest.2 i)⟩
    have size : (SHA256.hashBytes msg).size = 32 := digest.1
    have bound := i.isLt
    have addr : (BitVec.ofNat 64 ((sp+128).toNat + i.val)).toNat = sp.toNat+128+i.val := by
      rw [BitVec.toNat_ofNat, atOff 128 (by decide)]
      change (sp.toNat + 128 + i.val) % 2^64 = _
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨by change (BitVec.ofNat 64 ((sp+128).toNat + i.val)).toNat + 1 ≤ _; omega,
      fun reg hr => Or.inr ?_⟩
    change _ ≤ (BitVec.ofNat 64 ((sp+128).toNat + i.val)).toNat
    have := (regionBounds reg hr).2
    omega
  simp only [Fn10fa10.doneAt, Atom.All, Atom.Holds, Fin.getElem_fin] at done_
  obtain ⟨rsp,df',rbx,rbp',r12',r13',r14',r15',mx,ft,fc,_⟩ := done_
  have spRet : fr.rsp + 8 = sp := by change stackPtr initial - 544 + 8 = stackPtr initial - 536; bv_omega
  refine ⟨out.values,out.store,reach,⟨⟨finalMemory, rsp.trans (congrArg (Value.mk 64) spRet), ?_, ?_, df',
    congrArg Value.width r12', congrArg Value.width mx, congrArg Value.width ft,
    congrArg Value.width fc⟩, ?_, ⟨peer,di' ▸ stored,valid,value⟩, digest',
    finalOps.rAt,finalOps.sAt,argWidths 9 (by decide),congrArg Value.width r14',congrArg Value.width r15'⟩⟩
  · apply rbp'.trans
    change (⟨64,b[5].get 64⟩ : Value) = _
    exact congrArg (fun v : Value => Value.mk 64 (v.get 64)) rbp
  · apply r13'.trans
    change (⟨64,b[13].get 64⟩ : Value) = _
    exact congrArg (fun v : Value => Value.mk 64 (v.get 64)) r13
  · apply rbx.trans
    change (⟨64,b[3].get 64⟩ : Value) = _
    rw [bx]
    rfl

end K256.Proofs.Verify.Wrapper
