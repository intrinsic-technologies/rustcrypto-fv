import K256.Proofs.Signing.Composition.Attempt.Return.Recovery.State
import K256.Proofs.Signing.Composition.Attempt.Call
import K256.Proofs.Signing.Composition.Attempt.Return.Recovery.Memory
import K256.Proofs.Signing.Scalar.Normalize
import K256.Proofs.Signing.Transfer.Verify
import K256.Proofs.Signing.LIR.Generated.Values
import K256.Proofs.Common.Tactic
import K256.Proofs.Sec1.Serialize.Layout

namespace K256.Proofs.Signing.Composition.Attempt.Return.Recovery

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

private theorem normalizePush {a : Registers} {m : Ram} {p : BitVec 64}
    (rsp : a[4].get 64 = p)
    (push : StoreOk Extracted.programImage m (p-8) 8 0x105e0c 5) :
    ∃ b, LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105dff,a,m⟩ =
      .call ⟨.l104c90,b,memStore m (p-8) (0x105e11 : BitVec 64)⟩ (resume .l105e11 0x105e11) ∧
      b[4] = ⟨64,p-8⟩ ∧ b[6] = ⟨64,p+192⟩ ∧ b[7] = ⟨64,p+8⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  refine ⟨?_,?run,?post⟩
  case run =>
    cfg_eval [rsp,push]
    rfl
  refine ⟨rfl,rfl,rfl,?_⟩
  intro ⟨i,_⟩ h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem normalizeEntry {s : RamState} {secret msg : ByteArray} {b : Registers} {t : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (mem : Memory s t)
    (bsp : b[4] = ⟨64,sp s-8⟩) (df : b[22] = ⟨1,0⟩)
    (gp : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → b[i].width = 64)
    (fp : b[39].width = 32 ∧ b[50].width = 16 ∧ b[51].width = 16)
    (args : ParseSignature.ArgumentWidths b) (ret : memLoad t (sp s-8) 64 = 0x105e11) :
    Atom.All Extracted.programImage b t (Verify.LIR.Fn104c90.frameAt .l104c90 (activation s t b 464 0x105e11)) := by
  let fr := activation s t b 464 0x105e11
  let info := {Verify.LIR.Fn104c90.frameInfo with callSlots := []}
  have h := childAtoms call mem info rfl (by decide) (by decide) bsp df gp fp args ret (by decide)
  have got := Verify.LIR.Fn104c90.callSlots_loaded (sections := Extracted.programSections)
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (mem.image call)
  have g0 := got (0x203de0,0x129770) (by decide)
  have g1 := got (0x203e20,0x100a20) (by decide)
  have sep := Sec1.Serialize.writable_copy_slot_apart (mem.window call) (by decide)
  have bottom := Common.stackOffset (off := 11192) call.stackAvailable (by decide)
  change (stackPtr s-11192).toNat = (stackPtr s).toNat-11192 at bottom
  apply (Atom.all_append (info.entryAtoms fr)
    [.readable 0x203de0 8,.mem 0x203de0 64 0x129770,.readable 0x203e20 8,.mem 0x203e20 64 0x100a20,
      .fact (0x203ff8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]).2
  refine ⟨h,g0.1,g0.2,g1.1,g1.2,?_,trivial⟩
  change 0x203ff8 ≤ (sp s-8).toNat ∨ (sp s-8).toNat ≤ 0x203de0
  obtain ⟨room,_,base⟩ := stackBounds call
  have below : (sp s-8).toNat = (sp s).toNat-8 := belowNat call (by decide)
  omega

theorem normalize {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {r sigS : Nat}
    (input : Staged s d r sigS a m) (nz : ¬ (r = 0 ∨ sigS = 0))
    (rBound : r < domain.n) (sBound : sigS < domain.n) :
    ∃ b n, Reach (core .l105dff a m) (core .l105e11 b n) ∧ Normalized s d r sigS b n := by
  obtain ⟨room,high,base⟩ := stackBounds call
  have below : (sp s-8).toNat = (sp s).toNat-8 := belowNat call (by decide)
  have floor : (sp s-8-464).toNat = (sp s).toNat-472 := by
    rw [BitVec.sub_sub]
    exact belowNat call (by decide)
  have above : (sp s+8).toNat = (sp s).toNat+8 := offsetNat call (by decide)
  have slot : Writable Extracted.programImage m (sp s-8) 8 := by
    rw [addr_sub]
    exact stackWindow call input.toMemory (by decide)
  have guard : StoreOk Extracted.programImage m (sp s-8) 8 0x105e0c 5 :=
    ParseSignature.storeOk_of_codeRange (off := 13) slot
      (fun x hx => Common.fnCode_subset_programImage x (LIR.code_l105dff x hx)) (by decide)
  obtain ⟨b,step,bsp,bsi,bdi,keep⟩ := normalizePush
    (show a[4].get 64 = sp s from congrArg (Value.get 64) input.rsp) guard
  let t := memStore m (sp s-8) (0x105e11 : BitVec 64)
  let fr := activation s t b 464 0x105e11
  have pushed : RamWriteFrame m t [⟨(sp s-8).toNat,8⟩] :=
    (RamWriteFrame.refl _ _).memStore _ ⟨_,List.mem_singleton_self _,
      by simp only [InRegion,Nat.reduceDiv]; have := slot.readable.low; omega⟩
  have mem := preserveCore call input.toCoreMemory pushed (by
    intro t ht
    obtain rfl := List.mem_singleton.mp ht
    change _ ≤ (sp s-8).toNat ∧ (sp s-8).toNat+8 ≤ _
    omega)
  have ret : memLoad t (sp s-8) 64 = 0x105e11 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have df := (keep 22 (by decide)).trans input.df
  have args : ParseSignature.ArgumentWidths b := by
    intro ⟨i,hi⟩ h
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    · exact congrArg Value.width bdi
    · exact congrArg Value.width bsi
    · exact (congrArg Value.width (keep 2 (by decide))).trans (input.args 2 (by decide))
    · exact (congrArg Value.width (keep 1 (by decide))).trans (input.args 1 (by decide))
    · exact (congrArg Value.width (keep 8 (by decide))).trans (input.args 8 (by decide))
    · exact (congrArg Value.width (keep 9 (by decide))).trans (input.args 9 (by decide))
  have gp (i : Fin Reg.count) (h : i.val ∈ Activation.calleeSavedNumbers) : b[i].width = 64 := by
    apply (congrArg Value.width (keep i ?_)).trans (input.saved i h)
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    omega
  have fp : b[39].width = 32 ∧ b[50].width = 16 ∧ b[51].width = 16 :=
    ⟨(congrArg Value.width (keep 39 (by decide))).trans input.fp.1,
     (congrArg Value.width (keep 50 (by decide))).trans input.fp.2.1,
     (congrArg Value.width (keep 51 (by decide))).trans input.fp.2.2⟩
  have entry := normalizeEntry call mem.toMemory bsp df gp fp args ret
  have dst : fr.rdi = sp s+8 := congrArg (Value.get 64) bdi
  have src : fr.rsi = sp s+192 := congrArg (Value.get 64) bsi
  have src' : fr.rsi+32 = sp s+224 := by rw [src,BitVec.add_assoc]; rfl
  have apart (o : Nat) (lo : 0 < o) (hi : o ≤ 224) :
      Outside [⟨(sp s-8).toNat,8⟩] (sp s+BitVec.ofNat 64 o) 32 := by
    rw [Outside,offsetNat call (by omega)]
    exact ⟨by omega,by intro t ht; obtain rfl := List.mem_singleton.mp ht; right; change (sp s-8).toNat+8 ≤ _; omega⟩
  have wr : Writable Extracted.programImage t fr.rdi 64 := dst ▸ stackWindow call mem.toMemory (by decide)
  have rd : Readable t fr.rsi 64 := src ▸ (stackWindow call mem.toMemory (by decide)).readable
  obtain ⟨out,run,tag,done,first,second,writes⟩ := Scalar.normalize (fr := fr) entry (mem.image call)
    rfl (by change 464 ≤ (sp s-8).toNat; omega) (by change (sp s-8).toNat+264 < 2^32; omega)
    (by rw [dst]; change sp s+8 = sp s-8+16; bv_omega)
    (by rw [src]; change sp s+192 = sp s-8+200; bv_omega) wr rd
    (src ▸ input.first.of_frame pushed (by decide) (apart 192 (by decide) (by decide)))
    (src' ▸ input.second.of_frame pushed (by decide) (apart 224 (by decide) (by decide)))
    (by omega) rBound (by omega) sBound
  have memory := preserveCore call mem writes (by
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    · change _ ≤ (sp s-8-464).toNat ∧ (sp s-8-464).toNat+((sp s-8).toNat-(sp s-8-464).toNat) ≤ _
      omega
    · change _ ≤ fr.rdi.toNat ∧ fr.rdi.toNat+64 ≤ _
      rw [dst,above]
      omega)
  have full := callReaches step (Signing.Transfer.verifyExec (by simp only [Signing.Transfer.sharedLabels,List.mem_cons,true_or,or_true]) run) tag
  simp only [Verify.LIR.Fn104c90.doneAt,Atom.All,Atom.Holds] at done
  have spEq : fr.rsp+8 = sp s := BitVec.sub_add_cancel _ _
  rw [dst] at first second
  rw [BitVec.add_assoc] at second
  exact ⟨_,_,full,memory,spEq ▸ done.1,done.2.1,first,second⟩

end K256.Proofs.Signing.Composition.Attempt.Return.Recovery
