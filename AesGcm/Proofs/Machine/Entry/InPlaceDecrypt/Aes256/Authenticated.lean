import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Initialization
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Aes256.Authenticated.Buffer
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Aes256.Authenticated.Return
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Inputs
import AesGcm.Proofs.Machine.Runtime.Root.Calls
import AesGcm.Proofs.Machine.Core.Decrypt

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Aes256

open AesGcm.Spec AesGcm.Spec.Program Prelude X86 X86.Machine X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine X86.UserProcess X86Proofs
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1200000 in
theorem exec_with_tag {initial : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData sealed : ByteArray} {ret : BitVec 64}
    (hCall : InPlace.ValidCall aes256gcmDecryptInPlace initial key nonce associatedData sealed
      sealed.size sealed.size)
    (_hframe : LIR.Aes256gcmDecryptInPlace.frameInfo.Pre Extracted.programImage
      (Activation.ofEntry initial aes256gcmDecryptInPlace.minStackBytes ret) initial)
    (args : Values Value Reg.count) (mem : Ram)
    (hInit : initializationPost true Extracted.programImage key
      (Activation.ofEntry initial aes256gcmDecryptInPlace.minStackBytes ret) args mem)
    (hsize : 16 ≤ sealed.size) :
    ∃ output, LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l101560, args, mem⟩, []⟩ output ∧
      resultPost Extracted.programImage (Activation.ofEntry initial aes256gcmDecryptInPlace.minStackBytes ret)
        (sealed.size - 16) (GCM.authenticPlaintextOfCiphertextWithTag .aes256 key nonce associatedData sealed) output := by
  let entry := args
  let code := Extracted.programImage
  let fr := Activation.ofEntry initial aes256gcmDecryptInPlace.minStackBytes ret
  let ciphertext := sealed.extract 0 (sealed.size - 16)
  let tag : Vector UInt8 16 := Vector.ofFn fun i => sealed[sealed.size - 16 + i.val]'(by omega)
  have hcsize : ciphertext.size = sealed.size - 16 := by
    simp only [ciphertext, ByteArray.size_extract]
    omega
  have hlen : fr.r9.toNat = sealed.size := hCall.lengthArgumentMatchesBuffer
  obtain ⟨entryAtoms, h13len, contextBefore, outer, entryTypes⟩ := hInit
  obtain ⟨⟨lab, args, afterBranch⟩, branch, label, hmem, _, kept, typed⟩ :=
    length_runBlock true code entry mem entryTypes
  dsimp only at label hmem kept typed
  subst afterBranch
  have large : ¬ (entry[13].get 64).toNat < 16 := by rw [h13len, hlen]; omega
  simp only [large, ↓reduceIte] at label
  subst lab
  change Values Value Reg.count at args
  change LIR.program.runBlock (dialect code) ⟨.l101560, entry, mem⟩ =
    .jump ⟨.l10156b, args, mem⟩ at branch
  have working : Atom.All code args mem (LIR.Aes256gcmDecryptInPlace.frameAt .l10156b fr) := by
    obtain ⟨a,b,c,d,e,f,g,h,i,j,rest⟩ := entryAtoms
    exact ⟨(kept 4 (by decide)).trans a,(kept 22 (by decide)).trans b,(kept 3 (by decide)).trans c,
      (kept 12 (by decide)).trans d,(kept 13 (by decide)).trans e,(kept 14 (by decide)).trans f,
      (kept 15 (by decide)).trans g,(kept 39 (by decide)).trans h,(kept 50 (by decide)).trans i,
      (kept 51 (by decide)).trans j,rest⟩
  have atoms := working
  obtain ⟨h4,h22,h3,h12,h13,h14,h15,h39,h50,h51,_,_,_,_,_,_,hr,_,_,stack,room,align,
    s0r,s0,s1r,s1,s2r,s2,s3r,s3,slotSep,_⟩ := atoms
  change args[4] = ⟨64, fr.rsp - 584⟩ at h4
  change args[3] = ⟨64, fr.rcx⟩ at h3
  change args[12] = ⟨64, fr.r8⟩ at h12
  change args[13] = ⟨64, fr.r9⟩ at h13
  change args[14] = ⟨64, fr.rdx⟩ at h14
  change args[15] = ⟨64, fr.rsi⟩ at h15
  change args[22] = ⟨1, 0⟩ at h22
  change args[39] = ⟨32, fr.mxcsr⟩ at h39
  change args[50] = ⟨16, fr.ftw⟩ at h50
  change args[51] = ⟨16, fr.fcw⟩ at h51
  change fr.low.toNat + 3504 ≤ fr.rsp.toNat at room
  change fr.rsp.toNat % 16 = 8 at align
  change 0x201fe8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208 at slotSep
  change Writable code mem (fr.rsp - 3504) 3504 at stack
  change Readable mem fr.rsp 8 at hr
  have low := hr.low
  let workSP := fr.rsp - 584
  let childSP := fr.rsp - 592
  let lower := fr.rsp - 3504
  let ctx := fr.rsp - 328
  let desc := fr.rsp - 568
  have hwork : workSP.toNat = fr.rsp.toNat - 584 := stack_sub_toNat fr room (by decide : 584 ≤ 3504)
  have hchild : childSP.toNat = fr.rsp.toNat - 592 := stack_sub_toNat fr room (by decide : 592 ≤ 3504)
  have hlower : lower.toNat = fr.rsp.toNat - 3504 := stack_sub_toNat fr room (Nat.le_refl _)
  have hctx : ctx.toNat = fr.rsp.toNat - 328 := stack_sub_toNat fr room (by decide : 328 ≤ 3504)
  have hdesc : desc.toNat = fr.rsp.toNat - 568 := stack_sub_toNat fr room (by decide : 568 ≤ 3504)
  have sc : workSP - 8 = childSP := by dsimp only [workSP, childSP]; bv_omega
  have cd : workSP + 16 = desc := by dsimp only [workSP, desc]; bv_omega
  have cx : workSP + 256 = ctx := by dsimp only [workSP, ctx]; bv_omega
  have sp : args[4].get 64 = workSP := by rw [h4]; rfl
  have dst : args[12].get 64 = fr.r8 := by rw [h12]; rfl
  have len : args[13].get 64 = fr.r9 := by rw [h13]; rfl
  obtain ⟨nr, nb, ar, ab, sr, sb, wd, sep, dsep, slots⟩ := buffer_inputs_of_validCall hCall outer
  change ∀ r ∈ [span fr.rsi 12, span fr.rdx associatedData.size, span fr.r8 sealed.size], (callStack fr).Disjoint r at sep
  change ∀ r ∈ [span fr.rsi 12, span fr.rdx associatedData.size], (span fr.r8 (sealed.size - 16)).Disjoint r at dsep
  change Readable mem fr.r8 sealed.size at sr
  have bound := sr.low
  have workRead : Readable mem workSP 40 := stack.readable.sub
    (by change lower.toNat ≤ workSP.toNat; omega)
    (by change workSP.toNat + 40 ≤ lower.toNat + 3504; omega)
  have setupWrite : Writable code mem childSP 48 := stack.sub
    (by change lower.toNat ≤ childSP.toNat; omega)
    (by change childSP.toNat + 48 ≤ lower.toNat + 3504; omega)
  have tagAddr : (fr.r8 + fr.r9 - (16 : BitVec 64)).toNat = fr.r8.toNat + (sealed.size - 16) := by
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_add, hlen, Nat.mod_eq_of_lt (by omega)]
      change _ - 16 = _
      omega
    · change 16 ≤ (fr.r8 + fr.r9).toNat
      rw [BitVec.toNat_add, hlen, Nat.mod_eq_of_lt (by omega)]
      omega
  obtain ⟨callee, cont, call, calleeLab, target, guard, c4, c7, c8, c9, c6, c2, c1,
    keep, ctyped, cmem⟩ := core_runBlock true code fnCode_sub_programImage args mem typed
      (by rw [sp, sc]; exact setupWrite)
      (by rw [dst, len]; exact sr.sub (by omega) (by omega))
  have setup : RamWriteFrame mem callee.store [span childSP 48] := by
    rw [cmem]
    simpa only [sp, sc] using coreMemory_frame true args mem (by rw [sp]; omega) (by rw [sp]; omega)
  let af := activationOfValues callee.store callee.arguments 0x1015af lower
  have asp : af.rsp = childSP := by change (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = _; rw [c4, sp]; exact sc
  have alow : af.low = lower := rfl
  have ac : af.rdi = ctx := by change (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = _; rw [c7, sp]; exact cx
  have ad : af.r8 = desc := by change (callee.arguments[8]'(by change 8 < 53; decide)).get 64 = _; rw [c8, sp]; exact cd
  have atag : af.r9 = workSP := by change (callee.arguments[9]'(by change 9 < 53; decide)).get 64 = _; rw [c9, sp]; rfl
  have an : af.rsi = fr.rsi := by change (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = _; rw [c6,h15]; rfl
  have aa : af.rdx = fr.rdx := by change (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = _; rw [c2,h14]; rfl
  have aal : af.rcx = fr.rcx := by change (callee.arguments[1]'(by change 1 < 53; decide)).get 64 = _; rw [c1,h3]; rfl
  have localExternal {r : MemoryRegion} (hs : (callStack fr).Disjoint r)
      (n k : Nat) (hn : n ≤ 3504) (hk : k ≤ n) :=
    local_span_disjoint_external (n := n) (count := k) room hn hk hs
  have childExternal {r : MemoryRegion} (hs : (callStack fr).Disjoint r) :=
    childStack_disjoint_external room (by decide : 592 ≤ 3504) alow asp hs
  have externalBytes {p : BitVec 64} {n : Nat} {b : ByteArray}
      (hb : (span p n).HasBytes mem b) (read : Readable mem p n)
      (hs : (callStack fr).Disjoint (span p n)) : (span p n).HasBytes callee.store b :=
    hasBytes_of_frame setup hb (by change p.toNat + n ≤ 2^64; have := read.low; omega) (by
      intro r hin
      obtain rfl := List.mem_singleton.mp hin
      exact fun x hx hy => localExternal hs 592 48 (by decide) (by decide) x hy hx)
  have sepFull : (callStack fr).Disjoint (span fr.r8 sealed.size) := sep _ (by simp)
  have sepCipher : (callStack fr).Disjoint (span fr.r8 ciphertext.size) := by
    intro x hx hy
    apply sepFull x hx
    simp only [MemoryRegion.Contains, span, hcsize] at hy ⊢
    omega
  have setupApart : Outside [span childSP 48] fr.r8 sealed.size := by
    refine ⟨by omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    exact disjoint_bounds fr.r8.toNat sealed.size childSP.toNat 48 (by omega) (by decide)
      (fun x hx hy => localExternal sepFull 592 48 (by decide) (by decide) x hy hx)
  have contextOut : Outside [span childSP 48] ctx 272 := by
    refine ⟨by omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    right
    simp only [span, hctx, hchild]
    omega
  have input : Core.InputsIn true key nonce associatedData callee.store af.rdi af.rsi af.rdx af.rcx := by
    rw [ac, an, aa, aal]
    change GcmContext.ContextIn .aes256 key (workSP + 256) mem at contextBefore
    rw [cx] at contextBefore
    refine ⟨contextBefore.of_frame setup contextOut, ?_, nr.of_frame setup,
      externalBytes nb nr (sep _ (by simp)), ar.of_frame setup, externalBytes ab ar (sep _ (by simp)),
      hCall.associatedDataLengthArgumentMatchesData⟩
    apply (stack.readable.of_frame setup).sub
    · change lower.toNat ≤ ctx.toNat; omega
    · change ctx.toNat + 272 ≤ lower.toNat + 3504; omega
  have buf : Core.BufferIn callee.store af.r8 fr.r8 fr.r8 ciphertext := by
    rw [ad, cmem]
    have h := coreMemory_buffer true args mem sealed (by rw [len, hlen]) (by rw [dst]; exact sb)
      (by rw [dst]; exact sr) (by rw [sp]; exact workRead) (by rw [sp]; omega) hsize
      (by rw [sp, sc, dst]; exact setupApart)
    simpa only [sp, cd, dst] using h
  have tagBytes : (span af.r9 16).HasBytes callee.store ⟨tag.toArray⟩ := by
    rw [atag, cmem]
    have h := coreMemory_tag true args mem sealed (by rw [len, hlen]) (by rw [dst]; exact sb)
      (by rw [dst]; exact sr) (by rw [sp]; exact workRead) (by rw [sp]; omega) hsize
    simpa only [sp] using h
  have slotOutside (addr : BitVec 64) (hlo : 0x201208 ≤ addr.toNat)
      (hhi : addr.toNat + 8 ≤ 0x201238) : Outside [span childSP 48] addr 8 := by
    refine ⟨by omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hchild]; omega
  have slotValues : Atom.All code callee.arguments callee.store
      (LIR.Fn102720.frameInfo.callSlotAtoms LIR.Fn102720.frameInfo.callSlots af) := by
    exact ⟨s0r.of_frame setup,(setup.memLoad_eq (slotOutside 0x201208 (by decide) (by decide))).trans s0,
      s1r.of_frame setup,(setup.memLoad_eq (slotOutside 0x201210 (by decide) (by decide))).trans s1,
      s2r.of_frame setup,(setup.memLoad_eq (slotOutside 0x201228 (by decide) (by decide))).trans s2,
      s3r.of_frame setup,(setup.memLoad_eq (slotOutside 0x201230 (by decide) (by decide))).trans s3,
      (by change 0x201d98 ≤ af.rsp.toNat ∨ af.rsp.toNat ≤ 0x201208; rw [asp,hchild]; omega), trivial⟩
  have fp39 : callee.arguments[39]'(by change 39 < 53; decide) = ⟨32, fr.mxcsr⟩ := (keep 39 (by decide)).trans h39
  have fp50 : callee.arguments[50]'(by change 50 < 53; decide) = ⟨16, fr.ftw⟩ := (keep 50 (by decide)).trans h50
  have fp51 : callee.arguments[51]'(by change 51 < 53; decide) = ⟨16, fr.fcw⟩ := (keep 51 (by decide)).trans h51
  have calleeSP : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = childSP := asp
  have childLocal (n k : Nat) (hn : n + 8 ≤ 592) (hk : k ≤ n) :=
    childStack_disjoint_local (n := n) (count := k) room (by decide : 592 ≤ 3504) alow asp hn hk
  have localApart (n k m j : Nat) (hn : n ≤ 3504) (hm : m ≤ 3504) (hk : k ≤ n) (hj : j ≤ m)
      (apart : m + k ≤ n ∨ n + j ≤ m) :=
    stack_local_spans_disjoint (n := n) (m := m) (count := k) (count' := j) room hn hm hk hj apart
  have runCore : Core.DecryptCall true code key nonce associatedData ciphertext tag fr.r8 fr.r8 :=
    Core.decrypt_call true code fnCode_sub_programImage key nonce associatedData ciphertext tag fr.r8 fr.r8
  obtain ⟨out, exec, retTag, doneAtoms, outTypes, writes, post⟩ :=
    callResultContract_exec_values LIR.lifted code .l102720 LIR.Fn102720.frameInfo _ _ _ runCore
      callee.store callee.arguments 0x1015af lower ctyped (by rw [fp39]; rfl) (by rw [fp50]; rfl)
      (by rw [fp51]; rfl) ((keep 22 (by decide)).trans h22)
      (by rw [calleeSP]; exact (setupWrite.readable.sub (Nat.le_refl _) (by omega)).of_frame setup)
      (by rw [calleeSP, cmem]; simpa only [sp, sc, ↓reduceIte] using (coreMemory_loads true args mem).2.2.2.2.2)
      (by decide)
      (by intro _; rw [calleeSP]; change Writable code callee.store (childSP - 2912) 2912
          have he : childSP - 2912 = lower := by dsimp only [childSP, lower]; bv_omega
          rw [he]; exact (stack.of_frame setup).sub (Nat.le_refl _) (Nat.add_le_add_left (by decide : 2912 ≤ 3504) _))
      (by rw [calleeSP]; change lower.toNat + 2912 ≤ childSP.toNat; omega)
      (by rw [calleeSP, hchild]; omega) slotValues (by
        refine ⟨input, buf, ?_, ?_, tagBytes, ?_, ?_, ?_, ?_, ?_⟩
        · change Writable code callee.store af.r8 24
          rw [ad]
          apply (stack.of_frame setup).sub
          · change lower.toNat ≤ desc.toNat; omega
          · change desc.toNat + 24 ≤ lower.toNat + 3504; omega
        · change Readable callee.store af.r9 16
          rw [atag]
          exact (workRead.sub (Nat.le_refl _) (by omega)).of_frame setup
        · rw [hcsize]; intro hp; exact (wd hp).of_frame setup
        · intro slot hs
          refine ⟨(hcsize ▸ slots slot hs), ?_⟩
          change (span af.r8 24).Disjoint (span slot 8)
          rw [ad]
          have sbound : 0x201208 ≤ slot.toNat ∧ slot.toNat + 8 ≤ 0x201238 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
            rcases hs with rfl | rfl | rfl | rfl <;> decide
          intro x hx hy
          simp only [MemoryRegion.Contains, span, hdesc] at hx hy
          omega
        · change ∀ r ∈ [span af.rdi 272, span af.rsi 12, span af.rdx associatedData.size, span af.r8 24,
            span af.r9 16, span fr.r8 ciphertext.size, span fr.r8 ciphertext.size], (callStack af).Disjoint r
          rw [ac, an, aa, ad, atag]
          intro r hin
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact childLocal 328 272 (by decide) (by decide)
          · exact childExternal (sep _ (by simp))
          · exact childExternal (sep _ (by simp))
          · exact childLocal 568 24 (by decide) (by decide)
          · exact childLocal 584 16 (by decide) (by decide)
          · exact childExternal sepCipher
          · exact childExternal sepCipher
        · change ∀ r ∈ [span af.rdi 272, span af.rsi 12, span af.rdx associatedData.size, span af.r8 24,
            span af.r9 16], (span fr.r8 ciphertext.size).Disjoint r
          rw [ac, an, aa, ad, atag]
          intro r hin
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
          rcases hin with rfl | rfl | rfl | rfl | rfl
          · exact fun x hx hy => localExternal sepCipher 328 272 (by decide) (by decide) x hy hx
          · rw [hcsize]; exact dsep _ (by simp)
          · rw [hcsize]; exact dsep _ (by simp)
          · exact fun x hx hy => localExternal sepCipher 568 24 (by decide) (by decide) x hy hx
          · exact fun x hx hy => localExternal sepCipher 584 16 (by decide) (by decide) x hy hx
        · change ∀ r ∈ [span af.rdi 272, span af.rsi 12, span af.rdx associatedData.size, span af.r9 16,
            span fr.r8 ciphertext.size, span fr.r8 ciphertext.size], (span af.r8 24).Disjoint r
          rw [ac, an, aa, ad, atag]
          intro r hin
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl
          · exact localApart 568 24 328 272 (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact localExternal (sep _ (by simp)) 568 24 (by decide) (by decide)
          · exact localExternal (sep _ (by simp)) 568 24 (by decide) (by decide)
          · exact localApart 568 24 584 16 (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact localExternal sepCipher 568 24 (by decide) (by decide)
          · exact localExternal sepCipher 568 24 (by decide) (by decide))
  change RamWriteFrame af.original out.store [af.region, span fr.r8 ciphertext.size, span (af.r8 + 8) 8] at writes
  let result := AesGcm.Spec.GCM.authenticPlaintext .aes256 key nonce associatedData ciphertext tag
  obtain ⟨final, exitExec, finalPost⟩ := return_from_core (sealed := sealed) (result := result)
    working outer setup asp alow (ad.trans cd.symm)
    (congrArg (fun v => v.get 32) fp39) (congrArg (fun v => v.get 16) fp50)
    (congrArg (fun v => v.get 16) fp51) hsize sepFull doneAtoms outTypes
    (by rw [← hcsize]; exact writes) (by
      change (match result with | some p => _ | none => _) at post
      cases h : result with
      | none => simpa only [h] using post
      | some p =>
        simp only [h] at post
        exact ⟨post.1, hcsize ▸ post.2.1⟩)
  have calleeExec : LIR.program.Exec (dialect code) ⟨callee, []⟩ out := by
    change LIR.program.Exec (dialect code) ⟨⟨callee.label, callee.arguments, callee.store⟩, []⟩ out
    rw [calleeLab]
    exact exec
  have resumeExec : LIR.program.Exec (dialect code) ⟨cont.resume out, []⟩ final := by
    change LIR.program.Exec (dialect code) ⟨⟨cont.target, (cont.resume out).arguments, out.store⟩, []⟩ final
    rw [target, CFGCall.resume_arguments]
    exact exitExec
  have accepts : cont.Accepts (dialect code) out.tag = true := by
    simp only [StackFrame.Accepts, guard, retTag]
    rfl
  refine ⟨final, Program.Exec.next (next := ⟨⟨.l10156b, args, mem⟩, []⟩) ?_
    (CFGCall.exec_call call calleeExec accepts resumeExec), ?_⟩
  · change LIR.program.step (dialect code) ⟨⟨.l101560, entry, mem⟩, []⟩ = _
    rw [Program.step, branch]
    rfl
  · simpa only [AesGcm.Spec.GCM.authenticPlaintextOfCiphertextWithTag, dite_eq_left hsize] using finalPost

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Aes256
