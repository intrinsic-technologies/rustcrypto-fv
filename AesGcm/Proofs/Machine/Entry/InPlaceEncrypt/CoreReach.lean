import AesGcm.Proofs.Machine.Core.Encrypt
import AesGcm.Proofs.Machine.Core.Memory
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.CoreResult
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.CoreReach.Descriptor
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.CoreReach.EntryFrame
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.CoreReach.Inputs
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.CoreReach.Return
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Initialization
import AesGcm.Proofs.Machine.Runtime.Root.Program

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open AesGcm.Spec AesGcm.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

private theorem core_regions {fr af : Activation} {p : BitVec 64} {n a : Nat}
    (room : fr.low.toNat + 2848 ≤ fr.rsp.toNat)
    (sp : af.rsp = fr.rsp - 480) (low : af.low = fr.rsp - 2848)
    (ctx : af.rsi = fr.rsp - 264) (nonce : af.rdx = fr.rsi) (aad : af.rcx = fr.rdx)
    (desc : af.r9 = fr.rsp - 440) (res : af.rdi = fr.rsp - 457)
    (sep : ∀ r ∈ [span fr.rsi 12, span fr.rdx a, span p n], (callStack fr).Disjoint r)
    (dsep : ∀ r ∈ [span fr.rsi 12, span fr.rdx a], (span p n).Disjoint r) :
    (∀ r ∈ [span af.rsi 208, span af.rdx 12, span af.rcx a, span af.r9 24,
      span p n, span p n, span af.rdi 17], (callStack af).Disjoint r) ∧
    (∀ r ∈ [span af.rsi 208, span af.rdx 12, span af.rcx a, span af.r9 24],
      (span p n).Disjoint r) ∧
    (∀ r ∈ [span af.rsi 208, span af.rdx 12, span af.rcx a, span af.r9 24, span p n,
      span p n], (span af.rdi 17).Disjoint r) := by
  rw [ctx, nonce, aad, desc, res]
  have childLocal (d k : Nat) (hd : d + 8 ≤ 480) (hk : k ≤ d) :=
    childStack_disjoint_local (n := d) (count := k) room (by decide : 480 ≤ 2848) low sp hd hk
  have childExt {r} (hs : (callStack fr).Disjoint r) :=
    childStack_disjoint_external room (by decide : 480 ≤ 2848) low sp hs
  have localExt {r} (hs : (callStack fr).Disjoint r) (d k : Nat) (hd : d ≤ 2848) (hk : k ≤ d) :=
    local_span_disjoint_external (n := d) (count := k) room hd hk hs
  have localPair (d k e j : Nat) (hd : d ≤ 2848) (he : e ≤ 2848)
      (hk : k ≤ d) (hj : j ≤ e) (h : e + k ≤ d ∨ d + j ≤ e) :=
    stack_local_spans_disjoint (n := d) (count := k) (m := e) (count' := j) room hd he hk hj h
  have pn := sep (span p n) (by simp)
  have ns := sep (span fr.rsi 12) (by simp)
  have ad := sep (span fr.rdx a) (by simp)
  refine ⟨?_, ?_, ?_⟩ <;> intro r hr <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact childLocal 264 208 (by decide) (by decide)
    · exact childExt ns
    · exact childExt ad
    · exact childLocal 440 24 (by decide) (by decide)
    · exact childExt pn
    · exact childExt pn
    · exact childLocal 457 17 (by decide) (by decide)
  · rcases hr with rfl | rfl | rfl | rfl
    · exact fun x hx hy => localExt pn 264 208 (by decide) (by decide) x hy hx
    · exact dsep _ (by simp)
    · exact dsep _ (by simp)
    · exact fun x hx hy => localExt pn 440 24 (by decide) (by decide) x hy hx
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact localPair 457 17 264 208 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact localExt ns 457 17 (by decide) (by decide)
    · exact localExt ad 457 17 (by decide) (by decide)
    · exact localPair 457 17 440 24 (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact localExt pn 457 17 (by decide) (by decide)
    · exact localExt pn 457 17 (by decide) (by decide)

set_option maxHeartbeats 480000 in
theorem core_reaches {initial : RamState} {key : Vector UInt8 16} {nonce : Vector UInt8 12}
    {aad bytes : ByteArray} {capacity : Nat} {ret : BitVec 64}
    (hCall : ValidCall initial key nonce aad bytes capacity)
    (args : Values Value Reg.count) (mem : Ram)
    (hInit : initializationPost Extracted.programImage key (entryActivation initial ret) args mem) :
    ∃ nextArgs nextMem ciphertext tag,
      (LIR.program.sem (dialect Extracted.programImage)).Reaches
        ⟨⟨.l1013c8, args, mem⟩, []⟩ ⟨⟨.l101409, nextArgs, nextMem⟩, []⟩ ∧
      GCM.ciphertextAndTag .aes128 key nonce aad bytes = some (ciphertext, tag) ∧
      corePost initial ret bytes capacity ciphertext tag nextArgs nextMem := by
  let fr := entryActivation initial ret
  let code := Extracted.programImage
  let p := selectedPointer fr.r9 (args[5].get 64) fr.r8
  obtain ⟨working, _, capLoad, contextBefore, _, _, outer, typed⟩ := hInit
  change Atom.All code args mem (LIR.Aes128gcmEncryptInPlace.frameAt .l1013c8 fr) at working
  change RamWriteFrame fr.original mem [fr.region] at outer
  have frameFields := working
  obtain ⟨h4, _, h3, h12, h13, h14, h15, h39, h50, h51, _, _, _, _, _, _, hr, _, _, stack,
    room, _⟩ := frameFields
  change args[4] = ⟨64, fr.rsp - 472⟩ at h4
  change args[3] = ⟨64, fr.r9⟩ at h3
  change args[12] = ⟨64, fr.rdx⟩ at h12
  change args[13] = ⟨64, fr.rsi⟩ at h13
  change args[14] = ⟨64, fr.r8⟩ at h14
  change args[15] = ⟨64, fr.rcx⟩ at h15
  change args[39] = ⟨32, fr.mxcsr⟩ at h39
  change args[50] = ⟨16, fr.ftw⟩ at h50
  change args[51] = ⟨16, fr.fcw⟩ at h51
  change fr.low.toNat + 2848 ≤ fr.rsp.toNat at room
  change Writable code mem (fr.rsp - 2848) 2848 at stack
  change Readable mem fr.rsp 8 at hr
  have bound := hr.low
  have sub (n : Nat) (hn : n ≤ 2848) := stack_sub_toNat fr room hn
  have sub472 : (fr.rsp - (472 : BitVec 64)).toNat = fr.rsp.toNat - 472 := sub 472 (by decide)
  have sub480 : (fr.rsp - (480 : BitVec 64)).toNat = fr.rsp.toNat - 480 := sub 480 (by decide)
  have sub264 : (fr.rsp - (264 : BitVec 64)).toNat = fr.rsp.toNat - 264 := sub 264 (by decide)
  have sp : args[4].get 64 = fr.rsp - 472 := by rw [h4]; rfl
  have childSP : args[4].get 64 - 8 = fr.rsp - 480 := by rw [sp]; bv_omega
  have localWrite (n k : Nat) (hn : n ≤ 2848) (hk : k ≤ n) :
      Writable code mem (fr.rsp - BitVec.ofNat 64 n) k := by
    apply stack.sub
    · change (fr.rsp - BitVec.ofNat 64 2848).toNat ≤ _
      rw [sub 2848 (by decide), sub n hn]; omega
    · change _ ≤ (fr.rsp - BitVec.ofNat 64 2848).toNat + 2848
      rw [sub 2848 (by decide), sub n hn]; omega
  obtain ⟨callee, cont, call, label, target, guard, cmem, c4, c7, c6, c2, c1, c8, c9, keep, ct⟩ :=
    core_call false code fnCode_sub_programImage args mem
      (by rw [childSP]; exact localWrite 480 64 (by decide) (by decide))
  have eqMem : coreMemory false args mem = callee.store := cmem.symm
  have setup : RamWriteFrame mem callee.store [span (fr.rsp - 480) 64] := by
    rw [← eqMem, ← childSP]
    apply coreMemory_frame
    all_goals rw [sp, sub472]; omega
  have whole := outer.trans setup (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨fr.region, by simp, ?_, ?_⟩ <;>
      simp only [Activation.region, span, sub480] <;> omega)
  obtain ⟨cap, length, pointer, aadLength, nr, nb, ar, ab, sr, sb, dw, sep, dsep, slots⟩ :=
    core_inputs_of_validCall (ret := ret) hCall whole capLoad
  change p = fr.r8 ∨ bytes.size = 0 at pointer
  change ∀ r ∈ [span fr.rsi 12, span fr.rdx aad.size, span p bytes.size],
    (callStack fr).Disjoint r at sep
  let af := activationOfValues callee.store callee.arguments 0x101409 (fr.rsp - 2848)
  have asp : af.rsp = fr.rsp - 480 := (congrArg (fun v : Value => v.get 64) c4).trans childSP
  have ctx : af.rsi = fr.rsp - 264 := by
    change (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = _
    rw [c6, sp]; change fr.rsp - 472 + 208 = fr.rsp - 264; bv_omega
  have result : af.rdi = fr.rsp - 457 := by
    change (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = _
    rw [c7, sp]; change fr.rsp - 472 + 15 = fr.rsp - 457; bv_omega
  have desc : af.r9 = fr.rsp - 440 := by
    change (callee.arguments[9]'(by change 9 < 53; decide)).get 64 = _
    rw [c9, sp]; change fr.rsp - 472 + 32 = fr.rsp - 440; bv_omega
  have nonceReg : af.rdx = fr.rsi := by
    change (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = _; rw [c2, h13]; rfl
  have aadReg : af.rcx = fr.rdx := by
    change (callee.arguments[1]'(by change 1 < 53; decide)).get 64 = _; rw [c1, h12]; rfl
  have lenReg : af.r8 = fr.rcx := by
    change (callee.arguments[8]'(by change 8 < 53; decide)).get 64 = _; rw [c8, h15]; rfl
  obtain ⟨srcWord, dstWord, lenWord, retWord⟩ := coreMemory_loads false args mem
  rw [eqMem, h3, h14] at srcWord dstWord
  rw [eqMem, h3] at lenWord
  rw [eqMem, childSP] at retWord
  have atoms := core_entry_frame working setup asp retWord keep (ct typed)
  have contextOut : Outside [span (fr.rsp - 480) 64] (fr.rsp - 264) 208 := by
    refine ⟨?_, ?_⟩
    · rw [sub264]; omega
    · intro r hin; obtain rfl := List.mem_singleton.mp hin
      right; simp only [span, sub264, sub480]; omega
  have inputs : Core.InputsIn false key nonce aad callee.store af.rsi af.rdx af.rcx af.r8 := by
    rw [ctx, nonceReg, aadReg, lenReg]
    exact ⟨contextBefore.of_frame setup contextOut,
      (localWrite 264 208 (by decide) (by decide)).readable.of_frame setup, nr, nb, ar, ab, aadLength⟩
  have dp : af.r9 = args[4].get 64 + 32 := congrArg (fun v : Value => v.get 64) c9
  have buf : Core.BufferIn callee.store af.r9 p p bytes := by
    refine ⟨desc ▸ (localWrite 440 24 (by decide) (by decide)).readable.of_frame setup,
      ?_, ?_, ?_, sr, sb, Or.inl rfl⟩
    · rw [dp]; exact srcWord
    · rw [dp, BitVec.add_assoc]
      exact dstWord
    · rw [dp]
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using
        (congrArg BitVec.toNat lenWord).trans length
  have regs := core_regions room asp (show af.low = fr.rsp - 2848 from rfl)
    ctx nonceReg aadReg desc result sep dsep
  obtain ⟨out, exec, retTag, done, outTyped, writes, ciphertext, tag, model, status, cipherBytes, tagBytes⟩ :=
    Core.encrypt_call false code fnCode_sub_programImage key nonce aad bytes p p
      af callee label rfl atoms (ct typed)
      ⟨inputs, buf, dw, result ▸ (localWrite 457 17 (by decide) (by decide)).of_frame setup,
        slots, regs⟩
  have kept (r : Fin 53) (h : r.val ∈ [3,5,12,13,14,15,22,39,50,51]) (w : Nat) :=
    congrArg (fun v : Value => v.get w) (keep r h)
  obtain ⟨frameOut, capOut, writesOut⟩ := core_return_frame working outer setup asp rfl result
    ((kept 3 (by decide) 64).trans (congrArg (fun v : Value => v.get 64) h3))
    (kept 5 (by decide) 64)
    ((kept 12 (by decide) 64).trans (congrArg (fun v : Value => v.get 64) h12))
    ((kept 13 (by decide) 64).trans (congrArg (fun v : Value => v.get 64) h13))
    ((kept 14 (by decide) 64).trans (congrArg (fun v : Value => v.get 64) h14))
    ((kept 15 (by decide) 64).trans (congrArg (fun v : Value => v.get 64) h15))
    ((kept 39 (by decide) 32).trans (congrArg (fun v : Value => v.get 32) h39))
    ((kept 50 (by decide) 16).trans (congrArg (fun v : Value => v.get 16) h50))
    ((kept 51 (by decide) 16).trans (congrArg (fun v : Value => v.get 16) h51))
    (sep (span p bytes.size) (by simp)) pointer done writes
  have accepts : cont.Accepts (dialect code) out.tag = true := by
    simp only [StackFrame.Accepts, guard, retTag]; rfl
  change LIR.program.Exec (dialect code) ⟨callee, []⟩ out at exec
  change LIR.program.runBlock (dialect code) ⟨.l1013c8, args, mem⟩ = .call callee cont at call
  have run : (LIR.program.sem (dialect code)).Reaches ⟨⟨.l1013c8, args, mem⟩, []⟩
      ⟨cont.resume out, []⟩ := by
    apply Star.step (b := ⟨callee, [cont]⟩)
    · change LIR.program.step (dialect code) ⟨⟨.l1013c8, args, mem⟩, []⟩ = _
      rw [Program.step, call]; rfl
    · exact CFGCall.exec_reaches_resume exec cont [] accepts
  have resume : cont.resume out = ⟨.l101409, out.values, out.store⟩ := by
    change (⟨cont.target, (cont.resume out).arguments, out.store⟩ : LIR.lifted.Location) = _
    rw [CFGCall.resume_arguments, target]; rfl
  have outSP : out.values[4].get 64 = fr.rsp - 472 := congrArg (fun v : Value => v.get 64) frameOut.1
  have statusAddr : out.values[4].get 64 + 15 = af.rdi := by rw [outSP, result]; bv_omega
  have tagAddr : out.values[4].get 64 + 16 = af.rdi + 1 := by rw [outSP, result]; bv_omega
  refine ⟨out.values, out.store, ciphertext, tag, resume ▸ run, model, frameOut, outTyped,
    (congrArg BitVec.toNat capOut).trans cap, writesOut, statusAddr ▸ status, ?_, tagAddr ▸ tagBytes⟩
  rcases pointer with h | h
  · exact h ▸ cipherBytes
  · refine ⟨cipherBytes.1, fun i => False.elim ?_⟩
    have hs : ciphertext.size = bytes.size := cipherBytes.1
    have hi := i.isLt
    omega

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
