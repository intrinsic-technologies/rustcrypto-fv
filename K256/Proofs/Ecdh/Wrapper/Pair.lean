import K256.Proofs.Ecdh.Wrapper.Pair.Memory
import K256.Proofs.Ecdh.Wrapper.Pair.Block
import K256.Proofs.Ecdh.Wrapper.Pair.Memcpy
import K256.Proofs.Ecdh.Transfer
import K256.Proofs.Ecdh.Scalar.Calls

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

theorem copyPair {s : RamState} {secret key : ByteArray} {d : Nat} {peer : Generate.Generator.Multiply.Projective}
    {a : Arguments} {m : Ram}
    (call : ValidCall ecdhDiffieHellman s [secret, key]) (state : Caller s a m)
    (r15 : a[15] = ⟨64, localSp s + 0x158⟩) (scalar : ScalarAt s m 0x10 d)
    (source : peer.Stored m (localSp s + 0x158)) :
    ∃ b n, Reaches .l10185f a m .l1018b0 b n ∧ Caller s b n ∧
      b[13] = ⟨64, 0x12a820⟩ ∧ b[14] = ⟨64, localSp s + 0xc0⟩ ∧
      ScalarAt s n 0x138 d ∧ peer.Stored n (localSp s + 0xc0) := by
  let sp := localSp s
  let staged := Generate.Generator.Multiply.Prepare.Bases.Negate.storeFour m (sp + 464)
    (Generate.Generator.Multiply.scalarWords d)
  let pushed := memStore staged (sp - 8) (0x1018b0 : BitVec 64)
  let result := memCopy pushed (sp + 192) (sp + 344) 152
  obtain ⟨guard, after, finalMem, tag, sc, pt⟩ := Pair.recordMemory (d := d) call state.toMemory source
  obtain ⟨b, step, rsp, dst, src, count, rb13, rb14, args, kept⟩ := Pair.setup (sp := sp)
    (by rw [state.rsp]; rfl) (by rw [r15]; rfl)
    (state.toMemory.window call) scalar guard (state.widths 8 (by decide)) (state.widths 9 (by decide))
  have dir := congrArg (Value.get 1) ((kept 22 (by decide)).trans state.df)
  obtain ⟨room, low, top⟩ := Scalar.stack_geometry call
  have off (k : Nat) (h : k ≤ 344) : (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
    have small : sp.toNat + k < 2 ^ 64 := by dsimp only [sp]; omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt small]
  have a192 : (sp + 192).toNat = sp.toNat + 192 := off 192 (by decide)
  have a344 : (sp + 344).toNat = sp.toNat + 344 := off 344 (by decide)
  have align := call.stackAvailable.2.2.2
  change (stackPtr s).toNat % 16 = 8 at align
  have aligned : (sp + 192).toNat % 8 = 0 := by rw [a192]; dsimp only [sp]; omega
  have win : Writable Extracted.programImage pushed (sp - 3936) 10088 := after.window call
  have read : Readable pushed (sp + 344) 152 := by slot_state region
  have write : Writable Extracted.programImage pushed (sp + 192) 152 := by slot_state region
  have endWin : Writable Extracted.programImage result (sp - 3936) 10088 := finalMem.window call
  have readable : Writable Extracted.programImage result (sp - 8) 8 :=
    endWin.of_offsets (addr_sub sp 8) (addr_sub sp 3936) (by decide)
  have slotRead : LoadOk result (sp - 8) 8 := ⟨readable.readable.low, readable.readable.present⟩
  obtain ⟨out, run, ret, mem, widths, back, preserve⟩ := Pair.copyRecord dst src count rsp dir aligned args
    read write (Or.inr (by omega)) slotRead tag (by decide)
  have exec := Ecdh.Transfer.generateExec (dst := .l12a820) (by decide) rfl run
  have reach := Scalar.resumeCall step exec ret
  have keep (i : Fin Reg.count) (hi : i.val ∈ [3, 5, 12, 15, 22, 39, 50, 51]) : out.values[i] = a[i] := by
    apply (preserve i ?_).trans (kept i ?_)
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    all_goals omega
  refine ⟨out.values, out.store, reach, ?_, (preserve 13 (by decide)).trans rb13,
    (preserve 14 (by decide)).trans rb14, mem ▸ sc, mem ▸ pt⟩
  refine ⟨mem ▸ finalMem, ?_, (keep 3 (by decide)).trans state.output, (keep 22 (by decide)).trans state.df,
    ?_, ?_, ?_, ?_⟩
  · simpa only [BitVec.sub_add_cancel] using back
  · rintro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact widths 1 (by decide)
    · exact widths 2 (by decide)
    · exact (congrArg Value.width (keep 3 (by decide))).trans (state.widths 3 (by decide))
    · exact (congrArg Value.width (keep 5 (by decide))).trans (state.widths 5 (by decide))
    · exact widths 8 (by decide)
    · exact widths 9 (by decide)
    · exact (congrArg Value.width (keep 12 (by decide))).trans (state.widths 12 (by decide))
    · exact congrArg Value.width ((preserve 13 (by decide)).trans rb13)
    · exact congrArg Value.width ((preserve 14 (by decide)).trans rb14)
    · exact (congrArg Value.width (keep 15 (by decide))).trans (state.widths 15 (by decide))
  · exact (congrArg Value.width (keep 39 (by decide))).trans state.mxcsr
  · exact (congrArg Value.width (keep 50 (by decide))).trans state.ftw
  · exact (congrArg Value.width (keep 51 (by decide))).trans state.fcw

end K256.Proofs.Ecdh.Wrapper
