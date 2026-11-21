import K256.Proofs.Common.SignatureRun
import K256.Proofs.Generate.Wrapper.Memory
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.Generate.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Standards.SECG.ECC
  Standards.SECG.DomainParameters

variable {s : RamState} {random : ByteArray} {args : Vector Value Reg.count} {mem : Ram}

private abbrev cleanup (s : RamState) : MemoryRegion :=
  ⟨(s.regValue .rsp - 280).toNat, 120⟩

private theorem window {off : Nat} (call : ValidCall signingKeyGenerateFromRng s [random])
    (start : off ≤ 280) (stop : 168 ≤ off) :
    InRegions [cleanup s] (s.regValue .rsp - BitVec.ofNat 64 off) 8 := by
  refine ⟨_, List.mem_cons_self, ?_⟩
  change (s.regValue .rsp - 280).toNat ≤ _ ∧ _ + 8 ≤ (s.regValue .rsp - 280).toNat + 120 ∧ _
  have h := stackOffset call (off := off) (by omega)
  have b := stackOffset call (off := 280) (by decide)
  change (s.regValue .rsp - BitVec.ofNat 64 off).toNat = _ at h
  change (s.regValue .rsp - 280).toNat = _ at b
  rw [h, b]
  have room : 10584 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  have := (s.regValue .rsp).isLt
  omega

private theorem cleanup_post {m : Ram} {bytes : ByteArray}
    (call : ValidCall signingKeyGenerateFromRng s [random]) (f : CallerFrame s args mem)
    (writes : RamWriteFrame mem m [cleanup s]) (written : (outputRegion signingKeyGenerateFromRng s).HasBytes mem bytes) :
    RamWriteFrame s.external m (regions s).toList ∧
    (outputRegion signingKeyGenerateFromRng s).HasBytes m bytes ∧
    memLoad m (s.regValue .rsp - 16) 64 = s.regValue .rbx ∧
    memLoad m (s.regValue .rsp - 8) 64 = s.regValue .r14 ∧
    memLoad m (s.regValue .rsp) 64 = (returnBoundary s).rip := by
  have room : 10584 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  have low := (stackWritable (off := 0) (len := 8) call (by decide) (by decide) (by decide)).readable.low
  change (s.regValue .rsp - 0).toNat + 8 ≤ _ at low
  rw [show s.regValue .rsp - 0 = s.regValue .rsp by bv_omega] at low
  have base := stackOffset call (off := 280) (by decide)
  change (s.regValue .rsp - 280).toNat = (s.regValue .rsp).toNat - 280 at base
  have slots (off : Nat) (ho : off ≤ 16) : memLoad m (s.regValue .rsp - BitVec.ofNat 64 off) 64 =
      memLoad mem (s.regValue .rsp - BitVec.ofNat 64 off) 64 := by
    apply writes.memLoad_eq
    have a := stackOffset call (off := off) (by omega)
    change (s.regValue .rsp - BitVec.ofNat 64 off).toNat = (s.regValue .rsp).toNat - off at a
    refine ⟨by rw [a]; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    change (s.regValue .rsp - 280).toNat + 120 ≤ _
    rw [base, a]
    omega
  refine ⟨f.writes.trans writes ?_, ?_, (slots 16 (by decide)).trans f.rbx,
    (slots 8 (by decide)).trans f.r14, ?_⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, (stackRange (off := 280) (len := 120)
      call (by decide) (by decide)).1, (stackRange (off := 280) (len := 120) call (by decide) (by decide)).2.1⟩
  · refine ⟨written.1, fun i => ?_⟩
    have sep := output_stack_apart call
    have bound : (s.regValue .rdi).toNat + 97 < 2^32 := (call.outputInMemory rfl).2.1
    have size : bytes.size = 97 := written.1
    have hi := i.isLt
    have small : (s.regValue .rdi).toNat + i.val < 2^64 := by omega
    rw [writes.outside _ ?_]
    · exact written.2 i
    · change Outside _ (BitVec.ofNat 64 ((s.regValue .rdi).toNat + i.val)) 1
      refine ⟨by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]; omega, fun r hr => ?_⟩
      obtain rfl := List.mem_singleton.mp hr
      change _ ≤ (s.regValue .rsp - 280).toNat ∨ (s.regValue .rsp - 280).toNat + 120 ≤ _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, base]
      omega
  · have h := slots 0 (by decide)
    rw [show s.regValue .rsp - BitVec.ofNat 64 0 = s.regValue .rsp by bv_omega] at h
    exact h.trans f.ret

set_option maxHeartbeats 1500000 in
theorem finish {bytes : ByteArray} (call : ValidCall signingKeyGenerateFromRng s [random])
    (f : CallerFrame s args mem) (written : (outputRegion signingKeyGenerateFromRng s).HasBytes mem bytes) :
    ∃ out, LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l1025d2, args, mem⟩, []⟩ out ∧
      Common.Returned s (regions s) out ∧ (outputRegion signingKeyGenerateFromRng s).HasBytes out.store bytes := by
  let sp := s.regValue .rsp
  have rsp : Value.get 64 args[4] = sp - 280 := by rw [f.rsp]; rfl
  have inc := fun x hx => Common.fnCode_subset_programImage x (LIR.code_l1025d2 x hx)
  have writable {m : Ram} (hf : RamWriteFrame mem m [cleanup s]) {off : Nat} (h : off ≤ 10584) :=
    ((stackWritable (len := 8) call h (by omega) (by decide)).of_frame f.writes).of_frame hf
  have w0 : RamWriteFrame mem mem [cleanup s] := .refl _ _
  let m1 := memStore mem (sp - 280) (0 : BitVec 64)
  have w1 : RamWriteFrame mem m1 [cleanup s] := w0.memStore _ (window (off := 280) call (by decide) (by decide))
  have st0 : StoreOk Extracted.programImage mem (sp - 280) 8 0x1025d2 8 := ParseSignature.storeOk_of_codeRange (off := 0) (len := 8)
    (writable w0 (off := 280) (by decide)) inc (by decide)
  let m2 := memStore m1 (sp - 272) (0 : BitVec 64)
  have w2 : RamWriteFrame mem m2 [cleanup s] := w1.memStore _ (window (off := 272) call (by decide) (by decide))
  have st1 : StoreOk Extracted.programImage m1 (sp - 272) 8 0x1025da 9 := ParseSignature.storeOk_of_codeRange (off := 8) (len := 9)
    (writable w1 (off := 272) (by decide)) inc (by decide)
  let m3 := memStore m2 (sp - 264) (0 : BitVec 64)
  have w3 : RamWriteFrame mem m3 [cleanup s] := w2.memStore _ (window (off := 264) call (by decide) (by decide))
  have st2 : StoreOk Extracted.programImage m2 (sp - 264) 8 0x1025e3 9 := ParseSignature.storeOk_of_codeRange (off := 17) (len := 9)
    (writable w2 (off := 264) (by decide)) inc (by decide)
  let m4 := memStore m3 (sp - 256) (0 : BitVec 64)
  have w4 : RamWriteFrame mem m4 [cleanup s] := w3.memStore _ (window (off := 256) call (by decide) (by decide))
  have st3 : StoreOk Extracted.programImage m3 (sp - 256) 8 0x1025ec 9 := ParseSignature.storeOk_of_codeRange (off := 26) (len := 9)
    (writable w3 (off := 256) (by decide)) inc (by decide)
  let m5 := memStore m4 (sp - 192) (memLoad m4 (sp - 280) 64)
  have w5 : RamWriteFrame mem m5 [cleanup s] := w4.memStore _ (window (off := 192) call (by decide) (by decide))
  have st4 : StoreOk Extracted.programImage m4 (sp - 192) 8 0x1025f9 5 := ParseSignature.storeOk_of_codeRange (off := 39) (len := 5)
    (writable w4 (off := 192) (by decide)) inc (by decide)
  have rd4 : LoadOk m4 (sp - 280) 8 :=
    ⟨(writable w4 (off := 280) (by decide)).readable.low, (writable w4 (off := 280) (by decide)).readable.present⟩
  let m6 := memStore m5 (sp - 184) (memLoad m5 (sp - 272) 64)
  have w6 : RamWriteFrame mem m6 [cleanup s] := w5.memStore _ (window (off := 184) call (by decide) (by decide))
  have st5 : StoreOk Extracted.programImage m5 (sp - 184) 8 0x102603 5 := ParseSignature.storeOk_of_codeRange (off := 49) (len := 5)
    (writable w5 (off := 184) (by decide)) inc (by decide)
  have rd5 : LoadOk m5 (sp - 272) 8 :=
    ⟨(writable w5 (off := 272) (by decide)).readable.low, (writable w5 (off := 272) (by decide)).readable.present⟩
  let m7 := memStore m6 (sp - 176) (memLoad m6 (sp - 264) 64)
  have w7 : RamWriteFrame mem m7 [cleanup s] := w6.memStore _ (window (off := 176) call (by decide) (by decide))
  have st6 : StoreOk Extracted.programImage m6 (sp - 176) 8 0x10260d 5 := ParseSignature.storeOk_of_codeRange (off := 59) (len := 5)
    (writable w6 (off := 176) (by decide)) inc (by decide)
  have rd6 : LoadOk m6 (sp - 264) 8 :=
    ⟨(writable w6 (off := 264) (by decide)).readable.low, (writable w6 (off := 264) (by decide)).readable.present⟩
  let m8 := memStore m7 (sp - 168) (memLoad m7 (sp - 256) 64)
  have w8 : RamWriteFrame mem m8 [cleanup s] := w7.memStore _ (window (off := 168) call (by decide) (by decide))
  have st7 : StoreOk Extracted.programImage m7 (sp - 168) 8 0x102617 5 := ParseSignature.storeOk_of_codeRange (off := 69) (len := 5)
    (writable w7 (off := 168) (by decide)) inc (by decide)
  have rd7 : LoadOk m7 (sp - 256) 8 :=
    ⟨(writable w7 (off := 256) (by decide)).readable.low, (writable w7 (off := 256) (by decide)).readable.present⟩
  obtain ⟨writes, bytes', bx, r14, ret⟩ := cleanup_post call f w8 written
  have rd (off : Nat) (h : off ≤ 16) : LoadOk m8 (sp - BitVec.ofNat 64 off) 8 :=
    ⟨(writable w8 (off := off) (by omega)).readable.low, (writable w8 (off := off) (by omega)).readable.present⟩
  have rdBx : LoadOk m8 (sp - 16) 8 := rd 16 (by decide)
  have rd14 : LoadOk m8 (sp - 8) 8 := rd 8 (by decide)
  have rdRet : LoadOk m8 sp 8 := by simpa only [BitVec.sub_zero] using rd 0 (by decide)
  obtain ⟨ra, slot, low, _⟩ := call.returnAddress
  have lowRet : (memLoad m8 sp 64).toNat < 2^32 := by
    have eq : (returnBoundary s).rip = ra := memLoad_returnSlot slot
    rw [ret, eq]
    exact low
  have a8 : sp - 280 + 8 = sp - 272 := by bv_omega
  have a16 : sp - 280 + 16 = sp - 264 := by bv_omega
  have a24 : sp - 280 + 24 = sp - 256 := by bv_omega
  have a88 : sp - 280 + 88 = sp - 192 := by bv_omega
  have a96 : sp - 280 + 96 = sp - 184 := by bv_omega
  have a104 : sp - 280 + 104 = sp - 176 := by bv_omega
  have a112 : sp - 280 + 112 = sp - 168 := by bv_omega
  have a264 : sp - 280 + 264 = sp - 16 := by bv_omega
  have a272 : sp - 280 + 272 = sp - 8 := by bv_omega
  have a280 : sp - 280 + 280 = sp := by bv_omega
  have a288 : sp - 280 + 288 = sp + 8 := by bv_omega
  have fold1 : memStore mem (sp - 280) (0 : BitVec 64) = m1 := rfl
  have fold2 : memStore m1 (sp - 272) (0 : BitVec 64) = m2 := rfl
  have fold3 : memStore m2 (sp - 264) (0 : BitVec 64) = m3 := rfl
  have fold4 : memStore m3 (sp - 256) (0 : BitVec 64) = m4 := rfl
  have fold5 : memStore m4 (sp - 192) (memLoad m4 (sp - 280) 64) = m5 := rfl
  have fold6 : memStore m5 (sp - 184) (memLoad m5 (sp - 272) 64) = m6 := rfl
  have fold7 : memStore m6 (sp - 176) (memLoad m6 (sp - 264) 64) = m7 := rfl
  have fold8 : memStore m7 (sp - 168) (memLoad m7 (sp - 256) 64) = m8 := rfl
  have block : ∃ out, LIR.program.runBlock (dialect Extracted.programImage) ⟨.l1025d2, args, mem⟩ =
      .returned out ∧ Common.Returned s (regions s) out ∧ (outputRegion signingKeyGenerateFromRng s).HasBytes out.store bytes := by
    refine ⟨?_, ?eval, ?post⟩
    case eval =>
      cfg_eval [rsp, a8, a16, a24, a88, a96, a104, a112, a264, a272, a280, a288,
        st0, st1, st2, st3, st4, st5, st6, st7, rd4, rd5, rd6, rd7, rdBx, rd14, rdRet, lowRet,
        fold1, fold2, fold3, fold4, fold5, fold6, fold7, fold8, and_self]
      rfl
    case post =>
      refine ⟨⟨?_, rfl, (f.kept 22 (by decide)).trans (Reg.read_df_iff.mpr call.directionFlagUnset),
        ?_, writes, rfl⟩, bytes'⟩
      · exact congrArg (fun b => some (⟨64,b⟩ : Value)) ret
      · intro ⟨i, hi⟩ hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
        · exact congrArg (fun b => (⟨64,b⟩ : Value)) bx
        · exact f.kept 5 (by decide)
        · exact f.kept 12 (by decide)
        · exact f.kept 13 (by decide)
        · exact congrArg (fun b => (⟨64,b⟩ : Value)) r14
        · exact f.kept 15 (by decide)
  obtain ⟨out, he, post⟩ := block
  exact ⟨out, .done (congrArg (Transfer.next _ []) he), post⟩

end K256.Proofs.Generate.Wrapper
