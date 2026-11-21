import AesGcm.Proofs.Machine.Core.Encrypt.Padding
import AesGcm.Proofs.Machine.Core.Encrypt.TailCTR
import AesGcm.Proofs.Machine.Core.Encrypt.TailCopy
import AesGcm.Proofs.Machine.CTR.InitialCounter
import AesGcm.Proofs.Machine.CTR.GCTR

namespace AesGcm.Proofs.Machine.Core.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1800000 in
theorem tail (use256 : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (input : ByteArray)
    (hsize : input.size ≤ 16) (hpositive : 0 < input.size)
    (args : Values Value Reg.count) (mem : Ram) (sp schedule source destination : BitVec 64)
    (hsp : args[4].get 64 = sp) (hsource : args[15].get 64 = source)
    (hdest : args[12].get 64 = destination) (hcount : (args[14].get 64).toNat = input.size)
    (hroom : (if use256 then 0xa80 else 0x870) + 8 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hw : Writable code mem (sp - BitVec.ofNat 64 ((if use256 then 0xa80 else 0x870) + 8))
      ((if use256 then 0xa80 else 0x870) + 160))
    (hschedule : AES16.ScheduleIn (AES16.variant use256) key schedule mem)
    (hscheduleRead : Readable mem schedule (16 * ((AES16.variant use256).Nr + 1)))
    (hschedulePtr : memLoad mem (sp + 48) 64 = schedule)
    (hr : Readable mem source input.size) (hbytes : (span source input.size).HasBytes mem input)
    (hdw : Writable code mem destination input.size)
    (hsep : ∀ r ∈ [span schedule (16 * ((AES16.variant use256).Nr + 1)),
      span source input.size, span destination input.size],
      (span (sp - BitVec.ofNat 64 ((if use256 then 0xa80 else 0x870) + 8))
        ((if use256 then 0xa80 else 0x870) + 160)).Disjoint r)
    (hslots : Readable mem 0x201208 8 ∧ memLoad mem 0x201208 64 = 0x103f00 ∧
      Readable mem 0x201210 8 ∧ memLoad mem 0x201210 64 = 0x103880 ∧
      Readable mem 0x201230 8 ∧ memLoad mem 0x201230 64 = 0x101230 ∧
      Readable mem 0x201228 8 ∧ memLoad mem 0x201228 64 = 0x103eb0)
    (hslotsApart : sp.toNat + 152 ≤ 0x201208 ∨
      0x201238 + (if use256 then 0xa80 else 0x870) + 8 ≤ sp.toNat)
    (hTypes : GPRsTyped args) (hdf : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l102abe else .l10265e, args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l102b3e else .l1026de) ∧ GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      RamWriteFrame mem next.store
        [span (sp - BitVec.ofNat 64 ((if use256 then 0xa80 else 0x870) + 8))
          ((if use256 then 0xa80 else 0x870) + 96), span (sp + 136) 16, span destination input.size] ∧
      (span destination input.size).HasBytes next.store
        (AesGcm.Spec.GCM.byteArrayOfBits
          (Standards.NIST.GCM.GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
            (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock mem (sp + 56)))
            (AesGcm.Spec.GCM.bitsOfByteArray input))) := by
  let window : Nat := if use256 then 0xa80 else 0x870
  let lower := sp - BitVec.ofNat 64 (window + 8)
  let R := span lower (window + 160)
  have hlower : lower.toNat = sp.toNat - (window + 8) := by
    change (sp - BitVec.ofNat 64 (window + 8)).toNat = _
    rw [BitVec.toNat_sub_of_le (by change (window + 8) % 2^64 ≤ sp.toNat; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := sp.isLt; omega)]
  have hs8 : (sp - 8).toNat = sp.toNat - 8 := BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; omega)
  have hlow : sp.toNat + 152 ≤ 2^32 := by
    have hh := hw.readable.low
    change lower.toNat + (window + 160) ≤ 2^32 at hh
    rw [hlower] at hh
    omega
  have hplus (n : Nat) (hn : n ≤ 152) : (sp + BitVec.ofNat 64 n).toNat = sp.toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have h48 : (sp + 48).toNat = sp.toNat + 48 := hplus 48 (by decide)
  have h56 : (sp + 56).toNat = sp.toNat + 56 := hplus 56 (by decide)
  have h72 : (sp + 72).toNat = sp.toNat + 72 := hplus 72 (by decide)
  have h80 : (sp + 80).toNat = sp.toNat + 80 := hplus 80 (by decide)
  have h136 : (sp + 136).toNat = sp.toNat + 136 := hplus 136 (by decide)
  have hshort : Writable code mem (sp - 8) 160 := by
    apply hw.sub
    all_goals change _ ≤ _
    all_goals rw [show (sp - BitVec.ofNat 64 ((if use256 then 2688 else 2160) + 8)).toNat = lower.toNat from rfl, hlower, hs8]
    all_goals omega
  have remEq : args[14].get 64 = BitVec.ofNat 64 input.size := by
    apply BitVec.eq_of_toNat_eq
    rw [hcount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have padNat : (sp + args[14].get 64 + 136).toNat = sp.toNat + input.size + 136 := by
    rw [remEq]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  obtain ⟨z, zr, zl, zt, zk, zf, zz⟩ := zeroTail use256 code hcode args mem sp
    (args[14].get 64) hsp rfl (by omega) halign (by omega) hshort hslots.2.2.2.2.2.2.1 hslots.2.2.2.2.2.2.2
    hTypes hdf h39 h50 h51
  rcases z with ⟨zlabel, za, zm⟩
  dsimp only at zl zr zt zk zf zz
  subst zlabel
  change Values Value Reg.count at za
  have zk3 : za[3] = args[3] := zk 3 (by decide)
  have zk4 : za[4] = args[4] := zk 4 (by decide)
  have zk5 : za[5] = args[5] := zk 5 (by decide)
  have zk12 : za[12] = args[12] := zk 12 (by decide)
  have zk13 : za[13] = args[13] := zk 13 (by decide)
  have zk14 : za[14] = args[14] := zk 14 (by decide)
  have zk15 : za[15] = args[15] := zk 15 (by decide)
  have zk22 : za[22] = args[22] := zk 22 (by decide)
  have zk39 : za[39] = args[39] := zk 39 (by decide)
  have zk50 : za[50] = args[50] := zk 50 (by decide)
  have zk51 : za[51] = args[51] := zk 51 (by decide)
  have zfR : RamWriteFrame mem zm [R] := by
    apply (RamWriteFrame.refl _ _).trans zf
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals refine ⟨R, by simp, ?_, ?_⟩
    all_goals simp only [R, span, hlower, hs8, padNat]
    all_goals omega
  have sourceOutside : Outside [R] source input.size := by
    have hb := disjoint_bounds lower.toNat (window + 160) source.toNat input.size (by omega) hpositive (hsep (span source input.size) (by simp))
    refine ⟨by have := hr.low; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hb.symm
  have zb := hasBytes_of_frame zfR hbytes sourceOutside.1 (fun r hr ↦ outside_disjoint_span sourceOutside r hr)
  have sourceSepShort : (span (sp - 8) 160).Disjoint (span source input.size) := by
    intro x hx hy
    apply hsep (span source input.size) (by simp) x ?_ hy
    change lower.toNat ≤ x ∧ x < lower.toNat + (window + 160)
    simp only [MemoryRegion.Contains, span, hs8] at hx
    rw [hlower]
    omega
  obtain ⟨c, cr, cl, ct, ck, c3, c13, cf, csaved, cb⟩ := copyTailIn use256 code hcode za zm sp source input
    (by rw [zk4]; exact hsp) (by rw [zk15]; exact hsource)
    (by rw [zk14]; exact hcount) hsize (by omega) halign (hshort.of_frame zf)
    (hr.of_frame zf) zb sourceSepShort zt (by rw [zk22]; exact hdf)
    (by rw [zk39]; exact h39) (by rw [zk50]; exact h50)
    (by rw [zk51]; exact h51)
  rcases c with ⟨clabel, ca, cm⟩
  dsimp only at cr cl ct ck c3 c13 cf csaved cb
  subst clabel
  change Values Value Reg.count at ca
  let regions12 := [span (sp - 8) 8, span (sp + 80) 8, span (sp + 136) 16]
  have zf12 : RamWriteFrame mem zm regions12 := by
    apply (RamWriteFrame.refl _ _).trans zf
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨span (sp - 8) 8, by simp [regions12], Nat.le_refl _, Nat.le_refl _⟩
    · refine ⟨span (sp + 136) 16, by simp [regions12], ?_, ?_⟩ <;> simp only [span, h136, padNat] <;> omega
  have cf12 : RegionsWithin [span (sp - 8) 8, span (sp + 80) 8, span (sp + 136) input.size] regions12 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨span (sp - 8) 8, by simp [regions12], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨span (sp + 80) 8, by simp [regions12], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨span (sp + 136) 16, by simp [regions12], Nat.le_refl _, by simp only [span]; omega⟩
  have frame12 := zf12.trans cf cf12
  have frame12R : RamWriteFrame mem cm [R] := by
    apply (RamWriteFrame.refl _ _).trans frame12
    intro r hr
    simp only [regions12, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    all_goals refine ⟨R, by simp, ?_, ?_⟩
    all_goals simp only [R, span, hlower, hs8, h80, h136]
    all_goals omega
  have counterOutside : Outside regions12 (sp + 56) 20 := by
    refine ⟨by rw [h56]; omega, ?_⟩
    intro r hr
    simp only [regions12, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    all_goals simp only [span, h56, hs8, h80, h136]
    all_goals omega
  have initialCounter := CTR.initialCounterBlock_of_frame frame12 counterOutside
  have keyPtr : memLoad cm (sp + 48) 64 = schedule := by
    apply Eq.trans (frame12.memLoad_eq _) hschedulePtr
    refine ⟨by rw [h48]; omega, ?_⟩
    intro r hr
    simp only [regions12, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    all_goals simp only [span, h48, hs8, h80, h136]
    all_goals omega
  let zeros : ByteArray := ⟨Array.replicate (16 - input.size) 0⟩
  let padded := input ++ zeros
  have zerosSize : zeros.size = 16 - input.size := by
    change (Array.replicate (16 - input.size) (0 : UInt8)).size = _
    exact Array.size_replicate
  have paddedSize : padded.size = 16 := by simp only [padded, ByteArray.size_append, zerosSize]; omega
  have zerosBytes : (span (sp + 136 + BitVec.ofNat 64 input.size) (16 - input.size)).HasBytes cm zeros := by
    refine ⟨zerosSize, ?_⟩
    intro i
    have hi : i.val < 16 - input.size := by simpa only [zerosSize] using i.isLt
    have start : (sp + 136 + BitVec.ofNat 64 input.size).toNat = sp.toNat + 136 + input.size := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h136]
      omega
    have addr : (BitVec.ofNat 64 ((sp + 136 + BitVec.ofNat 64 input.size).toNat + i.val)).toNat =
        sp.toNat + 136 + input.size + i.val := by rw [start, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have he := cf.outside (BitVec.ofNat 64 ((sp + 136 + BitVec.ofNat 64 input.size).toNat + i.val)) (by
      refine ⟨by rw [addr]; omega, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      all_goals simp only [span, hs8, h80, h136, addr]
      all_goals omega)
    have hz := zz i.val (by rw [hcount]; exact hi)
    rw [remEq] at hz
    change cm[BitVec.ofNat 64 ((sp + 136 + BitVec.ofNat 64 input.size).toNat + i.val)]? = some zeros[i.val]
    rw [he]
    have haddress : BitVec.ofNat 64 ((sp + 136 + BitVec.ofNat 64 input.size).toNat + i.val) =
        sp + BitVec.ofNat 64 input.size + 136 + BitVec.ofNat 64 i.val := by
      rw [start]
      simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      bv_omega
    rw [haddress]
    change _ = some ((Array.replicate (16 - input.size) (0 : UInt8))[i.val]'(by rw [Array.size_replicate]; exact hi))
    simpa only [Array.getElem_replicate] using hz
  have paddedBytes : (span (sp + 136) 16).HasBytes cm padded := by
    have hz : (span (sp + 136 + BitVec.ofNat 64 input.size) zeros.size).HasBytes cm zeros := by
      rw [zerosSize]
      exact zerosBytes
    have hb := hasBytes_append cb hz (by rw [h136]; omega)
    have he : input.size + zeros.size = 16 := by rw [zerosSize]; omega
    simpa only [he] using hb
  have scheduleOutside : Outside [R] schedule (16 * ((AES16.variant use256).Nr + 1)) := by
    have hb := disjoint_bounds lower.toNat (window + 160) schedule.toNat (16 * ((AES16.variant use256).Nr + 1))
      (by omega) (by cases use256 <;> decide) (hsep (span schedule (16 * ((AES16.variant use256).Nr + 1))) (by simp))
    refine ⟨by have := hscheduleRead.low; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hb.symm
  have slotOutside (a : BitVec 64) (ha : 0x201208 ≤ a.toNat) (hb : a.toNat + 8 ≤ 0x201238) : Outside [R] a 8 := by
    refine ⟨by omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    simp only [R, span, hlower]
    omega
  have slotsCM : Readable cm 0x201208 8 ∧ memLoad cm 0x201208 64 = 0x103f00 ∧
      Readable cm 0x201210 8 ∧ memLoad cm 0x201210 64 = 0x103880 ∧
      Readable cm 0x201230 8 ∧ memLoad cm 0x201230 64 = 0x101230 := by
    obtain ⟨s0r, s0v, s1r, s1v, s3r, s3v, _, _⟩ := hslots
    exact ⟨s0r.of_frame frame12R, (frame12R.memLoad_eq (slotOutside _ (by decide) (by decide))).trans s0v,
      s1r.of_frame frame12R, (frame12R.memLoad_eq (slotOutside _ (by decide) (by decide))).trans s1v,
      s3r.of_frame frame12R, (frame12R.memLoad_eq (slotOutside _ (by decide) (by decide))).trans s3v⟩
  have ckz (r : Fin 53) (hr : r.val ∈ [4,5,12,14,15,22,39,50,51]) : ca[r] = args[r] :=
    (ck r hr).trans (zk r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      omega))
  have ckz4 : ca[4] = args[4] := ckz 4 (by decide)
  have ckz5 : ca[5] = args[5] := ckz 5 (by decide)
  have ckz12 : ca[12] = args[12] := ckz 12 (by decide)
  have ckz14 : ca[14] = args[14] := ckz 14 (by decide)
  have ckz15 : ca[15] = args[15] := ckz 15 (by decide)
  have ckz22 : ca[22] = args[22] := ckz 22 (by decide)
  have ckz39 : ca[39] = args[39] := ckz 39 (by decide)
  have ckz50 : ca[50] = args[50] := ckz 50 (by decide)
  have ckz51 : ca[51] = args[51] := ckz 51 (by decide)
  obtain ⟨t, tr, tl, tt, tk, tf, _, tb⟩ := cryptTail use256 code hcode key padded paddedSize ca cm sp schedule
    (by rw [ckz4]; exact hsp) c13 hroom halign (hw.of_frame frame12)
    (AES16.scheduleIn_of_frame hschedule frame12R scheduleOutside) (hscheduleRead.of_frame frame12)
    keyPtr paddedBytes (hsep _ (by simp)) slotsCM hslotsApart ct
    (by rw [ckz22]; exact hdf)
    (by rw [ckz39]; exact h39) (by rw [ckz50]; exact h50)
    (by rw [ckz51]; exact h51)
  rcases t with ⟨tlabel, ta, tm⟩
  dsimp only at tr tl tt tk tf tb
  subst tlabel
  change Values Value Reg.count at ta
  change RamWriteFrame cm tm [span lower (window + 64), span (sp + 72) 4, span (sp + 136) 16] at tf
  have tk3 : ta[3] = ca[3] := tk 3 (by decide)
  have tk4 : ta[4] = ca[4] := tk 4 (by decide)
  have tk5 : ta[5] = ca[5] := tk 5 (by decide)
  have tk12 : ta[12] = ca[12] := tk 12 (by decide)
  have tk13 : ta[13] = ca[13] := tk 13 (by decide)
  have tk14 : ta[14] = ca[14] := tk 14 (by decide)
  have tk15 : ta[15] = ca[15] := tk 15 (by decide)
  have tk22 : ta[22] = ca[22] := tk 22 (by decide)
  have tk39 : ta[39] = ca[39] := tk 39 (by decide)
  have tk50 : ta[50] = ca[50] := tk 50 (by decide)
  have tk51 : ta[51] = ca[51] := tk 51 (by decide)
  let regions123 := [span lower (window + 96), span (sp + 136) 16]
  have frame12Wide : RamWriteFrame mem cm regions123 := by
    apply (RamWriteFrame.refl _ _).trans frame12
    intro r hr
    simp only [regions12, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨span lower (window + 96), by simp [regions123], ?_, ?_⟩ <;> simp only [span, hlower, hs8] <;> omega
    · refine ⟨span lower (window + 96), by simp [regions123], ?_, ?_⟩ <;> simp only [span, hlower, h80] <;> omega
    · exact ⟨span (sp + 136) 16, by simp [regions123], Nat.le_refl _, Nat.le_refl _⟩
  have frame123 := frame12Wide.trans tf (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨span lower (window + 96), by simp [regions123], Nat.le_refl _, by simp only [span]; omega⟩
    · refine ⟨span lower (window + 96), by simp [regions123], ?_, ?_⟩ <;> simp only [span, hlower, h72] <;> omega
    · exact ⟨span (sp + 136) 16, by simp [regions123], Nat.le_refl _, Nat.le_refl _⟩)
  have saved : memLoad tm (sp + 80) 64 = args[13].get 64 := by
    have he := tf.memLoad_eq (a := sp + 80) (k := 64) (by
      refine ⟨by rw [h80]; omega, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      all_goals change _ ∨ _
      all_goals simp only [span, h80, h136, h72, hlower]
      all_goals omega)
    rw [he, csaved, zk13]
  let encrypted := AesGcm.Spec.GCM.byteArrayOfBits
    (Standards.NIST.GCM.GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
      (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock cm (sp + 56)))
      (AesGcm.Spec.GCM.bitsOfByteArray padded))
  have encryptedSize : encrypted.size = 16 := by
    simp only [encrypted, AesGcm.Spec.GCM.byteArrayOfBits, ByteArray.size, Vector.size_toArray]
    exact paddedSize
  let ciphertext := encrypted.extract 0 input.size
  have ciphertextSize : ciphertext.size = input.size := by
    simp only [ciphertext, ByteArray.size_extract, encryptedSize, Nat.min_eq_left hsize, Nat.sub_zero]
  have sliced : (span (sp + 136) input.size).HasBytes tm ciphertext := by
    have htb : (span (sp + 136) encrypted.size).HasBytes tm encrypted := by rw [encryptedSize]; exact tb
    have hh := hasBytes_extract htb 0 input.size (by omega) (by rw [encryptedSize]; exact hsize) (by rw [h136]; omega)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.sub_zero] using hh
  have destSepShort : (span (sp - 8) 160).Disjoint (span destination ciphertext.size) := by
    rw [ciphertextSize]
    intro x hx hy
    apply hsep (span destination input.size) (by simp) x ?_ hy
    change lower.toNat ≤ x ∧ x < lower.toNat + (window + 160)
    simp only [MemoryRegion.Contains, span, hs8] at hx
    rw [hlower]
    omega
  obtain ⟨next, nr, nl, nt, nk, n13, nf, nb⟩ := copyTailOut use256 code hcode ta tm sp destination ciphertext
    (by rw [tk4, ckz4]; exact hsp)
    (by rw [tk13]; exact c13)
    (by rw [tk12, ckz12]; exact hdest)
    (by rw [tk3]; exact c3)
    (by rw [tk14, ckz14, hcount, ciphertextSize])
    (by rw [ciphertextSize]; exact hsize) (by omega) halign (hshort.of_frame frame123)
    (by rw [ciphertextSize]; exact hdw.of_frame frame123)
    (by rw [ciphertextSize]; exact sliced) destSepShort tt
    (by rw [tk22, ckz22]; exact hdf)
    (by rw [tk39, ckz39]; exact h39)
    (by rw [tk50, ckz50]; exact h50)
    (by rw [tk51, ckz51]; exact h51)
  have frame123Wide : RamWriteFrame mem tm [span lower (window + 96), span (sp + 136) 16, span destination input.size] := by
    apply (RamWriteFrame.refl _ _).trans frame123
    intro r hr
    simp only [regions123, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨span lower (window + 96), by simp, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨span (sp + 136) 16, by simp, Nat.le_refl _, Nat.le_refl _⟩
  have hf := frame123Wide.trans nf (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨span lower (window + 96), by simp, ?_, ?_⟩ <;> simp only [span, hlower, hs8] <;> omega
    · exact ⟨span destination input.size, by simp, Nat.le_refl _, by simp only [span, ciphertextSize]; exact Nat.le_refl _⟩)
  refine ⟨next, zr.trans (cr.trans (tr.trans nr)), nl, nt, ?_, hf, ?_⟩
  · intro r hr
    by_cases hr13 : r.val = 13
    · have rr : r = 13 := Fin.ext hr13
      subst r
      exact (nt.value 13).trans (congrArg (Value.mk 64) (n13.trans saved)) |>.trans (hTypes.value 13).symm
    · have hin : r.val ∈ [4,5,12,14,15,22,39,50,51] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        omega
      exact (nk r hin).trans ((tk r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hin ⊢; omega)).trans (ckz r hin))
  · have he : ciphertext = AesGcm.Spec.GCM.byteArrayOfBits
        (Standards.NIST.GCM.GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
          (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock mem (sp + 56)))
          (AesGcm.Spec.GCM.bitsOfByteArray input)) := by
      dsimp only [ciphertext, encrypted]
      rw [CTR.gctr_bytes_extract_zero _ _ _ input.size (by rw [paddedSize]; exact hsize),
        show padded.extract 0 input.size = input from ByteArray.extract_append_eq_left rfl, initialCounter]
    rw [ciphertextSize] at nb
    rw [he] at nb
    exact nb

end AesGcm.Proofs.Machine.Core.Encrypt
