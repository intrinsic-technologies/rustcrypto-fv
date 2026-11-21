import AesGcm.Proofs.Machine.Core.Decrypt.Padding
import AesGcm.Proofs.Machine.Core.Decrypt.Copy
import AesGcm.Proofs.Machine.Core.Decrypt.TailCTR
import AesGcm.Proofs.Machine.CTR.GCTR

namespace AesGcm.Proofs.Machine.Core.Decrypt
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1800000 in
theorem tail_reaches (use256 : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (crypt : CTR.CryptCall use256 code key)
    (input : ByteArray)
    (hsize : input.size ≤ 16) (hpositive : 0 < input.size)
    (args : Values Value Reg.count) (mem : Ram) (sp schedule source descriptor destination : BitVec 64)
    (hsp : args[4].get 64 = sp) (hsource : args[13].get 64 = source)
    (hcount : (args[14].get 64).toNat = input.size) (hcounter : args[15].get 64 = sp + 96)
    (hroom : (if use256 then 2688 else 2160) + 8 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hw : Writable code mem (sp - BitVec.ofNat 64 ((if use256 then 2688 else 2160) + 8))
      ((if use256 then 2688 else 2160) + 176))
    (hschedule : AES16.ScheduleIn (AES16.variant use256) key schedule mem)
    (hscheduleRead : Readable mem schedule (16 * ((AES16.variant use256).Nr + 1)))
    (hkey : memLoad mem (sp + 88) 64 = schedule)
    (hr : Readable mem source input.size) (hbytes : (span source input.size).HasBytes mem input)
    (hrdesc : Readable mem descriptor 24) (hdescriptor : memLoad mem (sp + 64) 64 = descriptor)
    (hdestination : memLoad mem (descriptor + 8) 64 = destination)
    (hdw : Writable code mem destination input.size)
    (hsep : ∀ r ∈ [span schedule (16 * ((AES16.variant use256).Nr + 1)),
      span source input.size,span destination input.size,span descriptor 24],
      (span (sp - BitVec.ofNat 64 ((if use256 then 2688 else 2160) + 8))
        ((if use256 then 2688 else 2160) + 176)).Disjoint r)
    (hslots : Readable mem 0x201208 8 ∧ memLoad mem 0x201208 64 = 0x103f00 ∧
      Readable mem 0x201210 8 ∧ memLoad mem 0x201210 64 = 0x103880 ∧
      Readable mem 0x201230 8 ∧ memLoad mem 0x201230 64 = 0x101230 ∧
      Readable mem 0x201228 8 ∧ memLoad mem 0x201228 64 = 0x103eb0)
    (hslotsApart : sp.toNat + 168 ≤ 0x201208 ∨
      0x201238 + (if use256 then 2688 else 2160) + 8 ≤ sp.toNat)
    (hTypes : GPRsTyped args) (hdf : args[22] = ⟨1,0⟩)
    (h39 : args[39] = ⟨32,args[39].get 32⟩)
    (h50 : args[50] = ⟨16,args[50].get 16⟩)
    (h51 : args[51] = ⟨16,args[51].get 16⟩) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l1028e4 else .l102484,args,mem⟩,[]⟩ ⟨next,[]⟩ ∧
      next.label = (if use256 then .l10295f else .l1024ff) ∧ GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [4,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (next.arguments[5]'(by change 5 < 53; decide)).get 8 = args[0].get 8 ∧
      RamWriteFrame mem next.store
        [span (sp - BitVec.ofNat 64 ((if use256 then 2688 else 2160) + 8))
          ((if use256 then 2688 else 2160) + 64), span (sp + 112) 4,span (sp + 152) 16,
          span destination input.size] ∧
      (span destination input.size).HasBytes next.store (AesGcm.Spec.GCM.byteArrayOfBits
        (Standards.NIST.GCM.GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
          (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock mem (sp + 96)))
          (AesGcm.Spec.GCM.bitsOfByteArray input))) := by
  let window : Nat := if use256 then 2688 else 2160
  let lower := sp - BitVec.ofNat 64 (window + 8)
  let R := span lower (window + 176)
  have nlow : lower.toNat = sp.toNat - (window + 8) := by
    change (sp - BitVec.ofNat 64 (window + 8)).toNat = _
    rw [BitVec.toNat_sub_of_le (by change (window + 8) % 2^64 ≤ sp.toNat; omega),
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := sp.isLt; omega)]
  have ns : (sp - 8).toNat = sp.toNat - 8 := BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; omega)
  have low : sp.toNat + 168 ≤ 2^32 := by
    have hh := hw.readable.low
    change lower.toNat + (window + 176) ≤ 2^32 at hh
    rw [nlow] at hh
    omega
  have plus (n : Nat) (hn : n ≤ 168) : (sp + BitVec.ofNat 64 n).toNat = sp.toNat + n := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  have n64 : (sp + 64).toNat = sp.toNat + 64 := plus 64 (by decide)
  have n88 : (sp + 88).toNat = sp.toNat + 88 := plus 88 (by decide)
  have n96 : (sp + 96).toNat = sp.toNat + 96 := plus 96 (by decide)
  have n112 : (sp + 112).toNat = sp.toNat + 112 := plus 112 (by decide)
  have n152 : (sp + 152).toNat = sp.toNat + 152 := plus 152 (by decide)
  have short : Writable code mem (sp - 8) 176 := by
    apply hw.sub <;> change _ ≤ _ <;> rw [show (sp - BitVec.ofNat 64 ((if use256 then 2688 else 2160) + 8)).toNat = lower.toNat from rfl,nlow,ns] <;> omega
  have external (ptr : BitVec 64) (count : Nat) (hread : Readable mem ptr count) (hp : 0 < count)
      (hs : R.Disjoint (span ptr count)) : Outside [R] ptr count := by
    have ap := disjoint_bounds _ _ _ _ (by change 0 < window + 176; omega) hp hs
    refine ⟨Nat.le_trans hread.low (by decide),?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    exact ap.symm
  have shortSep (ptr : BitVec 64) (count : Nat) (hs : R.Disjoint (span ptr count)) :
      (span (sp - 8) 176).Disjoint (span ptr count) := by
    intro x hx hy
    apply hs x ?_ hy
    simp only [R,span,MemoryRegion.Contains,nlow,ns] at hx ⊢
    omega
  have remEq : args[14].get 64 = BitVec.ofNat 64 input.size := by
    apply BitVec.eq_of_toNat_eq
    rw [hcount,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have padNat : (sp + args[14].get 64 + 152).toNat = sp.toNat + input.size + 152 := by
    rw [remEq]
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat,BitVec.reduceToNat]
    omega
  obtain ⟨z,zr,zl,zt,zk,zstatus,zf,zz⟩ := zero_tail_reaches use256 code hcode args mem sp
    (args[14].get 64) hsp rfl (by omega) halign (by omega) short
    hslots.2.2.2.2.2.2.1 hslots.2.2.2.2.2.2.2 hTypes hdf h39 h50 h51
  rcases z with ⟨zl',za,zm⟩
  dsimp only at zr zl zt zk zstatus zf zz
  subst zl'
  change Values Value Reg.count at za
  have zk3 : za[3] = args[3] := zk 3 (by decide)
  have zk4 : za[4] = args[4] := zk 4 (by decide)
  have zk12 : za[12] = args[12] := zk 12 (by decide)
  have zk13 : za[13] = args[13] := zk 13 (by decide)
  have zk14 : za[14] = args[14] := zk 14 (by decide)
  have zk15 : za[15] = args[15] := zk 15 (by decide)
  have zk22 : za[22] = args[22] := zk 22 (by decide)
  have zk39 : za[39] = args[39] := zk 39 (by decide)
  have zk50 : za[50] = args[50] := zk 50 (by decide)
  have zk51 : za[51] = args[51] := zk 51 (by decide)
  let R12 := [span (sp - 8) 8,span (sp + 152) 16]
  have zf12 : RamWriteFrame mem zm R12 := by
    apply (RamWriteFrame.refl _ _).trans zf
    intro r hin
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl
    · exact ⟨span (sp - 8) 8,by simp [R12],Nat.le_refl _,Nat.le_refl _⟩
    · refine ⟨span (sp + 152) 16,by simp [R12],?_,?_⟩ <;> simp only [span,n152,padNat] <;> omega
  have zfR : RamWriteFrame mem zm [R] := by
    apply (RamWriteFrame.refl _ _).trans zf12
    intro r hin
    simp only [R12,List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl
    all_goals refine ⟨R,by simp,?_,?_⟩ <;> simp only [R,span,nlow,ns,n152] <;> omega
  have sourceOutside := external source input.size hr hpositive (hsep _ (by simp))
  have zb := hasBytes_of_frame zfR hbytes sourceOutside.1 (outside_disjoint_span sourceOutside)
  obtain ⟨c,cr,cl,ct,ck,cblock,ctarget,cf,cb⟩ := copyTailIn_reaches use256 code hcode za zm sp source input
    (by rw [zk4]; exact hsp) (by rw [zk13]; exact hsource)
    (by rw [zk14]; exact hcount) hsize hpositive (by omega) halign
    (short.of_frame zf) (hr.of_frame zf) zb (shortSep _ _ (hsep _ (by simp))) zt
    ((zk22).trans hdf)
    (by rw [zk39]; exact h39) (by rw [zk50]; exact h50)
    (by rw [zk51]; exact h51)
  rcases c with ⟨cl',ca,cm⟩
  dsimp only at cr cl ct ck cblock ctarget cf cb
  subst cl'
  change Values Value Reg.count at ca
  have cf12 : RegionsWithin [span (sp - 8) 8,span (sp + 152) input.size] R12 := by
    intro r hin
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl
    · exact ⟨span (sp - 8) 8,by simp [R12],Nat.le_refl _,Nat.le_refl _⟩
    · exact ⟨span (sp + 152) 16,by simp [R12],Nat.le_refl _,by simp only [span]; omega⟩
  have frame12 := zf12.trans cf cf12
  have frame12R : RamWriteFrame mem cm [R] := by
    apply (RamWriteFrame.refl _ _).trans frame12
    intro r hin
    simp only [R12,List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl
    all_goals refine ⟨R,by simp,?_,?_⟩ <;> simp only [R,span,nlow,ns,n152] <;> omega
  have localOutside (n count : Nat) (hn : n ≤ 152) (hc : n + count ≤ 152) :
      Outside R12 (sp + BitVec.ofNat 64 n) count := by
    refine ⟨by rw [plus n (by omega)]; omega,?_⟩
    intro r hin
    simp only [R12,List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl <;> simp only [span,plus n (by omega),ns,n152] <;> omega
  have counterOutside : Outside R12 (sp + 96) 20 := localOutside 96 20 (by decide) (by decide)
  have initialCounter := CTR.initialCounterBlock_of_frame frame12 counterOutside
  have keyPtr : memLoad cm (sp + 88) 64 = schedule :=
    (frame12.memLoad_eq (localOutside 88 8 (by decide) (by decide))).trans hkey
  let zeros : ByteArray := ⟨Array.replicate (16 - input.size) 0⟩
  let padded := input ++ zeros
  have zerosSize : zeros.size = 16 - input.size := Array.size_replicate
  have paddedSize : padded.size = 16 := by simp only [padded,ByteArray.size_append,zerosSize]; omega
  have zerosBytes : (span (sp + 152 + BitVec.ofNat 64 input.size) (16 - input.size)).HasBytes cm zeros := by
    refine ⟨zerosSize,?_⟩
    intro i
    have hi : i.val < 16 - input.size := by simpa only [zerosSize] using i.isLt
    have start : (sp + 152 + BitVec.ofNat 64 input.size).toNat = sp.toNat + 152 + input.size := by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat,n152]
      omega
    have addr : (BitVec.ofNat 64 ((sp + 152 + BitVec.ofNat 64 input.size).toNat + i.val)).toNat =
        sp.toNat + 152 + input.size + i.val := by rw [start,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have preserved := cf.outside (BitVec.ofNat 64 ((sp + 152 + BitVec.ofNat 64 input.size).toNat + i.val)) (by
      refine ⟨by rw [addr]; omega,?_⟩
      intro r hin
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
      rcases hin with rfl | rfl <;> simp only [span,ns,n152,addr] <;> omega)
    have zero := zz i.val (by rw [hcount]; exact hi)
    rw [remEq] at zero
    change cm[BitVec.ofNat 64 ((sp + 152 + BitVec.ofNat 64 input.size).toNat + i.val)]? = some zeros[i.val]
    rw [preserved]
    have address : BitVec.ofNat 64 ((sp + 152 + BitVec.ofNat 64 input.size).toNat + i.val) =
        sp + BitVec.ofNat 64 input.size + 152 + BitVec.ofNat 64 i.val := by
      rw [start]
      simp only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
      bv_omega
    rw [address]
    change _ = some ((Array.replicate (16 - input.size) (0 : UInt8))[i.val]'(by rw [Array.size_replicate]; exact hi))
    simpa only [Array.getElem_replicate] using zero
  have paddedBytes : (span (sp + 152) 16).HasBytes cm padded := by
    have zb : (span (sp + 152 + BitVec.ofNat 64 input.size) zeros.size).HasBytes cm zeros := by rw [zerosSize]; exact zerosBytes
    have all := hasBytes_append cb zb (by rw [n152]; omega)
    have len : input.size + zeros.size = 16 := by rw [zerosSize]; omega
    simpa only [len] using all
  have scheduleOutside := external schedule (16 * ((AES16.variant use256).Nr + 1)) hscheduleRead
    (by cases use256 <;> decide) (hsep _ (by simp))
  have slotOutside (a : BitVec 64) (ha : 0x201208 ≤ a.toNat) (hb : a.toNat + 8 ≤ 0x201238) : Outside [R] a 8 := by
    refine ⟨by omega,?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [R,span,nlow]
    omega
  have slotsCM : Readable cm 0x201208 8 ∧ memLoad cm 0x201208 64 = 0x103f00 ∧
      Readable cm 0x201210 8 ∧ memLoad cm 0x201210 64 = 0x103880 ∧
      Readable cm 0x201230 8 ∧ memLoad cm 0x201230 64 = 0x101230 := by
    obtain ⟨s0r,s0v,s1r,s1v,s3r,s3v,_,_⟩ := hslots
    exact ⟨s0r.of_frame frame12R,(frame12R.memLoad_eq (slotOutside _ (by decide) (by decide))).trans s0v,
      s1r.of_frame frame12R,(frame12R.memLoad_eq (slotOutside _ (by decide) (by decide))).trans s1v,
      s3r.of_frame frame12R,(frame12R.memLoad_eq (slotOutside _ (by decide) (by decide))).trans s3v⟩
  have ckz (r : Fin 53) (hin : r.val ∈ [4,13,14,15,22,39,50,51]) : ca[r] = args[r] :=
    (ck r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hin ⊢; omega)).trans
      (zk r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hin ⊢; omega))
  have ckz4 : ca[4] = args[4] := ckz 4 (by decide)
  have ckz13 : ca[13] = args[13] := ckz 13 (by decide)
  have ckz14 : ca[14] = args[14] := ckz 14 (by decide)
  have ckz15 : ca[15] = args[15] := ckz 15 (by decide)
  have ckz22 : ca[22] = args[22] := ckz 22 (by decide)
  have ckz39 : ca[39] = args[39] := ckz 39 (by decide)
  have ckz50 : ca[50] = args[50] := ckz 50 (by decide)
  have ckz51 : ca[51] = args[51] := ckz 51 (by decide)
  obtain ⟨t,tr,tl,tt,tk,tf,_,tb⟩ := tailCtr_reaches use256 code hcode key crypt padded paddedSize ca cm sp schedule
    (by rw [ckz4]; exact hsp) cblock (by rw [ckz15]; exact hcounter)
    hroom halign (hw.of_frame frame12) (AES16.scheduleIn_of_frame hschedule frame12R scheduleOutside)
    (hscheduleRead.of_frame frame12) keyPtr paddedBytes (hsep _ (by simp)) slotsCM hslotsApart ct
    ((ckz22).trans hdf)
    (by rw [ckz39]; exact h39) (by rw [ckz50]; exact h50)
    (by rw [ckz51]; exact h51)
  rcases t with ⟨tl',ta,tm⟩
  dsimp only at tr tl tt tk tf tb
  subst tl'
  change Values Value Reg.count at ta
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
  let R123 := [span lower (window + 64),span (sp + 112) 4,span (sp + 152) 16]
  have frame12Wide : RamWriteFrame mem cm R123 := by
    apply (RamWriteFrame.refl _ _).trans frame12
    intro r hin
    simp only [R12,List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨span lower (window + 64),by simp [R123],?_,?_⟩ <;> simp only [span,nlow,ns] <;> omega
    · exact ⟨span (sp + 152) 16,by simp [R123],Nat.le_refl _,Nat.le_refl _⟩
  have frame123 : RamWriteFrame mem tm R123 := frame12Wide.trans tf (fun r hin ↦ ⟨r,hin,Nat.le_refl _,Nat.le_refl _⟩)
  have frame123R : RamWriteFrame mem tm [R] := by
    apply (RamWriteFrame.refl _ _).trans frame123
    intro r hin
    simp only [R123,List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl | rfl
    all_goals refine ⟨R,by simp,?_,?_⟩ <;> simp only [R,span,nlow,n112,n152] <;> omega
  have descOutside := external descriptor 24 hrdesc (by decide) (hsep _ (by simp))
  have descPtr : memLoad tm (sp + 64) 64 = descriptor := by
    apply Eq.trans (frame123.memLoad_eq _) hdescriptor
    refine ⟨by rw [n64]; omega,?_⟩
    intro r hin
    simp only [R123,List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with rfl | rfl | rfl <;> simp only [span,n64,nlow,n112,n152] <;> omega
  have destPtr : memLoad tm (descriptor + 8) 64 = destination :=
    (frame123R.memLoad_eq (outside_subregion descOutside (offset := 8) (count := 8) (by decide) (by decide))).trans hdestination
  let encrypted := AesGcm.Spec.GCM.byteArrayOfBits
    (Standards.NIST.GCM.GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
      (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock cm (sp + 96)))
      (AesGcm.Spec.GCM.bitsOfByteArray padded))
  have encryptedSize : encrypted.size = 16 := by
    simp only [encrypted,AesGcm.Spec.GCM.byteArrayOfBits,ByteArray.size,Vector.size_toArray]
    exact paddedSize
  let result := encrypted.extract 0 input.size
  have resultSize : result.size = input.size := by simp only [result,ByteArray.size_extract,encryptedSize,Nat.min_eq_left hsize,Nat.sub_zero]
  have sliced : (span (sp + 152) input.size).HasBytes tm result := by
    have original : (span (sp + 152) encrypted.size).HasBytes tm encrypted := by rw [encryptedSize]; exact tb
    have hh := hasBytes_extract original 0 input.size (by omega) (by rw [encryptedSize]; exact hsize) (by rw [n152]; omega)
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero,Nat.sub_zero] using hh
  obtain ⟨next,nr,nl,nt,nk,nf,nb⟩ := copyTailOut_reaches use256 code hcode ta tm sp descriptor destination result
    (by rw [tk4,ckz4]; exact hsp) (by rw [tk3]; exact cblock)
    (by rw [tk12]; exact ctarget)
    (by rw [tk14,ckz14,hcount,resultSize])
    (by rw [resultSize]; exact hsize) (by rw [resultSize]; exact hpositive) (by omega) halign
    (short.of_frame frame123) (hrdesc.of_frame frame123) descPtr destPtr
    (by rw [resultSize]; exact hdw.of_frame frame123) (by rw [resultSize]; exact sliced)
    (by rw [resultSize]; exact shortSep _ _ (hsep _ (by simp))) tt
    ((tk22).trans ((ckz22).trans hdf))
    (by rw [tk39,ckz39]; exact h39)
    (by rw [tk50,ckz50]; exact h50)
    (by rw [tk51,ckz51]; exact h51)
  have through : (LIR.program.sem (dialect code)).Reaches
      ⟨⟨if use256 then .l1028e4 else .l102484,args,mem⟩,[]⟩ ⟨next,[]⟩ := zr.trans (cr.trans (tr.trans nr))
  refine ⟨next,through,nl,nt,?_,?_,?_,?_⟩
  · intro r hin
    exact (nk r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hin ⊢; omega)).trans
      ((tk r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hin ⊢; omega)).trans (ckz r hin))
  · exact (congrArg (Value.get 8) (nk 5 (by decide))).trans
      ((congrArg (Value.get 8) (tk5)).trans ((congrArg (Value.get 8) (ck 5 (by decide))).trans zstatus))
  · apply ((RamWriteFrame.refl _ _).trans frame123 ?_).trans nf ?_
    · intro r hin
      simp only [R123,List.mem_cons,List.not_mem_nil,or_false] at hin
      rcases hin with rfl | rfl | rfl <;> exact ⟨_,by simp [lower,window],Nat.le_refl _,Nat.le_refl _⟩
    · intro r hin
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
      rcases hin with rfl | rfl
      · refine ⟨span lower (window + 64),by simp [lower,window],?_,?_⟩ <;> simp only [span,nlow,ns] <;> omega
      · exact ⟨span destination input.size,by simp,Nat.le_refl _,by simp only [span,resultSize]; exact Nat.le_refl _⟩
  · have he : result = AesGcm.Spec.GCM.byteArrayOfBits
        (Standards.NIST.GCM.GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
          (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock mem (sp + 96)))
          (AesGcm.Spec.GCM.bitsOfByteArray input)) := by
      dsimp only [result,encrypted]
      rw [CTR.gctr_bytes_extract_zero _ _ _ input.size (by rw [paddedSize]; exact hsize),
        show padded.extract 0 input.size = input from ByteArray.extract_append_eq_left rfl,initialCounter]
    rw [resultSize,he] at nb
    exact nb

end AesGcm.Proofs.Machine.Core.Decrypt
