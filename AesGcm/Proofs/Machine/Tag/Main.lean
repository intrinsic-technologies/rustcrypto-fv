import AesGcm.Proofs.Machine.Tag.Execution.Entry
import AesGcm.Proofs.Machine.Tag.Execution.Branches
import AesGcm.Proofs.Machine.Tag.Execution.PaddingCalls
import AesGcm.Proofs.Machine.Tag.Execution.Reverse
import AesGcm.Proofs.Machine.Tag.Execution.Length
import AesGcm.Proofs.Machine.Tag.Execution.Finish
import AesGcm.Proofs.Machine.Tag.Consumer
import AesGcm.Proofs.Machine.Tag.Finalize
import AesGcm.Proofs.Machine.Runtime.Root.Memory
import AesGcm.Proofs.Machine.Runtime.EntryFacts
import AesGcm.Proofs.Machine.Runtime.Memset.Unaligned
import AesGcm.Proofs.Machine.Runtime.Memcpy
import AesGcm.Proofs.Machine.GHASHExecution.Multiply
import AesGcm.Proofs.Machine.Tag.Model
import AesGcm.Proofs.Machine.Tag.Calls
import AesGcm.Proofs.Machine.GcmContext
import AesGcm.Proofs.Machine.GHASHInterface
import AesGcm.Proofs.Machine.LIR.Fn101800.Frame
import AesGcm.Proofs.Machine.LIR.Fn101c20.Frame
import AesGcm.Spec.GCM

namespace AesGcm.Proofs.Machine.Tag
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
private theorem paddedTail_exec (use256 isCipher : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (hmultiply : GHASHInterface.MultiplyContract code)
    (h : Vector UInt8 16) (sp : BitVec 64) (hroom : 408 ≤ sp.toNat)
    (halign : sp.toNat % 16 = 0) (v : Values Value Reg.count) (m : Ram)
      (src rem offset : BitVec 64) (bytes : ByteArray)
      (v4 : v[4].get 64 = sp)
      (vrem : (if isCipher then v[12].get 64 else v[13].get 64) = rem)
      (vsrc : (if isCipher then v[14].get 64 else v[12].get 64) = src)
      (voff : (if isCipher then 0xffffffff0 &&& v[15].get 64 else
        0x1ffffffffffffff0 &&& v[3].get 64) = offset)
      (roff : offset.toNat = 16 * (bytes.size / 16))
      (rrem : rem.toNat = bytes.size % 16) (rpos : 0 < rem.toNat)
      (vt : GPRsTyped v) (vdf : v[22] = ⟨1, 0⟩)
      (v39 : v[39] = ⟨32, v[39].get 32⟩)
      (v50 : v[50] = ⟨16, v[50].get 16⟩)
      (v51 : v[51] = ⟨16, v[51].get 16⟩)
      (wm : Writable code m (sp - 408) 520)
      (rm : Readable m src bytes.size) (bm : (span src bytes.size).HasBytes m bytes)
      (sep : (span (sp - 408) 520).Disjoint
        (span src bytes.size))
      (slot0 : Readable m 0x201228 8) (slot1 : Readable m 0x201208 8)
      (slot0val : memLoad m 0x201228 64 = 0x103eb0)
      (slot1val : memLoad m 0x201208 64 = 0x103f00)
      (slotBounds : sp.toNat + 112 ≤ 0x201208 ∨ 0x201230 ≤ (sp - 408).toNat)
      (key0 : memLoad m (sp + 80) 64 =
        (GHASH.polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)).1)
      (key1 : memLoad m (sp + 88) 64 =
        (GHASH.polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)).2) :
      ∃ o : Output Value Ram Reg.count,
        (LIR.program.sem (dialect code)).Reaches
          ⟨⟨if use256 then (if isCipher then .l101d7f else .l101c93)
            else (if isCipher then .l10195f else .l101873), v, m⟩, []⟩
          ⟨⟨if use256 then (if isCipher then .l101e4a else .l101d5e)
            else (if isCipher then .l101a2a else .l10193e), o.values, o.store⟩, []⟩ ∧
        o.values[4] = ⟨64, sp⟩ ∧
        (∀ r : Fin 53, r.val ∈ [3,5,13,15,22,39,50,51] → o.values[r] = v[r]) ∧
        (isCipher = false → o.values[14] = v[14]) ∧
        GPRsTyped o.values ∧ RamWriteFrame m o.store [span (sp - 408) 520] ∧
        stateBits (memLoad o.store (sp + 96) 64, memLoad o.store (sp + 104) 64) =
          Standards.NIST.GCM.mul
            (Standards.NIST.GCM.xor
              (stateBits (memLoad m (sp + 96) 64, memLoad m (sp + 104) 64))
              (paddedBlock bytes (bytes.size / 16))) (Standards.NIST.GCM.bitsOfBytes h) ∧
        memLoad o.store (sp + 80) 64 = memLoad m (sp + 80) 64 ∧
        memLoad o.store (sp + 88) 64 = memLoad m (sp + 88) 64 := by
    have esp8 : (sp - 8).toNat = sp.toNat - 8 := by
      exact BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; omega)
    have sp408 : (sp - 408).toNat = sp.toNat - 408 := by
      exact BitVec.toNat_sub_of_le (by change 408 ≤ sp.toNat; omega)
    let R := [span (sp - 408) 520]
    have rlt : rem.toNat < 16 := by omega
    have lo : sp.toNat + 112 ≤ 2^32 := by
      have := wm.readable.low
      rw [sp408] at this
      omega
    have srem : (sp + rem + 64).toNat = sp.toNat + rem.toNat + 64 := by bv_omega
    have sn : (16 - rem).toNat = 16 - rem.toNat := by bv_omega
    have slotPreserved {x y : Ram} (hf : RamWriteFrame x y R) :
        memLoad y 0x201208 64 = memLoad x 0x201208 64 ∧
        memLoad y 0x201228 64 = memLoad x 0x201228 64 := by
      constructor
      all_goals
        apply hf.memLoad_eq
        refine ⟨by decide, ?_⟩
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        simp only [span, BitVec.reduceToNat]
        change _ ∨ (sp - 408).toNat + 520 ≤ _
        rw [sp408] at slotBounds ⊢
        omega
    obtain ⟨z, zcont, zrun, zlab, ztarget, zguard, zmem, z4, z7, z6, z2, z12, z14,
      zkeep, ztyped⟩ := Execution.zero_runBlock use256 isCipher code hcode v m
      (by rw [v4]; exact wm.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) slot0 slot0val
    let zret : BitVec 64 := if use256 then (if isCipher then 0x101da7 else 0x101cbb)
      else (if isCipher then 0x101987 else 0x10189b)
    let zm := memStore m (sp - 8) zret
    have zmemory : z.store = zm := by simpa only [v4] using zmem
    have zp : (z.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 := by rw [z4, v4]; rfl
    have zd : (z.arguments[7]'(by change 7 < 53; decide)).get 64 = sp + rem + 64 := by
      rw [z7, v4, vrem]; rfl
    have zn : (z.arguments[2]'(by change 2 < 53; decide)).get 64 = 16 - rem := by rw [z2, vrem]; rfl
    have zzero : (z.arguments[6]'(by change 6 < 53; decide)).get 64 = 0 := by rw [z6]; rfl
    have zslotFrame : RamWriteFrame m zm [span (sp - 8) 8] := by
      apply (RamWriteFrame.refl m _).memStore
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [InRegion, span, esp8]
      omega
    have z39 : (z.arguments[39]'(by change 39 < 53; decide)) = v[39] := zkeep 39 (by decide)
    have z50 : (z.arguments[50]'(by change 50 < 53; decide)) = v[50] := zkeep 50 (by decide)
    have z51 : (z.arguments[51]'(by change 51 < 53; decide)) = v[51] := zkeep 51 (by decide)
    have zdf := (zkeep 22 (by decide)).trans vdf
    obtain ⟨zo, zexec, ztag, zdone, zot, zframe, zeros⟩ :=
      callContract_exec_values LIR.lifted code .l103eb0 LIR.Fn103eb0.frameInfo
        (fun fr ↦ [span fr.rdi fr.rdx.toNat]) _ _ (memset_zero_call_of_writable code hcode)
        zm z.arguments zret (sp - 8) (ztyped vt)
        (by rw [z39]; exact v39) (by rw [z50]; exact v50) (by rw [z51]; exact v51) zdf
        (by rw [zp]; exact (wm.readable.of_frame zslotFrame).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
        (by rw [zp]; exact memLoad_memStore_same _ _ _ (by decide) (by decide))
        (by dsimp only [zret]; split <;> split <;> decide)
        (by intro hn; contradiction)
        (by change (sp-8).toNat + 0 ≤ ((z.arguments[4]'(by change 4 < 53; decide)).get 64).toNat; rw [zp]; omega)
        (by rw [zp, esp8]; omega) (by trivial)
        (by
          simp only [activationOfValues, zd, zn, zzero, zp, sn]
          refine ⟨by trivial, ?_, ?_⟩
          · have base : (sp - 408).toNat = sp.toNat - 408 := sp408
            apply (wm.of_frame zslotFrame).sub
            · rw [srem, base]; omega
            · rw [srem, base]; omega
          · have bound := lo
            apply RangeApart.of_diff
            simp only [BitVec.toNat_sub, srem, esp8]
            constructor <;> omega)
    have zpres := Execution.preserved_of_doneAtoms code zm z.arguments zret (sp - 8) zo
      (ztyped vt) (by rw [z39]; exact v39) (by rw [z50]; exact v50)
      (by rw [z51]; exact v51) zdf zdone
    have zo4 : zo.values[4] = ⟨64, sp⟩ := by
      simpa only [zp, BitVec.sub_add_cancel] using zpres.1
    have zosp : zo.values[4].get 64 = sp := by rw [zo4]; rfl
    have zsource : (if isCipher then zo.values[14].get 64 else zo.values[12].get 64) =
        src + offset := by
      cases isCipher
      · simp only [Bool.false_eq_true, ↓reduceIte] at vsrc voff z12 ⊢
        have he : zo.values[12] = ⟨64, v[12].get 64 + (0x1ffffffffffffff0 &&& v[3].get 64)⟩ :=
          (zpres.2 12 (by decide)).trans z12
        rw [he]
        change v[12].get 64 + (0x1ffffffffffffff0 &&& v[3].get 64) = _
        rw [vsrc, voff]
      · simp only [↓reduceIte] at vsrc voff z14 ⊢
        have he : zo.values[14] = ⟨64, v[14].get 64 + (0xffffffff0 &&& v[15].get 64)⟩ :=
          (zpres.2 14 (by decide)).trans z14
        rw [he]
        change v[14].get 64 + (0xffffffff0 &&& v[15].get 64) = _
        rw [vsrc, voff]
    have zrem : (if isCipher then zo.values[12].get 64 else zo.values[13].get 64) = rem := by
      cases isCipher
      · simp only [Bool.false_eq_true, ↓reduceIte] at vrem ⊢
        have he : zo.values[13] = v[13] := (zpres.2 13 (by decide)).trans (zkeep 13 (by decide))
        rw [he]; exact vrem
      · simp only [↓reduceIte] at vrem z12 ⊢
        have he : zo.values[12] = v[12] := (zpres.2 12 (by decide)).trans z12
        rw [he]; exact vrem
    have zeroNarrow : RamWriteFrame m zo.store [span (sp - 8) 88] := by
      have zprefix : RamWriteFrame m zm [span (sp - 8) 88] := by
        apply (RamWriteFrame.refl m [span (sp - 8) 88]).trans zslotFrame
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;>
          simp only [span, esp8 ] <;> omega
      apply zprefix.trans zframe
      intro r hr
      change r ∈ [⟨(sp-8).toNat, ((z.arguments[4]'(by change 4 < 53; decide)).get 64).toNat - (sp-8).toNat⟩,
        span ((z.arguments[7]'(by change 7 < 53; decide)).get 64)
          ((z.arguments[2]'(by change 2 < 53; decide)).get 64).toNat] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;>
          simp only [zp, span, esp8 ] <;> omega
      · refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;>
          simp only [zd, zn, sn, span, srem ] <;> omega
    have zeroFrame : RamWriteFrame m zo.store R := by
      apply (RamWriteFrame.refl m R).trans zeroNarrow
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;>
        simp only [span, esp8, sp408] <;> omega
    have zreach : (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then (if isCipher then .l101d7f else .l101c93)
          else (if isCipher then .l10195f else .l101873), v, m⟩, []⟩
        ⟨⟨if use256 then (if isCipher then .l101da7 else .l101cbb)
          else (if isCipher then .l101987 else .l10189b), zo.values, zo.store⟩, []⟩ := by
      have hexec : LIR.program.Exec (dialect code) ⟨z, []⟩ zo := by
        have he : z = ⟨.l103eb0, z.arguments, zm⟩ := by
          cases z with
          | mk lab vals st => dsimp only at zlab zmemory; subst lab st; rfl
        rw [he]; exact zexec
      have haccept : zcont.Accepts (dialect code) zo.tag = true := by
        rw [ztag]
        simp only [StackFrame.Accepts, zguard]
        cases use256 <;> cases isCipher <;> rfl
      have he := Execution.call_reaches code _ _ _ _ zrun hexec haccept
      rw [ztarget] at he
      exact he
    obtain ⟨c, ccont, crun, clab, ctarget, cguard, cmem, c4, c7, c6, c2, ckeep, ctyped⟩ :=
      Execution.copy_runBlock use256 isCipher code hcode zo.values zo.store
        (by rw [zosp]; exact (wm.of_frame zeroFrame).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
        (slot1.of_frame zeroFrame) ((slotPreserved zeroFrame).1.trans slot1val)
    let cret : BitVec 64 := if use256 then (if isCipher then 0x101db8 else 0x101ccc)
      else (if isCipher then 0x101998 else 0x1018ac)
    let cm := memStore zo.store (sp - 8) cret
    have cmemory : c.store = cm := by simpa only [zosp] using cmem
    have cp : (c.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 := by rw [c4, zosp]; rfl
    have cd : (c.arguments[7]'(by change 7 < 53; decide)).get 64 = sp + 64 := by rw [c7, zosp]; rfl
    have cs : (c.arguments[6]'(by change 6 < 53; decide)).get 64 = src + offset := by rw [c6, zsource]; rfl
    have cn : (c.arguments[2]'(by change 2 < 53; decide)).get 64 = rem := by rw [c2, zrem]; rfl
    have cslotFrame : RamWriteFrame zo.store cm [span (sp - 8) 8] := by
      apply (RamWriteFrame.refl zo.store _).memStore
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [InRegion, span, esp8]
      omega
    have c39 : (c.arguments[39]'(by change 39 < 53; decide)) = v[39] :=
      (ckeep 39 (by decide)).trans ((zpres.2 39 (by decide)).trans z39)
    have c50 : (c.arguments[50]'(by change 50 < 53; decide)) = v[50] :=
      (ckeep 50 (by decide)).trans ((zpres.2 50 (by decide)).trans z50)
    have c51 : (c.arguments[51]'(by change 51 < 53; decide)) = v[51] :=
      (ckeep 51 (by decide)).trans ((zpres.2 51 (by decide)).trans z51)
    have cdf := (ckeep 22 (by decide)).trans ((zpres.2 22 (by decide)).trans zdf)
    have srcOffset : (src + offset).toNat = src.toNat + offset.toNat := by
      have := rm.low
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have s64 : (sp + 64).toNat = sp.toNat + 64 := by bv_omega
    have sepBounds := disjoint_bounds (sp - 408).toNat 520
      src.toNat bytes.size (by decide) (by omega) sep
    obtain ⟨co, cexec, ctag, cdone, cot, cframe, copied⟩ :=
      callContract_exec_values LIR.lifted code .l103f00 LIR.Fn103f00.frameInfo
        (fun fr ↦ [span fr.rdi fr.rdx.toNat]) _ _
        (memcpy_call code (fun x hx ↦ hcode x (LIR.code_l103f00 x hx)))
        cm c.arguments cret (sp - 8) (ctyped zot)
        (by rw [c39]; exact v39) (by rw [c50]; exact v50) (by rw [c51]; exact v51) cdf
        (by rw [cp]; exact ((wm.readable.of_frame zeroFrame).of_frame cslotFrame).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
        (by rw [cp]; exact memLoad_memStore_same _ _ _ (by decide) (by decide))
        (by dsimp only [cret]; split <;> split <;> decide)
        (by intro hn; contradiction)
        (by change (sp-8).toNat + 0 ≤ ((c.arguments[4]'(by change 4 < 53; decide)).get 64).toNat; rw [cp]; omega)
        (by rw [cp, esp8]; omega) (by trivial)
        (by
          change Readable cm ((c.arguments[6]'(by change 6 < 53; decide)).get 64)
              ((c.arguments[2]'(by change 2 < 53; decide)).get 64).toNat ∧
            Writable code cm ((c.arguments[7]'(by change 7 < 53; decide)).get 64)
              ((c.arguments[2]'(by change 2 < 53; decide)).get 64).toNat ∧ _
          simp only [activationOfValues, cp, cd, cs, cn]
          refine ⟨?_, ?_, ?_, ?_⟩
          · apply ((rm.of_frame zeroFrame).of_frame cslotFrame).sub
            · rw [srcOffset]; omega
            · rw [srcOffset]; omega
          · apply ((wm.of_frame zeroFrame).of_frame cslotFrame).sub
            · rw [s64, sp408]; omega
            · rw [s64, sp408]; omega
          · rw [srcOffset, s64]
            rw [sp408] at sepBounds
            omega
          · apply RangeApart.of_diff
            simp only [BitVec.toNat_sub, s64, esp8]
            constructor <;> omega)
    have cpres := Execution.preserved_of_doneAtoms code cm c.arguments cret (sp - 8) co
      (ctyped zot) (by rw [c39]; exact v39) (by rw [c50]; exact v50)
      (by rw [c51]; exact v51) cdf cdone
    have co4 : co.values[4] = ⟨64, sp⟩ := by simpa only [cp, BitVec.sub_add_cancel] using cpres.1
    have cosp : co.values[4].get 64 = sp := by rw [co4]; rfl
    have preCopyNarrow : RamWriteFrame m cm [span (sp - 8) 88] := by
      apply zeroNarrow.trans cslotFrame
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;>
        simp only [span, esp8] <;> omega
    have copyNarrow : RamWriteFrame m co.store [span (sp - 8) 88] := by
      apply preCopyNarrow.trans cframe
      intro r hr
      change r ∈ [⟨(sp-8).toNat, ((c.arguments[4]'(by change 4 < 53; decide)).get 64).toNat - (sp-8).toNat⟩,
        span ((c.arguments[7]'(by change 7 < 53; decide)).get 64)
          ((c.arguments[2]'(by change 2 < 53; decide)).get 64).toNat] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;> simp only [cp, span, esp8] <;> omega
      · refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;> simp only [cd, cn, span, esp8, s64] <;> omega
    have copyWide : RamWriteFrame m co.store R := by
      apply (RamWriteFrame.refl m R).trans copyNarrow
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;>
        simp only [span, esp8, sp408] <;> omega
    have tailBytes (i : Nat) (hi : i < 16) :
        co.store[sp + 64 + BitVec.ofNat 64 i]? =
          some (if hb : 16 * (bytes.size / 16) + i < bytes.size then
            bytes[16 * (bytes.size / 16) + i] else 0) := by
      have addr : (sp + 64 + BitVec.ofNat 64 i).toNat = sp.toNat + 64 + i := by
        rw [BitVec.toNat_add, s64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
      by_cases hin : i < rem.toNat
      · have ce := copied i (by simpa only [activationOfValues, cn] using hin)
        simp only [activationOfValues, cd, cs] at ce
        rw [ce]
        have sin : offset.toNat + i < bytes.size := by omega
        have saddr : src + offset + BitVec.ofNat 64 i = src + BitVec.ofNat 64 (offset.toNat + i) := by
          simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc]
        rw [saddr, preCopyNarrow.outside]
        · have be := bm.2 ⟨offset.toNat + i, sin⟩
          simp only [span, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at be
          rw [← BitVec.add_assoc, saddr] at be
          rw [be]
          simp only [roff, dite_eq_left (by omega : 16 * (bytes.size / 16) + i < bytes.size)]
        · have sa : (src + BitVec.ofNat 64 (offset.toNat + i)).toNat = src.toNat + offset.toNat + i := by
            have := rm.low
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]
            omega
          refine ⟨by rw [sa]; have := rm.low; omega, ?_⟩
          intro r hr
          obtain rfl := List.mem_singleton.mp hr
          simp only [span, esp8, sa]
          rw [sp408] at sepBounds
          omega
      · have ce : co.store[sp + 64 + BitVec.ofNat 64 i]? = cm[sp + 64 + BitVec.ofNat 64 i]? := by
          apply cframe.outside
          refine ⟨by rw [addr]; omega, ?_⟩
          intro r hr
          change r ∈ [⟨(sp-8).toNat, ((c.arguments[4]'(by change 4 < 53; decide)).get 64).toNat - (sp-8).toNat⟩,
            span ((c.arguments[7]'(by change 7 < 53; decide)).get 64)
              ((c.arguments[2]'(by change 2 < 53; decide)).get 64).toNat] at hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · simp only [cp, esp8, addr]; omega
          · simp only [cd, cn, span, s64, addr]; omega
        rw [ce, cslotFrame.outside]
        · have he := zeros (i - rem.toNat) (by simpa only [activationOfValues, zn, sn] using
            (show i - rem.toNat < 16 - rem.toNat by omega))
          simp only [activationOfValues, zd] at he
          have hb : sp + rem + 64 + BitVec.ofNat 64 (i - rem.toNat) =
              sp + 64 + BitVec.ofNat 64 i := by bv_omega
          rw [hb] at he
          rw [he, dite_eq_right (by omega : ¬16 * (bytes.size / 16) + i < bytes.size)]
        · refine ⟨by rw [addr]; omega, ?_⟩
          intro r hr
          obtain rfl := List.mem_singleton.mp hr
          simp only [span, esp8, addr]
          omega
    have tailBits : sourceBlockBits co.store (sp + 64) 0 = paddedBlock bytes (bytes.size / 16) := by
      apply sourceBlockBits_eq_paddedBlock_of_memByte
      intro i hi
      simp only [memByte, PhysicalMemory.read, tailBytes i hi, Option.getD_some]
    have creach : (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then (if isCipher then .l101da7 else .l101cbb)
          else (if isCipher then .l101987 else .l10189b), zo.values, zo.store⟩, []⟩
        ⟨⟨if use256 then (if isCipher then .l101db8 else .l101ccc)
          else (if isCipher then .l101998 else .l1018ac), co.values, co.store⟩, []⟩ := by
      have hexec : LIR.program.Exec (dialect code) ⟨c, []⟩ co := by
        have he : c = ⟨.l103f00, c.arguments, cm⟩ := by
          cases c with
          | mk lab vals st => dsimp only at clab cmemory; subst lab st; rfl
        rw [he]; exact cexec
      have haccept : ccont.Accepts (dialect code) co.tag = true := by
        rw [ctag]
        simp only [StackFrame.Accepts, cguard]
        cases use256 <;> cases isCipher <;> rfl
      have he := Execution.call_reaches code _ _ _ _ crun hexec haccept
      rw [ctarget] at he
      exact he
    obtain ⟨r, rcont, rrun, rlab, rtarget, rguard, r4, r7, r6, rkeep, rtyped,
      rframe, rreturn, rword0, rword1⟩ := Execution.reverse_runBlock use256 isCipher code hcode
        co.values co.store
        (by rw [cosp]; exact (wm.of_frame copyNarrow).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
        (by rw [cosp]; exact (wm.readable.of_frame copyNarrow).of_offsets rfl (addr_sub _ _) (by decide))
    have rp : (r.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 := by rw [r4, cosp]; rfl
    have rd : (r.arguments[7]'(by change 7 < 53; decide)).get 64 = sp + 80 := by rw [r7, cosp]; rfl
    have rs : (r.arguments[6]'(by change 6 < 53; decide)).get 64 = sp + 16 := by rw [r6, cosp]; rfl
    rw [cosp] at rframe rreturn rword0 rword1
    have addNat (off : Nat) (ho : off ≤ 112) :
        (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have rstate (off : Nat) (hlo : 80 ≤ off) (hhi : off + 8 ≤ 112) :
        memLoad r.store (sp + BitVec.ofNat 64 off) 64 =
          memLoad m (sp + BitVec.ofNat 64 off) 64 := by
      rw [rframe.memLoad_eq, copyNarrow.memLoad_eq]
      all_goals
        refine ⟨by rw [addNat off (by omega)]; omega, ?_⟩
        intro region hr
        obtain rfl := List.mem_singleton.mp hr
        simp only [span, esp8, addNat off (by omega)]
        omega
    have rstate0 : memLoad r.store (sp + 80) 64 = memLoad m (sp + 80) 64 := rstate 80 (by decide) (by decide)
    have rstate8 : memLoad r.store (sp + 88) 64 = memLoad m (sp + 88) 64 := rstate 88 (by decide) (by decide)
    have rstate16 : memLoad r.store (sp + 96) 64 = memLoad m (sp + 96) 64 := rstate 96 (by decide) (by decide)
    have rstate24 : memLoad r.store (sp + 104) 64 = memLoad m (sp + 104) 64 := rstate 104 (by decide) (by decide)
    have r39 : (r.arguments[39]'(by change 39 < 53; decide)) = v[39] :=
      (rkeep 39 (by decide)).trans ((cpres.2 39 (by decide)).trans c39)
    have r50 : (r.arguments[50]'(by change 50 < 53; decide)) = v[50] :=
      (rkeep 50 (by decide)).trans ((cpres.2 50 (by decide)).trans c50)
    have r51 : (r.arguments[51]'(by change 51 < 53; decide)) = v[51] :=
      (rkeep 51 (by decide)).trans ((cpres.2 51 (by decide)).trans c51)
    have rdf := (rkeep 22 (by decide)).trans ((cpres.2 22 (by decide)).trans cdf)
    let rret : BitVec 64 := if use256 then (if isCipher then 0x101e4a else 0x101d5e)
      else (if isCipher then 0x101a2a else 0x10193e)
    have sub136 : (sp - 136).toNat = sp.toNat - 136 :=
      BitVec.toNat_sub_of_le (by change 136 ≤ sp.toNat; omega)
    have s80 : (sp + 80).toNat = sp.toNat + 80 := addNat 80 (by decide)
    obtain ⟨o, oexec, otag, odone, ot, oframe, post⟩ :=
      callContract_exec_values LIR.lifted code .l1034c0 LIR.Fn1034c0.frameInfo
        (fun fr ↦ [span (fr.rdi + 16) 16]) _ _ (GHASHUpdate.oneBlock_call code hmultiply)
        r.store r.arguments rret (sp - 136) (rtyped cot)
        (by rw [r39]; exact v39) (by rw [r50]; exact v50) (by rw [r51]; exact v51) rdf
        (by rw [rp]; exact ((wm.readable.of_frame copyNarrow).of_frame rframe).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
        (by rw [rp]; exact rreturn)
        (by dsimp only [rret]; split <;> split <;> decide)
        (fun _ ↦ by
          change Writable code r.store ((r.arguments[4]'(by change 4 < 53; decide)).get 64 - 128) 128
          rw [rp, show sp - 8 - 128 = sp - 136 by bv_omega]
          exact ((wm.of_frame copyNarrow).of_frame rframe).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
        (by change (sp-136).toNat + 128 ≤ ((r.arguments[4]'(by change 4 < 53; decide)).get 64).toNat
            rw [rp, esp8, sub136]; omega)
        (by rw [rp, esp8]; omega) (by trivial)
        (by
          simp only [activationOfValues, callStack, rp, rd, rs]
          refine ⟨((wm.readable.of_frame copyNarrow).of_frame rframe).of_offsets rfl (addr_sub _ _) (by decide),
            ((wm.of_frame copyNarrow).of_frame rframe).of_offsets rfl (addr_sub _ _) (by decide), ?_⟩
          intro x hx hy
          simp only [MemoryRegion.Contains, span, esp8, sub136, s80] at hx hy
          omega)
    have opres := Execution.preserved_of_doneAtoms code r.store r.arguments rret (sp - 136) o
      (rtyped cot) (by rw [r39]; exact v39) (by rw [r50]; exact v50)
      (by rw [r51]; exact v51) rdf odone
    have rreach : (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then (if isCipher then .l101db8 else .l101ccc)
          else (if isCipher then .l101998 else .l1018ac), co.values, co.store⟩, []⟩
        ⟨⟨if use256 then (if isCipher then .l101e4a else .l101d5e)
          else (if isCipher then .l101a2a else .l10193e), o.values, o.store⟩, []⟩ := by
      have hexec : LIR.program.Exec (dialect code) ⟨r, []⟩ o := by
        have he : r = ⟨.l1034c0, r.arguments, r.store⟩ := by
          cases r with
          | mk lab vals st => dsimp only at rlab; subst lab; rfl
        conv => lhs; rw [he]
        exact oexec
      have haccept : rcont.Accepts (dialect code) o.tag = true := by
        rw [otag]
        simp only [StackFrame.Accepts, rguard]
        cases use256 <;> cases isCipher <;> rfl
      have he := Execution.call_reaches code _ _ _ _ rrun hexec haccept
      rw [rtarget] at he
      exact he
    refine ⟨o, (zreach.trans creach).trans rreach, ?_, ?_, ?_, ot, ?_, ?_, ?_, ?_⟩
    · simpa only [rp, BitVec.sub_add_cancel] using opres.1
    · intro j hj
      have hbig : j.val ∈ [3,5,12,13,14,15,22,39,50,51] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
        omega
      exact (opres.2 j hbig).trans ((rkeep j hbig).trans ((cpres.2 j hbig).trans
        ((ckeep j hbig).trans ((zpres.2 j hbig).trans (zkeep j hj)))))
    · intro hc
      subst isCipher
      simp only [Bool.false_eq_true, ↓reduceIte] at z14
      exact (opres.2 14 (by decide)).trans ((rkeep 14 (by decide)).trans
        ((cpres.2 14 (by decide)).trans ((ckeep 14 (by decide)).trans
          ((zpres.2 14 (by decide)).trans z14))))
    · have reverseWide : RamWriteFrame m r.store R := by
        apply copyWide.trans rframe
        intro region hr
        obtain rfl := List.mem_singleton.mp hr
        refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;>
          simp only [span, esp8, sp408] <;> omega
      apply reverseWide.trans oframe
      intro region hr
      change region ∈ [⟨(sp-136).toNat, ((r.arguments[4]'(by change 4 < 53; decide)).get 64).toNat - (sp-136).toNat⟩,
        span ((r.arguments[7]'(by change 7 < 53; decide)).get 64 + 16) 16] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;>
          simp only [span, rp, sub136, esp8, sp408] <;> omega
      · have sa : (sp + 80 + 16).toNat = sp.toNat + 96 := by
          rw [show sp + 80 + 16 = sp + BitVec.ofNat 64 96 by bv_omega]
          exact addNat 96 (by decide)
        refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;>
          simp only [rd, span, sa, sp408] <;> omega
    · simp only [activationOfValues, rd, rs,
        show sp + 80 + 8 = sp + 88 by bv_omega,
        show sp + 80 + 16 = sp + 96 by bv_omega,
        show sp + 80 + 24 = sp + 104 by bv_omega,
        show sp + 16 + 8 = sp + 24 by bv_omega,
        rstate0, rstate8, rstate16, rstate24, key0, key1, rword0, rword1] at post
      rw [post.1, post.2]
      rw [BitVec.xor_comm (bswapSpec _) _, BitVec.xor_comm (bswapSpec _) _]
      have hb : stateBits (bswapSpec (memLoad co.store (sp + 72) 64),
          bswapSpec (memLoad co.store (sp + 64) 64)) = paddedBlock bytes (bytes.size / 16) := by
        simpa only [sourceBlockBits, Nat.mul_zero, Nat.zero_add, BitVec.ofNat_eq_ofNat,
          BitVec.add_zero, show sp + 64#64 + 8#64 = sp + 72#64 by bv_omega] using tailBits
      exact (stateBits_multiply h
        (memLoad m (sp + 96) 64, memLoad m (sp + 104) 64)
        (bswapSpec (memLoad co.store (sp + 72) 64), bswapSpec (memLoad co.store (sp + 64) 64))).trans
        (congrArg (fun x ↦ Standards.NIST.GCM.mul
          (Standards.NIST.GCM.xor
            (stateBits (memLoad m (sp + 96) 64, memLoad m (sp + 104) 64)) x)
          (Standards.NIST.GCM.bitsOfBytes h)) hb)
    all_goals
      rw [oframe.memLoad_eq]
      · first | exact rstate0 | exact rstate8
      · refine ⟨?_, ?_⟩
        · first
            | (rw [show (sp + 80).toNat = sp.toNat + 80 from addNat 80 (by decide)]; omega)
            | (rw [show (sp + 88).toNat = sp.toNat + 88 from addNat 88 (by decide)]; omega)
        · intro region hr
          change region ∈ [⟨(sp-136).toNat, ((r.arguments[4]'(by change 4 < 53; decide)).get 64).toNat - (sp-136).toNat⟩,
            span ((r.arguments[7]'(by change 7 < 53; decide)).get 64 + 16) 16] at hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          all_goals
            simp only [rp, rd, span, sub136, esp8,
              show sp + 80 + 16 = sp + BitVec.ofNat 64 96 by bv_omega,
              show (sp + 80).toNat = sp.toNat + 80 from addNat 80 (by decide),
              show (sp + 88).toNat = sp.toNat + 88 from addNat 88 (by decide),
              addNat 96 (by decide)]
            omega

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
private theorem completePaddedHash_exec (use256 isCipher : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (hmultiply : GHASHInterface.MultiplyContract code)
    (h : Vector UInt8 16) (sp : BitVec 64) (hroom : 408 ≤ sp.toNat)
    (halign : sp.toNat % 16 = 0) (v : Values Value Reg.count) (m : Ram)
    (src : BitVec 64) (bytes : ByteArray) (initial : Vector Bool 128)
    (v4 : v[4].get 64 = sp)
    (vcount : (if isCipher then v[15].get 64 else v[3].get 64).toNat = bytes.size)
    (vsrc : (if isCipher then v[14].get 64 else v[12].get 64) = src)
    (vt : GPRsTyped v) (vdf : v[22] = ⟨1, 0⟩)
    (v39 : v[39] = ⟨32, v[39].get 32⟩)
    (v50 : v[50] = ⟨16, v[50].get 16⟩)
    (v51 : v[51] = ⟨16, v[51].get 16⟩)
    (wm : Writable code m (sp - 408) 520)
    (rm : 0 < bytes.size → Readable m src bytes.size) (bm : (span src bytes.size).HasBytes m bytes)
    (sep : (span (sp - 408) 520).Disjoint (span src bytes.size))
    (slot0 : Readable m 0x201228 8) (slot1 : Readable m 0x201208 8)
    (slot0val : memLoad m 0x201228 64 = 0x103eb0)
    (slot1val : memLoad m 0x201208 64 = 0x103f00)
    (slotBounds : sp.toNat + 112 ≤ 0x201208 ∨ 0x201230 ≤ (sp - 408).toNat)
    (key0 : memLoad m (sp + 80) 64 =
      (GHASH.polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)).1)
    (key1 : memLoad m (sp + 88) 64 =
      (GHASH.polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)).2)
    (hfull : stateBits (memLoad m (sp + 96) 64, memLoad m (sp + 104) 64) =
      (Standards.NIST.GCM.blocks (AesGcm.Spec.GCM.bitsOfByteArray bytes)).toList.foldl
        (fun acc b ↦ Standards.NIST.GCM.mul (Standards.NIST.GCM.xor acc b)
          (Standards.NIST.GCM.bitsOfBytes h)) initial) :
    ∃ o : Output Value Ram Reg.count,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then (if isCipher then .l101d72 else .l101c86)
          else (if isCipher then .l101952 else .l101866), v, m⟩, []⟩
        ⟨⟨if use256 then (if isCipher then .l101e4a else .l101d5e)
          else (if isCipher then .l101a2a else .l10193e), o.values, o.store⟩, []⟩ ∧
      o.values[4] = ⟨64, sp⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,15,22,39,50,51] → o.values[r] = v[r]) ∧
      (isCipher = false → o.values[14] = v[14]) ∧
      GPRsTyped o.values ∧ RamWriteFrame m o.store [span (sp - 408) 520] ∧
      stateBits (memLoad o.store (sp + 96) 64, memLoad o.store (sp + 104) 64) =
        hashPadded h bytes initial ∧
      memLoad o.store (sp + 80) 64 = memLoad m (sp + 80) 64 ∧
      memLoad o.store (sp + 88) 64 = memLoad m (sp + 88) 64 := by
  let count := if isCipher then v[15].get 64 else v[3].get 64
  have remNat : (count &&& 15).toNat = bytes.size % 16 := by
    rw [BitVec.toNat_and]
    change count.toNat &&& (2^4-1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact congrArg (fun n => n % 16) vcount
  obtain ⟨n, run, label, mem, nr, ns, nc, keep, nt⟩ :
      ∃ n : Location Value Ram LIR.Label signature,
        LIR.program.runBlock (dialect code)
          ⟨if use256 then (if isCipher then .l101d72 else .l101c86)
            else (if isCipher then .l101952 else .l101866), v, m⟩ = .jump n ∧
        n.label = (if count &&& 15 = 0 then
          (if use256 then (if isCipher then .l101e4a else .l101d5e)
            else (if isCipher then .l101a2a else .l10193e)) else
          (if use256 then (if isCipher then .l101d7f else .l101c93)
            else (if isCipher then .l10195f else .l101873))) ∧
        n.store = m ∧
        (if isCipher then (n.arguments[12]'(by change 12 < 53; decide)).get 64
          else (n.arguments[13]'(by change 13 < 53; decide)).get 64) = count &&& 15 ∧
        (if isCipher then (n.arguments[14]'(by change 14 < 53; decide)).get 64
          else (n.arguments[12]'(by change 12 < 53; decide)).get 64) = src ∧
        (if isCipher then (n.arguments[15]'(by change 15 < 53; decide)).get 64
          else (n.arguments[3]'(by change 3 < 53; decide)).get 64) = count ∧
        (∀ r : Fin 53, r.val ∈ [3,4,5,14,15,22,39,50,51] → n.arguments[r] = v[r]) ∧
        GPRsTyped n.arguments := by
    cases isCipher
    · obtain ⟨n, run, lab, mem, rem, keep, types⟩ := Execution.aad_tail_branch use256 code v m
      refine ⟨n, run, lab, mem, ?_, ?_, ?_, ?_, types vt⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]; rw [rem]; rfl
      · simp only [Bool.false_eq_true, ↓reduceIte] at vsrc ⊢
        exact (congrArg (Value.get 64) (keep 12 (by decide))).trans vsrc
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact congrArg (Value.get 64) (keep 3 (by decide))
      · intro r hr
        apply keep r
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        omega
    · obtain ⟨n, run, lab, mem, rem, keep, types⟩ := Execution.ciphertext_tail_branch use256 code v m
      refine ⟨n, run, lab, mem, ?_, ?_, ?_, ?_, types vt⟩
      · simp only [↓reduceIte]; rw [rem]; rfl
      · simp only [↓reduceIte] at vsrc ⊢
        exact (congrArg (Value.get 64) (keep 14 (by decide))).trans vsrc
      · simp only [↓reduceIte]
        exact congrArg (Value.get 64) (keep 15 (by decide))
      · intro r hr
        apply keep r
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        omega
  have n4 : (n.arguments[4]'(by change 4 < 53; decide)) = ⟨64, sp⟩ :=
    (keep 4 (by decide)).trans ((vt.value ⟨4, by decide⟩).trans (congrArg (fun x : BitVec 64 ↦ (⟨64, x⟩ : Value)) v4))
  have reached : (LIR.program.sem (dialect code)).Reaches
      ⟨⟨if use256 then (if isCipher then .l101d72 else .l101c86)
        else (if isCipher then .l101952 else .l101866), v, m⟩, []⟩ ⟨n, []⟩ := by
    apply Semantics.Reaches.single
    change LIR.program.step (dialect code) _ = _
    simp only [Program.step, run, Transfer.next]
  by_cases hz : bytes.size % 16 = 0
  · have bz : count &&& 15 = 0 := BitVec.eq_of_toNat_eq (by simpa only [hz, BitVec.reduceToNat] using remNat)
    simp only [bz, ↓reduceIte] at label
    refine ⟨{values := n.arguments, store := n.store, tag := none}, ?_, n4, ?_, fun _ ↦ keep 14 (by decide), nt, ?_, ?_, ?_, ?_⟩
    · have ne : n = ⟨if use256 then (if isCipher then .l101e4a else .l101d5e)
          else (if isCipher then .l101a2a else .l10193e), n.arguments, n.store⟩ := by
        cases n with
        | mk lab vals st => dsimp only at label; subst lab; rfl
      conv at reached => rhs; rw [ne]
      exact reached
    · intro r hr
      apply keep r
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      omega
    · change RamWriteFrame m n.store _
      rw [mem]; exact .refl _ _
    · change stateBits (memLoad n.store _ _, memLoad n.store _ _) = _
      rw [mem, hashPadded_eq_full_tail, ite_eq_left hz]
      exact hfull
    · change memLoad n.store _ _ = _; rw [mem]
    · change memLoad n.store _ _ = _; rw [mem]
  · have rm := rm (by omega)
    have bz : count &&& 15 ≠ 0 := by
      intro he
      have := congrArg BitVec.toNat he
      rw [remNat] at this
      exact hz this
    simp only [bz, ↓reduceIte] at label
    let offset := if isCipher then 0xffffffff0 &&& count else 0x1ffffffffffffff0 &&& count
    have offNat : offset.toNat = 16 * (bytes.size / 16) := by
      have bound : count.toNat ≤ 2^32 := by have := rm.low; change count.toNat = _ at vcount; omega
      cases isCipher
      all_goals
        simp only [offset, Bool.false_eq_true, ↓reduceIte]
        rw [BitVec.toNat_and, Nat.and_comm]
      · change count.toNat &&& ((2^57-1)*2^4) = _
        rw [GHASHUpdate.nat_and_shifted_mask]
        simp only [Nat.reducePow]
        rw [Nat.mod_eq_of_lt (by omega)]
        change count.toNat = _ at vcount
        omega
      · change count.toNat &&& ((2^32-1)*2^4) = _
        rw [GHASHUpdate.nat_and_shifted_mask]
        simp only [Nat.reducePow]
        rw [Nat.mod_eq_of_lt (by omega)]
        change count.toNat = _ at vcount
        omega
    have noff : (if isCipher then 0xffffffff0 &&& (n.arguments[15]'(by change 15 < 53; decide)).get 64
        else 0x1ffffffffffffff0 &&& (n.arguments[3]'(by change 3 < 53; decide)).get 64) = offset := by
      cases isCipher <;> simp only [Bool.false_eq_true, ↓reduceIte] at nc ⊢ <;>
        simp only [nc, offset, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat] <;> rfl
    have n39 : (n.arguments[39]'(by change 39 < 53; decide)) = v[39] := keep 39 (by decide)
    have n50 : (n.arguments[50]'(by change 50 < 53; decide)) = v[50] := keep 50 (by decide)
    have n51 : (n.arguments[51]'(by change 51 < 53; decide)) = v[51] := keep 51 (by decide)
    obtain ⟨o, reach, osp, regs, reg14, types, frame, post, key0out, key1out⟩ :=
      paddedTail_exec use256 isCipher code hcode hmultiply h sp hroom halign n.arguments m
        src (count &&& 15) offset bytes (by rw [n4]; rfl) nr ns noff offNat remNat
        (by rw [remNat]; omega) nt ((keep 22 (by decide)).trans vdf)
        (by rw [n39]; exact v39) (by rw [n50]; exact v50) (by rw [n51]; exact v51)
        wm rm bm sep slot0 slot1 slot0val slot1val slotBounds key0 key1
    refine ⟨o, ?_, osp, ?_, ?_, types, frame, ?_, key0out, key1out⟩
    · apply reached.trans
      have ne : n = ⟨if use256 then (if isCipher then .l101d7f else .l101c93)
          else (if isCipher then .l10195f else .l101873), n.arguments, m⟩ := by
        cases n with
        | mk lab vals st => dsimp only at label mem; subst lab st; rfl
      conv => lhs; rw [ne]
      exact reach
    · intro r hr
      have hsmall : r.val ∈ [3,5,13,15,22,39,50,51] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega
      apply (regs r hsmall).trans
      apply keep r
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega
    · intro hc
      exact (reg14 hc).trans (keep 14 (by decide))
    · rw [hashPadded_eq_full_tail, ite_eq_right hz, ← hfull]
      exact post

set_option maxHeartbeats 1400000 in
private theorem ciphertext_zero_exec (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (v : Values Value Reg.count) (m : Ram) (sp : BitVec 64)
    (v4 : v[4].get 64 = sp) (v15 : v[15].get 64 = 0)
    (vt : GPRsTyped v) (wm : Writable code m (sp - 96) 96)
    (room : 96 ≤ sp.toNat) :
    ∃ o : Output Value Ram Reg.count,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l101d5e else .l10193e, v, m⟩, []⟩
        ⟨⟨if use256 then .l101d72 else .l101952, o.values, o.store⟩, []⟩ ∧
      o.values[4] = ⟨64, sp⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → o.values[r] = v[r]) ∧
      GPRsTyped o.values ∧ RamWriteFrame m o.store [span (sp - 96) 96] := by
  have sub8 : (sp - 8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; omega)
  have sub96 : (sp - 96).toNat = sp.toNat - 96 :=
    BitVec.toNat_sub_of_le (by change 96 ≤ sp.toNat; omega)
  have low : sp.toNat ≤ 2^32 := by have := wm.readable.low; rw [sub96] at this; omega
  obtain ⟨c, cont, run, lab, target, guard, memory, c4, c7, c6, c2, keep, types⟩ :=
    Execution.ciphertext_runBlock use256 code hcode v m
      (by rw [v4]; exact wm.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
  let ret : BitVec 64 := if use256 then 0x101d72 else 0x101952
  let cm := memStore m (sp - 8) ret
  have cmem : c.store = cm := by simpa only [v4] using memory
  have cp : (c.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 := by rw [c4, v4]; rfl
  have cn : (c.arguments[2]'(by change 2 < 53; decide)).get 64 = 0 := by rw [c2, v15]; rfl
  have ct := types vt
  have cframe : RamWriteFrame m cm [span (sp - 8) 8] := by
    apply (RamWriteFrame.refl m _).memStore
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [InRegion, span, sub8]
    omega
  have cret : memLoad cm (sp - 8) 64 = ret := by
    dsimp only [cm]
    runtime_finish []
  obtain ⟨a, am, arun, a4, a3, a14, a13, a5, ak, aty, af, acount, adst,
      as3, as12, as13, as14, as15, as5⟩ :=
    GHASHUpdate.driver_entry_runBlock code hcode c.arguments cm (sp - 8)
      ((c.arguments[6]'(by change 6 < 53; decide)).get 64)
      ((c.arguments[7]'(by change 7 < 53; decide)).get 64) 0 cp rfl rfl cn ct
      (by rw [show sp - 8 - 88 = sp - 96 by bv_omega]
          exact (wm.of_frame cframe).sub (Nat.le_refl _) (by omega))
      (by rw [sub8]; omega)
  change LIR.program.runBlock (dialect code) ⟨.l109980, c.arguments, cm⟩ =
    .jump ⟨.l1099d5, a, am⟩ at arun
  have a4' : a[4].get 64 = sp - 96 := by rw [a4]; change sp - 8 - 88 = _; bv_omega
  obtain ⟨b, brun, b13, bk, bt⟩ := GHASHUpdate.driver_tail_dispatch_runBlock code a am 0
    (by rw [a13]; rfl) aty
  change LIR.program.runBlock (dialect code) ⟨.l1099d5, a, am⟩ =
    .jump ⟨.l109aaa, b, am⟩ at brun
  have bf : RamWriteFrame m am [span (sp - 96) 96] := by
    have f : RamWriteFrame m cm [span (sp - 96) 96] := by
      apply (RamWriteFrame.refl m _).trans cframe
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;> simp only [span, sub8, sub96] <;> omega
    apply f.trans af
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;>
      simp only [span, show sp - 8 - 88 = sp - 96 by bv_omega, sub96] <;> omega
  have aret : memLoad am (sp - 8) 64 = ret := by
    rw [af.memLoad_eq, cret]
    refine ⟨by rw [sub8]; omega, ?_⟩
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    simp only [span, show sp - 8 - 88 = sp - 96 by bv_omega, sub8, sub96]
    omega
  obtain ⟨o, orun, otag, omem, osp, o3, o12, o13, o14, o15, o5, ok, ot⟩ :=
    GHASHUpdate.driver_exit_runBlock code b am (sp - 96)
      (by have hb : b[4] = a[4] := bk 4 (by decide); rw [hb]; exact a4') bt
      (by rw [show sp - 96 + 40 = sp - 56 by bv_omega]
          exact (wm.readable.of_frame bf).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      (by rw [show sp - 96 + 88 = sp - 8 by bv_omega, aret]; dsimp only [ret]; split <;> decide)
  have exec : LIR.program.Exec (dialect code) ⟨⟨.l109980, c.arguments, cm⟩, []⟩ o := by
    apply Program.Exec.next
    · rw [Program.step, arun]; rfl
    apply Program.Exec.next
    · rw [Program.step, brun]; rfl
    apply Program.Exec.done
    rw [Program.step, orun]; rfl
  have ce : c = ⟨.l109980, c.arguments, cm⟩ := by
    cases c with
    | mk lab' vals st => dsimp only at lab cmem; subst lab' st; rfl
  have cexec : LIR.program.Exec (dialect code) ⟨c, []⟩ o := by rw [ce]; exact exec
  have accept : cont.Accepts (dialect code) o.tag = true := by
    rw [otag, show sp - 96 + 88 = sp - 8 by bv_omega, aret]
    simp only [StackFrame.Accepts, guard]
    cases use256 <;> rfl
  have reach := Execution.call_reaches code _ _ _ _ run cexec accept
  rw [target] at reach
  refine ⟨o, reach, ?_, ?_, ot, ?_⟩
  · simpa only [show sp - 96 + 96 = sp by bv_omega] using osp
  · rintro ⟨r, hrange⟩ hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change o.values[3] = v[3]
      rw [o3, show sp - 96 + 40 = sp - 8 - 48 by bv_omega, as3]
      exact (ct.value ⟨3, by decide⟩).symm.trans (keep 3 (by decide))
    · change o.values[5] = v[5]
      rw [o5, show sp - 96 + 80 = sp - 8 - 8 by bv_omega, as5]
      exact (ct.value ⟨5, by decide⟩).symm.trans (keep 5 (by decide))
    · change o.values[12] = v[12]
      rw [o12, show sp - 96 + 48 = sp - 8 - 40 by bv_omega, as12]
      exact (ct.value ⟨12, by decide⟩).symm.trans (keep 12 (by decide))
    · change o.values[13] = v[13]
      rw [o13, show sp - 96 + 56 = sp - 8 - 32 by bv_omega, as13]
      exact (ct.value ⟨13, by decide⟩).symm.trans (keep 13 (by decide))
    · change o.values[14] = v[14]
      rw [o14, show sp - 96 + 64 = sp - 8 - 24 by bv_omega, as14]
      exact (ct.value ⟨14, by decide⟩).symm.trans (keep 14 (by decide))
    · change o.values[15] = v[15]
      rw [o15, show sp - 96 + 72 = sp - 8 - 16 by bv_omega, as15]
      exact (ct.value ⟨15, by decide⟩).symm.trans (keep 15 (by decide))
    · change o.values[22] = v[22]
      exact (ok 22 (by decide)).trans ((bk 22 (by decide)).trans
        ((ak 22 (by decide)).trans (keep 22 (by decide))))
    · change o.values[39] = v[39]
      exact (ok 39 (by decide)).trans ((bk 39 (by decide)).trans
        ((ak 39 (by decide)).trans (keep 39 (by decide))))
    · change o.values[50] = v[50]
      exact (ok 50 (by decide)).trans ((bk 50 (by decide)).trans
        ((ak 50 (by decide)).trans (keep 50 (by decide))))
    · change o.values[51] = v[51]
      exact (ok 51 (by decide)).trans ((bk 51 (by decide)).trans
        ((ak 51 (by decide)).trans (keep 51 (by decide))))
  · rw [omem]; exact bf

set_option maxHeartbeats 1200000 in
private theorem length_exec (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (hmultiply : GHASHInterface.MultiplyContract code)
    (v : Values Value Reg.count) (m : Ram) (sp : BitVec 64)
    (v4 : v[4].get 64 = sp) (vt : GPRsTyped v)
    (v39 : v[39] = ⟨32, v[39].get 32⟩)
    (v50 : v[50] = ⟨16, v[50].get 16⟩)
    (v51 : v[51] = ⟨16, v[51].get 16⟩) (vdf : v[22] = ⟨1,0⟩)
    (wm : Writable code m (sp-408) 520) (room : 408 ≤ sp.toNat) (align : sp.toNat % 16 = 0)
    (bound : (v[15].get 64).toNat < 2^36) :
    ∃ o : Output Value Ram Reg.count,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l101e4a else .l101a2a, v, m⟩, []⟩
        ⟨⟨if use256 then .l101eeb else .l101acb, o.values, o.store⟩, []⟩ ∧
      o.values[4] = ⟨64,sp⟩ ∧
      (∀ r : Fin 53, r.val ∈ [5,22,39,50,51] → o.values[r] = v[r]) ∧
      GPRsTyped o.values ∧ RamWriteFrame m o.store [span (sp-408) 520] ∧
      (let result := GHASH.polyvalMultiplyWords
        (memLoad m (sp+96) 64 ^^^ (v[15].get 64 <<< 3))
        (memLoad m (sp+104) 64 ^^^ (v[3].get 64 <<< 3))
        (memLoad m (sp+80) 64) (memLoad m (sp+88) 64)
       memLoad o.store (sp+96) 64 = result.1 ∧ memLoad o.store (sp+104) 64 = result.2) := by
  have sub (n : Nat) (hn : n ≤ 408) : (sp-BitVec.ofNat 64 n).toNat=sp.toNat-n := by
    rw [BitVec.toNat_sub_of_le (by change (BitVec.ofNat 64 n).toNat ≤ sp.toNat; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have s8 : (sp-8).toNat=sp.toNat-8 := sub 8 (by decide)
  have s136 : (sp-136).toNat=sp.toNat-136 := sub 136 (by decide)
  have s408 : (sp-408).toNat=sp.toNat-408 := sub 408 (by decide)
  have low : sp.toNat+112 ≤ 2^32 := by have := wm.readable.low; rw [s408] at this; omega
  have add (n : Nat) (hn : n ≤ 112) : (sp+BitVec.ofNat 64 n).toNat=sp.toNat+n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have a80 : (sp+80).toNat=sp.toNat+80 := add 80 (by decide)
  have a96 : (sp+96).toNat=sp.toNat+96 := add 96 (by decide)
  obtain ⟨r, cont, run, lab, target, guard, r4, r7, r6, keep, types, frame, ret, word0, word1⟩ :=
    Execution.length_runBlock use256 code hcode v m
      (by rw [v4]; exact wm.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) bound
  rw [v4] at frame ret word0 word1
  have rp : (r.arguments[4]'(by change 4<53; decide)).get 64=sp-8 := by rw [r4, v4]; rfl
  have rd : (r.arguments[7]'(by change 7<53; decide)).get 64=sp+80 := by rw [r7, v4]; rfl
  have rs : (r.arguments[6]'(by change 6<53; decide)).get 64=sp+16 := by rw [r6, v4]; rfl
  have state (n : Nat) (hn : 80 ≤ n) (hn' : n+8 ≤ 112) :
      memLoad r.store (sp+BitVec.ofNat 64 n) 64=memLoad m (sp+BitVec.ofNat 64 n) 64 := by
    apply frame.memLoad_eq
    refine ⟨by rw [add n (by omega)]; omega, ?_⟩
    intro region hr; obtain rfl := List.mem_singleton.mp hr
    simp only [span, s8, add n (by omega)]
    omega
  have state80 : memLoad r.store (sp+80) 64=memLoad m (sp+80) 64 := state 80 (by decide) (by decide)
  have state88 : memLoad r.store (sp+88) 64=memLoad m (sp+88) 64 := state 88 (by decide) (by decide)
  have state96 : memLoad r.store (sp+96) 64=memLoad m (sp+96) 64 := state 96 (by decide) (by decide)
  have state104 : memLoad r.store (sp+104) 64=memLoad m (sp+104) 64 := state 104 (by decide) (by decide)
  have r39 : (r.arguments[39]'(by change 39<53; decide))=v[39] := keep 39 (by decide)
  have r50 : (r.arguments[50]'(by change 50<53; decide))=v[50] := keep 50 (by decide)
  have r51 : (r.arguments[51]'(by change 51<53; decide))=v[51] := keep 51 (by decide)
  have rdf : (r.arguments[22]'(by change 22<53; decide))=⟨1,0⟩ := (keep 22 (by decide)).trans vdf
  let rr : BitVec 64 := if use256 then 0x101eeb else 0x101acb
  obtain ⟨o, exec, tag, doneAtoms, ot, oframe, post⟩ :=
    callContract_exec_values LIR.lifted code .l1034c0 LIR.Fn1034c0.frameInfo
      (fun fr ↦ [span (fr.rdi+16) 16]) _ _ (GHASHUpdate.oneBlock_call code hmultiply)
      r.store r.arguments rr (sp-136) (types vt)
      (by rw [r39]; exact v39) (by rw [r50]; exact v50) (by rw [r51]; exact v51) rdf
      (by rw [rp]; exact (wm.readable.of_frame frame).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      (by rw [rp]; exact ret) (by dsimp only [rr]; split <;> decide)
      (fun _ ↦ by
        change Writable code r.store ((r.arguments[4]'(by change 4<53; decide)).get 64-128) 128
        rw [rp, show sp-8-128=sp-136 by bv_omega]
        exact (wm.of_frame frame).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      (by change (sp-136).toNat+128 ≤ ((r.arguments[4]'(by change 4<53; decide)).get 64).toNat
          rw [rp, s136, s8]; omega)
      (by rw [rp, s8]; omega) (by trivial)
      (by
        simp only [activationOfValues, callStack, rp, rd, rs]
        refine ⟨(wm.readable.of_frame frame).of_offsets rfl (addr_sub _ _) (by decide),
          (wm.of_frame frame).of_offsets rfl (addr_sub _ _) (by decide), ?_⟩
        intro x hx hy
        simp only [MemoryRegion.Contains, span, s8, s136, a80] at hx hy
        omega)
  have op := Execution.preserved_of_doneAtoms code r.store r.arguments rr (sp-136) o
    (types vt) (by rw [r39]; exact v39) (by rw [r50]; exact v50) (by rw [r51]; exact v51) rdf doneAtoms
  have re : r=⟨.l1034c0,r.arguments,r.store⟩ := by
    cases r with
    | mk l a m => dsimp only at lab; subst l; rfl
  have rExec : LIR.program.Exec (dialect code) ⟨r,[]⟩ o := by
    conv => lhs; rw [re]
    exact exec
  have accept : cont.Accepts (dialect code) o.tag=true := by
    rw [tag]; simp only [StackFrame.Accepts, guard]; cases use256 <;> rfl
  have reach := Execution.call_reaches code _ _ _ _ run rExec accept
  rw [target] at reach
  refine ⟨o, reach, ?_, ?_, ot, ?_, ?_⟩
  · simpa only [rp, BitVec.sub_add_cancel] using op.1
  · intro j hj
    have hbig : j.val ∈ [3,5,12,13,14,15,22,39,50,51] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega
    exact (op.2 j hbig).trans (keep j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega))
  · have f : RamWriteFrame m r.store [span (sp-408) 520] := by
      apply (RamWriteFrame.refl _ _).trans frame
      intro region hr; obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;> simp only [span, s8, s408] <;> omega
    apply f.trans oframe
    intro region hr
    change region ∈ [⟨(sp-136).toNat, ((r.arguments[4]'(by change 4<53; decide)).get 64).toNat-(sp-136).toNat⟩,
      span ((r.arguments[7]'(by change 7<53; decide)).get 64+16) 16] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals
      refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;>
        simp only [span, rp, rd, s8, s136, s408,
          show sp+80+16=sp+96 by bv_omega, a96] <;> omega
  · simpa only [activationOfValues, rd, rs,
      show sp+80+8=sp+88 by bv_omega,
      show sp+80+16=sp+96 by bv_omega,
      show sp+80+24=sp+104 by bv_omega,
      show sp+16+8=sp+24 by bv_omega,
      state80, state88,
      state96, state104, word0, word1,
      BitVec.xor_comm] using post

set_option maxHeartbeats 1200000 in
private theorem finalize_exec (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (v : Values Value Reg.count) (m : Ram) (sp : BitVec 64)
    (v4 : v[4].get 64 = sp) (vt : GPRsTyped v)
    (wm : Writable code m (sp-408) 520) (room : 408 ≤ sp.toNat) :
    ∃ o : Output Value Ram Reg.count,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l101eeb else .l101acb, v, m⟩, []⟩
        ⟨⟨if use256 then .l101f22 else .l101b02, o.values, o.store⟩, []⟩ ∧
      o.values[4] = ⟨64,sp⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → o.values[r] = v[r]) ∧
      GPRsTyped o.values ∧ RamWriteFrame m o.store [span (sp-408) 520] ∧
      memLoad o.store (sp+64) 64 = memLoad m (sp+96) 64 ∧
      memLoad o.store (sp+72) 64 = memLoad m (sp+104) 64 := by
  have sub408 : (sp-408).toNat=sp.toNat-408 :=
    BitVec.toNat_sub_of_le (by change 408 ≤ sp.toNat; omega)
  have sub8 : (sp-8).toNat=sp.toNat-8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; omega)
  have low : sp.toNat+112 ≤ 2^32 := by have := wm.readable.low; rw [sub408] at this; omega
  have add (n : Nat) (hn : n ≤ 112) : (sp+BitVec.ofNat 64 n).toNat=sp.toNat+n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have a64 : (sp+64).toNat=sp.toNat+64 := add 64 (by decide)
  obtain ⟨c, cont, run, lab, target, guard, memory, c4, c7, c6, keep, types⟩ :=
    Execution.finalize_runBlock use256 code hcode v m
      (by rw [v4]; exact wm.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      (by rw [v4]; exact wm.of_offsets rfl (addr_sub _ _) (by decide))
      (by rw [v4]; exact wm.readable.of_offsets rfl (addr_sub _ _) (by decide))
  let fm := Execution.finalizeMemory use256 v m
  have cm : c.store=fm := memory
  have cp : (c.arguments[4]'(by change 4<53; decide)).get 64=sp-8 := by rw [c4,v4]; rfl
  have cd : (c.arguments[7]'(by change 7<53; decide)).get 64=sp+64 := by rw [c7,v4]; rfl
  have cs : (c.arguments[6]'(by change 6<53; decide)).get 64=sp+16 := by rw [c6,v4]; rfl
  have ff : RamWriteFrame m fm [span (sp-8) 56] := by
    dsimp only [fm, Execution.finalizeMemory]
    rw [v4]
    runtime_finish [span]
  have words : memLoad fm (sp+32) 64=memLoad m (sp+96) 64 ∧
      memLoad fm (sp+40) 64=memLoad m (sp+104) 64 := by
    dsimp only [fm, Execution.finalizeMemory]
    rw [v4]
    constructor <;> runtime_finish []
  have fre : memLoad fm (sp-8) 64=(if use256 then 0x101f22 else 0x101b02) := by
    dsimp only [fm, Execution.finalizeMemory]
    rw [v4]
    runtime_finish []
  have wr : Writable code fm (sp+64) 16 :=
    (wm.of_frame ff).of_offsets rfl (addr_sub _ _) (by decide)
  have frf := finalizeRam_frame fm (sp+64) (sp+16) wr.readable
  have fret : memLoad (finalizeRam fm (sp+64) (sp+16)) (sp-8) 64 =
      (if use256 then 0x101f22 else 0x101b02) := by
    rw [frf.memLoad_eq, fre]
    refine ⟨by rw [sub8]; omega, ?_⟩
    intro region hr; obtain rfl := List.mem_singleton.mp hr
    simp only [span, sub8, a64]
    omega
  obtain ⟨o, orun, om, otag, osp, ok, typeso⟩ := finalize_runBlock code hcode c.arguments fm
    (by rw [cs, show sp+16+16=sp+32 by bv_omega]
        exact (wm.readable.of_frame ff).of_offsets rfl (addr_sub _ _) (by decide))
    (by rw [cd]; exact wr)
    (by
      rw [cp, cd, cs]
      refine ⟨LoadOk.of_region ((wm.readable.of_frame ff).of_frame frf) ?_ ?_, ?_⟩
      · rw [sub408,sub8]; omega
      · rw [sub408,sub8]; omega
      rw [fret]; split <;> decide)
  have ce : c=⟨.l1034a0,c.arguments,fm⟩ := by
    cases c with
    | mk l a mem => dsimp only at lab cm; subst l mem; rfl
  have exec : LIR.program.Exec (dialect code) ⟨⟨.l1034a0,c.arguments,fm⟩,[]⟩ o := by
    apply Program.Exec.done
    change (LIR.program.runBlock (dialect code) ⟨.l1034a0,c.arguments,fm⟩).next (dialect code) [] = .done o
    rw [orun]; rfl
  have cexec : LIR.program.Exec (dialect code) ⟨c,[]⟩ o := by
    conv => lhs; rw [ce]
    exact exec
  simp only [cp, cd, cs] at om otag osp
  have accept : cont.Accepts (dialect code) o.tag=true := by
    rw [otag,om,fret]
    simp only [StackFrame.Accepts,guard]
    cases use256 <;> rfl
  have reach := Execution.call_reaches code _ _ _ _ run cexec accept
  rw [target] at reach
  refine ⟨o, reach, ?_, ?_, typeso (types vt), ?_, ?_, ?_⟩
  · simpa only [BitVec.sub_add_cancel] using osp
  · intro j hj
    exact (ok j hj).trans (keep j hj)
  · rw [om]
    have f : RamWriteFrame m fm [span (sp-408) 520] := by
      apply (RamWriteFrame.refl _ _).trans ff
      intro region hr; obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;> simp only [span,sub8,sub408] <;> omega
    apply f.trans frf
    intro region hr; obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;> simp only [span,sub408,a64] <;> omega
  · rw [om, (finalizeRam_words fm (sp+64) (sp+16) wr.readable).1,
      show sp+16+16=sp+32 by bv_omega]
    exact words.1
  · have e := (finalizeRam_words fm (sp+64) (sp+16) wr.readable).2
    rw [show sp+64+8=sp+72 by bv_omega, show sp+16+24=sp+40 by bv_omega] at e
    rw [om,e]; exact words.2

set_option maxHeartbeats 1000000 in
private theorem finish_tag_exec (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (fr : Activation)
    (args : Values Value Reg.count)
    (ef : EntryFacts (if use256 then LIR.Fn101c20.frameInfo else LIR.Fn101800.frameInfo)
      fr code args fr.original)
    (sp : BitVec 64) (spEq : sp=fr.rsp-184)
    (hroom : fr.low.toNat+592 ≤ fr.rsp.toNat)
    (hw : Writable code fr.original (fr.rsp-592) 592)
    (hdst : Writable code fr.original fr.rdi 16)
    (hmask : Readable fr.original fr.rdx 16)
    (mask tag : Vector UInt8 16)
    (hmaskBytes : (span fr.rdx 16).HasBytes fr.original ⟨mask.toArray⟩)
    (hdstSep : (callStack fr).Disjoint (span fr.rdi 16))
    (hmaskSep : (callStack fr).Disjoint (span fr.rdx 16))
    (f : Output Value Ram Reg.count) (f4 : f.values[4]=⟨64,sp⟩)
    (ft : GPRsTyped f.values)
    (fFrame : RamWriteFrame (Execution.entryMemory use256 args fr.original) f.store
      [span (sp-408) 520])
    (fpk : ∀ r : Fin 53, r.val ∈ [22,39,50,51] → f.values[r]=args[r])
    (s : BitVec 64 × BitVec 64)
    (fword0 : memLoad f.store (sp+64) 64=s.1)
    (fword1 : memLoad f.store (sp+72) 64=s.2)
    (tagState : tag=Standards.NIST.GCM.bytesOfBits
      (Standards.NIST.GCM.xor (stateBits s) (Standards.NIST.GCM.bitsOfBytes mask))) :
    ∃ o : Output Value Ram Reg.count,
      LIR.program.Exec (dialect code)
        ⟨⟨if use256 then .l101f22 else .l101b02,f.values,f.store⟩,[]⟩ o ∧
      o.tag=some ⟨64,fr.ret⟩ ∧
      Atom.All code o.values o.store
        ((if use256 then LIR.Fn101c20.frameInfo else LIR.Fn101800.frameInfo).doneAtoms fr) ∧
      GPRsTyped o.values ∧ RamWriteFrame fr.original o.store [fr.region,span fr.rdi 16] ∧
      (span fr.rdi 16).HasBytes o.store ⟨tag.toArray⟩ := by
  let prepared := Execution.entryMemory use256 args fr.original
  let low := sp-408
  have spNat : sp.toNat=fr.rsp.toNat-184 := by
    rw [spEq]; exact BitVec.toNat_sub_of_le (by change 184 ≤ fr.rsp.toNat; omega)
  have lowNat : low.toNat=sp.toNat-408 :=
    BitVec.toNat_sub_of_le (by change 408 ≤ sp.toNat; rw [spNat]; omega)
  have rsp192 : (fr.rsp-192).toNat=fr.rsp.toNat-192 :=
    BitVec.toNat_sub_of_le (by change 192 ≤ fr.rsp.toNat; omega)
  have spAdd (n : Nat) (hn : n ≤ 192) : (sp+BitVec.ofNat 64 n).toNat=sp.toNat+n := by
    have hb := ef.slot.low
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
  have hsp : args[4].get 64=fr.rsp := by rw [ef.rsp]; rfl
  have hdstarg : args[7].get 64=fr.rdi := by rw [ef.rdi]; rfl
  have hmaskarg : args[2].get 64=fr.rdx := by rw [ef.rdx]; rfl
  have entryFrame : RamWriteFrame fr.original prepared [span (fr.rsp-192) 192] := by
    simpa only [hsp] using Execution.entryMemory_frame use256 args fr.original (by rw [hsp]; omega)
  have fOriginal : RamWriteFrame fr.original f.store [span (fr.rsp-592) 592] := by
    have e : RamWriteFrame fr.original prepared [span (fr.rsp-592) 592] := by
      apply (RamWriteFrame.refl _ _).trans entryFrame
      intro region hr; obtain rfl := List.mem_singleton.mp hr
      refine ⟨_,List.mem_singleton_self _,?_,?_⟩ <;>
        simp only [span,rsp192,show (fr.rsp-592).toNat=fr.rsp.toNat-592 from
          BitVec.toNat_sub_of_le (by change 592 ≤ fr.rsp.toNat; omega)] <;> omega
    apply e.trans fFrame
    intro region hr; obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_singleton_self _,?_,?_⟩ <;>
      simp only [span,show (sp-408).toNat=sp.toNat-408 from lowNat,spNat,
        show (fr.rsp-592).toNat=fr.rsp.toNat-592 from
          BitVec.toNat_sub_of_le (by change 592 ≤ fr.rsp.toNat; omega)] <;> omega
  have saved := Execution.entryMemory_saved use256 args fr.original
  change memLoad prepared _ 64 = _ ∧ _ at saved
  simp only [hsp] at saved
  have fSlot (n : Nat) (hn : 112 ≤ n) (hn' : n+8 ≤ 192) :
      memLoad f.store (sp+BitVec.ofNat 64 n) 64=memLoad prepared (sp+BitVec.ofNat 64 n) 64 := by
    apply fFrame.memLoad_eq
    refine ⟨by rw [spAdd n (by omega)]; have := ef.slot.low; rw [spNat]; omega, ?_⟩
    intro region hr; obtain rfl := List.mem_singleton.mp hr
    simp only [span,show (sp-408).toNat=sp.toNat-408 from lowNat,spAdd n (by omega)]
    omega
  have fs120 : memLoad f.store (sp+120) 64=memLoad prepared (sp+120) 64 := fSlot 120 (by decide) (by decide)
  have fs128 : memLoad f.store (sp+128) 64=memLoad prepared (sp+128) 64 := fSlot 128 (by decide) (by decide)
  have fs136 : memLoad f.store (sp+136) 64=memLoad prepared (sp+136) 64 := fSlot 136 (by decide) (by decide)
  have fs144 : memLoad f.store (sp+144) 64=memLoad prepared (sp+144) 64 := fSlot 144 (by decide) (by decide)
  have fs152 : memLoad f.store (sp+152) 64=memLoad prepared (sp+152) 64 := fSlot 152 (by decide) (by decide)
  have fs160 : memLoad f.store (sp+160) 64=memLoad prepared (sp+160) 64 := fSlot 160 (by decide) (by decide)
  have fs168 : memLoad f.store (sp+168) 64=memLoad prepared (sp+168) 64 := fSlot 168 (by decide) (by decide)
  have fs176 : memLoad f.store (sp+176) 64=memLoad prepared (sp+176) 64 := fSlot 176 (by decide) (by decide)
  have fs184 : memLoad f.store (sp+184) 64=memLoad prepared (sp+184) 64 := fSlot 184 (by decide) (by decide)
  have freturn : memLoad f.store (sp+184) 64=fr.ret := by
    rw [fs184,show sp+184=fr.rsp by rw [spEq]; bv_omega]
    rw [entryFrame.memLoad_eq,ef.ret]
    refine ⟨by have := ef.slot.low; omega, ?_⟩
    intro region hr; obtain rfl := List.mem_singleton.mp hr
    simp only [span,rsp192]; omega
  have fdst : memLoad f.store (sp+128) 64=fr.rdi := by
    rw [fs128,show sp+128=fr.rsp-56 by rw [spEq]; bv_omega,saved.2.2.1,hdstarg]
  have fmask : memLoad f.store (sp+120) 64=fr.rdx := by
    rw [fs120,show sp+120=fr.rsp-64 by rw [spEq]; bv_omega,saved.2.1,hmaskarg]
  have fRead : Readable f.store sp 192 := by
    have hw' : Readable fr.original sp 184 := by
      rw [spEq]
      exact hw.readable.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
    have ret' : Readable fr.original (sp+BitVec.ofNat 64 184) 8 := by
      rw [show sp+BitVec.ofNat 64 184=fr.rsp by rw [spEq]; bv_omega]; exact ef.slot
    exact (readable_append hw' ret').of_frame fOriginal
  have fMaskBytes : (span fr.rdx 16).HasBytes f.store ⟨mask.toArray⟩ := by
    apply hasBytes_of_frame fOriginal hmaskBytes (by change fr.rdx.toNat+16 ≤ 2^64; have := hmask.low; omega)
    intro region hr x hx hy
    obtain rfl := List.mem_singleton.mp hr
    apply hmaskSep x ?_ hx
    have h592 : (fr.rsp-592).toNat=fr.rsp.toNat-592 :=
      BitVec.toNat_sub_of_le (by change 592 ≤ fr.rsp.toNat; omega)
    simp only [MemoryRegion.Contains,span,callStack,h592] at hy ⊢
    omega
  have fp : f.values[4].get 64=sp := by rw [f4]; rfl
  obtain ⟨o, orun, otag, o4, o3, o12, o13, o14, o15, o5, ok, typed, oframe, obytes⟩ :=
    Execution.finish_runBlock use256 code hcode f.values f.store fr.rdi fr.rdx
      (by rw [fp,spEq]
          exact (hw.of_frame fOriginal).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      (by rw [fp]; exact fRead) (by rw [fp]; exact fdst) (by rw [fp]; exact fmask)
      (hdst.of_frame fOriginal) (hmask.of_frame fOriginal)
      (by rw [fp]; intro x hx hy; apply hdstSep x ?_ hy
          simp only [MemoryRegion.Contains,span,callStack,spNat] at hx ⊢; omega)
      (by rw [fp]; intro x hx hy; apply hmaskSep x ?_ hy
          simp only [MemoryRegion.Contains,span,callStack,spNat] at hx ⊢; omega)
      (by rw [fp]; change (memLoad f.store (sp+184) 64).toNat < 2^32; rw [freturn]; exact ef.retLow)
  simp only [fp] at otag o4 o3 o12 o13 o14 o15 o5 oframe obytes
  have ofull : RamWriteFrame fr.original o.store [fr.region,span fr.rdi 16] := by
    have ff : RamWriteFrame fr.original f.store [fr.region,span fr.rdi 16] := by
      apply (RamWriteFrame.refl _ _).trans fOriginal
      intro region hr; obtain rfl := List.mem_singleton.mp hr
      refine ⟨fr.region, by simp only [List.mem_cons,true_or], ?_, ?_⟩ <;>
        simp only [Activation.region,span,show (fr.rsp-592).toNat=fr.rsp.toNat-592 from
          BitVec.toNat_sub_of_le (by change 592 ≤ fr.rsp.toNat; omega)] <;> omega
    apply ff.trans oframe
    intro region hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨fr.region,by simp only [List.mem_cons,true_or],?_,?_⟩ <;>
        simp only [Activation.region,span,spNat] <;> omega
    · exact ⟨span fr.rdi 16,by simp only [List.mem_cons,List.not_mem_nil,or_false,or_true],Nat.le_refl _,Nat.le_refl _⟩
  have finishExec : LIR.program.Exec (dialect code)
      ⟨⟨if use256 then .l101f22 else .l101b02,f.values,f.store⟩,[]⟩ o := by
    apply Program.Exec.done
    rw [Program.step,orun]; rfl
  refine ⟨o,finishExec,?_,?_,typed ft,ofull,?_⟩
  · rw [otag,freturn]
  · have done : o.values[4]=⟨64,fr.rsp+8⟩ ∧ o.values[22]=⟨1,0⟩ ∧
        o.values[3]=⟨64,fr.rbx⟩ ∧ o.values[5]=⟨64,fr.rbp⟩ ∧
        o.values[12]=⟨64,fr.r12⟩ ∧ o.values[13]=⟨64,fr.r13⟩ ∧
        o.values[14]=⟨64,fr.r14⟩ ∧ o.values[15]=⟨64,fr.r15⟩ ∧
        o.values[39]=⟨32,fr.mxcsr⟩ ∧ o.values[50]=⟨16,fr.ftw⟩ ∧
        o.values[51]=⟨16,fr.fcw⟩ ∧ True := by
      refine ⟨?_,(ok 22 (by decide)).trans ((fpk 22 (by decide)).trans ef.df),?_,?_,?_,?_,?_,?_,
        (ok 39 (by decide)).trans ((fpk 39 (by decide)).trans ef.mxcsr),
        (ok 50 (by decide)).trans ((fpk 50 (by decide)).trans ef.ftw),
        (ok 51 (by decide)).trans ((fpk 51 (by decide)).trans ef.fcw),trivial⟩
      · simpa only [show sp+192=fr.rsp+8 by rw [spEq]; bv_omega] using o4
      · rw [o3,fs136,show sp+136=fr.rsp-48 by rw [spEq]; bv_omega,
          saved.2.2.2.1,ef.rbx]; rfl
      · rw [o5,fs176,show sp+176=fr.rsp-8 by rw [spEq]; bv_omega,
          saved.2.2.2.2.2.2.2.2,ef.rbp]; rfl
      · rw [o12,fs144,show sp+144=fr.rsp-40 by rw [spEq]; bv_omega,
          saved.2.2.2.2.1,ef.r12]; rfl
      · rw [o13,fs152,show sp+152=fr.rsp-32 by rw [spEq]; bv_omega,
          saved.2.2.2.2.2.1,ef.r13]; rfl
      · rw [o14,fs160,show sp+160=fr.rsp-24 by rw [spEq]; bv_omega,
          saved.2.2.2.2.2.2.1,ef.r14]; rfl
      · rw [o15,fs168,show sp+168=fr.rsp-16 by rw [spEq]; bv_omega,
          saved.2.2.2.2.2.2.2.1,ef.r15]; rfl
    cases use256 <;> exact done
  · refine ⟨by simp only [MemoryRegion.HasLength,ByteArray.size,Vector.size_toArray,span],?_⟩
    intro i
    have hi : i.val<16 := by have := i.isLt; simpa only [ByteArray.size,Vector.size_toArray] using this
    have hm (j : Nat) (hj : j<16) : memByte f.store (fr.rdx+BitVec.ofNat 64 j)=mask[j] := by
      have hb := fMaskBytes.2 ⟨j,by simpa only [ByteArray.size,Vector.size_toArray] using hj⟩
      simp only [span,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] at hb
      change f.store[fr.rdx+BitVec.ofNat 64 j]?=some mask[j] at hb
      simp only [memByte,PhysicalMemory.read,hb,Option.getD_some]
    have hs : memByte f.store (sp+BitVec.ofNat 64 (64+(15-i.val))) =
        (if i.val<8 then storedByte (s.2) (7-i.val)
          else storedByte (s.1) (15-i.val)) := by
      by_cases hi8 : i.val<8
      · rw [ite_eq_left hi8,show sp+BitVec.ofNat 64 (64+(15-i.val))=(sp+72)+BitVec.ofNat 64 (7-i.val) by bv_omega,
          ←storedByte_memLoad (n := 64) _ _ _ (by omega),fword1]
      · rw [ite_eq_right hi8,show sp+BitVec.ofNat 64 (64+(15-i.val))=(sp+64)+BitVec.ofNat 64 (15-i.val) by bv_omega,
          ←storedByte_memLoad (n := 64) _ _ _ (by omega),fword0]
    have hb := obytes i.val hi
    simp only [memLoad_8,hs,hm _ hi] at hb
    have ht := bytesOfBits_xor_stateBits_getElem
      s mask i.val hi
    rw [←tagState] at ht
    have ob : memByte o.store (fr.rdi+BitVec.ofNat 64 i.val)=
        (tag)[i.val] := by
      apply UInt8.toBitVec_inj.1
      rw [ht,UInt8.toBitVec_xor]
      exact hb
    have present := (hdst.readable.of_frame ofull).present i.val hi
    change o.store[BitVec.ofNat 64 (fr.rdi.toNat+i.val)]? = _
    simp only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    cases he : o.store[fr.rdi+BitVec.ofNat 64 i.val]? with
    | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at present
    | some byte =>
      simp only [memByte,PhysicalMemory.read,he,Option.getD_some] at ob
      exact congrArg some ob


set_option maxHeartbeats 2400000 in
theorem tag_call (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (h mask : Vector UInt8 16) (associatedData ciphertext : ByteArray) :
    CallContract LIR.lifted code (if use256 then .l101c20 else .l101800)
      (if use256 then LIR.Fn101c20.frameInfo else LIR.Fn101800.frameInfo)
      (fun fr ↦ [span fr.rdi 16])
      (fun fr mem ↦
        let k := GHASH.polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)
        Readable mem fr.rsi 32 ∧ memLoad mem fr.rsi 64 = k.1 ∧
        memLoad mem (fr.rsi + 8) 64 = k.2 ∧ memLoad mem (fr.rsi + 16) 64 = 0 ∧
        memLoad mem (fr.rsi + 24) 64 = 0 ∧
        Readable mem fr.rdx 16 ∧ (span fr.rdx 16).HasBytes mem ⟨mask.toArray⟩ ∧
        Readable mem fr.rcx associatedData.size ∧
        (span fr.rcx associatedData.size).HasBytes mem associatedData ∧
        fr.r8.toNat = associatedData.size ∧
        (0 < ciphertext.size → Readable mem fr.r9 ciphertext.size) ∧
        (span fr.r9 ciphertext.size).HasBytes mem ciphertext ∧
        Readable mem (fr.rsp + 8) 8 ∧
        (memLoad mem (fr.rsp + 8) 64).toNat = ciphertext.size ∧
        associatedData.size ≤ AesGcm.Spec.GCM.maxAssociatedDataBytes ∧
        ciphertext.size ≤ AesGcm.Spec.GCM.maxMessageBytes ∧
        Writable code mem fr.rdi 16 ∧
        (callStack fr).Disjoint (span fr.rdi 16) ∧
        (callStack fr).Disjoint (span fr.rsi 32) ∧
        (callStack fr).Disjoint (span fr.rdx 16) ∧
        (callStack fr).Disjoint (span fr.rcx associatedData.size) ∧
        (callStack fr).Disjoint (span fr.r9 ciphertext.size))
      (fun fr mem ↦ (span fr.rdi 16).HasBytes mem
        ⟨(authenticationTagFromMask h mask associatedData ciphertext).toArray⟩) := by
  intro fr loc hl hm he htypes hp
  rcases loc with ⟨label, args, mem⟩
  dsimp only at hl hm he htypes hp
  subst label mem
  change Values Value Reg.count at args
  have ef := entryFacts_of_atoms he
  have hw : Writable code fr.original (fr.rsp - 592) 592 := by
    have e := ef.window (by cases use256 <;> decide)
    cases use256 <;> exact e
  have hroom : fr.low.toNat + 592 ≤ fr.rsp.toNat := by
    have e := ef.room
    cases use256 <;> exact e
  rcases hp with ⟨hcontext, hk0, hk1, hs0, hs1, hmask, hmaskBytes, haad, haadBytes,
    hA, hcipher, hcipherBytes, hlenRead, hC, hAbound, hCbound, hdst, hdstSep,
    hcontextSep, hmaskSep, haadSep, hcipherSep⟩
  let sp := fr.rsp - 184
  have spNat : sp.toNat = fr.rsp.toNat - 184 := by
    exact BitVec.toNat_sub_of_le (by change 184 ≤ fr.rsp.toNat; omega)
  have spSub (n : Nat) (hn : n ≤ 408) :
      (sp - BitVec.ofNat 64 n).toNat = sp.toNat - n := by
    have hn64 : n < 2^64 := by omega
    rw [BitVec.toNat_sub_of_le (by
      change (BitVec.ofNat 64 n).toNat ≤ sp.toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, spNat]
      omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  have spAdd (n : Nat) (hn : n ≤ 200) :
      (sp + BitVec.ofNat 64 n).toNat = sp.toNat + n := by
    have := hlenRead.low
    have hreturn := ef.slot.low
    have hb : (fr.rsp + 8).toNat = fr.rsp.toNat + 8 := by
      simp only [BitVec.toNat_add, BitVec.reduceToNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hb] at this
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hsp : args[4].get 64 = fr.rsp := by rw [ef.rsp]; rfl
  have hsrc : args[6].get 64 = fr.rsi := by rw [ef.rsi]; rfl
  have ha : args[1].get 64 = fr.rcx := by rw [ef.rcx]; rfl
  have hn : args[8].get 64 = fr.r8 := by rw [ef.r8]; rfl
  have hc : args[9].get 64 = fr.r9 := by rw [ef.r9]; rfl
  have hmaskarg : args[2].get 64 = fr.rdx := by rw [ef.rdx]; rfl
  have hdstarg : args[7].get 64 = fr.rdi := by rw [ef.rdi]; rfl
  have hmultiply : GHASHInterface.MultiplyContract code := GHASHExecution.multiply_call code hcode
  let low := sp - 408
  have lowNat : low.toNat = sp.toNat - 408 := spSub 408 (by decide)
  have sp408 : (sp - 408).toNat = sp.toNat - 408 := lowNat
  let R : List MemoryRegion := [span low 520]
  have subStack {r : MemoryRegion} (hin : r ∈ R) (x : Nat) (hx : r.Contains x) :
      (callStack fr).Contains x := by
    obtain rfl := List.mem_singleton.mp hin
    simp only [MemoryRegion.Contains, callStack, span, spNat, lowNat] at hx ⊢
    omega
  have stackSub (n m : Nat) (hn : n ≤ m) (hm : m ≤ 192) :
      (span (sp + BitVec.ofNat 64 n) (m-n)).Disjoint (span fr.rdx 16) := by
    intro x hx hy
    apply hmaskSep x ?_ hy
    simp only [MemoryRegion.Contains, span, spAdd n (by omega), callStack, spNat] at hx ⊢
    omega
  obtain ⟨entry, continuation, entryRun, entryLabel, entryTarget, entryGuard, entryMem,
    e4, e7, e6, e2, e3, e12, e14, e15, ekeep, etypes⟩ :=
    Execution.entry_runBlock use256 code hcode args fr.original
      (by rw [hsp]; exact hw.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      (by rw [hsrc]; exact hcontext) (by rw [hsp]; exact hlenRead)
  let prepared := Execution.entryMemory use256 args fr.original
  have emem : entry.store = prepared := entryMem
  have entryFrame : RamWriteFrame fr.original prepared [span (fr.rsp - 192) 192] := by
    simpa only [hsp] using Execution.entryMemory_frame use256 args fr.original (by rw [hsp]; omega)
  have savedFrame : RamWriteFrame fr.original (Execution.savedMemory args fr.original)
      [span (fr.rsp - 192) 192] := by
    simpa only [hsp] using Execution.savedMemory_frame args fr.original (by rw [hsp]; omega)
  have rsp192 : (fr.rsp - 192).toNat = fr.rsp.toNat - 192 := by
    exact BitVec.toNat_sub_of_le (by change 192 ≤ fr.rsp.toNat; omega)
  have outerOutside (a : BitVec 64) (n : Nat) (hn : 0 < n)
      (hr : Readable fr.original a n) (hs : (callStack fr).Disjoint (span a n)) :
      Outside [span (fr.rsp - 192) 192] a n := by
    have bounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
      a.toNat n (by omega) hn hs
    refine ⟨by have := hr.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, rsp192]
    omega
  have eKey (off : Nat) (ho : off + 8 ≤ 32) :
      memLoad (Execution.savedMemory args fr.original) (fr.rsi + BitVec.ofNat 64 off) 64 =
        memLoad fr.original (fr.rsi + BitVec.ofNat 64 off) 64 :=
    savedFrame.memLoad_eq (GHASHUpdate.outside_add_offset
      (outerOutside fr.rsi 32 (by decide) hcontext hcontextSep) (by decide) ho)
  have hAreg : (entry.arguments[3]'(by change 3 < 53; decide)).get 64 = fr.r8 := by
    rw [e3, hn]; rfl
  have hCreg : (entry.arguments[15]'(by change 15 < 53; decide)).get 64 =
      memLoad fr.original (fr.rsp + 8) 64 := by
    rw [e15]
    change memLoad (Execution.savedMemory args fr.original) (args[4].get 64 + 8) 64 = _
    rw [hsp]
    apply savedFrame.memLoad_eq
    refine ⟨by have := hlenRead.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, rsp192]
    have ha : (fr.rsp + 8).toNat = fr.rsp.toNat + 8 := by
      have := ef.slot.low
      simp only [BitVec.toNat_add, BitVec.reduceToNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [ha]
    omega
  have preparedState : memLoad prepared (sp + 80) 64 =
        (GHASH.polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)).1 ∧
      memLoad prepared (sp + 88) 64 =
        (GHASH.polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)).2 ∧
      memLoad prepared (sp + 96) 64 = 0 ∧ memLoad prepared (sp + 104) 64 = 0 := by
    have k0 := eKey 0 (by decide)
    have k8 := eKey 8 (by decide)
    have k16 := eKey 16 (by decide)
    have k24 := eKey 24 (by decide)
    simp only [BitVec.add_zero] at k0 k8 k16 k24
    dsimp only [prepared, Execution.entryMemory]
    rw [hsp, hsrc]
    have hlow := hw.readable.low
    have hb := hcontext.low
    have contextBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
      fr.rsi.toNat 32 (by omega) (by decide) hcontextSep
    runtime_context [k0, k8, k16, k24, hk0, hk1, hs0, hs1]
    dsimp only [sp]
    repeat' apply And.intro
    all_goals
      simp only [BitVec.ofNat_eq_ofNat] at *
      runtime_finish [k0, k8, k16, k24, hk0, hk1, hs0, hs1]
      all_goals simp only [BitVec.ofNat_eq_ofNat, k16, k24, hs0, hs1]
  have e4get : (entry.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 := by
    rw [e4, hsp]; change fr.rsp - 192 = sp - 8; dsimp only [sp]; bv_omega
  have e7get : (entry.arguments[7]'(by change 7 < 53; decide)).get 64 = sp + 80 := by
    rw [e7, hsp]; change fr.rsp - 104 = sp + 80; dsimp only [sp]; bv_omega
  have e6get : (entry.arguments[6]'(by change 6 < 53; decide)).get 64 = fr.rcx := by
    rw [e6, ha]; rfl
  have e2get : ((entry.arguments[2]'(by change 2 < 53; decide)).get 64).toNat =
      associatedData.size / 16 := by
    rw [e2, hn]
    simp only [Value.get, BitVec.setWidth_eq, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, hA]
  have esp8 : (sp - 8).toNat = sp.toNat - 8 := spSub 8 (by decide)
  have esp80 : (sp + 80).toNat = sp.toNat + 80 := spAdd 80 (by decide)
  have esp112 : (sp + 112).toNat = sp.toNat + 112 := spAdd 112 (by decide)
  have childStateSep :
      (⟨low.toNat, (sp - 8).toNat + 8 - low.toNat⟩ : MemoryRegion).Disjoint
        (span (sp + 80) 32) := by
    intro x hx hy
    simp only [MemoryRegion.Contains, span, esp8, esp80, lowNat] at hx hy
    omega
  have childInputSep (src : BitVec 64) (len : Nat)
      (hs : (callStack fr).Disjoint (span src len)) (n : Nat) (hn : n ≤ len) :
      (⟨low.toNat, (sp - 8).toNat + 8 - low.toNat⟩ : MemoryRegion).Disjoint
        (span src n) := by
    intro x hx hy
    apply hs x ?_ ?_
    · simp only [MemoryRegion.Contains, callStack, esp8, spNat, lowNat] at hx ⊢; omega
    · simp only [MemoryRegion.Contains, span] at hy ⊢; omega
  have stateInputSep (src : BitVec 64) (len : Nat)
      (hs : (callStack fr).Disjoint (span src len)) (n : Nat) (hn : n ≤ len) :
      (span (sp + 80) 32).Disjoint (span src n) := by
    intro x hx hy
    apply hs x ?_ ?_
    · simp only [MemoryRegion.Contains, callStack, span, esp80, spNat] at hx ⊢; omega
    · simp only [MemoryRegion.Contains, span] at hy ⊢; omega
  let eret : BitVec 64 := if use256 then 0x101c86 else 0x101866
  have epop : memLoad prepared (sp - 8) 64 = eret := by
    have e := (Execution.entryMemory_saved use256 args fr.original).1
    rw [hsp] at e
    simpa only [show sp - 8 = fr.rsp - 192 by dsimp only [sp]; bv_omega] using e
  have e39 : (entry.arguments[39]'(by change 39 < 53; decide)) = args[39] := ekeep 39 (by decide)
  have e50 : (entry.arguments[50]'(by change 50 < 53; decide)) = args[50] := ekeep 50 (by decide)
  have e51 : (entry.arguments[51]'(by change 51 < 53; decide)) = args[51] := ekeep 51 (by decide)
  have edf : (entry.arguments[22]'(by change 22 < 53; decide)) = ⟨1, 0⟩ :=
    (ekeep 22 (by decide)).trans ef.df
  have e39typed : (entry.arguments[39]'(by change 39 < 53; decide)) =
      ⟨32, (entry.arguments[39]'(by change 39 < 53; decide)).get 32⟩ := by
    rw [e39, ef.mxcsr]; rfl
  have e50typed : (entry.arguments[50]'(by change 50 < 53; decide)) =
      ⟨16, (entry.arguments[50]'(by change 50 < 53; decide)).get 16⟩ := by
    rw [e50, ef.ftw]; rfl
  have e51typed : (entry.arguments[51]'(by change 51 < 53; decide)) =
      ⟨16, (entry.arguments[51]'(by change 51 < 53; decide)).get 16⟩ := by
    rw [e51, ef.fcw]; rfl
  obtain ⟨a, aexec, atag, adone, atypes, aframe, apost⟩ :=
    callContract_exec_values LIR.lifted code .l109980 LIR.Fn109980.frameInfo
      (fun fr ↦ [span (fr.rdi + 16) 16]) _ _ (GHASHUpdate.update_call code hcode hmultiply)
      prepared entry.arguments eret low (etypes htypes) e39typed e50typed e51typed edf
      (by rw [e4get, show sp - 8 = fr.rsp - 192 by dsimp only [sp]; bv_omega]
          exact (hw.readable.of_frame entryFrame).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
      (by rw [e4get]; exact epop) (by dsimp only [eret]; split <;> decide)
      (fun _ ↦ by
        change Writable code prepared ((entry.arguments[4]'(by change 4 < 53; decide)).get 64 - 400) 400
        rw [e4get, show sp - 8 - 400 = fr.rsp - 592 by dsimp only [sp]; bv_omega]
        exact (hw.of_frame entryFrame).sub (Nat.le_refl _) (by omega))
      (by change low.toNat + 400 ≤ ((entry.arguments[4]'(by change 4 < 53; decide)).get 64).toNat
          rw [e4get, esp8, lowNat, spNat]; omega)
      (by rw [e4get, esp8, spNat]; have := ef.align; omega) (by trivial)
      (by
        simp only [activationOfValues, callStack, e4get, e7get, e6get, e2get]
        refine ⟨?_, (haad.of_frame entryFrame).sub (Nat.le_refl _) (by omega), childStateSep,
          childInputSep _ _ haadSep _ (by omega), stateInputSep _ _ haadSep _ (by omega)⟩
        rw [show sp + 80 = fr.rsp - 104 by dsimp only [sp]; bv_omega]
        exact (hw.of_frame entryFrame).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide))
  have apres := Execution.preserved_of_doneAtoms code prepared entry.arguments eret low a
    (etypes htypes) e39typed e50typed e51typed edf adone
  have areach : (LIR.program.sem (dialect code)).Reaches
      ⟨⟨if use256 then .l101c20 else .l101800, args, fr.original⟩, []⟩
      ⟨⟨if use256 then .l101c86 else .l101866, a.values, a.store⟩, []⟩ := by
    have eexec : LIR.program.Exec (dialect code) ⟨entry, []⟩ a := by
      have ee : entry = ⟨.l109980, entry.arguments, prepared⟩ := by
        cases entry with
        | mk lab vals st =>
          dsimp only at entryLabel emem
          subst lab st
          rfl
      rw [ee]
      exact aexec
    have accepted : continuation.Accepts (dialect code) a.tag = true := by
      rw [atag]
      simp only [StackFrame.Accepts, entryGuard]
      cases use256 <;> rfl
    have e := Execution.call_reaches code _ _ _ _ entryRun eexec accepted
    rw [entryTarget] at e
    exact e
  have a4 : a.values[4] = ⟨64, sp⟩ := by
    simpa only [e4get, BitVec.sub_add_cancel] using apres.1
  have aFrame : RamWriteFrame prepared a.store R := by
    apply (RamWriteFrame.refl prepared R).trans aframe
    intro r hin
    change r ∈ [⟨low.toNat, ((entry.arguments[4]'(by change 4 < 53; decide)).get 64).toNat - low.toNat⟩,
      span ((entry.arguments[7]'(by change 7 < 53; decide)).get 64 + 16) 16] at hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨_, List.mem_singleton_self _, Nat.le_refl _, ?_⟩
      simp only [e4get, span, esp8, lowNat]
      omega
    · refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩
      all_goals
        simp only [e7get, span]
        have haddr : (sp + 80 + 16).toNat = sp.toNat + 96 := by
          rw [show sp + 80 + 16 = sp + BitVec.ofNat 64 96 by bv_omega]
          exact spAdd 96 (by decide)
        rw [haddr]
        rw [lowNat, spNat]
        omega
  have aadPrepared : (span fr.rcx associatedData.size).HasBytes prepared associatedData := by
    apply hasBytes_of_frame entryFrame haadBytes (by have := haad.low; exact Nat.le_trans this (by decide))
    intro r hin x hx hy
    obtain rfl := List.mem_singleton.mp hin
    apply haadSep x ?_ hx
    simp only [MemoryRegion.Contains, span, callStack, rsp192] at hy ⊢
    omega
  have astate : stateBits (memLoad a.store (sp + 96) 64, memLoad a.store (sp + 104) 64) =
      (Standards.NIST.GCM.blocks (AesGcm.Spec.GCM.bitsOfByteArray associatedData)).toList.foldl
        (fun acc b ↦ Standards.NIST.GCM.mul (Standards.NIST.GCM.xor acc b)
          (Standards.NIST.GCM.bitsOfBytes h)) (Standards.NIST.GCM.zeros 128) := by
    simp only [activationOfValues, e7get, e6get, e2get] at apost
    simp only [show sp + 80 + 8 = sp + 88 by bv_omega,
      show sp + 80 + 16 = sp + 96 by bv_omega,
      show sp + 80 + 24 = sp + 104 by bv_omega,
      preparedState.1, preparedState.2.1, preparedState.2.2.1, preparedState.2.2.2] at apost
    rw [apost.1, apost.2]
    simpa only [stateBits_zero] using updateBlocks_full_bits prepared fr.rcx associatedData h (0, 0) aadPrepared
  have minus96 : (sp-96).toNat=sp.toNat-96 := spSub 96 (by decide)
  have plus96 : (sp+96).toNat=sp.toNat+96 := spAdd 96 (by decide)
  have room : 408 ≤ sp.toNat := by rw [spNat]; omega
  have align : sp.toNat % 16 = 0 := by have := ef.align; rw [spNat]; omega
  have slot0 : Readable fr.original 0x201228 8 ∧ memLoad fr.original 0x201228 64 = 0x103eb0 :=
    ef.callSlots (0x201228, 0x103eb0) (by cases use256 <;> decide)
  have slot1 : Readable fr.original 0x201208 8 ∧ memLoad fr.original 0x201208 64 = 0x103f00 :=
    ef.callSlots (0x201208, 0x103f00) (by cases use256 <;> decide)
  have slots : 0x201230 + 592 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208 := by
    have hs := ef.callSlotsApart (by cases use256 <;> decide)
    cases use256 <;> exact hs
  have slotBounds : sp.toNat + 112 ≤ 0x201208 ∨ 0x201230 ≤ (sp-408).toNat := by
    rw [spNat, sp408]; omega
  have fullFrame {mem : Ram} (hf : RamWriteFrame prepared mem R) :
      RamWriteFrame fr.original mem [span (fr.rsp - 592) 592] := by
    have e : RamWriteFrame fr.original prepared [span (fr.rsp - 592) 592] := by
      apply (RamWriteFrame.refl _ _).trans entryFrame
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;>
        simp only [span, rsp192, show (fr.rsp-592).toNat = fr.rsp.toNat-592 from
          BitVec.toNat_sub_of_le (by change 592 ≤ fr.rsp.toNat; omega)] <;> omega
    apply e.trans hf
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;>
      simp only [span, lowNat, spNat, show (fr.rsp-592).toNat = fr.rsp.toNat-592 from
        BitVec.toNat_sub_of_le (by change 592 ≤ fr.rsp.toNat; omega)] <;> omega
  have wideWritable {mem : Ram} (hf : RamWriteFrame prepared mem R) :
      Writable code mem (sp-408) 520 := by
    rw [show sp-408=fr.rsp-592 by dsimp only [sp]; bv_omega]
    exact (hw.of_frame (fullFrame hf)).sub (Nat.le_refl _) (by omega)
  have inputSep (src : BitVec 64) (n : Nat)
      (hs : (callStack fr).Disjoint (span src n)) :
      (span (sp-408) 520).Disjoint (span src n) := by
    intro x hx hy
    exact hs x (subStack (List.mem_singleton_self _) x hx) hy
  have fullInputOutside (src : BitVec 64) (n : Nat)
      (hs : (callStack fr).Disjoint (span src n)) :
      ∀ r ∈ [span (fr.rsp-592) 592], (span src n).Disjoint r := by
    intro r hr x hx hy
    obtain rfl := List.mem_singleton.mp hr
    apply hs x ?_ hx
    have h592 : (fr.rsp-592).toNat=fr.rsp.toNat-592 :=
      BitVec.toNat_sub_of_le (by change 592 ≤ fr.rsp.toNat; omega)
    simp only [MemoryRegion.Contains, span, callStack, h592] at hy ⊢
    omega
  have inputBytes {mem : Ram} (hf : RamWriteFrame prepared mem R)
      (src : BitVec 64) (bytes : ByteArray)
      (hb : (span src bytes.size).HasBytes fr.original bytes)
      (hr : 0 < bytes.size → Readable fr.original src bytes.size)
      (hs : (callStack fr).Disjoint (span src bytes.size)) :
      (span src bytes.size).HasBytes mem bytes := by
    apply hasBytes_of_frame (fullFrame hf) hb
    · by_cases hp : 0 < bytes.size
      · have := (hr hp).low; exact Nat.le_trans this (by decide)
      · have := src.isLt; simp only [span]; omega
    · exact fullInputOutside src bytes.size hs
  have slotsAt {mem : Ram} (hf : RamWriteFrame prepared mem R) :
      Readable mem 0x201228 8 ∧ memLoad mem 0x201228 64 = 0x103eb0 ∧
      Readable mem 0x201208 8 ∧ memLoad mem 0x201208 64 = 0x103f00 := by
    have f := fullFrame hf
    refine ⟨slot0.1.of_frame f, ?_, slot1.1.of_frame f, ?_⟩
    all_goals
      rw [f.memLoad_eq]
      · first | exact slot0.2 | exact slot1.2
      · refine ⟨by decide, ?_⟩
        intro r hr; obtain rfl := List.mem_singleton.mp hr
        simp only [span, BitVec.reduceToNat,
          show (fr.rsp-592).toNat=fr.rsp.toNat-592 from
            BitVec.toNat_sub_of_le (by change 592 ≤ fr.rsp.toNat; omega)]
        omega
  have aKeys (off : Nat) (hlo : 80 ≤ off) (hhi : off + 8 ≤ 96) :
      memLoad a.store (sp + BitVec.ofNat 64 off) 64 =
        memLoad prepared (sp + BitVec.ofNat 64 off) 64 := by
    apply aframe.memLoad_eq
    refine ⟨by rw [spAdd off (by omega)]; have := ef.slot.low; rw [spNat]; omega, ?_⟩
    intro r hr
    change r ∈ [⟨low.toNat, ((entry.arguments[4]'(by change 4 < 53; decide)).get 64).toNat-low.toNat⟩,
      span ((entry.arguments[7]'(by change 7 < 53; decide)).get 64+16) 16] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals
      simp only [e4get, e7get, span, esp8, lowNat, spAdd off (by omega),
        show sp+80+16=sp+96 by bv_omega, plus96]
      omega
  have a0 : memLoad a.store (sp+80) 64 =
      (GHASH.polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)).1 :=
    (aKeys 80 (by decide) (by decide)).trans preparedState.1
  have a1 : memLoad a.store (sp+88) 64 =
      (GHASH.polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)).2 :=
    (aKeys 88 (by decide) (by decide)).trans preparedState.2.1
  have a3 : a.values[3].get 64 = fr.r8 :=
    (congrArg (Value.get 64) (apres.2 3 (by decide))).trans hAreg
  have a12 : a.values[12].get 64 = fr.rcx := by
    have e : (entry.arguments[12]'(by change 12 < 53; decide)).get 64 = fr.rcx := by rw [e12, ha]; rfl
    exact (congrArg (Value.get 64) (apres.2 12 (by decide))).trans e
  have a14 : a.values[14].get 64 = fr.r9 := by
    have e : (entry.arguments[14]'(by change 14 < 53; decide)).get 64 = fr.r9 := by rw [e14, hc]; rfl
    exact (congrArg (Value.get 64) (apres.2 14 (by decide))).trans e
  have a15 : a.values[15].get 64 = memLoad fr.original (fr.rsp+8) 64 :=
    (congrArg (Value.get 64) (apres.2 15 (by decide))).trans hCreg
  have ap (r : Fin 53) (hr : r.val ∈ [5,22,39,50,51]) : a.values[r] = args[r] := by
    exact (apres.2 r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)).trans
      (ekeep r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega))
  have a39 : a.values[39] = args[39] := ap 39 (by decide)
  have a50 : a.values[50] = args[50] := ap 50 (by decide)
  have a51 : a.values[51] = args[51] := ap 51 (by decide)
  have aSlots := slotsAt aFrame
  obtain ⟨b, breach, b4, bk, b14, bt, bframe, bstate, b0, b1⟩ :=
    completePaddedHash_exec use256 false code hcode hmultiply h sp room align a.values a.store
      fr.rcx associatedData (Standards.NIST.GCM.zeros 128) (by rw [a4]; rfl)
      (by simpa only [Bool.false_eq_true, ↓reduceIte, a3] using hA) a12 atypes
      ((ap 22 (by decide)).trans ef.df)
      (by rw [a39, ef.mxcsr]; rfl) (by rw [a50, ef.ftw]; rfl) (by rw [a51, ef.fcw]; rfl)
      (wideWritable aFrame) (fun _ ↦ haad.of_frame (fullFrame aFrame))
      (inputBytes aFrame fr.rcx associatedData haadBytes (fun _ ↦ haad) haadSep)
      (inputSep _ _ haadSep) aSlots.1 aSlots.2.2.1 aSlots.2.1 aSlots.2.2.2 slotBounds a0 a1 astate
  have bFrame : RamWriteFrame prepared b.store R :=
    aFrame.trans bframe (fun r hr ↦ ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
  have b39 : b.values[39] = args[39] := (bk 39 (by decide)).trans a39
  have b50 : b.values[50] = args[50] := (bk 50 (by decide)).trans a50
  have b51 : b.values[51] = args[51] := (bk 51 (by decide)).trans a51
  have b3 : b.values[3].get 64 = fr.r8 := (congrArg (Value.get 64) (bk 3 (by decide))).trans a3
  have b15 : b.values[15].get 64 = memLoad fr.original (fr.rsp+8) 64 :=
    (congrArg (Value.get 64) (bk 15 (by decide))).trans a15
  have bsrc : b.values[14].get 64 = fr.r9 := (congrArg (Value.get 64) (b14 rfl)).trans a14
  have bdf : b.values[22] = ⟨1,0⟩ := (bk 22 (by decide)).trans ((ap 22 (by decide)).trans ef.df)
  let clen := memLoad fr.original (fr.rsp+8) 64
  obtain ⟨c, creach, c4, ck, ct, cframe, cpost⟩ :
      ∃ c : Output Value Ram Reg.count,
        (LIR.program.sem (dialect code)).Reaches
          ⟨⟨if use256 then .l101d5e else .l10193e, b.values, b.store⟩, []⟩
          ⟨⟨if use256 then .l101d72 else .l101952, c.values, c.store⟩, []⟩ ∧
        c.values[4] = ⟨64,sp⟩ ∧
        (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → c.values[r] = b.values[r]) ∧
        GPRsTyped c.values ∧
        RamWriteFrame b.store c.store [⟨low.toNat, sp.toNat-low.toNat⟩, span (sp+96) 16] ∧
        (let result  := GHASHInterface.updateBlocks b.store fr.r9 (ciphertext.size/16)
          (memLoad b.store (sp+80) 64) (memLoad b.store (sp+88) 64)
          (memLoad b.store (sp+96) 64, memLoad b.store (sp+104) 64)
         memLoad c.store (sp+96) 64 = result.1 ∧ memLoad c.store (sp+104) 64 = result.2) := by
    by_cases hp : 0 < ciphertext.size
    · obtain ⟨c, reach, cs, keep, typed, frame, post⟩ :=
        ciphertext_update_exec use256 code hcode hmultiply b.values b.store sp fr.r9 clen low
          (by rw [b4]; rfl) bsrc b15 bt
          (by rw [b39, ef.mxcsr]; rfl) (by rw [b50, ef.ftw]; rfl) (by rw [b51, ef.fcw]; rfl)
          bdf (wideWritable bFrame) (by rw [lowNat]; omega) align
          (by rw [show clen.toNat = ciphertext.size from hC]; exact (hcipher hp).of_frame (fullFrame bFrame))
          (by
            rw [show clen.toNat = ciphertext.size from hC]
            have sep := inputSep _ _ hcipherSep
            simpa only [span, lowNat, sp408, show sp.toNat+112-(sp.toNat-408)=520 by omega] using sep)
      refine ⟨c, reach, cs, keep, typed, frame, ?_⟩
      simpa only [show clen.toNat = ciphertext.size from hC] using post
    · have hz : ciphertext.size = 0 := by omega
      have vz : b.values[15].get 64 = 0 := by
        rw [b15]; apply BitVec.eq_of_toNat_eq; simpa only [hz, BitVec.reduceToNat] using hC
      obtain ⟨c, reach, cs, keep, typed, frame⟩ := ciphertext_zero_exec use256 code hcode b.values b.store sp
        (by rw [b4]; rfl) vz bt
        ((wideWritable bFrame).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)) (by omega)
      refine ⟨c, reach, cs, keep, typed, ?_, ?_⟩
      · apply (RamWriteFrame.refl _ _).trans frame
        intro r hr; obtain rfl := List.mem_singleton.mp hr
        refine ⟨⟨low.toNat, sp.toNat-low.toNat⟩, by simp only [List.mem_cons, true_or], ?_, ?_⟩ <;>
          simp only [span, lowNat, minus96] <;> omega
      · simp only [hz, Nat.zero_div, GHASHUpdate.updateBlocks_zero]
        constructor
        all_goals
          apply frame.memLoad_eq
          refine ⟨?_, ?_⟩
          · first
              | (rw [show (sp+96).toNat=sp.toNat+96 from plus96]; have := ef.slot.low; rw [spNat]; omega)
              | (rw [show (sp+104).toNat=sp.toNat+104 from spAdd 104 (by decide)]; have := ef.slot.low; rw [spNat]; omega)
          · intro r hr; obtain rfl := List.mem_singleton.mp hr
            simp only [span, minus96,
              show (sp+96).toNat=sp.toNat+96 from plus96,
              show (sp+104).toNat=sp.toNat+104 from spAdd 104 (by decide)]
            omega
  have cFrame : RamWriteFrame prepared c.store R := by
    apply bFrame.trans cframe
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals
      refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;>
        simp only [span, lowNat, plus96] <;> omega
  have ckeys (off : Nat) (hlo : 80 ≤ off) (hhi : off+8 ≤ 96) :
      memLoad c.store (sp+BitVec.ofNat 64 off) 64 = memLoad b.store (sp+BitVec.ofNat 64 off) 64 := by
    apply cframe.memLoad_eq
    refine ⟨by rw [spAdd off (by omega)]; have := ef.slot.low; rw [spNat]; omega, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals simp only [span, lowNat, spAdd off (by omega), plus96]; omega
  have c0 : memLoad c.store (sp+80) 64 = (GHASH.polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)).1 := (ckeys 80 (by decide) (by decide)).trans (b0.trans a0)
  have c1 : memLoad c.store (sp+88) 64 = (GHASH.polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)).2 := (ckeys 88 (by decide) (by decide)).trans (b1.trans a1)
  have cipherB := inputBytes bFrame fr.r9 ciphertext hcipherBytes hcipher hcipherSep
  have cstate : stateBits (memLoad c.store (sp+96) 64, memLoad c.store (sp+104) 64) =
      (Standards.NIST.GCM.blocks (AesGcm.Spec.GCM.bitsOfByteArray ciphertext)).toList.foldl
        (fun acc block ↦ Standards.NIST.GCM.mul (Standards.NIST.GCM.xor acc block)
          (Standards.NIST.GCM.bitsOfBytes h)) (hashPadded h associatedData (Standards.NIST.GCM.zeros 128)) := by
    rw [cpost.1, cpost.2, b0, b1, a0, a1]
    exact (updateBlocks_full_bits b.store fr.r9 ciphertext h
      (memLoad b.store (sp+96) 64, memLoad b.store (sp+104) 64) cipherB).trans
      (congrArg (fun x ↦ (Standards.NIST.GCM.blocks (AesGcm.Spec.GCM.bitsOfByteArray ciphertext)).toList.foldl
        (fun acc block ↦ Standards.NIST.GCM.mul (Standards.NIST.GCM.xor acc block)
          (Standards.NIST.GCM.bitsOfBytes h)) x) bstate)
  have c39 : c.values[39] = args[39] := (ck 39 (by decide)).trans b39
  have c50 : c.values[50] = args[50] := (ck 50 (by decide)).trans b50
  have c51 : c.values[51] = args[51] := (ck 51 (by decide)).trans b51
  have c15 : c.values[15].get 64 = clen := (congrArg (Value.get 64) (ck 15 (by decide))).trans b15
  have csrc : c.values[14].get 64 = fr.r9 := (congrArg (Value.get 64) (ck 14 (by decide))).trans bsrc
  have cslots := slotsAt cFrame
  obtain ⟨d, dreach, d4, dk, _, dt, dframe, dstate, d0, d1⟩ :=
    completePaddedHash_exec use256 true code hcode hmultiply h sp room align c.values c.store fr.r9 ciphertext
      (hashPadded h associatedData (Standards.NIST.GCM.zeros 128)) (by rw [c4]; rfl)
      (by simpa only [↓reduceIte, c15] using hC) csrc ct ((ck 22 (by decide)).trans bdf)
      (by rw [c39, ef.mxcsr]; rfl) (by rw [c50, ef.ftw]; rfl) (by rw [c51, ef.fcw]; rfl)
      (wideWritable cFrame) (fun hp ↦ (hcipher hp).of_frame (fullFrame cFrame))
      (inputBytes cFrame fr.r9 ciphertext hcipherBytes hcipher hcipherSep)
      (inputSep _ _ hcipherSep) cslots.1 cslots.2.2.1 cslots.2.1 cslots.2.2.2 slotBounds c0 c1 cstate
  have dFrame : RamWriteFrame prepared d.store R :=
    cFrame.trans dframe (fun r hr ↦ ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
  have d39 : d.values[39]=args[39] := (dk 39 (by decide)).trans c39
  have d50 : d.values[50]=args[50] := (dk 50 (by decide)).trans c50
  have d51 : d.values[51]=args[51] := (dk 51 (by decide)).trans c51
  have ddf : d.values[22]=⟨1,0⟩ := (dk 22 (by decide)).trans ((ck 22 (by decide)).trans bdf)
  have d15 : d.values[15].get 64=clen := (congrArg (Value.get 64) (dk 15 (by decide))).trans c15
  have d3 : d.values[3].get 64=fr.r8 :=
    (congrArg (Value.get 64) (dk 3 (by decide))).trans ((congrArg (Value.get 64) (ck 3 (by decide))).trans b3)
  obtain ⟨e, ereach, e4', ek, et, eframe, epost⟩ := length_exec use256 code hcode hmultiply d.values d.store sp
    (by rw [d4]; rfl) dt (by rw [d39,ef.mxcsr]; rfl) (by rw [d50,ef.ftw]; rfl)
    (by rw [d51,ef.fcw]; rfl) ddf (wideWritable dFrame) room align
    (by rw [d15]; change clen.toNat < 2^36; rw [show clen.toNat=ciphertext.size from hC]
        have := hCbound; change ciphertext.size ≤ 2^36-32 at this; omega)
  have eFrame : RamWriteFrame prepared e.store R :=
    dFrame.trans eframe (fun r hr ↦ ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩)
  have shift (x : BitVec 64) (n : Nat) (hx : x.toNat=n) : x <<< 3=BitVec.ofNat 64 (8*n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hx, BitVec.toNat_ofNat, Nat.reducePow, Nat.mul_comm]
  have tagState : authenticationTagFromMask h mask associatedData ciphertext =
      Standards.NIST.GCM.bytesOfBits (Standards.NIST.GCM.xor
        (stateBits (memLoad e.store (sp+96) 64,memLoad e.store (sp+104) 64))
        (Standards.NIST.GCM.bitsOfBytes mask)) := by
    have ht := authenticationTagFromMask_eq_state h mask associatedData ciphertext
      (memLoad d.store (sp+96) 64,memLoad d.store (sp+104) 64) dstate
    dsimp only at ht epost
    rw [epost.1,epost.2,d0,d1,c0,c1,d15,d3,shift clen ciphertext.size hC,shift fr.r8 associatedData.size hA]
    exact ht
  obtain ⟨f, freach, f4, fk, ft, fframe, fword0, fword1⟩ :=
    finalize_exec use256 code hcode e.values e.store sp (by rw [e4']; rfl) et (wideWritable eFrame) room
  have fFrame : RamWriteFrame prepared f.store R :=
    eFrame.trans fframe (fun r hr ↦ ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩)
  have fpk (r : Fin 53) (hr : r.val ∈ [22,39,50,51]) : f.values[r]=args[r] := by
    have h0 : r.val ∈ [3,5,12,13,14,15,22,39,50,51] := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; omega
    have h1 : r.val ∈ [5,22,39,50,51] := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; omega
    have h2 : r.val ∈ [3,5,15,22,39,50,51] := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; omega
    exact (fk r h0).trans ((ek r h1).trans ((dk r h2).trans ((ck r h0).trans ((bk r h2).trans (ap r h1)))))
  obtain ⟨o, exec, tag, doneAtoms, types, frame, post⟩ :=
    finish_tag_exec use256 code hcode fr args ef sp rfl hroom hw hdst hmask mask
      (authenticationTagFromMask h mask associatedData ciphertext) hmaskBytes hdstSep hmaskSep
      f f4 ft fFrame fpk (memLoad e.store (sp+96) 64,memLoad e.store (sp+104) 64)
      fword0 fword1 tagState
  have reach := ((((areach.trans breach).trans creach).trans dreach).trans ereach).trans freach
  exact ⟨o,Program.Exec.of_sem (reach.exec exec.sem),tag,doneAtoms,types,frame,post⟩

end AesGcm.Proofs.Machine.Tag
