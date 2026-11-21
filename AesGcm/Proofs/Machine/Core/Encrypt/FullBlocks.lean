import AesGcm.Proofs.Machine.Core.Encrypt.Calls
import AesGcm.Proofs.Machine.CTR.Main
import AesGcm.Proofs.Machine.CTR.InitialCounter
import AesGcm.Proofs.Machine.Runtime.Root.Memory
import AesGcm.Proofs.Machine.Runtime.StackGeometry
import AesGcm.Proofs.Machine.Runtime.Atoms
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.LIR.Fn102520.Frame
import AesGcm.Proofs.Machine.LIR.Fn102980.Frame

namespace AesGcm.Proofs.Machine.Core.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

private theorem cryptFullMemory_loads (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) :
    memLoad (cryptFullMemory use256 args mem) (args[4].get 64 - 8) 64 =
      (if use256 then 0x102aa2 else 0x102642) ∧
    memLoad (cryptFullMemory use256 args mem) (args[4].get 64 + 16) 64 = args[1].get 64 ∧
    memLoad (cryptFullMemory use256 args mem) (args[4].get 64 + 24) 64 = args[15].get 64 ∧
    memLoad (cryptFullMemory use256 args mem) (args[4].get 64 + 32) 64 = args[13].get 64 ∧
    memLoad (cryptFullMemory use256 args mem) (args[4].get 64 + 40) 64 = args[5].get 64 >>> 4 := by
  repeat' apply And.intro
  all_goals
    simp only [cryptFullMemory]
    repeat first
      | rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
      | (rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          apply RangeApart.of_diff
          bv_omega)])

private theorem fullBlocks_frame (use256 : Bool) (code : CodeMap) (fr : Activation)
    (args values : Values Value Reg.count) (mem output : Ram) (regions : List MemoryRegion)
    (hworking : Atom.All code args mem
      (if use256 then LIR.Fn102980.frameAt .l102aa2 fr else LIR.Fn102520.frameAt .l102642 fr))
    (hf : RamWriteFrame mem output regions)
    (hkeep : ∀ r : Fin 53, r.val ∈ [4,22,39,50,51] → values[r] = args[r])
    (hsaved : ∀ n : Nat, n ≤ 112 → Outside regions (fr.rsp - BitVec.ofNat 64 n) 8)
    (hslots : ∀ address ∈ ([0x201208,0x201210,0x201228,0x201230] : List (BitVec 64)),
      Outside regions address 8) :
    Atom.All code values output
      (if use256 then LIR.Fn102980.frameAt .l102aa2 fr else LIR.Fn102520.frameAt .l102642 fr) := by
  apply atomsAll_of_frame hf ?_ hworking
  intro atom ha
  cases use256
  all_goals simp only [LIR.Fn102980.frameAt, LIR.Fn102520.frameAt,
    LIR.Fn102980.frameAtG2, LIR.Fn102520.frameAtG2, Bool.false_eq_true, ↓reduceIte,
    List.mem_cons, List.not_mem_nil, or_false] at ha
  all_goals rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hkeep _ (by decide)
    | exact trivial
    | exact hsaved _ (by decide)
    | exact (show Outside regions fr.rsp 8 from by
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using hsaved 0 (by decide))
    | exact hslots _ (by decide)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem fullBlocks (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (input : ByteArray)
    (length source destination : BitVec 64) (fr : Activation) (loc : LIR.lifted.Location)
    (hlabel : loc.label = (if use256 then .l102a59 else .l1025f9))
    (hworking : Atom.All code loc.arguments loc.store
      (if use256 then LIR.Fn102980.frameAt .l102a59 fr else LIR.Fn102520.frameAt .l1025f9 fr))
    (hTypes : GPRsTyped loc.arguments)
    (hlen : (loc.arguments[5]'(by change 5 < 53; decide)).get 64 = length)
    (hsource : (loc.arguments[15]'(by change 15 < 53; decide)).get 64 = source)
    (hdest : (loc.arguments[13]'(by change 13 < 53; decide)).get 64 = destination)
    (hcounter : (loc.arguments[1]'(by change 1 < 53; decide)).get 64 = fr.rsp - 144)
    (hlengthBound : length.toNat ≤ 2^32) (hpositive : 16 < length.toNat)
    (hsize : input.size = 16 * (length.toNat / 16))
    (hschedule : AES16.ScheduleIn (AES16.variant use256) key (fr.rsi + 32) loc.store)
    (hrSchedule : Readable loc.store (fr.rsi + 32) (16 * ((AES16.variant use256).Nr + 1)))
    (hkeyPtr : memLoad loc.store (fr.rsp - 152) 64 = fr.rsi + 32)
    (hread : Readable loc.store source input.size)
    (hbytes : (span source input.size).HasBytes loc.store input)
    (hwrite : Writable code loc.store destination input.size)
    (halias : source = destination ∨ (span source input.size).Disjoint (span destination input.size))
    (hstackSep : ∀ r ∈ [span (fr.rsi + 32) (16 * ((AES16.variant use256).Nr + 1)),
      span source input.size, span destination input.size], (callStack fr).Disjoint r)
    (hdataSep : (span destination input.size).Disjoint
      (span (fr.rsi + 32) (16 * ((AES16.variant use256).Nr + 1))))
    (hslotSep : ∀ slot ∈ ([0x201208, 0x201210, 0x201228, 0x201230] : List (BitVec 64)),
      (span destination input.size).Disjoint (span slot 8)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l102aa2 else .l102642) ∧
      Atom.All code next.arguments next.store
        (if use256 then LIR.Fn102980.frameAt .l102aa2 fr else LIR.Fn102520.frameAt .l102642 fr) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame loc.store next.store
        [span (fr.rsp - BitVec.ofNat 64 (if use256 then 0xb50 else 0x940))
          ((if use256 then 0xb50 else 0x940) - 124), span destination input.size] ∧
      (next.arguments[5]'(by change 5 < 53; decide)).get 64 = length ∧
      (next.arguments[13]'(by change 13 < 53; decide)).get 64 = destination ∧
      (next.arguments[3]'(by change 3 < 53; decide)).get 64 = source + BitVec.ofNat 64 input.size ∧
      (next.arguments[12]'(by change 12 < 53; decide)).get 64 = destination + BitVec.ofNat 64 input.size ∧
      (next.arguments[14]'(by change 14 < 53; decide)).get 64 = BitVec.ofNat 64 (length.toNat % 16) ∧
      memLoad next.store (fr.rsp - 128) 32 =
        memLoad loc.store (fr.rsp - 128) 32 + BitVec.ofNat 32 (length.toNat / 16) ∧
      Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock next.store (fr.rsp - 144)) =
        Nat.repeat (Standards.NIST.GCM.inc 32) (length.toNat / 16)
          (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock loc.store (fr.rsp - 144))) ∧
      memLoad next.store (fr.rsp - 152) 64 = fr.rsi + 32 ∧
      (span destination input.size).HasBytes next.store
        (AesGcm.Spec.GCM.byteArrayOfBits
          (Standards.NIST.GCM.GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
            (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock loc.store (fr.rsp - 144)))
            (AesGcm.Spec.GCM.bitsOfByteArray input))) := by
  rcases loc with ⟨label, args, mem⟩
  change Values Value Reg.count at args
  dsimp only at hlabel hworking hTypes hlen hsource hdest hcounter hschedule hrSchedule hkeyPtr hread hbytes hwrite ⊢
  subst label
  let window : Nat := if use256 then 0xb50 else 0x940
  let ctrWindow : Nat := if use256 then 0xa80 else 0x870
  let slotHigh : Nat := if use256 then 0x201d88 else 0x201b78
  have hwindow : window = 208 + ctrWindow := by cases use256 <;> decide
  have facts : args[4] = ⟨64, fr.rsp - 200⟩ ∧ args[22] = ⟨1, 0⟩ ∧
      args[14] = ⟨64, fr.r9⟩ ∧ args[39] = ⟨32, fr.mxcsr⟩ ∧
      args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
      memLoad mem (fr.rsp - 112) 64 = fr.rdi ∧ memLoad mem (fr.rsp - 104) 64 = fr.rsi ∧
      memLoad mem (fr.rsp - 96) 64 = fr.rcx ∧ memLoad mem (fr.rsp - 88) 64 = fr.r8 ∧
      memLoad mem (fr.rsp - 48) 64 = fr.rbx ∧ memLoad mem (fr.rsp - 40) 64 = fr.r12 ∧
      memLoad mem (fr.rsp - 32) 64 = fr.r13 ∧ memLoad mem (fr.rsp - 24) 64 = fr.r14 ∧
      memLoad mem (fr.rsp - 16) 64 = fr.r15 ∧ memLoad mem (fr.rsp - 8) 64 = fr.rbp ∧
      Readable mem fr.rsp 8 ∧ memLoad mem fr.rsp 64 = fr.ret ∧ fr.ret.toNat < 2^32 ∧
      Writable code mem (fr.rsp - BitVec.ofNat 64 window) window ∧
      fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
      Readable mem 0x201208 8 ∧ memLoad mem 0x201208 64 = 0x103f00 ∧
      Readable mem 0x201210 8 ∧ memLoad mem 0x201210 64 = 0x103880 ∧
      Readable mem 0x201228 8 ∧ memLoad mem 0x201228 64 = 0x103eb0 ∧
      Readable mem 0x201230 8 ∧ memLoad mem 0x201230 64 = 0x101230 ∧
      (slotHigh ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True := by
    cases use256 <;> exact hworking
  obtain ⟨h4, h22, _, h39, h50, h51, _, _, _, _, _, _, _, _, _, _, hretRead,
    _, _, hstack, hroom, halign, s0r, s0v, s1r, s1v, _, _, s3r, s3v, slotsApart, _⟩ := facts
  have h4get : args[4].get 64 = fr.rsp - 200 := by rw [h4]; rfl
  have hretBound := hretRead.low
  have hsub (n : Nat) (hn : n ≤ window) :
      (fr.rsp - BitVec.ofNat 64 n).toNat = fr.rsp.toNat - n := by
    have hle : BitVec.ofNat 64 n ≤ fr.rsp := by change n % 2^64 ≤ fr.rsp.toNat; omega
    rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := fr.rsp.isLt; omega)]
  let lower := fr.rsp - BitVec.ofNat 64 window
  have hlower : lower.toNat = fr.rsp.toNat - window := hsub window (Nat.le_refl _)
  have hs208 : (fr.rsp - 208).toNat = fr.rsp.toNat - 208 := hsub 208 (by omega)
  have hs200 : (fr.rsp - 200).toNat = fr.rsp.toNat - 200 := hsub 200 (by omega)
  have hs184 : (fr.rsp - 184).toNat = fr.rsp.toNat - 184 := hsub 184 (by omega)
  have hs152 : (fr.rsp - 152).toNat = fr.rsp.toNat - 152 := hsub 152 (by omega)
  have hs144 : (fr.rsp - 144).toNat = fr.rsp.toNat - 144 := hsub 144 (by omega)
  have hs128 : (fr.rsp - 128).toNat = fr.rsp.toNat - 128 := hsub 128 (by omega)
  obtain ⟨callee, continuation, hcall, hcalleeLabel, htarget, hguard, hcalleeMem,
    hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc22, hc39, hc50, hc51, hcalleeTypes⟩ :=
    cryptFull_runBlock use256 code hcode args mem (by
      rw [h4get, show fr.rsp - 200 - 8 = fr.rsp - 208 by bv_omega]
      apply hstack.of_offsets (addr_sub _ _) (addr_sub _ _)
      cases use256 <;> decide +kernel)
  have hmem : RamWriteFrame mem callee.store [span (fr.rsp - 208) 56] := by
    rw [hcalleeMem]
    have hh := cryptFullMemory_frame use256 args mem
      (by rw [h4get, hs200]; omega) (by rw [h4get, hs200]; omega)
    simpa only [h4get, show fr.rsp - 200 - 8 = fr.rsp - 208 by bv_omega] using hh
  have hpos : 0 < input.size := by omega
  have externalOutside {base : BitVec 64} {count : Nat} (hp : 0 < count)
      (hr : Readable mem base count) (hsep : (callStack fr).Disjoint (span base count)) :
      Outside [span (fr.rsp - 208) 56] base count := by
    have hb := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
      base.toNat count (by omega) hp hsep
    refine ⟨by have := hr.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hs208]
    omega
  have hschedOutside := externalOutside (by cases use256 <;> decide) hrSchedule
    (hstackSep _ (by simp))
  have hsourceOutside := externalOutside hpos hread (hstackSep _ (by simp))
  have hsched := AES16.scheduleIn_of_frame hschedule hmem hschedOutside
  have hb := hasBytes_of_frame hmem hbytes hsourceOutside.1
    (fun r hr ↦ outside_disjoint_span hsourceOutside r hr)
  have hcallee4 : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = fr.rsp - 208 := by
    rw [hc4, h4get]; bv_omega
  let af := activationOfValues callee.store callee.arguments
    (if use256 then 0x102aa2 else 0x102642) lower
  have hafsp : af.rsp = fr.rsp - 208 := hcallee4
  have hafkey : af.rdi = fr.rsp - 152 := by
    change (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = _
    rw [hc7, h4get]; bv_omega
  have hafdesc : af.rsi = fr.rsp - 184 := by
    change (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = _
    rw [hc6, h4get]; bv_omega
  have haflow : af.low = lower := rfl
  have hCTRwindow : (if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo).window = ctrWindow := by
    cases use256 <;> rfl
  have hloads := cryptFullMemory_loads use256 args mem
  rw [h4get, hcounter, hsource, hdest, hlen,
    show fr.rsp - 200 - 8 = fr.rsp - 208 by bv_omega,
    show fr.rsp - 200 + 16 = fr.rsp - 184 by bv_omega,
    show fr.rsp - 200 + 24 = fr.rsp - 176 by bv_omega,
    show fr.rsp - 200 + 32 = fr.rsp - 168 by bv_omega,
    show fr.rsp - 200 + 40 = fr.rsp - 160 by bv_omega, ← hcalleeMem] at hloads
  have hkey : memLoad callee.store (fr.rsp - 152) 64 = fr.rsi + 32 := by
    apply Eq.trans (hmem.memLoad_eq _) hkeyPtr
    refine ⟨by rw [hs152]; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hs152, hs208]
    omega
  have hcounterOutside : Outside [span (fr.rsp - 208) 56] (fr.rsp - 144) 20 := by
    refine ⟨by rw [hs144]; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hs144, hs208]
    omega
  have counterLoad (n : Nat) (hn : n ≤ 16) :
      memLoad callee.store ((fr.rsp - 144) + BitVec.ofNat 64 n) 32 =
      memLoad mem ((fr.rsp - 144) + BitVec.ofNat 64 n) 32 :=
    hmem.memLoad_eq (outside_subregion hcounterOutside (by omega) (by omega))
  have counterInitial : CTR.initialCounterBlock callee.store (fr.rsp - 144) =
      CTR.initialCounterBlock mem (fr.rsp - 144) := by
    apply Vector.ext
    intro i hi
    simp only [CTR.initialCounterBlock, Vector.getElem_ofFn, CTR.counterWord]
    split
    · rw [counterLoad _ (by omega)]
    · have h12 : memLoad callee.store (fr.rsp - 144 + 12) 32 = memLoad mem (fr.rsp - 144 + 12) 32 := counterLoad 12 (by decide)
      have h16 : memLoad callee.store (fr.rsp - 144 + 16) 32 = memLoad mem (fr.rsp - 144 + 16) 32 := counterLoad 16 (by decide)
      rw [h12, h16]
  have slotOutside (address : BitVec 64) (hlo : 0x201208 ≤ address.toNat)
      (hhi : address.toNat + 8 ≤ 0x201238) : Outside [span (fr.rsp - 208) 56] address 8 := by
    refine ⟨by omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    have hhigh : 0x201238 + window ≤ slotHigh := by cases use256 <;> decide
    simp only [span, hs208]
    omega
  have hslots : Atom.All code callee.arguments callee.store
      ((if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo).callSlotAtoms
        (if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo).callSlots af) := by
    have s0 := (hmem.memLoad_eq (slotOutside 0x201208 (by decide) (by decide))).trans s0v
    have s1 := (hmem.memLoad_eq (slotOutside 0x201210 (by decide) (by decide))).trans s1v
    have s3 := (hmem.memLoad_eq (slotOutside 0x201230 (by decide) (by decide))).trans s3v
    have hhigh : 0x201238 + ctrWindow + 208 ≤ slotHigh := by cases use256 <;> decide
    have sep : 0x201238 + ctrWindow ≤ af.rsp.toNat ∨ af.rsp.toNat ≤ 0x201208 := by
      rw [hafsp, hs208]
      omega
    cases use256 <;> exact ⟨s0r.of_frame hmem, s0, s1r.of_frame hmem, s1, s3r.of_frame hmem, s3, sep, trivial⟩
  have localRead (n count : Nat) (hn : n ≤ window) (hc : count ≤ n) :
      Readable callee.store (fr.rsp - BitVec.ofNat 64 n) count := by
    apply (hstack.readable.of_frame hmem).sub
    all_goals rw [hsub n hn, hsub window (Nat.le_refl _)]
    all_goals omega
  have localWrite (n count : Nat) (hn : n ≤ window) (hc : count ≤ n) :
      Writable code callee.store (fr.rsp - BitVec.ofNat 64 n) count := by
    apply (hstack.of_frame hmem).sub
    all_goals rw [hsub n hn, hsub window (Nat.le_refl _)]
    all_goals omega
  have localApartExternal (n count : Nat) (hn : n ≤ window) (hc : count ≤ n)
      {base : BitVec 64} {size : Nat} (hsep : (callStack fr).Disjoint (span base size)) :
      (span (fr.rsp - BitVec.ofNat 64 n) count).Disjoint (span base size) := by
    intro x hx hy
    apply hsep x ?_ hy
    simp only [MemoryRegion.Contains, span, callStack, hsub n hn] at hx ⊢
    omega
  have localApart (n count m count' : Nat) (hn : n ≤ window) (hm : m ≤ window)
      (hc : count ≤ n) (hc' : count' ≤ m) (hap : m + count ≤ n ∨ n + count' ≤ m) :
      (span (fr.rsp - BitVec.ofNat 64 n) count).Disjoint
        (span (fr.rsp - BitVec.ofNat 64 m) count') := by
    intro x hx hy
    simp only [MemoryRegion.Contains, span, hsub n hn, hsub m hm] at hx hy
    omega
  have stackApartLocal (n count : Nat) (hn : n ≤ window) (hc : count ≤ n) (htop : n ≤ 200) :
      (callStack af).Disjoint (span (fr.rsp - BitVec.ofNat 64 n) count) := by
    intro x hx hy
    simp only [MemoryRegion.Contains, span, callStack, hafsp, haflow, hlower, hs208, hsub n hn] at hx hy
    omega
  have stackApartExternal {base : BitVec 64} {size : Nat}
      (hsep : (callStack fr).Disjoint (span base size)) :
      (callStack af).Disjoint (span base size) := by
    intro x hx hy
    apply hsep x ?_ hy
    simp only [MemoryRegion.Contains, callStack, hafsp, haflow, hlower, hs208] at hx ⊢
    omega
  have counterSlot (address : BitVec 64) (ha : 0x201208 ≤ address.toNat)
      (hb : address.toNat + 8 ≤ 0x201238) :
      (span (fr.rsp - 144) 20).Disjoint (span address 8) := by
    have hhigh : 0x201238 + window ≤ slotHigh := by cases use256 <;> decide
    intro x hx hy
    simp only [MemoryRegion.Contains, span, hs144] at hx hy
    omega
  have hpre :
      Readable callee.store af.rdi 8 ∧ memLoad callee.store af.rdi 64 = fr.rsi + 32 ∧
      AES16.ScheduleIn (AES16.variant use256) key (fr.rsi + 32) callee.store ∧
      Readable callee.store (fr.rsi + 32) (16 * ((AES16.variant use256).Nr + 1)) ∧
      Readable callee.store af.rsi 32 ∧ memLoad callee.store af.rsi 64 = fr.rsp - 144 ∧
      memLoad callee.store (af.rsi + 8) 64 = source ∧
      memLoad callee.store (af.rsi + 16) 64 = destination ∧
      (memLoad callee.store (af.rsi + 24) 64).toNat = length.toNat / 16 ∧
      Writable code callee.store (fr.rsp - 144) 20 ∧ Readable callee.store source input.size ∧
      (span source input.size).HasBytes callee.store input ∧ Writable code callee.store destination input.size ∧
      (source = destination ∨ (span source input.size).Disjoint (span destination input.size)) ∧
      (∀ slot ∈ ([0x201208, 0x201210, 0x201230] : List (BitVec 64)),
        (span destination input.size).Disjoint (span slot 8) ∧
        (span (fr.rsp - 144) 20).Disjoint (span slot 8)) ∧
      (∀ region ∈ [span af.rdi 8, span af.rsi 32,
        span (fr.rsi + 32) (16 * ((AES16.variant use256).Nr + 1)), span (fr.rsp - 144) 20,
        span source input.size, span destination input.size], (callStack af).Disjoint region) ∧
      (∀ region ∈ [span af.rdi 8, span af.rsi 32,
        span (fr.rsi + 32) (16 * ((AES16.variant use256).Nr + 1)), span (fr.rsp - 144) 20],
        (span destination input.size).Disjoint region) ∧
      (∀ region ∈ [span af.rdi 8, span af.rsi 32,
        span (fr.rsi + 32) (16 * ((AES16.variant use256).Nr + 1)),
        span source input.size, span destination input.size],
        (span (fr.rsp - 144) 20).Disjoint region) := by
    refine ⟨?_, ?_, hsched, hrSchedule.of_frame hmem, ?_, ?_, ?_, ?_, ?_, ?_,
      hread.of_frame hmem, hb, hwrite.of_frame hmem, halias, ?_, ?_, ?_, ?_⟩
    · rw [hafkey]; exact localRead 152 8 (by omega) (by decide)
    · simpa only [hafkey] using hkey
    · rw [hafdesc]; exact localRead 184 32 (by omega) (by decide)
    · simpa only [hafdesc] using hloads.2.1
    · rw [hafdesc, show fr.rsp - 184 + 8 = fr.rsp - 176 by bv_omega]; exact hloads.2.2.1
    · rw [hafdesc, show fr.rsp - 184 + 16 = fr.rsp - 168 by bv_omega]; exact hloads.2.2.2.1
    · rw [hafdesc, show fr.rsp - 184 + 24 = fr.rsp - 160 by bv_omega, hloads.2.2.2.2]
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    · exact localWrite 144 20 (by omega) (by decide)
    · intro slot hin
      refine ⟨hslotSep slot ?_, counterSlot slot ?_ ?_⟩
      all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hin ⊢
      all_goals rcases hin with rfl | rfl | rfl <;> decide
    · intro r hin
      simp only [List.mem_cons, List.not_mem_nil, or_false, hafkey, hafdesc] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl
      · exact stackApartLocal 152 8 (by omega) (by decide) (by decide)
      · exact stackApartLocal 184 32 (by omega) (by decide) (by decide)
      · exact stackApartExternal (hstackSep _ (by simp))
      · exact stackApartLocal 144 20 (by omega) (by decide) (by decide)
      · exact stackApartExternal (hstackSep _ (by simp))
      · exact stackApartExternal (hstackSep _ (by simp))
    · intro r hin
      simp only [List.mem_cons, List.not_mem_nil, or_false, hafkey, hafdesc] at hin
      rcases hin with rfl | rfl | rfl | rfl
      · intro x hx hy
        exact localApartExternal 152 8 (by omega) (by decide)
          (hstackSep (span destination input.size) (by simp)) x hy hx
      · intro x hx hy
        exact localApartExternal 184 32 (by omega) (by decide)
          (hstackSep (span destination input.size) (by simp)) x hy hx
      · exact hdataSep
      · intro x hx hy
        exact localApartExternal 144 20 (by omega) (by decide)
          (hstackSep (span destination input.size) (by simp)) x hy hx
    · intro r hin
      simp only [List.mem_cons, List.not_mem_nil, or_false, hafkey, hafdesc] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl
      · exact localApart 144 20 152 8 (by omega) (by omega) (by decide) (by decide) (by decide)
      · exact localApart 144 20 184 32 (by omega) (by omega) (by decide) (by decide) (by decide)
      · exact localApartExternal 144 20 (by omega) (by decide) (hstackSep _ (by simp))
      · exact localApartExternal 144 20 (by omega) (by decide) (hstackSep _ (by simp))
      · exact localApartExternal 144 20 (by omega) (by decide) (hstackSep _ (by simp))
  have hc39' := hc39.trans h39
  have hc50' := hc50.trans h50
  have hc51' := hc51.trans h51
  obtain ⟨output, hexec, htag, hdone, houtTypes, hframe, hpost⟩ :=
    callContract_exec_values LIR.lifted code (if use256 then .l1084e0 else .l107050)
      (if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo)
      (fun _ ↦ [span ((fr.rsp - 144) + 16) 4, span destination input.size]) _ _
      (CTR.crypt_call use256 code hcode key input (length.toNat / 16) hsize (fr.rsi + 32)
        (fr.rsp - 144) source destination)
      callee.store callee.arguments (if use256 then 0x102aa2 else 0x102642) lower
      (hcalleeTypes hTypes) (by rw [hc39']; rfl) (by rw [hc50']; rfl) (by rw [hc51']; rfl)
      (hc22.trans h22)
      (by rw [hcallee4]; exact localRead 208 8 (by omega) (by decide))
      (by rw [hcallee4]; exact hloads.1)
      (by cases use256 <;> decide)
      (by
        intro _
        rw [hCTRwindow, hcallee4, BitVec.sub_sub]
        have heq : (208 : BitVec 64) + BitVec.ofNat 64 ctrWindow = BitVec.ofNat 64 window := by
          change BitVec.ofNat 64 208 + _ = _
          rw [← BitVec.ofNat_add, hwindow]
        rw [heq]
        have hw : Writable code callee.store (fr.rsp - BitVec.ofNat 64 window) window := hstack.of_frame hmem
        exact hw.sub (Nat.le_refl _) (by omega))
      (by rw [hCTRwindow, hcallee4, hlower, hs208]; omega)
      (by rw [hcallee4, hs208]; omega) hslots hpre
  change Atom.All code output.values output.store
    ((if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo).doneAtoms af) at hdone
  change RamWriteFrame callee.store output.store
    [af.region, span ((fr.rsp - 144) + 16) 4, span destination input.size] at hframe
  change memLoad output.store ((fr.rsp - 144) + 16) 32 =
      memLoad callee.store ((fr.rsp - 144) + 16) 32 + BitVec.ofNat 32 (length.toNat / 16) ∧ _ at hpost
  have hdone' : output.values[4] = ⟨64, af.rsp + 8⟩ ∧ output.values[22] = ⟨1, 0⟩ ∧
      output.values[3] = ⟨64, af.rbx⟩ ∧ output.values[5] = ⟨64, af.rbp⟩ ∧
      output.values[12] = ⟨64, af.r12⟩ ∧ output.values[13] = ⟨64, af.r13⟩ ∧
      output.values[14] = ⟨64, af.r14⟩ ∧ output.values[15] = ⟨64, af.r15⟩ ∧
      output.values[39] = ⟨32, af.mxcsr⟩ ∧ output.values[50] = ⟨16, af.ftw⟩ ∧
      output.values[51] = ⟨16, af.fcw⟩ ∧ True := by cases use256 <;> exact hdone
  rcases hdone' with ⟨ho4, ho22, ho3, ho5, ho12, ho13, ho14, ho15, ho39, ho50, ho51, -⟩
  have hmemTight : RamWriteFrame mem callee.store
      [span lower (window - 124), span destination input.size] := by
    apply (RamWriteFrame.refl _ _).trans hmem
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    refine ⟨span lower (window - 124), by simp only [List.mem_cons, true_or], ?_, ?_⟩ <;>
      simp only [span, hlower, hs208] <;> omega
  have within : RegionsWithin [af.region, span ((fr.rsp - 144) + 16) 4, span destination input.size]
      [span lower (window - 124), span destination input.size] := by
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl
    · refine ⟨span lower (window - 124), by simp only [List.mem_cons, true_or], ?_, ?_⟩ <;>
        simp only [Activation.region, span, haflow, hafsp, hlower, hs208] <;> omega
    · refine ⟨span lower (window - 124), by simp only [List.mem_cons, true_or], ?_, ?_⟩ <;>
        simp only [span, show fr.rsp - 144 + 16 = fr.rsp - 128 by bv_omega, hlower, hs128] <;> omega
    · exact ⟨span destination input.size, by simp only [List.mem_cons, true_or, or_true],
        Nat.le_refl _, Nat.le_refl _⟩
  have hf := hmemTight.trans hframe within
  have destinationBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    destination.toNat input.size (by omega) hpos (hstackSep (span destination input.size) (by simp))
  have savedOutside (n : Nat) (hn : n ≤ 112) :
      Outside [span lower (window - 124), span destination input.size]
        (fr.rsp - BitVec.ofNat 64 n) 8 := by
    refine ⟨by rw [hsub n (by omega)]; omega, ?_⟩
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · simp only [span, hlower, hsub n (by omega)]; omega
    · simp only [span, hsub n (by omega)]; omega
  have slotsOutside (address : BitVec 64) (hlo : 0x201208 ≤ address.toNat)
      (hhi : address.toNat + 8 ≤ 0x201238)
      (hsep : (span destination input.size).Disjoint (span address 8)) :
      Outside [span lower (window - 124), span destination input.size] address 8 := by
    refine ⟨by omega, ?_⟩
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · have hhigh : 0x201238 + window ≤ slotHigh := by cases use256 <;> decide
      simp only [span, hlower]
      omega
    · have hd := disjoint_bounds destination.toNat input.size address.toNat 8 hpos (by decide) hsep
      simp only [span]
      omega
  have outsp : output.values[4] = args[4] := by
    rw [ho4, hafsp, h4, show fr.rsp - 208 + 8 = fr.rsp - 200 by bv_omega]
  have out39 : output.values[39] = args[39] := by
    rw [ho39]
    change Value.mk 32 ((callee.arguments[39]'(by change 39 < 53; decide)).get 32) = _
    rw [hc39', h39]; rfl
  have out50 : output.values[50] = args[50] := by
    rw [ho50]
    change Value.mk 16 ((callee.arguments[50]'(by change 50 < 53; decide)).get 16) = _
    rw [hc50', h50]; rfl
  have out51 : output.values[51] = args[51] := by
    rw [ho51]
    change Value.mk 16 ((callee.arguments[51]'(by change 51 < 53; decide)).get 16) = _
    rw [hc51', h51]; rfl
  have workingBefore : Atom.All code args mem
      (if use256 then LIR.Fn102980.frameAt .l102aa2 fr else LIR.Fn102520.frameAt .l102642 fr) := by
    cases use256 <;> exact ⟨hworking.1, hworking.2.1, hworking.2.2.2⟩
  have workingAfter : Atom.All code output.values output.store
      (if use256 then LIR.Fn102980.frameAt .l102aa2 fr else LIR.Fn102520.frameAt .l102642 fr) := by
    apply fullBlocks_frame use256 code fr args output.values mem output.store
      [span lower (window - 124), span destination input.size] workingBefore hf
    · intro r hr
      rcases r with ⟨r, hlt⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact outsp
      · exact ho22.trans h22.symm
      · exact out39
      · exact out50
      · exact out51
    · exact savedOutside
    · intro address ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl
      all_goals exact slotsOutside _ (by decide) (by decide) (hslotSep _ (by decide))
  have hmask : (0xffffffff0 : BitVec 64) &&& length = BitVec.ofNat 64 input.size := by
    rw [hsize]
    exact length_full_block_mask length hlengthBound
  have hmod : ((length.setWidth 32) &&& 15).setWidth 64 = BitVec.ofNat 64 (length.toNat % 16) :=
    length_tail_byte_mask length
  have counterKept (n : Nat) (hn : n ≤ 12) :
      memLoad output.store ((fr.rsp - 144) + BitVec.ofNat 64 n) 32 =
      memLoad mem ((fr.rsp - 144) + BitVec.ofNat 64 n) 32 := by
    apply Eq.trans (hframe.memLoad_eq _) (counterLoad n (by omega))
    have ha : ((fr.rsp - 144) + BitVec.ofNat 64 n).toNat = fr.rsp.toNat - 144 + n := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hs144]
      omega
    refine ⟨by rw [ha]; omega, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [Activation.region, haflow, hafsp, hlower, hs208, ha]
      omega
    · simp only [span, show fr.rsp - 144 + 16 = fr.rsp - 128 by bv_omega, hs128, ha]
      omega
    · simp only [span, ha]
      omega
  have counterAdvanced : Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock output.store (fr.rsp - 144)) =
      Nat.repeat (Standards.NIST.GCM.inc 32) (length.toNat / 16)
        (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock mem (fr.rsp - 144))) := by
    apply CTR.initialCounterBlock_advance mem output.store (fr.rsp - 144) (length.toNat / 16)
    · intro k
      exact counterKept (4 * k.val) (by omega)
    · exact counterKept 12 (by decide)
    · have hp := hpost.1
      have he : memLoad callee.store (fr.rsp - 144 + 16) 32 = memLoad mem (fr.rsp - 144 + 16) 32 := counterLoad 16 (by decide)
      rw [he] at hp
      exact hp
  have schedulePointer : memLoad output.store (fr.rsp - 152) 64 = fr.rsi + 32 := by
    apply Eq.trans (hframe.memLoad_eq _) hkey
    refine ⟨by rw [hs152]; omega, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [Activation.region, haflow, hafsp, hlower, hs208, hs152]
      omega
    · simp only [span, show fr.rsp - 144 + 16 = fr.rsp - 128 by bv_omega, hs128, hs152]
      omega
    · simp only [span, hs152]
      omega
  let next := continuation.resume output
  have hnextArgs : next.arguments = output.values := CFGCall.resume_arguments continuation output
  have hnextStore : next.store = output.store := rfl
  have hexecc : LIR.program.Exec (dialect code) ⟨callee, []⟩ output := by
    change LIR.program.Exec (dialect code) ⟨⟨callee.label, callee.arguments, callee.store⟩, []⟩ output
    rw [hcalleeLabel]
    exact hexec
  have ha : continuation.Accepts (dialect code) output.tag = true := by
    simp only [StackFrame.Accepts, hguard, htag]
    cases use256 <;> rfl
  have hresume := CFGCall.exec_reaches_resume hexecc continuation [] ha
  have hstep : LIR.program.step (dialect code)
      ⟨⟨(if use256 then .l102a59 else .l1025f9), args, mem⟩, []⟩ =
      .next ⟨callee, [continuation]⟩ := by rw [Program.step, hcall]; rfl
  refine ⟨next, (Semantics.Reaches.single hstep).trans hresume, htarget, ?_,
    by simpa only [hnextArgs] using houtTypes, hf, ?_, ?_, ?_, ?_, ?_, ?_, counterAdvanced, schedulePointer, ?_⟩
  · simpa only [hnextArgs, hnextStore] using workingAfter
  · rw [hnextArgs, ho5]; exact hc5.trans hlen
  · rw [hnextArgs, ho13]; exact hc13.trans hdest
  · rw [hnextArgs, ho3]
    change (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = _
    rw [hc3, hsource, hlen]
    exact congrArg (fun x : BitVec 64 ↦ source + x) hmask
  · rw [hnextArgs, ho12]
    change (callee.arguments[12]'(by change 12 < 53; decide)).get 64 = _
    rw [hc12, hlen, hdest]
    exact (congrArg (fun x : BitVec 64 ↦ x + destination) hmask).trans (BitVec.add_comm _ _)
  · rw [hnextArgs, ho14]
    change (callee.arguments[14]'(by change 14 < 53; decide)).get 64 = _
    rw [hc14, hlen, hmod]
  · have hp := hpost.1
    have h16 : memLoad callee.store (fr.rsp - 144 + 16) 32 = memLoad mem (fr.rsp - 144 + 16) 32 := counterLoad 16 (by decide)
    rw [h16, show fr.rsp - 144 + 16 = fr.rsp - 128 by bv_omega] at hp
    exact hp
  · have hp := hpost.2
    change (span destination input.size).HasBytes output.store
      (AesGcm.Spec.GCM.byteArrayOfBits (Standards.NIST.GCM.GCTR _
        (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock callee.store (fr.rsp - 144))) _)) at hp
    rw [counterInitial] at hp
    exact hp

end AesGcm.Proofs.Machine.Core.Encrypt
