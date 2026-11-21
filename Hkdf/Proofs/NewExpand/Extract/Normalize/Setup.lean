import Hkdf.Proofs.NewExpand.Extract.Normalize.Entry
import Hkdf.Proofs.NewExpand.Extract.Frame
import Hkdf.Proofs.Common.Memory.Copy.RegisterOps.Cmov
import X86Proofs.Instructions.Cmov.Generated.RR.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Normalize

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Program
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev saltAddress (initial : RamState) : BitVec 64 := stackPtr initial - 368

structure Prepared [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop
    extends Frame initial s boundary where
  rip : s.RIP = 0x10fada
  ikmPtr : s.regValue .r15 = initial.regValue .rcx
  ikmLen : s.regValue .r14 = initial.regValue .r8
  output : s.regValue .rdi = stackPtr initial - 336
  input : s.regValue .rsi =
    if initial.regValue .rsi = 0 then saltAddress initial else initial.regValue .rsi
  length : s.regValue .rdx = if initial.regValue .rsi = 0 then 32 else initial.regValue .rdx
  zeros : ∀ j < 4, memLoad s.external (saltAddress initial + BitVec.ofNat 64 (8*j)) 64 = 0

private theorem step_store [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {offset next slot len : Nat} {bytes : List UInt8}
    {addr : RamState → BitVec 64} {value : RamState → BitVec 64}
    (running : Running initial s boundary) (stack : Stack.Valid initial 2264)
    (avoid : (Stack.region initial 2264).Avoids (fun a ↦ InProgram a ∨ InPageTables a))
    (outside : ¬ InProgram boundary.rip)
    (step : StepEffect (StorePre (Extracted.textAddress + BitVec.ofNat 64 offset) len addr 8)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes)
      (storeEffect (Extracted.textAddress + BitVec.ofNat 64 offset) len addr value))
    (codeBound : offset + bytes.length ≤ 115149)
    (insnBound : offset + len ≤ 115149)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (address : addr s = stackPtr initial - BitVec.ofNat 64 slot)
    (slotBound : slot ≤ 2264) (slotRoom : 8 ≤ slot) (slotAligned : slot % 8 = 0)
    (nextEq : (Extracted.textAddress + BitVec.ofNat 64 offset) + BitVec.ofNat 64 len =
      Extracted.textAddress + BitVec.ofNat 64 next) (nextBound : next < 115149) :
    ∃ t, Running initial t boundary ∧ t.RIP = Extracted.textAddress + BitVec.ofNat 64 next ∧
      AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 slot) 8, .rip] s t ∧
      stackPtr t = stackPtr s ∧
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 slot) 64 = value s := by
  have writable : MemWritable s (addr s) 8 := by
    rw [address]
    exact stack_writable8 stack avoid running.allocated slotBound slotAligned
  have apart : RangeApart (addr s) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
    rw [address]
    exact stack_codeApart stack (fun a ha hp ↦ avoid a ha (.inl hp))
      slotBound (by omega) insnBound
  have writes : WritesWithin
      (storeEffect (Extracted.textAddress + BitVec.ofNat 64 offset) len addr value s).components
      #v[Stack.region initial 2264] := by
    rw [storeEffect_components, address]
    apply stack_slot_within stack slotBound slotRoom
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ha
    · exact ha.elim
  obtain ⟨t, current, effect, ip⟩ := step_text running avoid outside step codeBound code
    ⟨rip, writable, apart⟩ nextEq nextBound writes (by simp)
  have frame : AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 slot) 8, .rip] s t := by
    simpa only [storeEffect_components, address, Nat.reduceDiv] using effect.agrees
  refine ⟨t, current, ip, frame, frame.read (n := 64) (r := 4) (by simp), ?_⟩
  have stored : memLoad t.external (addr s) 64 = value s := effect.writes
  rwa [address] at stored

private theorem cmove_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (valid : modrmMod modrm = 3) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x48, 0x0f, 0x44, modrm])
      (Instructions.cmovR64R64Effect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  intro s ready loaded rip
  exact cmov_r64_r64_effect_step p 4 0x48 (by constructor <;> decide) modrm valid
    (condHolds 4 (StatusFlags.ofRFLAGS s.RFLAGS)) s ready loaded ⟨rip, rfl⟩

private theorem load_untouched {s t : RamState} {base offset : BitVec 64}
    {size : Nat} {slots : List (BitVec 64)} {components : List Component}
    (frame : AgreesExcept components s t)
    (writes : ∀ c ∈ components, ∀ a, c.Covers a →
      ∃ slot ∈ slots, (Component.mem (base + slot) 8).Covers a)
    (apart : ∀ slot ∈ slots, OffsetsApart offset size slot 8) (small : size + 8 < 2^64) :
    (Component.mem (base + offset) size).Agrees s t := by
  intro i hi
  apply frame.memory
  intro c hc cover
  obtain ⟨slot, member, j, hj, eq⟩ := writes c hc _ cover
  exact (apart slot member).ne base hi hj small eq

private theorem cmove_components (p : BitVec 64) (cc : BitVec 4) (dst src : BitVec 5)
    (s : RamState) :
    (Instructions.cmovR64R64Effect p cc dst src s).components = [.reg dst, .rip] := rfl

attribute [local simp] cmove_components

macro "salt_step " running:term ", " pre:term ", " first:term ", " next:term ", "
    step:term ", " ip:term : term =>
  `(step_text (offset := $first) (next := $next) $running ($pre).call.stackAvoid
    ($pre).call.outerBoundary $step (by decide) (by decide +kernel) $ip rfl (by decide)
    (no_memory_writes (by simp [Component.Covers])) (by simp))

macro "salt_store " running:term ", " pre:term ", " first:term ", " next:term ", "
    slot:term ", " step:term ", " ip:term ", " sp:term ", " disp:term : term =>
  `(step_store (offset := $first) (next := $next) (slot := $slot) $running ($pre).call.stack
    ($pre).call.stackAvoid ($pre).call.outerBoundary $step (by decide) (by decide) (by decide +kernel)
    $ip (by
      change stackPtr _ + $disp = _
      rw [($sp), base]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd])
    (by decide) (by decide) (by decide) rfl (by decide))

macro "zero_store_step " ip:term ", " disp:term : term =>
  `(mov_m64_imm32_effect_step $ip 0x48 (by constructor <;> decide)
    (.sib 4 none 0 (.d8 $disp)) (by decide) rfl rfl 0)

macro "salt_mov " ip:term ", " rex:term ", " modrm:term ", " dst:term ", " src:term : term =>
  `(show StepEffect (fun s ↦ s.RIP = $ip) (codeRange $ip [$rex, 0x89, $modrm])
    (movR64R64Effect $ip $dst $src) from
    mov_r64_r64_effect_step $ip $rex $modrm (by simp [RexWPrefix]) rfl)

macro "salt_lea " ip:term ", " dst:term ", " disp:term ", " modrm:term : term =>
  `(show StepEffect (fun s ↦ s.RIP = $ip) (codeRange $ip [0x48, 0x8d, $modrm, 0x24, $disp])
    (leaR64Effect $ip $dst (.sib 4 none 0 (.d8 $disp))) from
    lea_r64_effect_step $ip 0x48 (by simp [RexWPrefix]) $dst
      (.sib 4 none 0 (.d8 $disp)) (by decide) rfl rfl)

macro "salt_cmove " ip:term ", " modrm:term ", " dst:term : term =>
  `(show StepEffect (fun s ↦ s.RIP = $ip) (codeRange $ip [0x48, 0x0f, 0x44, $modrm])
    (Instructions.cmovR64R64Effect $ip 4 $dst 0) from cmove_step $ip $modrm (by decide))

macro "salt_apart " frame:term ", " slots:term : term =>
  `(load_untouched $frame (slots := $slots)
    (by
      intro c hc a ha
      simp only [BitVec.sub_eq_add_neg, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, cmove_components, movR64R64Effect_components, movR32Imm32Effect_components,
        leaR64Effect_components, testR64R64Effect_components, BitVec.reduceNeg] at hc
      repeat' first | subst c | (rcases hc with hc | hc)
      all_goals first | exact ha.elim | exact ⟨_, by simp, ha⟩)
    (by
      intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      repeat' first | subst slot | (rcases member with member | member)
      all_goals unfold OffsetsApart
      all_goals decide +kernel)
    (by decide))

theorem prepare [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray} (pre : ExtractPre initial boundary salt ikm) :
    ∃ t, Prepared initial t boundary := by
  obtain ⟨s, running, ip, sp, saved, entry⟩ := enter pre
  obtain ⟨u1, r1, e1, ip1⟩ := salt_step running, pre, 0xfa91, 0xfa94,
    (salt_mov 0x10fa91, 0x4d, 0xc6, 14, 8), ip
  obtain ⟨u2, r2, e2, ip2⟩ := salt_step r1, pre, 0xfa94, 0xfa97,
    (salt_mov 0x10fa94, 0x49, 0xcf, 15, 1), ip1
  have sp2 : stackPtr u2 = base initial :=
    ((e1.agrees.trans e2.agrees).read (n := 64) (r := 4) (by simp)).trans sp
  obtain ⟨u3, r3, ip3, f3, rsp3, out3⟩ := salt_store r2, pre, 0xfa97, 0xfa9c, 376,
    (mov_m64_r64_effect_step 0x10fa97 0x48 (by constructor <;> decide) 7
      (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl), ip2, sp2, 80
  have sp3 := rsp3.trans sp2
  obtain ⟨u4, r4, ip4, f4, rsp4, z4⟩ := salt_store r3, pre, 0xfa9c, 0xfaa5, 344,
    (zero_store_step 0x10fa9c, 112), ip3, sp3, 112
  have sp4 := rsp4.trans sp3
  obtain ⟨u5, r5, ip5, f5, rsp5, z5⟩ := salt_store r4, pre, 0xfaa5, 0xfaae, 352,
    (zero_store_step 0x10faa5, 104), ip4, sp4, 104
  have sp5 := rsp5.trans sp4
  obtain ⟨u6, r6, ip6, f6, rsp6, z6⟩ := salt_store r5, pre, 0xfaae, 0xfab7, 360,
    (zero_store_step 0x10faae, 96), ip5, sp5, 96
  have sp6 := rsp6.trans sp5
  obtain ⟨u7, r7, e7, ip7⟩ := salt_step r6, pre, 0xfab7, 0xfaba,
    (show StepEffect (fun s ↦ s.RIP = 0x10fab7) (codeRange 0x10fab7 [0x48, 0x85, 0xf6])
      (testR64R64Effect 0x10fab7 6 6) from
      test_r64_r64_effect_step 0x10fab7 0x48 0xf6 (by simp [RexWPrefix]) rfl), ip6
  obtain ⟨u8, r8, e8, ip8⟩ := salt_step r7, pre, 0xfaba, 0xfabf,
    (salt_lea 0x10faba, 0, 88, 0x44), ip7
  obtain ⟨u9, r9, e9, ip9⟩ := salt_step r8, pre, 0xfabf, 0xfac3,
    (salt_cmove 0x10fabf, 0xf0, 6), ip8
  have sp9 : stackPtr u9 = base initial :=
    (((e7.agrees.trans e8.agrees).trans e9.agrees).read (n := 64) (r := 4) (by simp)).trans sp6
  obtain ⟨u10, r10, ip10, f10, rsp10, z10⟩ := salt_store r9, pre, 0xfac3, 0xfacc, 368,
    (zero_store_step 0x10fac3, 88), ip9, sp9, 88
  obtain ⟨u11, r11, e11, ip11⟩ := salt_step r10, pre, 0xfacc, 0xfad1,
    (show StepEffect (fun s ↦ s.RIP = 0x10facc) (codeRange 0x10facc [0xb8, 32, 0, 0, 0])
      (movR32Imm32Effect 0x10facc 5 0 32) from
      mov_r32_imm32_effect_step 0x10facc 0xb8 (by decide) 32), ip10
  obtain ⟨u12, r12, e12, ip12⟩ := salt_step r11, pre, 0xfad1, 0xfad5,
    (salt_cmove 0x10fad1, 0xd0, 2), ip11
  obtain ⟨t, current, e13, ip13⟩ := salt_step r12, pre, 0xfad5, 0xfada,
    (salt_lea 0x10fad5, 7, 120, 0x7c), ip12
  have beforeTest := ((((e1.agrees.trans e2.agrees).trans f3).trans f4).trans f5).trans f6
  have afterTest := ((e7.agrees.trans e8.agrees).trans e9.agrees).trans f10
  have afterStore := (e11.agrees.trans e12.agrees).trans e13.agrees
  have all := (beforeTest.trans afterTest).trans afterStore
  have spT : stackPtr t = base initial :=
    (afterStore.read (n := 64) (r := 4) (by simp)).trans (rsp10.trans sp9)
  have origIn : u6.regValue .rsi = initial.regValue .rsi :=
    (entry.trans beforeTest).read (n := 64) (r := 6)
      (by simp [Encoding.Serialize.saveFrame])
  have testZF : (StatusFlags.ofRFLAGS u7.RFLAGS).ZF = (initial.regValue .rsi == 0) := by
    have flags := e7.flags
    change (testFlags ((u6.regValue .rsi) &&& (u6.regValue .rsi))).Allows _ at flags
    have zf := flags.2.2.2.1
    change _ = (u6.regValue .rsi &&& u6.regValue .rsi == 0) at zf
    simpa only [origIn, BitVec.and_self] using zf
  have unchangedZF8 : StatusFlags.ofRFLAGS u8.RFLAGS = StatusFlags.ofRFLAGS u7.RFLAGS :=
    e8.agrees.statusFlags (by simp)
  have unchangedZF11 : StatusFlags.ofRFLAGS u11.RFLAGS = StatusFlags.ofRFLAGS u8.RFLAGS :=
    (((e9.agrees.trans f10).trans e11.agrees).statusFlags (by simp))
  have rax8 : u8.regValue .rax = saltAddress initial := by
    have value : u8.regValue .rax = stackPtr u7 + 88 := e8.writes
    have rsp : stackPtr u7 = stackPtr u6 := e7.agrees.read (n := 64) (r := 4) (by simp)
    rw [value, rsp, sp6, base]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have input8 : u8.regValue .rsi = initial.regValue .rsi :=
    ((e7.agrees.trans e8.agrees).read (n := 64) (r := 6) (by simp)).trans origIn
  have input9 : u9.regValue .rsi = if initial.regValue .rsi = 0 then
      saltAddress initial else initial.regValue .rsi := by
    have value : u9.regValue .rsi =
        if (StatusFlags.ofRFLAGS u8.RFLAGS).ZF then u8.regValue .rax else u8.regValue .rsi :=
      e9.writes
    simpa only [unchangedZF8, testZF, rax8, input8, beq_iff_eq] using value
  have length11 : u11.regValue .rdx = initial.regValue .rdx :=
    (((entry.trans beforeTest).trans afterTest).trans e11.agrees).read
      (n := 64) (r := 2) (by simp [Encoding.Serialize.saveFrame])
  have rax11 : u11.regValue .rax = 32 := e11.writes
  have length12 : u12.regValue .rdx =
      if initial.regValue .rsi = 0 then 32 else initial.regValue .rdx := by
    have value : u12.regValue .rdx =
        if (StatusFlags.ofRFLAGS u11.RFLAGS).ZF then u11.regValue .rax else u11.regValue .rdx :=
      e12.writes
    simpa only [unchangedZF11, unchangedZF8, testZF, rax11, length11, beq_iff_eq] using value
  have output : t.regValue .rdi = stackPtr initial - 336 := by
    have value : t.regValue .rdi = stackPtr u12 + 120 := e13.writes
    have rsp : stackPtr t = stackPtr u12 := e13.agrees.read (n := 64) (r := 4) (by simp)
    rw [value, ← rsp, spT, base]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have input : t.regValue .rsi = if initial.regValue .rsi = 0 then
      saltAddress initial else initial.regValue .rsi :=
    ((f10.trans afterStore).read (n := 64) (r := 6) (by simp)).trans input9
  have length : t.regValue .rdx = if initial.regValue .rsi = 0 then 32 else initial.regValue .rdx :=
    (e13.agrees.read (n := 64) (r := 2) (by simp)).trans length12
  have ikmPtr : t.regValue .r15 = initial.regValue .rcx := by
    have fromMov : u2.regValue .r15 = u1.regValue .rcx := e2.writes
    have afterMov := ((((f3.trans f4).trans f5).trans f6).trans afterTest).trans afterStore
    exact (afterMov.read (n := 64) (r := 15) (by simp)).trans
      (fromMov.trans ((entry.trans e1.agrees).read (n := 64) (r := 1)
        (by simp [Encoding.Serialize.saveFrame])))
  have ikmLen : t.regValue .r14 = initial.regValue .r8 := by
    have fromMov : u1.regValue .r14 = s.regValue .r8 := e1.writes
    have afterMov := (((((e2.agrees.trans f3).trans f4).trans f5).trans f6).trans afterTest).trans
      afterStore
    exact (afterMov.read (n := 64) (r := 14) (by simp)).trans
      (fromMov.trans (entry.read (n := 64) (r := 8) (by simp [Encoding.Serialize.saveFrame])))
  have saves : (Component.mem (stackPtr initial - 48) 56).Agrees s t := by
    rw [BitVec.sub_eq_add_neg]
    exact salt_apart all, [-376, -344, -352, -360, -368]
  have savedT : Saved initial t :=
    saved.of_agrees saves (all.mxcsr (by simp)) (all.fcw (by simp))
  have spill : memLoad t.external (base initial + 80) 64 = initial.regValue .rdi := by
    have rhs : base initial + 80 = stackPtr initial + (-376) := by unfold base; bv_omega
    rw [rhs]
    have same : (Component.mem (stackPtr initial + (-376)) 8).Agrees u3 t :=
      salt_apart ((((f4.trans f5).trans f6).trans afterTest).trans afterStore),
        [-344, -352, -360, -368]
    have fromStore : memLoad u3.external (stackPtr initial + (-376)) 64 = u2.regValue .rdi := by
      change memLoad u3.external (stackPtr initial - 376) 64 = u2.regValue .rdi at out3
      simpa only [BitVec.sub_eq_add_neg] using out3
    exact (agrees_memLoad same).trans (fromStore.trans
      ((entry.trans (e1.agrees.trans e2.agrees)).read (n := 64) (r := 7)
        (by simp [Encoding.Serialize.saveFrame])))
  have zeroOffsets : ∀ slot ∈ ([-368, -360, -352, -344] : List (BitVec 64)),
      memLoad t.external (stackPtr initial + slot) 64 = 0 := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · have same : (Component.mem (stackPtr initial + (-368)) 8).Agrees u10 t := by
        have memory := afterStore.external (by simp [Component.Covers])
        exact fun i _ ↦ congrArg (fun m : Ram ↦ m[stackPtr initial + (-368) + BitVec.ofNat 64 i]?) memory
      change memLoad u10.external (stackPtr initial - 368) 64 = 0 at z10
      exact (agrees_memLoad same).trans (by simpa only [BitVec.sub_eq_add_neg] using z10)
    · have same : (Component.mem (stackPtr initial + (-360)) 8).Agrees u6 t :=
        salt_apart (afterTest.trans afterStore), [-368]
      change memLoad u6.external (stackPtr initial - 360) 64 = 0 at z6
      exact (agrees_memLoad same).trans (by simpa only [BitVec.sub_eq_add_neg] using z6)
    · have same : (Component.mem (stackPtr initial + (-352)) 8).Agrees u5 t :=
        salt_apart ((f6.trans afterTest).trans afterStore), [-360, -368]
      change memLoad u5.external (stackPtr initial - 352) 64 = 0 at z5
      exact (agrees_memLoad same).trans (by simpa only [BitVec.sub_eq_add_neg] using z5)
    · have same : (Component.mem (stackPtr initial + (-344)) 8).Agrees u4 t :=
        salt_apart (((f5.trans f6).trans afterTest).trans afterStore), [-352, -360, -368]
      change memLoad u4.external (stackPtr initial - 344) 64 = 0 at z4
      exact (agrees_memLoad same).trans (by simpa only [BitVec.sub_eq_add_neg] using z4)
  refine ⟨t, ⟨⟨current, savedT, spT, spill⟩, ip13, ikmPtr, ikmLen, output, input, length, ?_⟩⟩
  intro j bound
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  all_goals
    simp only [saltAddress, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
    apply zeroOffsets
    simp

end Hkdf.Proofs.NewExpand.Extract.Normalize
