import AesGcm.Proofs.Machine.CTR.Loop.Frame
import AesGcm.Proofs.Machine.CTR.Loop.CallResume
import AesGcm.Proofs.Machine.AES64.Sbox
import AesGcm.Proofs.Machine.AES64.MixColumns

namespace AesGcm.Proofs.Machine.CTR.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.Fixslice

def helperLabel (kind : Fin 3) : LIR.Label :=
  if kind = 0 then .l100e90 else if kind = 1 then .l1002a0 else .l100830

def helperFrame (kind : Fin 3) : FrameInfo :=
  if kind = 0 then LIR.Fn100e90.frameInfo
  else if kind = 1 then LIR.Fn1002a0.frameInfo else LIR.Fn100830.frameInfo

def helperTransform (kind : Fin 3) : Planes → Planes :=
  if kind = 0 then Fixslice.subBytes
  else if kind = 1 then Fixslice.mixColumns1 else Fixslice.mixColumns3

private theorem helper_contract (kind : Fin 3) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (planes : Planes) :
    CallContract LIR.lifted code (helperLabel kind) (helperFrame kind)
      (fun f => [span f.rdi 64])
      (fun f m => WordsAt m f.rdi 64 (Vector.ofFn planes) ∧
        (kind = 0 → f.rsi = 8) ∧ Writable code m f.rdi 64 ∧
        (callStack f).Disjoint (span f.rdi 64))
      (fun f m => WordsAt m f.rdi 64 (Vector.ofFn (helperTransform kind planes))) := by
  intro f loc hl hm he ht hp
  obtain ⟨hw, h6, hwrite, ha⟩ := hp
  have hk : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega
  rcases hk with rfl | rfl | rfl
  · obtain ⟨out, hexec, htag, hd, hot, hf, hp⟩ :=
      AES64.subBytes_callContract code hcode f loc hl hm he ht ⟨h6 rfl, hwrite, ha⟩
    refine ⟨out, hexec, htag, hd, hot, hf, ?_⟩
    have hi : (fun q : Fin 8 => memLoad f.original (f.rdi + BitVec.ofNat 64 (8 * q.val)) 64) =
        planes := by
      funext q
      rw [← hm]
      simpa only [wordAddr, Vector.getElem_ofFn] using hw q.val q.isLt
    intro i hi'
    simp only [Vector.getElem_ofFn]
    change _ = subBytes planes ⟨i, hi'⟩
    rw [← hi]
    exact hp ⟨i, hi'⟩
  · exact AES64.mixColumns1_call code hcode planes f loc hl hm he ht ⟨hw, hwrite.readable, hwrite, ha⟩
  · exact AES64.mixColumns3_call code hcode planes f loc hl hm he ht ⟨hw, hwrite.readable, hwrite, ha⟩

set_option maxHeartbeats 800000 in
theorem call_advance
    {use256 : Bool} {kind : Fin 3} {code : CodeMap} {fr : Activation}
    {args : Values Value Reg.count} {mem : Ram} {sp : BitVec 64}
    {words : Vector (BitVec 16) (keyWords use256)} {before callee : LIR.lifted.Location}
    {target : LIR.Label} {ret : BitVec 64} {planes : Planes}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hw : CipherWorkingState use256 code fr args mem sp words before)
    (hcall : LIR.program.runBlock (dialect code) before = .call callee
      {target := target, kept := #v[], arity := rfl, guard := some ⟨64, ret⟩})
    (hl : callee.label = helperLabel kind)
    (ht : GPRsTyped callee.arguments)
    (h4 : callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp - 8⟩)
    (h7 : callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, sp + 8⟩)
    (h6 : kind = 0 → callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, 8⟩)
    (hs : ∀ r : Fin 53, r.val ∈ [22,39,50,51] → callee.arguments[r] = before.arguments[r])
    (hret : memLoad callee.store (sp - 8) 64 = ret) (hretLow : ret.toNat < 2 ^ 32)
    (hf : RamWriteFrame before.store callee.store [span (sp - 296) 512, span (sp + 224) 8])
    (hc : memLoad callee.store (sp + 224) 64 = memLoad before.store (sp + 224) 64)
    (hwords : WordsAt callee.store (sp + 8) 64 (Vector.ofFn planes)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨before, []⟩ ⟨next, []⟩ ∧
      CipherWorkingState use256 code fr args mem sp words next ∧
      next.label = target ∧
      WordsAt next.store (sp + 8) 64 (Vector.ofFn (helperTransform kind planes)) ∧
      ∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] →
        next.arguments[r] = callee.arguments[r] := by
  let af := activationOfValues callee.store callee.arguments ret (sp - 296)
  have hsp : af.rsp = sp - 8 := congrArg (Value.get 64) h4
  have hbuf : af.rdi = sp + 8 := congrArg (Value.get 64) h7
  have hlow : af.low = sp - 296 := rfl
  have hstack := hw.stack.of_frame hf
  have low := hw.stack.readable.low
  have sub : (sp - 296).toNat + 296 = sp.toNat := by bv_omega
  have retNat : (sp - 8).toNat + 8 = sp.toNat := by bv_omega
  have bufNat : (sp + 8).toNat = sp.toNat + 8 := by bv_omega
  have countNat : (sp + 224).toNat = sp.toNat + 224 := by bv_omega
  have hwrite : Writable code callee.store af.rdi 64 := by
    rw [hbuf]; exact hstack.sub (by omega) (by omega)
  have hap : (callStack af).Disjoint (span af.rdi 64) := by
    intro x hx hy
    simp only [callStack, span, MemoryRegion.Contains, hsp, hlow, hbuf] at hx hy
    omega
  have hk : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega
  have win : (helperFrame kind).window = 288 ∨ (helperFrame kind).window = 96 := by
    rcases hk with rfl | rfl | rfl <;> decide
  have hslots : Atom.All code callee.arguments callee.store
      ((helperFrame kind).callSlotAtoms (helperFrame kind).callSlots af) := by
    rcases hk with rfl | rfl | rfl
    · have hb := hw.slotsApart
      have hgt : 0x201358 ≤ af.rsp.toNat ∨ af.rsp.toNat ≤ 0x201210 := by
        rw [hsp]
        cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hb <;> omega
      exact ⟨hw.slot1Readable.of_frame hf,
        (hf.memLoad_eq (native_slot_outside hw _ (by decide) (by decide))).trans hw.slot1Value,
        hw.slot2Readable.of_frame hf,
        (hf.memLoad_eq (native_slot_outside hw _ (by decide) (by decide))).trans hw.slot2Value,
        hgt, trivial⟩
    · trivial
    · trivial
  have h39 : callee.arguments[39]'(by change 39 < 53; decide) = before.arguments[39]'(by change 39 < 53; decide) := hs 39 (by decide)
  have h50 : callee.arguments[50]'(by change 50 < 53; decide) = before.arguments[50]'(by change 50 < 53; decide) := hs 50 (by decide)
  have h51 : callee.arguments[51]'(by change 51 < 53; decide) = before.arguments[51]'(by change 51 < 53; decide) := hs 51 (by decide)
  have t39 : callee.arguments[39]'(by change 39 < 53; decide) = ⟨32, (callee.arguments[39]'(by change 39 < 53; decide)).get 32⟩ := by
    rw [h39]; exact hw.x87.1
  have t50 : callee.arguments[50]'(by change 50 < 53; decide) = ⟨16, (callee.arguments[50]'(by change 50 < 53; decide)).get 16⟩ := by
    rw [h50]; exact hw.x87.2.1
  have t51 : callee.arguments[51]'(by change 51 < 53; decide) = ⟨16, (callee.arguments[51]'(by change 51 < 53; decide)).get 16⟩ := by
    rw [h51]; exact hw.x87.2.2
  have df := (hs 22 (by decide)).trans hw.df
  obtain ⟨out, hex, htag, hd, hout, hframe, hp⟩ :=
    callContract_exec_values LIR.lifted code _ _ _ _ _ (helper_contract kind code hcode planes)
      callee.store callee.arguments ret (sp - 296) ht t39 t50 t51 df
      (by change Readable _ af.rsp 8; rw [hsp]; exact hstack.readable.sub (by omega) (by omega))
      (by change memLoad _ af.rsp 64 = ret; rwa [hsp]) hretLow
      (by intro _; change Writable _ _ (af.rsp - _) _; rw [hsp]; rcases win with h | h <;> rw [h]
          all_goals apply hstack.sub <;> bv_omega)
      (by change _ + _ ≤ af.rsp.toNat; rw [hsp]; omega)
      (by change af.rsp.toNat % 16 = 8; rw [hsp]; have := hw.aligned; omega)
      hslots ⟨by change WordsAt _ af.rdi _ _; rwa [hbuf],
        fun h => congrArg (Value.get 64) (h6 h), hwrite, hap⟩
  change WordsAt out.store af.rdi 64 _ at hp
  rw [hbuf] at hp
  change RamWriteFrame callee.store out.store [af.region, span af.rdi 64] at hframe
  have hd' : out.values[4] = ⟨64, af.rsp + 8⟩ ∧ out.values[22] = ⟨1, 0⟩ ∧
      out.values[3] = ⟨64, af.rbx⟩ ∧ out.values[5] = ⟨64, af.rbp⟩ ∧
      out.values[12] = ⟨64, af.r12⟩ ∧ out.values[13] = ⟨64, af.r13⟩ ∧
      out.values[14] = ⟨64, af.r14⟩ ∧ out.values[15] = ⟨64, af.r15⟩ ∧
      out.values[39] = ⟨32, af.mxcsr⟩ ∧ out.values[50] = ⟨16, af.ftw⟩ ∧
      out.values[51] = ⟨16, af.fcw⟩ ∧ True := by
    rcases hk with rfl | rfl | rfl <;> exact hd
  rcases hd' with ⟨o4, o22, o3, o5, o12, o13, o14, o15, o39, o50, o51, _⟩
  have same (r : Fin 53) (hr : r.val ∈ [3,5,12,13,14,15,22,39,50,51]) :
      out.values[r] = callee.arguments[r] := by
    rcases r with ⟨r, hrlt⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact o3.trans (ht.value 3).symm
    · exact o5.trans (ht.value 5).symm
    · exact o12.trans (ht.value 12).symm
    · exact o13.trans (ht.value 13).symm
    · exact o14.trans (ht.value 14).symm
    · exact o15.trans (ht.value 15).symm
    · exact o22.trans df.symm
    · exact o39.trans t39.symm
    · exact o50.trans t50.symm
    · exact o51.trans t51.symm
  have whole := hf.trans hframe (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine ⟨span (sp - 296) 512, by simp, ?_, ?_⟩ <;>
      simp only [Activation.region, span, hsp, hlow, hbuf] <;> omega)
  have count : memLoad out.store (sp + 224) 64 = memLoad callee.store (sp + 224) 64 := by
    apply hframe.memLoad_eq
    refine ⟨by change (sp + 224).toNat + 8 ≤ 2^64; omega, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> right <;>
      simp only [Activation.region, span, hsp, hlow, hbuf] <;> omega
  refine ⟨⟨target, out.values, out.store⟩, call_contract_resume (code := code) (caller := before) (callee := callee) (output := out) hcall hl hex htag, ?_, rfl, hp, same⟩
  refine native_frame (after := ⟨target, out.values, out.store⟩) hw hout ?_ ?_ whole (count.trans hc)
  · change out.values[4] = ⟨64, sp⟩
    rw [o4, hsp, show sp - 8 + 8 = sp by bv_omega]
  · intro r hr
    exact (same r (List.mem_append_right [3,5,12,13,14,15] hr)).trans (hs r hr)

theorem pushed_call_advance
    {use256 : Bool} {kind : Fin 3} {code : CodeMap} {fr : Activation}
    {args : Values Value Reg.count} {mem : Ram} {sp : BitVec 64}
    {words : Vector (BitVec 16) (keyWords use256)} {before callee : LIR.lifted.Location}
    {target : LIR.Label} {ret : BitVec 64} {planes : Planes}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hw : CipherWorkingState use256 code fr args mem sp words before)
    (hcall : LIR.program.runBlock (dialect code) before = .call callee
      {target := target, kept := #v[], arity := rfl, guard := some ⟨64, ret⟩})
    (hl : callee.label = helperLabel kind)
    (ht : GPRsTyped callee.arguments)
    (h4 : callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp - 8⟩)
    (h7 : callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, sp + 8⟩)
    (h6 : kind = 0 → callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, 8⟩)
    (hstore : callee.store = memStore before.store (sp - 8) ret)
    (hkeep : ∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] →
      callee.arguments[r] = before.arguments[r])
    (hpush : RamWriteFrame before.store callee.store [span (sp - 8) 8])
    (hretLow : ret.toNat < 2^32)
    (hwords : WordsAt before.store (sp + 8) 64 (Vector.ofFn planes)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨before, []⟩ ⟨next, []⟩ ∧
      CipherWorkingState use256 code fr args mem sp words next ∧
      next.label = target ∧
      WordsAt next.store (sp + 8) 64 (Vector.ofFn (helperTransform kind planes)) ∧
      ∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] →
        next.arguments[r] = before.arguments[r] := by
  have low := hw.stack.readable.low
  have hf0 : RamWriteFrame before.store callee.store [span (sp - 296) 512] := by
    apply (RamWriteFrame.refl _ _).trans hpush
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;> simp only [span] <;> bv_omega
  obtain ⟨hf, hc⟩ := native_frame_of_scratch hw hf0
  have ho : Outside [span (sp - 8) 8] (sp + 8) 64 := by
    refine ⟨by bv_omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    change (sp - 8).toNat + 8 ≤ (sp + 8).toNat
    bv_omega
  have hr : memLoad callee.store (sp - 8) 64 = ret := by
    rw [hstore]
    exact memLoad_memStore_eq _ _ rfl (by decide) (by decide)
  obtain ⟨next, reaches, hn, hlabel, hplanes, hsame⟩ :=
    call_advance hcode hw hcall hl ht h4 h7 h6
      (fun r h => hkeep r (List.mem_append_right [3,5,12,13,14,15] h))
      hr hretLow hf hc (hwords.of_frame hpush (by decide) ho)
  refine ⟨next, reaches, hn, hlabel, hplanes, ?_⟩
  intro r h
  by_cases h4' : r = 4
  · subst r
    exact hn.stackPointer.trans hw.stackPointer.symm
  · have h' : r.val ∈ [3,5,12,13,14,15,22,39,50,51] := by
      have hn4 : r.val ≠ 4 := fun h => h4' (Fin.ext h)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      omega
    exact (hsame r h').trans (hkeep r h')

end AesGcm.Proofs.Machine.CTR.Loop
