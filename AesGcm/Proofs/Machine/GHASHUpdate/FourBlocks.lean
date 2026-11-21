import AesGcm.Proofs.Machine.GHASHInterface
import AesGcm.Proofs.Machine.GHASHUpdate.MultiplyValues
import AesGcm.Proofs.Machine.GHASHUpdate.Memory
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Guards
import AesGcm.Proofs.Machine.LIR.Fn1034d0.Frame

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASHInterface
open AesGcm.Proofs.Machine.GHASH

def fourMiddleLabel : Bool → LIR.Label
  | false => .l1034e6
  | true => .l1034f6

def fourMiddleReturn : Bool → LIR.Label
  | false => .l1034f6
  | true => .l103506

def fourMiddleReturnAddress : Bool → BitVec 64
  | false => 0x1034f6
  | true => 0x103506

def fourMiddleOffset : Bool → BitVec 64
  | false => 16
  | true => 32

def fourMiddleFrame (second : Bool) : StackFrame Value LIR.Label signature Reg.count :=
  { target := fourMiddleReturn second, kept := #v[], arity := rfl,
    guard := some ⟨64, fourMiddleReturnAddress second⟩ }

theorem fourBlock_middle_runBlock (second : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (src dst sp : BitVec 64) (hsrc : args[3].get 64 = src)
    (hdst : args[14].get 64 = dst) (hsp : args[4].get 64 = sp)
    (hr : Readable mem src 64) (hw : Writable code mem (sp - 8) 8)
    (htypes : GPRsTyped args) :
    ∃ nextArgs : Values Value Reg.count,
      LIR.program.runBlock (dialect code) ⟨fourMiddleLabel second, args, mem⟩ =
        .call ⟨.l102bd0, nextArgs, memStore mem (sp - 8) (fourMiddleReturnAddress second)⟩
          (fourMiddleFrame second) ∧
      nextArgs[2] = ⟨64, memLoad mem (src + fourMiddleOffset second + 8) 64⟩ ∧
      nextArgs[6] = ⟨64, memLoad mem (src + fourMiddleOffset second) 64⟩ ∧
      nextArgs[7] = ⟨64, dst⟩ ∧ nextArgs[4] = ⟨64, sp - 8⟩ ∧
      (∀ r : Fin 53, r.val ∈ [1, 3, 5, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51] →
        nextArgs[r] = args[r]) ∧ GPRsTyped nextArgs := by
  have read16 : LoadOk mem (src + 16) 8 := LoadOk.of_offsets hr rfl (addr_self _) (by decide)
  have read24 : LoadOk mem (src + 24) 8 := LoadOk.of_offsets hr rfl (addr_self _) (by decide)
  have read32 : LoadOk mem (src + 32) 8 := LoadOk.of_offsets hr rfl (addr_self _) (by decide)
  have read40 : LoadOk mem (src + 40) 8 := LoadOk.of_offsets hr rfl (addr_self _) (by decide)
  have store1 : StoreOk code mem (sp - 8) 8 0x1034f1 5 := by
    apply storeOk_of_writable hw
    exact RangeApart.right_sub (storeOk_of_codeRange hw
      (fun x hx => hcode x (LIR.code_l1034e6 x hx))).apart (off := 11) (by decide)
  have store2 : StoreOk code mem (sp - 8) 8 0x103501 5 := by
    apply storeOk_of_writable hw
    exact RangeApart.right_sub (storeOk_of_codeRange hw
      (fun x hx => hcode x (LIR.code_l1034f6 x hx))).apart (off := 11) (by decide)
  have a1 : src + 16 + 8 = src + 24 := by bv_omega
  have a2 : src + 32 + 8 = src + 40 := by bv_omega
  cases second <;> dsimp only [fourMiddleLabel]
  all_goals cfg_eval [hsrc, hdst, hsp]
  all_goals simp only [BitVec.ofNat_eq_ofNat] at read16 read24 read32 read40 store1 store2 a1 a2 ⊢
  all_goals simp only [read16, read24, read32, read40, store1, store2, ite_true]
  all_goals refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_, ?_⟩
  all_goals first
    | (solve | simp only [fourMiddleOffset, BitVec.ofNat_eq_ofNat, a1, a2]; rfl)
    | (rintro ⟨r, hr⟩ hin
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
       rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    | (apply GPRsTyped.of_updates htypes [2, 4, 6, 7]
       · rintro ⟨r, hr⟩ hin
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
         rcases hin with rfl | rfl | rfl | rfl <;> rfl
       · rintro ⟨r, hr⟩ hout
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
         have hc : r = 0 ∨ r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨
             r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by omega
         rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

def fourSavedMemory (mem : Ram) (rsp v14 v3 v0 : BitVec 64) : Ram :=
  memStore (memStore (memStore mem (rsp - 8) v14) (rsp - 16) v3) (rsp - 24) v0

theorem fourSavedMemory_frame (mem : Ram) (rsp v14 v3 v0 : BitVec 64)
    (hroom : 24 ≤ rsp.toNat) :
    RamWriteFrame mem (fourSavedMemory mem rsp v14 v3 v0) [span (rsp - 24) 24] := by
  have h24 : (rsp - 24).toNat = rsp.toNat - 24 := by
    have hle : (24 : BitVec 64) ≤ rsp := hroom
    simpa using BitVec.toNat_sub_of_le hle
  have slot (k : Nat) (hk : k ∈ [8,16,24]) :
      InRegions [span (rsp - 24) 24] (rsp - BitVec.ofNat 64 k) 8 := by
    have hb : 8 ≤ k ∧ k ≤ 24 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      omega
    have hklt : k < 2^64 := by omega
    have hle : BitVec.ofNat 64 k ≤ rsp := by
      change (BitVec.ofNat 64 k).toNat ≤ rsp.toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hklt]
      omega
    refine ⟨span (rsp - 24) 24, by simp, ?_⟩
    simp only [InRegion, span, h24, BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hklt]
    have := rsp.isLt
    omega
  exact (((RamWriteFrame.refl mem _).memStore v14 (slot 8 (by decide))).memStore v3
    (slot 16 (by decide))).memStore v0 (slot 24 (by decide))

theorem fourSavedMemory_load (mem : Ram) (rsp v14 v3 v0 : BitVec 64) :
    memLoad (fourSavedMemory mem rsp v14 v3 v0) (rsp - 16) 64 = v3 ∧
    memLoad (fourSavedMemory mem rsp v14 v3 v0) (rsp - 8) 64 = v14 := by
  have a2416 : RangeApart (rsp - 24) 8 (rsp - 16) 8 :=
    RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have a248 : RangeApart (rsp - 24) 8 (rsp - 8) 8 :=
    RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have a168 : RangeApart (rsp - 16) 8 (rsp - 8) 8 :=
    RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  constructor
  · simp only [fourSavedMemory]
    rw [memLoad_memStore_of_rangeApart _ _ _ _ 64 a2416]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · simp only [fourSavedMemory]
    rw [memLoad_memStore_of_rangeApart _ _ _ _ 64 a248,
      memLoad_memStore_of_rangeApart _ _ _ _ 64 a168]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)


def fourEntryFrame : StackFrame Value LIR.Label signature Reg.count :=
  { target := .l1034e6, kept := #v[], arity := rfl, guard := some ⟨64, 0x1034e6⟩ }

theorem fourBlock_entry_runBlock (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (src dst rsp : BitVec 64) (hsrc : args[6].get 64 = src)
    (hdst : args[7].get 64 = dst) (hsp : args[4].get 64 = rsp)
    (hr : Readable mem src 64) (hw : Writable code mem (rsp - 160) 160)
    (htypes : GPRsTyped args) :
    let saved := fourSavedMemory mem rsp (args[14].get 64) (args[3].get 64) (args[0].get 64)
    ∃ nextArgs : Values Value Reg.count,
      LIR.program.runBlock (dialect code) ⟨.l1034d0, args, mem⟩ =
        .call ⟨.l102bd0, nextArgs, memStore saved (rsp - 32) (0x1034e6#64)⟩ fourEntryFrame ∧
      nextArgs[2] = ⟨64, memLoad saved (src + 8) 64⟩ ∧
      nextArgs[6] = ⟨64, memLoad saved src 64⟩ ∧
      nextArgs[3] = ⟨64, src⟩ ∧ nextArgs[14] = ⟨64, dst⟩ ∧
      nextArgs[4] = ⟨64, rsp - 32⟩ ∧
      (∀ r : Fin 53, r.val ∈ [1, 5, 7, 8, 9, 12, 13, 15, 22, 39, 50, 51] →
        nextArgs[r] = args[r]) ∧ GPRsTyped nextArgs := by
  have load0 : LoadOk mem src 8 := LoadOk.of_offsets hr (addr_self _) (addr_self _) (by decide)
  have load1 : LoadOk mem (src + 8) 8 := LoadOk.of_offsets hr rfl (addr_self _) (by decide)
  have slot (k : Fin 4) : Writable code mem (rsp - BitVec.ofNat 64 (8 * (k.val+1))) 8 := by
    apply hw.of_offsets (addr_sub _ _) (addr_sub _ _)
    exact (by decide +kernel : ∀ k : Fin 4,
      ((0 - BitVec.ofNat 64 (8*(k.val+1))) - (0 - 160#64)).toNat + 8 ≤ 160) k
  have guard (k : Fin 4) (off len : Nat) (hb : off + len ≤ 22) :
      StoreOk code mem (rsp - BitVec.ofNat 64 (8*(k.val+1))) 8
        (0x1034d0 + BitVec.ofNat 64 off) len := by
    apply storeOk_of_writable (slot k)
    exact RangeApart.right_sub (storeOk_of_codeRange (slot k)
      (fun x hx => hcode x (LIR.code_l1034d0 x hx))).apart hb
  have s0 := guard 0 0 2 (by decide)
  have s1 := guard 1 2 1 (by decide)
  have s2 := guard 2 3 1 (by decide)
  have s3 := guard 3 17 5 (by decide)
  change StoreOk code mem (rsp - 8) 8 0x1034d0 2 at s0
  change StoreOk code mem (rsp - 16) 8 0x1034d2 1 at s1
  change StoreOk code mem (rsp - 24) 8 0x1034d3 1 at s2
  change StoreOk code mem (rsp - 32) 8 0x1034e1 5 at s3
  dsimp only
  cfg_eval [hsrc, hdst, hsp]
  simp only [BitVec.ofNat_eq_ofNat] at s0 s1 s2 s3 load0 load1 ⊢
  simp (config := {bitVecOfNat := false, maxDischargeDepth := 20}) only
    [storeOk_memStore, loadOk_memStore, s0, s1, s2, s3, load0, load1, ite_true]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rintro ⟨r, hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · apply GPRsTyped.of_updates htypes [2, 3, 4, 6, 14]
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl <;> rfl
    · rintro ⟨r, hr⟩ hout
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
      have hc : r = 0 ∨ r = 1 ∨ r = 5 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨
          r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 15 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl


theorem fourBlock_tail_runBlock (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (src dst sp : BitVec 64) (hsrc : args[3].get 64 = src)
    (hdst : args[14].get 64 = dst) (hsp : args[4].get 64 = sp)
    (hr : Readable mem src 64) (hs : Readable mem sp 24) (htypes : GPRsTyped args) :
    ∃ nextArgs : Values Value Reg.count,
      LIR.program.runBlock (dialect code) ⟨.l103506, args, mem⟩ =
        .jump ⟨.l102bd0, nextArgs, mem⟩ ∧
      nextArgs[2] = ⟨64, memLoad mem (src + 56) 64⟩ ∧
      nextArgs[6] = ⟨64, memLoad mem (src + 48) 64⟩ ∧
      nextArgs[7] = ⟨64, dst⟩ ∧ nextArgs[4] = ⟨64, sp + 24⟩ ∧
      nextArgs[3] = ⟨64, memLoad mem (sp + 8) 64⟩ ∧
      nextArgs[14] = ⟨64, memLoad mem (sp + 16) 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [1, 5, 8, 9, 12, 13, 15, 22, 39, 50, 51] →
        nextArgs[r] = args[r]) ∧ GPRsTyped nextArgs := by
  have read48 : LoadOk mem (src + 48) 8 := LoadOk.of_offsets hr rfl (addr_self _) (by decide)
  have read56 : LoadOk mem (src + 56) 8 := LoadOk.of_offsets hr rfl (addr_self _) (by decide)
  have read8 : LoadOk mem (sp + 8) 8 := LoadOk.of_offsets hs rfl (addr_self _) (by decide)
  have read16 : LoadOk mem (sp + 16) 8 := LoadOk.of_offsets hs rfl (addr_self _) (by decide)
  cfg_eval [hsrc, hdst, hsp]
  simp only [BitVec.ofNat_eq_ofNat] at read48 read56 read8 read16 ⊢
  simp only [read48, read56, read8, read16, ite_true]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rintro ⟨r, hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · apply GPRsTyped.of_updates htypes [2, 3, 4, 6, 7, 14]
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rintro ⟨r, hr⟩ hout
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
      have hc : r = 0 ∨ r = 1 ∨ r = 5 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨
          r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 15 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl


theorem fourBlock_middle_exec (second : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (hmultiply : MultiplyContract code)
    (args : Values Value Reg.count) (mem : Ram) (src dst sp low : BitVec 64)
    (hsrc : args[3].get 64 = src) (hdst : args[14].get 64 = dst) (hsp : args[4].get 64 = sp)
    (htypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩)
    (hdf : args[22] = ⟨1, 0⟩)
    (hr : Readable mem src 64) (hstack : Writable code mem (sp - 136) 136)
    (hroom : low.toNat + 136 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hw : Writable code mem dst 32)
    (hsep : (⟨low.toNat, sp.toNat - low.toNat⟩ : MemoryRegion).Disjoint (span dst 32)) :
    ∃ o : Output Value Ram Reg.count,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨fourMiddleLabel second, args, mem⟩, []⟩
        ⟨⟨fourMiddleReturn second, o.values, o.store⟩, []⟩ ∧
      o.values[4] = ⟨64, sp⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] → o.values[r] = args[r]) ∧
      GPRsTyped o.values ∧
      RamWriteFrame mem o.store [⟨low.toNat, sp.toNat - low.toNat⟩, span (dst + 16) 16] ∧
      (let result := polyvalMultiplyWords
          (memLoad mem (src + fourMiddleOffset second) 64 ^^^ memLoad mem (dst + 16) 64)
          (memLoad mem (src + fourMiddleOffset second + 8) 64 ^^^ memLoad mem (dst + 24) 64)
          (memLoad mem dst 64) (memLoad mem (dst + 8) 64)
       memLoad o.store (dst + 16) 64 = result.1 ∧ memLoad o.store (dst + 24) 64 = result.2) := by
  have hwret : Writable code mem (sp - 8) 8 :=
    hstack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  obtain ⟨nextArgs, hcall, h2, h6, h7, h4, hkeep, htypes'⟩ :=
    fourBlock_middle_runBlock second code hcode args mem src dst sp hsrc hdst hsp hr hwret htypes
  have keep39 := hkeep 39 (by decide)
  have keep50 := hkeep 50 (by decide)
  have keep51 := hkeep 51 (by decide)
  have keep22 := hkeep 22 (by decide)
  change nextArgs[39] = args[39] at keep39
  change nextArgs[50] = args[50] at keep50
  change nextArgs[51] = args[51] at keep51
  change nextArgs[22] = args[22] at keep22
  obtain ⟨o, hexec, htag, hspout, hpres, htypesout, hframe, hpost⟩ :=
    multiply_pushed code hmultiply mem nextArgs sp dst (fourMiddleReturnAddress second) low
      (by rw [h4]; rfl) (by rw [h7]; rfl) htypes'
      (by rw [keep39]; exact h39) (by rw [keep50]; exact h50) (by rw [keep51]; exact h51)
      (keep22.trans hdf) (by cases second <;> decide) hstack hroom halign hw hsep
  have ha : (fourMiddleFrame second).Accepts (dialect code) o.tag = true := by
    rw [htag]
    cases second <;> rfl
  have hresume := CFGCall.exec_reaches_resume hexec (fourMiddleFrame second) [] ha
  have hreach : (LIR.program.sem (dialect code)).Reaches
      ⟨⟨fourMiddleLabel second, args, mem⟩, []⟩
      ⟨⟨fourMiddleReturn second, o.values, o.store⟩, []⟩ := by
    have hstep : LIR.program.step (dialect code)
        ⟨⟨fourMiddleLabel second, args, mem⟩, []⟩ =
        .next ⟨⟨.l102bd0, nextArgs, memStore mem (sp - 8) (fourMiddleReturnAddress second)⟩,
          [fourMiddleFrame second]⟩ := by
      rw [Program.step, hcall]
      rfl
    exact (Semantics.Reaches.single hstep).trans hresume
  refine ⟨o, hreach, hspout, ?_, htypesout, hframe, ?_⟩
  · intro r hr
    apply (hpres r hr).trans
    apply hkeep
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    omega
  · have e2 : nextArgs[2].get 64 = memLoad mem (src + fourMiddleOffset second + 8) 64 := by
      rw [h2]; rfl
    have e6 : nextArgs[6].get 64 = memLoad mem (src + fourMiddleOffset second) 64 := by
      rw [h6]; rfl
    simpa only [e2, e6] using hpost


end AesGcm.Proofs.Machine.GHASHUpdate
