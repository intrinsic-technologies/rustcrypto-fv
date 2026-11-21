import AesGcm.Proofs.Machine.LIR.Fn102b80.Frame
import AesGcm.Proofs.Machine.GHASHUpdate.Memory
import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.Runtime.Guards
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def initializeStack (mem : Ram) (sp k0 k1 : BitVec 64) : Ram :=
  memStore (memStore (memStore (memStore mem (sp + 8) k1) sp k0) (sp + 16) (0#64))
    (sp + 24) (0#64)

def initializeState (mem : Ram) (dst k0 k1 : BitVec 64) : Ram :=
  memStore (memStore (memStore (memStore mem dst k0) (dst + 8) k1) (dst + 24) (0#64))
    (dst + 16) (0#64)

theorem initialize_store_guard (code : CodeMap) (mem : Ram) (a : BitVec 64)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (hw : Writable code mem a 8)
    (off len : Nat) (hb : off + len ≤ 69) :
    StoreOk code mem a 8 (0x102b80 + BitVec.ofNat 64 off) len := by
  apply storeOk_of_writable hw
  apply RangeApart.right_sub (storeOk_of_codeRange hw
    (fun x hx => hcode x (LIR.code_l102b80 x hx))).apart
  exact hb

theorem initialize_runBlock (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (src dst rsp : BitVec 64) (hsrc : args[6].get 64 = src)
    (hdst : args[7].get 64 = dst) (hsp : args[4].get 64 = rsp)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (htypes : GPRsTyped args)
    (hr : Readable mem src 16) (hw : Writable code mem dst 32)
    (hs : Writable code mem (rsp - 40) 40)
    (hret :
      let m := initializeState (initializeStack mem (rsp - 40)
        (memLoad mem src 64) (memLoad mem (src + 8) 64)) dst
        (memLoad mem src 64) (memLoad mem (src + 8) 64)
      LoadOk m rsp 8 ∧ (memLoad m rsp 64).toNat < 2^32) :
    ∃ o : Output Value Ram Reg.count,
      LIR.program.runBlock (dialect code) ⟨.l102b80, args, mem⟩ = .returned o ∧
      o.store = initializeState (initializeStack mem (rsp - 40)
        (memLoad mem src 64) (memLoad mem (src + 8) 64)) dst
        (memLoad mem src 64) (memLoad mem (src + 8) 64) ∧
      o.tag = some ⟨64, memLoad o.store rsp 64⟩ ∧
      o.values[4] = ⟨64, rsp + 8⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] → o.values[r] = args[r]) ∧
      GPRsTyped o.values := by
  have load0 : LoadOk mem src 8 := LoadOk.of_offsets hr (addr_self src) (addr_self src) (by decide)
  have load1 : LoadOk mem (src + 8) 8 := LoadOk.of_offsets hr rfl (addr_self src) (by decide)
  have slot (k : Fin 4) : Writable code mem ((rsp - 40) + BitVec.ofNat 64 (8*k.val)) 8 := by
    apply hs.of_offsets rfl (addr_self _)
    exact (by decide +kernel : ∀ k : Fin 4, (BitVec.ofNat 64 (8*k.val) - 0).toNat + 8 ≤ 40) k
  have target (k : Fin 4) : Writable code mem (dst + BitVec.ofNat 64 (8*k.val)) 8 := by
    apply hw.of_offsets rfl (addr_self _)
    exact (by decide +kernel : ∀ k : Fin 4, (BitVec.ofNat 64 (8*k.val) - 0).toNat + 8 ≤ 32) k
  have s1 := initialize_store_guard code mem _ hcode (slot 1) 14 5 (by decide)
  have s0 := initialize_store_guard code mem _ hcode (slot 0) 19 4 (by decide)
  have s2 := initialize_store_guard code mem _ hcode (slot 2) 23 9 (by decide)
  have s3 := initialize_store_guard code mem _ hcode (slot 3) 32 9 (by decide)
  have t0 := initialize_store_guard code mem _ hcode (target 0) 41 3 (by decide)
  have t1 := initialize_store_guard code mem _ hcode (target 1) 44 4 (by decide)
  have t3 := initialize_store_guard code mem _ hcode (target 3) 48 8 (by decide)
  have t2 := initialize_store_guard code mem _ hcode (target 2) 56 8 (by decide)
  have hs8 : rsp - 40 + 8 = rsp - 32 := by bv_omega
  have hs16 : rsp - 40 + 16 = rsp - 24 := by bv_omega
  have hs24 : rsp - 40 + 24 = rsp - 16 := by bv_omega
  change StoreOk code mem (rsp - 40 + 8) 8 0x102b8e 5 at s1
  change StoreOk code mem (rsp - 40 + 0) 8 0x102b93 4 at s0
  change StoreOk code mem (rsp - 40 + 16) 8 0x102b97 9 at s2
  change StoreOk code mem (rsp - 40 + 24) 8 0x102ba0 9 at s3
  change StoreOk code mem (dst + 0) 8 0x102ba9 3 at t0
  change StoreOk code mem (dst + 8) 8 0x102bac 4 at t1
  change StoreOk code mem (dst + 24) 8 0x102bb0 8 at t3
  change StoreOk code mem (dst + 16) 8 0x102bb8 8 at t2
  rw [hs8] at s1
  rw [hs16] at s2
  rw [hs24] at s3
  have hz (x : BitVec 64) : x + 0 = x := by bv_omega
  rw [hz] at s0 t0
  simp only [initializeState, initializeStack, hs8, hs16, hs24] at hret
  cfg_eval [hsrc, hdst, hsp]
  simp only [BitVec.ofNat_eq_ofNat] at hs8 hs16 hs24 hret load0 load1 s0 s1 s2 s3 t0 t1 t2 t3 ⊢
  simp (config := {bitVecOfNat := false, maxDischargeDepth := 20}) only
    [storeOk_memStore, s0, s1, s2, s3, t0, t1, t2, t3, load0, load1,
      hret, ↓reduceIte]
  refine ⟨_, rfl, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [initializeState, initializeStack, BitVec.ofNat_eq_ofNat, hs8, hs16, hs24]
  · rintro ⟨r, hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · apply GPRsTyped.of_updates htypes [0, 1, 2, 4]
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl <;> rfl
    · rintro ⟨r, hr⟩ hout
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
      have hc : r = 3 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨
          r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem initializeStack_frame {original mem : Ram} {regions : List MemoryRegion}
    (sp k0 k1 : BitVec 64) (hf : RamWriteFrame original mem regions)
    (hin : InRegions regions sp 32) :
    RamWriteFrame original (initializeStack mem sp k0 k1) regions := by
  have h0 : InRegions regions sp 8 := by
    have h := inRegions_add_offset (off := 0) hin (by decide : 0 < 8) (by decide)
    simpa using h
  have h8 := inRegions_add_offset (off := 8) hin (by decide : 0 < 8) (by decide)
  have h16 := inRegions_add_offset (off := 16) hin (by decide : 0 < 8) (by decide)
  have h24 := inRegions_add_offset (off := 24) hin (by decide : 0 < 8) (by decide)
  exact (((hf.memStore k1 h8).memStore k0 h0).memStore (0#64) h16).memStore (0#64) h24

theorem initializeState_frame {original mem : Ram} {regions : List MemoryRegion}
    (dst k0 k1 : BitVec 64) (hf : RamWriteFrame original mem regions)
    (hin : InRegions regions dst 32) :
    RamWriteFrame original (initializeState mem dst k0 k1) regions := by
  have h0 : InRegions regions dst 8 := by
    have h := inRegions_add_offset (off := 0) hin (by decide : 0 < 8) (by decide)
    simpa using h
  have h8 := inRegions_add_offset (off := 8) hin (by decide : 0 < 8) (by decide)
  have h16 := inRegions_add_offset (off := 16) hin (by decide : 0 < 8) (by decide)
  have h24 := inRegions_add_offset (off := 24) hin (by decide : 0 < 8) (by decide)
  exact (((hf.memStore k0 h0).memStore k1 h8).memStore (0#64) h24).memStore (0#64) h16

theorem initializeState_load (mem : Ram) (dst k0 k1 : BitVec 64) :
    memLoad (initializeState mem dst k0 k1) dst 64 = k0 ∧
    memLoad (initializeState mem dst k0 k1) (dst + 8) 64 = k1 ∧
    memLoad (initializeState mem dst k0 k1) (dst + 16) 64 = 0 ∧
    memLoad (initializeState mem dst k0 k1) (dst + 24) 64 = 0 := by
  have h20 (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (dst + 16) v) dst 64 = memLoad m dst 64 := by
    simpa [show BitVec.ofNat 64 (8 * (3 : Fin 4).val) = 24#64 from by decide +kernel] using memLoad_store_word4 m dst 2 0 v
  have h21 (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (dst + 16) v) (dst + 8) 64 = memLoad m (dst + 8) 64 := by
    simpa [show BitVec.ofNat 64 (8 * (3 : Fin 4).val) = 24#64 from by decide +kernel] using memLoad_store_word4 m dst 2 1 v
  have h22 (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (dst + 16) v) (dst + 16) 64 = v := by
    simpa [show BitVec.ofNat 64 (8 * (3 : Fin 4).val) = 24#64 from by decide +kernel] using memLoad_store_word4 m dst 2 2 v
  have h23 (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (dst + 16) v) (dst + 24) 64 = memLoad m (dst + 24) 64 := by
    simpa [show BitVec.ofNat 64 (8 * (3 : Fin 4).val) = 24#64 from by decide +kernel] using memLoad_store_word4 m dst 2 3 v
  have h30 (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (dst + 24) v) dst 64 = memLoad m dst 64 := by
    simpa [show BitVec.ofNat 64 (8 * (3 : Fin 4).val) = 24#64 from by decide +kernel] using memLoad_store_word4 m dst 3 0 v
  have h31 (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (dst + 24) v) (dst + 8) 64 = memLoad m (dst + 8) 64 := by
    simpa [show BitVec.ofNat 64 (8 * (3 : Fin 4).val) = 24#64 from by decide +kernel] using memLoad_store_word4 m dst 3 1 v
  have h33 (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (dst + 24) v) (dst + 24) 64 = v := by
    simpa [show BitVec.ofNat 64 (8 * (3 : Fin 4).val) = 24#64 from by decide +kernel] using memLoad_store_word4 m dst 3 3 v
  have h10 (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (dst + 8) v) dst 64 = memLoad m dst 64 := by
    simpa [show BitVec.ofNat 64 (8 * (3 : Fin 4).val) = 24#64 from by decide +kernel] using memLoad_store_word4 m dst 1 0 v
  have h11 (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (dst + 8) v) (dst + 8) 64 = v := by
    simpa [show BitVec.ofNat 64 (8 * (3 : Fin 4).val) = 24#64 from by decide +kernel] using memLoad_store_word4 m dst 1 1 v
  have h00 (m : Ram) (v : BitVec 64) :
      memLoad (memStore m dst v) dst 64 = v := by
    simpa [show BitVec.ofNat 64 (8 * (3 : Fin 4).val) = 24#64 from by decide +kernel] using memLoad_store_word4 m dst 0 0 v
  simp only [initializeState, h20, h21, h22, h23, h30, h31, h33, h10, h11, h00]
  simp


theorem initialize_call (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) :
    CallContract LIR.lifted code .l102b80 LIR.Fn102b80.frameInfo
      (fun fr ↦ [span fr.rdi 32])
      (fun fr mem ↦ Readable mem fr.rsi 16 ∧ Writable code mem fr.rdi 32 ∧
        (callStack fr).Disjoint (span fr.rsi 16) ∧
        (callStack fr).Disjoint (span fr.rdi 32))
      (fun fr mem ↦ memLoad mem fr.rdi 64 = memLoad fr.original fr.rsi 64 ∧
        memLoad mem (fr.rdi + 8) 64 = memLoad fr.original (fr.rsi + 8) 64 ∧
        memLoad mem (fr.rdi + 16) 64 = 0 ∧ memLoad mem (fr.rdi + 24) 64 = 0) := by
  intro fr loc hl hm hentry htypes hpre
  rcases loc with ⟨label, args, mem⟩
  dsimp only at hl hm hentry htypes hpre
  subst label mem
  change args[4] = ⟨64, fr.rsp⟩ ∧ args[22] = ⟨1, 0⟩ ∧ args[1] = ⟨64, fr.rcx⟩ ∧
    args[2] = ⟨64, fr.rdx⟩ ∧ args[3] = ⟨64, fr.rbx⟩ ∧ args[5] = ⟨64, fr.rbp⟩ ∧
    args[6] = ⟨64, fr.rsi⟩ ∧ args[7] = ⟨64, fr.rdi⟩ ∧ args[8] = ⟨64, fr.r8⟩ ∧
    args[9] = ⟨64, fr.r9⟩ ∧ args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
    args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
    args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
    Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
    fr.ret.toNat < 2^32 ∧ Writable code fr.original (fr.rsp - 40) 40 ∧
    fr.low.toNat + 40 ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧ True at hentry
  rcases hentry with ⟨hsp, hdf, -, -, h3, h5, hsrc, hdst, -, -, h12, h13, h14, h15,
    h39, h50, h51, hreadret, hret, hretlow, hstack, hroom, -, -⟩
  rcases hpre with ⟨hr, hw, _, hsep⟩
  have hsub : (fr.rsp - 40).toNat = fr.rsp.toNat - 40 := by
    have hle : (40 : BitVec 64) ≤ fr.rsp := by change 40 ≤ fr.rsp.toNat; omega
    simpa using BitVec.toNat_sub_of_le hle
  let regions := [fr.region, span fr.rdi 32]
  have hsIn : InRegions regions (fr.rsp - 40) 32 := by
    refine ⟨fr.region, by simp [regions], ?_⟩
    simp only [InRegion, Activation.region, hsub]
    have := fr.rsp.isLt
    omega
  have hdIn : InRegions regions fr.rdi 32 := by
    refine ⟨span fr.rdi 32, by simp [regions], ?_⟩
    have := hw.readable.low
    simp only [InRegion, span]
    omega
  let k0 := memLoad fr.original fr.rsi 64
  let k1 := memLoad fr.original (fr.rsi + 8) 64
  let finalMem := initializeState (initializeStack fr.original (fr.rsp - 40) k0 k1)
    fr.rdi k0 k1
  have hf : RamWriteFrame fr.original finalMem regions :=
    initializeState_frame _ _ _
      (initializeStack_frame _ _ _ (RamWriteFrame.refl _ _) hsIn) hdIn
  have hreturn : memLoad finalMem fr.rsp 64 = fr.ret := by
    rw [hf.memLoad_eq, hret]
    refine ⟨by have := hreadret.low; omega, ?_⟩
    intro r hin
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · simp only [Activation.region]
      omega
    · have hd := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
        fr.rdi.toNat 32 (by omega) (by decide) hsep
      simp only [span]
      omega
  have hrfinal := hreadret.of_frame hf
  obtain ⟨o, hrun, hmem, htag, houtsp, hregs, houtTypes⟩ :=
    initialize_runBlock code args fr.original fr.rsi fr.rdi fr.rsp
      (by rw [hsrc]; rfl) (by rw [hdst]; rfl) (by rw [hsp]; rfl)
      hcode htypes hr hw hstack
      ⟨⟨hrfinal.low, hrfinal.present⟩, by change (memLoad finalMem fr.rsp 64).toNat < _; rw [hreturn]; exact hretlow⟩
  change o.store = finalMem at hmem
  refine ⟨o, .done ?_, ?_, ?_, houtTypes, ?_, ?_⟩
  · change (LIR.program.runBlock (dialect code) ⟨.l102b80, args, fr.original⟩).next
      (dialect code) [] = .done o
    rw [hrun]
    rfl
  · rw [htag, hmem, hreturn]
  · change o.values[4] = ⟨64, fr.rsp + 8⟩ ∧ o.values[22] = ⟨1, 0⟩ ∧
      o.values[3] = ⟨64, fr.rbx⟩ ∧ o.values[5] = ⟨64, fr.rbp⟩ ∧
      o.values[12] = ⟨64, fr.r12⟩ ∧ o.values[13] = ⟨64, fr.r13⟩ ∧
      o.values[14] = ⟨64, fr.r14⟩ ∧ o.values[15] = ⟨64, fr.r15⟩ ∧
      o.values[39] = ⟨32, fr.mxcsr⟩ ∧ o.values[50] = ⟨16, fr.ftw⟩ ∧
      o.values[51] = ⟨16, fr.fcw⟩ ∧ True
    exact ⟨houtsp, (hregs 22 (by decide)).trans hdf,
      (hregs 3 (by decide)).trans h3, (hregs 5 (by decide)).trans h5,
      (hregs 12 (by decide)).trans h12, (hregs 13 (by decide)).trans h13,
      (hregs 14 (by decide)).trans h14, (hregs 15 (by decide)).trans h15,
      (hregs 39 (by decide)).trans h39, (hregs 50 (by decide)).trans h50,
      (hregs 51 (by decide)).trans h51, trivial⟩
  · rw [hmem]
    exact hf
  · rw [hmem]
    exact initializeState_load _ _ _ _

end AesGcm.Proofs.Machine.GHASHUpdate
