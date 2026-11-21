import Sha3.Proofs.Permutation.LoadStore.Memory
import Sha3.Proofs.X86.Instructions.MemAlu.Step

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_89_memory [Bindings] (s : RamState) (h : ReadyToStep s) (bytes : List UInt8)
    (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some 0x89)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.MOV_MEMv_GPRv_1 (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0x89 modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcode89 a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe => decodeLegacy0Opcode89_run_of_memory a u _ ctx _ hmod hmode hfe hf)

theorem mov_scan_m_r_step_of_readable [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 2 + am.tail.length)) (n / 8)) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := am.addrAt s (pre.length + 2 + am.tail.length)
    let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t ↦
      writeResult (dataAccess t "store") (.mem addr : Operand n) (movSpec (src.read t))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x89 :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by
    simp only [List.length_append, List.length_cons]
    omega
  have hlow' : s.RIP.toNat + (pre ++ 0x89 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_89_memory s h _ pre.length (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow' (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) ctx hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea s h pre 0x89 reg am hv [] ctx hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [mov_m_r_form_of_readable _ t _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ hea hrip (memAlu_dataReady h _) hmode
    (hread.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x89 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem mov_m32_r32_legacy_step_of_readable [Bindings] (s : RamState) (h : ReadyToStep s)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32)
    (hw : MemReadable s (am.addrAt s (2 + am.tail.length)) 4) :
    X86.Machine.step s = some (.next (afterStep s (2 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (2 + am.tail.length)) : Operand 32)
        (movSpec ((Operand.reg (gprNumber 0 0 reg) : Operand 32).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))))) := by
  exact mov_scan_m_r_step_of_readable s h [] (by simp) (by simp) 32 (.inr rfl)
    rfl rfl rfl rfl reg am hv (AddrContext.legacy _ am hx hb) hcode hlow hw

theorem mov_m32_r32_legacy_effect_step_of_readable [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePreReadable p (storeAddrAt p am (2 + am.tail.length)) 4)
      (codeRange p (0x89 :: am.modrm reg :: am.tail))
      (storeEffect p (2 + am.tail.length) (storeAddrAt p am (2 + am.tail.length))
        (fun s => (Operand.reg (gprNumber 0 0 reg) : Operand 32).read s)) := by
  refine StepEffect.of_store_readable (n := 32) (by decide) (by decide) _ _
    (fun _ h => h.2) ?_
  intro s h hcode hpre
  obtain ⟨⟨hp, hw⟩, _⟩ := hpre
  subst hp
  have := am.tail_length_le
  exact mov_m32_r32_legacy_step_of_readable s h reg am hv hx hb hcode.bytesAt
    (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

theorem mov_m32_r32_effect_step_of_readable [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePreReadable p (storeAddrAt p am (3 + am.tail.length)) 4)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM32R32Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) :=
  StepEffect.of_store_readable (n := 32) (by decide) (by decide) _ _ (fun _ h => h.2)
    fun s h hcode hpre => by
      obtain ⟨⟨hp, hw⟩, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m32_r32_step_of_readable s h rex hrex reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

end X86Proofs
