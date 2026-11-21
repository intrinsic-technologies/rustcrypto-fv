import P256.Proofs.Nonce.Initialize.Conversions.Bsr.Memory.Decode
import P256.Proofs.Nonce.Initialize.Conversions.Bsr.Memory.Form
import X86Proofs.Instructions.MovLoad.Step

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Nonce.Initialize.Conversions.Bsr

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem bsr64_memory_run [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hrep : ctx.rep_prefix = 0) (hsize : ctx.operand_size = 64) (haddr64 : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : AddrContext ctx am) (bytes : List UInt8) (k : Nat) (hk : k ≤ 2)
    (hopcode : bytes[k]? = some 0xbd) (hm : bytes[k + 1]? = some (am.modrm reg))
    (htail : ∀ j < am.tail.length, bytes[k + 2 + j]? = am.tail[j]?)
    (hlen : bytes.length = k + 2 + am.tail.length)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hread : MemReadable s (am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length))) 8) :
    let dst := gprNumber ctx.rex_r4 ctx.rex_r3 reg
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some (.ok (), writeOutputs (dataAccess (afterFetches (beforeFetch s) (bytes.length + 1)) "load")
        (.reg dst : Operand 64)
        (bsrSpec64 ((Operand.reg dst : Operand 64).read s)
          ((Operand.mem (am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length))) :
            Operand 64).read s))
        (bsrOracleUsed ((Operand.mem (am.addr s
          (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length))) : Operand 64).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length))) := by
  intro dst
  have hdecode := decodeLegacy1_run_of_bsr_memory s h ctx hrex2 hrep (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three)
    bytes k (by omega) hopcode hm hcode hlow
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hea := effectiveAddress_run (beforeFetch s) (k + 3) h.fetchReady h.cpu.ds h.cpu.ss am hv
    ctx hctx hc hlow (k + 2) htail (by omega) (by have := am.tail_length_le; omega)
  rw [show k + 3 + am.tail.length = bytes.length + 1 by omega,
    show k + 2 + am.tail.length = bytes.length by omega] at hea
  let t := afterFetches (beforeFetch s) (bytes.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have haddr : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length)) =
      am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length)) := AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length))
  rw [haddr] at hrip
  replace hea : (Effective_Address 64 ctx am.mod am.rm 1
      (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)))).run (afterFetches (beforeFetch s) (k + 3)) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 bytes.length), am.isRip, am.baseUsesRsp), t) := hea
  rw [bsr_r64_m64_form _ t _ _ _ _ _ hsize haddr64 hlock _ _ _ _ _ hea hrip ht hmode
    (hread.of_external_eq rfl)] at hdecode
  exact hdecode

theorem bsr_r64_m64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x0f :: 0xbd :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length))))
      8) :
    let dst := gprNumber 0 (rexR rex.toBitVec) reg
    X86.Machine.step s = some (.next (afterStep s (4 + am.tail.length) fun t =>
      writeOutputs (dataAccess t "load") (.reg dst : Operand 64)
        (bsrSpec64 ((Operand.reg dst : Operand 64).read t)
          ((Operand.mem (am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))) :
            Operand 64).read t))
        (bsrOracleUsed ((Operand.mem (am.addr s
          (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))) : Operand 64).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length))))) := by
  intro dst
  have hlen : (rex :: 0x0f :: 0xbd :: am.modrm reg :: am.tail : List UInt8).length =
      4 + am.tail.length := by simp only [List.length_cons]; omega
  have hlow' : s.RIP.toNat + (rex :: 0x0f :: 0xbd :: am.modrm reg :: am.tail : List UInt8).length
      ≤ 2^32 := by rw [hlen]; exact hlow
  have hdecode := bsr64_memory_run s h (rexContext s.DS rex.toBitVec) rfl rfl
    (hrex.operand_size s.DS) rfl rfl reg am hv (AddrContext.rex _ _ am hx hb) _ 2
    (by decide) rfl rfl
    (fun j _ => by rw [show 2 + 2 + j = j + 1 + 1 + 1 + 1 by omega]; rfl)
    (by simp only [List.length_cons]; omega) hcode hlow' (by rw [hlen]; exact hread)
  rw [hlen] at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (4 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0xbd _ hrex.rexPrefix (by decide) hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

end P256.Proofs.Nonce.Initialize.Conversions.Bsr
