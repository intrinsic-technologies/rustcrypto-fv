import X86Proofs.Instructions.MovStore.Step
import P256.Proofs.Common.Instructions.Setb.Memory.Decode
import P256.Proofs.Common.Instructions.Setb.Memory.Form

namespace P256.Proofs.Common.Instructions.Setb

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem setcc_m8_scan_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (opcode : UInt8) (hop : SupportedOpcode opcode)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: opcode :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (am.addrAt s (pre.length + 3 + am.tail.length)) 1) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store")
        (.mem (am.addrAt s (pre.length + 3 + am.tail.length)) : Operand 8)
        (setccValue (opcode.toBitVec.extractLsb' 0 4) s)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  have h5 := am.tail_length_le
  have hlow' : s.RIP.toNat + (pre ++ 0x0F :: opcode :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons]; omega
  have hdecode := decodeLegacy1_run_of_setcc_memory s h (scanContext s.DS (PrefixSegments.ofState s) pre) hrex2
    (am.modrm reg) opcode hop (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three)
    _ (pre.length + 1) (by omega)
    (by rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; rfl)
    (by rw [List.getElem?_append_right (by omega)];
        rw [show pre.length + 1 + 1 - pre.length = 2 by omega]; rfl) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0x0F :: opcode :: am.modrm reg :: am.tail) := hcode
  have hea := effectiveAddress_run (beforeFetch s) (pre.length + 4) h.fetchReady h.cpu.ds h.cpu.ss
    am hv (scanContext s.DS (PrefixSegments.ofState s) pre) hctx hc hlow' (pre.length + 3)
    (fun j _ => by
      rw [List.getElem?_append_right (by omega)]
      rw [show pre.length + 3 + j - pre.length = 3 + j by omega]
      exact getElem?_cons3 _ _ _ _ j)
    (by simp; omega) (by omega)
  rw [show pre.length + 4 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  have headdr : am.addr (beforeFetch s)
      (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))) =
      am.addrAt s (pre.length + 3 + am.tail.length) := AddrMode.addr_of_gpr rfl _
  rw [headdr] at hrip
  rw [show pre.length + 1 + 2 = pre.length + 3 by omega,
    show pre.length + 1 + 3 = pre.length + 4 by omega,
    setcc_m8_form _ t (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3)))
      _ _ _ opcode.toBitVec haddr hlock _ _ _ _ _ hea hrip ht
      (hw.of_external_eq rfl)] at hdecode
  rw [show pre.length + 1 + 1 = pre.length + 2 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre opcode _ hpre
    (by rcases hop with rfl | rfl <;> decide) (by omega) hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem setcc_m8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (opcode : UInt8) (hop : SupportedOpcode opcode) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x0F :: opcode :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (am.addrAt s (3 + am.tail.length)) 1) :
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand 8)
        (setccValue (opcode.toBitVec.extractLsb' 0 4) s)
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) :=
  setcc_m8_scan_step s h [] (by simp) (by decide) opcode hop rfl rfl rfl reg am hv
    (AddrContext.legacy _ am hx hb) hcode hlow hw

end P256.Proofs.Common.Instructions.Setb
