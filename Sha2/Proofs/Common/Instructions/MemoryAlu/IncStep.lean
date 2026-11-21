import Sha2.Proofs.Common.Instructions.MemoryAlu.IncForm
import Sha2.Proofs.Common.Instructions.MemoryAlu.IncDecode
import X86Proofs.Step.MemOperand
import X86Proofs.Instructions.Xor.Generated.MR.Step
import X86Proofs.Instructions.Xor.Generated.M8R8.Step
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Step
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Step

set_option autoImplicit false

namespace Sha2.Proofs.Common.Instructions.MemoryAlu

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem inc_m64_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 64)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid)
    (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xFF :: am.modrm 0 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 2 + am.tail.length)) 8) :
    let addr := am.addrAt s (pre.length + 2 + am.tail.length)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (incSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        ((Operand.mem addr : Operand 64).read t)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro addr
  let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
  have hlen' : (pre ++ 0xFF :: am.modrm 0 :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp only [List.length_append, List.length_cons]; omega
  have hlow' : s.RIP.toNat + (pre ++ 0xFF :: am.modrm 0 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_FF_inc_memory s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (by rw [AddrMode.modrmReg_modrm]) hcode hlow' (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) ctx hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea s h pre 0xFF 0 am hv [] ctx hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [inc_m64_form _ t _ _ _ _ hsize haddr _ _ _ _ _ hea hrip (memAlu_dataReady h _)
    hread.low hread.mem] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

end Sha2.Proofs.Common.Instructions.MemoryAlu
