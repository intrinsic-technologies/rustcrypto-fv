import Sha2.Proofs.Common.Encoding.Parser.LengthCheck.Step

set_option autoImplicit false

namespace Sha2.Proofs.Common.Encoding.Parser.LengthCheck

open X86Proofs X86 X86.Machine X86.UserProcess X86.Helpers

def cmpR64M64Effect (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (addr : RamState → BitVec 64) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    flags := some (.ofStatusFlags
      (cmpSpec ((Operand.reg src : Operand 64).read s)
        ((Operand.mem (addr s) : Operand 64).read s))) }

theorem cmp_r64_m64_effect_holds [Bindings] {s : RamState} (h : ReadyToStep s)
    (p : BitVec 64) (len : Nat) (src : BitVec 5) (addr : RamState → BitVec 64) :
    (cmpR64M64Effect p len src addr s).Holds s (afterStep s len fun t =>
      writeFlagsOutputs (dataAccess t "load")
        (cmpSpec ((Operand.reg src : Operand 64).read t)
          ((Operand.mem (addr s) : Operand 64).read t)) 0 (p + BitVec.ofNat 64 len)) := by
  refine ⟨afterStep_loadFlags_rip h _ _ _, trivial, ?_,
    AgreesExcept.afterStep_loadFlags s len _ _⟩
  change (StatusFlagsOutcome.ofStatusFlags
    (cmpSpec ((Operand.reg src : Operand 64).read s)
      ((Operand.mem (addr s) : Operand 64).read s))).Allows
    (StatusFlags.ofRFLAGS ((cmpSpec
      ((Operand.reg src : Operand 64).read (afterFetches (beforeFetch s) (len + 1)))
      ((Operand.mem (addr s) : Operand 64).read (afterFetches (beforeFetch s) (len + 1)))).store s.RFLAGS))
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _

theorem cmp_r64_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
      (codeRange p (rex :: 0x3b :: am.modrm reg :: am.tail))
      (cmpR64M64Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length)))) := by
  rintro s h hcode ⟨rfl, hread⟩
  have hlow : s.RIP.toNat + (rex :: 0x3b :: am.modrm reg :: am.tail).length ≤ 2^32 :=
    hcode.low (by simp) (by simp; have := am.tail_length_le; omega)
  have hea := effectiveAddress_run (beforeFetch s) 4 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (rexContext s.DS rex.toBitVec) (AddrContext.rex _ _ am hx hb) hcode.bytesAt hlow 3
    (fun j _ => getElem?_cons3 _ _ _ _ j) (by simp; omega)
    (by have := am.tail_length_le; omega)
  rw [show 4 + am.tail.length = 3 + am.tail.length + 1 by omega] at hea
  have ha : am.addr (beforeFetch s)
      (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) =
        am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) :=
    AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)))
  rw [ha] at hrip
  have hs := cmp_r64_m64_step_of_address s h rex (am.modrm reg) hrex
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) am.tail _ _ _ _
    hcode.bytesAt (by simp only [List.length_cons] at hlow; omega)
    (by simpa only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm,
      show (beforeFetch s).RIP = s.RIP from rfl] using hea) hrip hread
  simp only [AddrMode.modrmReg_modrm] at hs
  exact ⟨_, hs, ReadyToStep.afterStep_loadFlags h _ _ _,
    cmp_r64_m64_effect_holds h _ _ _ _⟩

end Sha2.Proofs.Common.Encoding.Parser.LengthCheck
