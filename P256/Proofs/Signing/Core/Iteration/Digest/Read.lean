import P256.Proofs.Signing.Core.Iteration.Digest.Setup
import P256.Proofs.Signing.Core.Iteration.Digest.Branch
import P256.Proofs.Signing.Core.Iteration.Digest.CallPre
import P256.Proofs.ReadBe.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Digest

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar

theorem read [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {state : Nonce.State} {nonce secret : Nat} {digest : ByteArray}
    (pre : SignPre s boundary) (input : SignInput s secret digest)
    (stateT : Reading s t state nonce) (rip : t.RIP = 0x10cc94) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cca1 ∧
      NonceState s u state nonce ∧ Nat256At u (frameBase s + 1328) (Arith.uint digest) := by
  obtain ⟨a,runA,readyA,call⟩ := ScalarFrame.scalar_call pre.toCalleePre (by decide) (by decide)
    (NextNonce.scalarFrame stateT.frame) 0xcc94 0xc3f7 (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x19090 (by decide)) rip
  change (callEffect (fun _ => 0x119090) 0x10cc99 t).Holds t a at call
  have stateA := (NextNonce.scalarFrame stateT.frame).after_call pre.toCalleePre
    (by decide) (by decide) readyA call
  have source : a.regValue .rdi = s.regValue .rdx :=
    (call.agrees.read (n := 64) (r := 7) (by simp)).trans stateT.source
  have destination : a.regValue .rdx = frameBase s + 1328 :=
    (call.agrees.read (n := 64) (r := 2) (by simp)).trans stateT.destination
  have cp := call_pre pre stateA call.rip source destination
    ((call.agrees.read (n := 64) (r := 6) (by simp)).trans stateT.count)
    ((call.agrees.read (n := 64) (r := 1) (by simp)).trans stateT.limbs)
    ((call.agrees.read (n := 64) (r := 8) (by simp)).trans stateT.bits)
    (by change InProgram (stackTop a); rw [(callEffect_stack call).1]; exact inProgram_of_textOffset 0xcc99 (by decide))
  have inputBytes : (registerRegion a .rdi 32).HasBytes a.external digest := by
    have region : registerRegion a .rdi 32 = registerRegion s .rdx 32 := by
      simp only [registerRegion,source]
    rw [region]
    exact ReadBeCall.digest_bytes pre stateA.frame input.digest
  obtain ⟨b,result⟩ := ReadBe.read_be_correct cp inputBytes
  have frameB := ReadBeCall.readBe_result_frame pre stateA result destination
  have valueB : Nat256At b (frameBase s+1328) (Arith.uint digest) := by
    apply nat256At_of_memLoad_limbs
    · have size : digest.size = 32 := input.digest.1
      simpa only [Arith.uint,Arith.decodeBigEndian,size,
        show (256 : Nat)^32 = 2^256 by decide +kernel] using
        SecretKeyFromBytes.Encoding.octetsToNat_lt digest
    · exact (local_readable pre frameB (offset := 1328) (len := 32) (by decide)).mem
    · exact destination ▸ result.value
  obtain ⟨u,runU,readyU,ripU,agreesU⟩ := status
    (readyToStep frameB.machine frameB.bindingsSupported) frameB.loaded
    (result.rip.trans (callEffect_stack call).1) result.status pre.outerBoundary
  have frameU := after_registers frameB readyU agreesU
    (by simp [Component.Covers]) (by simp) (by simp) (by simp) (by simp)
  have memoryU := agreesU.external (by simp [Component.Covers])
  have preserved : Preserved s t u := by
    intro i hi
    unfold LiveOffset at hi
    rw [memoryU,ReadBeCall.result_byte pre stateA result destination (by omega) (by omega)]
    have h := local_call_copy stateT.frame call (offset := i) (len := 1) (by omega) 0 (by decide)
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h
  have regs (reg : Syntax.Reg) (member : reg ∈ [.rbp,.r13,.r14,.r15]) :
      u.regValue reg = t.regValue reg := by
    have saved := result.calleeSaved reg (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      rcases member with rfl|rfl|rfl|rfl <;> simp)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · exact (agreesU.read (n := 64) (r := 5) (by simp)).trans (saved.trans (call.agrees.read (n := 64) (r := 5) (by simp)))

    · exact (agreesU.read (n := 64) (r := 13) (by simp)).trans (saved.trans (call.agrees.read (n := 64) (r := 13) (by simp)))
    · exact (agreesU.read (n := 64) (r := 14) (by simp)).trans (saved.trans (call.agrees.read (n := 64) (r := 14) (by simp)))
    · exact (agreesU.read (n := 64) (r := 15) (by simp)).trans (saved.trans (call.agrees.read (n := 64) (r := 15) (by simp)))
  obtain ⟨n,runB⟩ := result.execution
  exact ⟨1+n+2,u,(runA.trans runB).trans runU,ripU,
    stateT.toNonceState.copy frameU preserved regs,
    ⟨valueB.1,fun i hi => by rw [memoryU]; exact valueB.2 i hi⟩⟩

end P256.Proofs.Signing.Core.Iteration.Digest
