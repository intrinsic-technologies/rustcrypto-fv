import P256.Proofs.Signing.Core.Iteration.ReadBeCall
import P256.Proofs.Signing.Core.Iteration.Call
import P256.Proofs.Signing.Core.Iteration.Components.ParseBranch
import P256.Proofs.ReadBe.Correct
import P256.Proofs.SignatureFromDer.Model
import P256.Proofs.Program.CopyBytes
import P256.Proofs.SecretKeyFromBytes.Encoding

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar

theorem read [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d20d)
    (source : t.regValue .rdi = frameBase s+432)
    (destination : t.regValue .rdx = frameBase s+1328)
    (count : t.regValue .rsi = 32) (limbs : t.regValue .rcx = 4) (bits : t.regValue .r8 = 256)
    (bound : x < 2^256)
    (bytes : (MemoryRegion.mk (frameBase s+432).toNat 32).HasBytes t.external
      (Standards.SECG.ECC.Encoding.natToOctets 32 x)) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10d21a ∧
      Nat256At u (frameBase s+1328) x ∧
      (∀ offset < 2280, offset < 1328 ∨ 1360 ≤ offset →
        u.external[frameBase s+BitVec.ofNat 64 offset]? =
          t.external[frameBase s+BitVec.ofNat 64 offset]?) ∧
      (∀ reg ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15],
        u.regValue reg = t.regValue reg) := by
  obtain ⟨a,callRun,readyA,call⟩ := ScalarFrame.scalar_call hp.toCalleePre
    (by decide) (by decide) (NextNonce.scalarFrame frame) 0xd20d 0xbe7e
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x19090 (by decide)) rip
  have called := (NextNonce.scalarFrame frame).after_call hp.toCalleePre
    (by decide) (by decide) readyA call
  have src : a.regValue .rdi = frameBase s+432 :=
    (call.agrees.read (n := 64) (r := 7) (by simp)).trans source
  have dst : a.regValue .rdx = frameBase s+1328 :=
    (call.agrees.read (n := 64) (r := 2) (by simp)).trans destination
  have bounds := stack_bounds hp.stack
  have sn : (a.regValue .rdi).toNat = (stackPtr s).toNat-2280+432 := by
    rw [src]
    exact NextNonce.base_nat hp (by decide)
  have dn : (a.regValue .rdx).toNat = (stackPtr s).toNat-2280+1328 := by
    rw [dst]
    exact NextNonce.base_nat hp (by decide)
  have sp : (stackPtr a).toNat = (stackPtr s).toNat-2288 := by
    rw [called.rsp]
    exact stack_sub_toNat hp.stack (by decide)
  have sb : (registerRegion a .rdi 32).Bounded := by
    change (a.regValue .rdi).toNat+32 < 2^32
    rw [sn]
    omega
  have input : (registerRegion a .rdi 32).HasBytes a.external
      (Standards.SECG.ECC.Encoding.natToOctets 32 x) := by
    change (MemoryRegion.mk (a.regValue .rdi).toNat 32).HasBytes _ _
    rw [src]
    exact hasBytes_copy bytes (local_call_copy frame call (by decide))
  have cp := ReadBeCall.readBe_pre hp called call.rip dst
    ((call.agrees.read (n := 64) (r := 6) (by simp)).trans count)
    ((call.agrees.read (n := 64) (r := 1) (by simp)).trans limbs)
    ((call.agrees.read (n := 64) (r := 8) (by simp)).trans bits)
    (by change InProgram (stackTop a); rw [(callEffect_stack call).1]
        exact inProgram_of_textOffset 0xd212 (by decide)) sb
    (hasBytes_allocated input)
    (by
      intro address ha hb
      change (a.regValue .rdi).toNat ≤ address ∧ address < (a.regValue .rdi).toNat+32 at ha
      change (a.regValue .rdx).toNat ≤ address ∧ address < (a.regValue .rdx).toNat+32 at hb
      rw [sn] at ha
      rw [dn] at hb
      omega)
    (by
      intro address ha hb
      change (a.regValue .rdi).toNat ≤ address ∧ address < (a.regValue .rdi).toNat+32 at ha
      change (Stack.region a 128).start ≤ address ∧
        address < (Stack.region a 128).start+(Stack.region a 128).size at hb
      rw [stack_region_end] at hb
      change _ ∧ address < (stackPtr a).toNat+8 at hb
      rw [sn] at ha
      rw [sp] at hb
      omega)
  obtain ⟨b,result⟩ := ReadBe.read_be_correct cp input
  have frameB := ReadBeCall.readBe_result_frame hp called result dst
  have decoded : Arith.uint (Standards.SECG.ECC.Encoding.natToOctets 32 x) = x := by
    change Standards.SECG.ECC.Encoding.octetsToNat _ = _
    rw [SignatureFromDer.octetsToNat_natToOctets,
      show (256 : Nat)^32 = 2^256 by decide +kernel,Nat.mod_eq_of_lt bound]
  have value : Nat256At b (frameBase s+1328) x := by
    apply nat256At_of_memLoad_limbs bound
    · exact (local_readable hp frameB (offset := 1328) (len := 32) (by decide)).mem
    · intro j hj
      have h := result.value j hj
      rwa [dst,decoded] at h
  obtain ⟨u,runU,readyU,ripU,agrees⟩ := status
    (readyToStep frameB.machine frameB.bindingsSupported) frameB.loaded
    (result.rip.trans (callEffect_stack call).1) result.status hp.outerBoundary
  have frameU := after_registers frameB readyU agrees (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  have memory := agrees.external (by simp [Component.Covers])
  obtain ⟨n,runB⟩ := result.execution
  refine ⟨1+n+2,u,(callRun.trans runB).trans runU,frameU,ripU,?_,?_,?_⟩
  · exact ⟨value.1,fun i hi => by rw [memory]; exact value.2 i hi⟩
  · intro offset ho apart
    rw [memory,ReadBeCall.result_byte hp called result dst ho apart]
    have h := local_call_copy frame call (offset := offset) (len := 1) (by omega) 0 (by decide)
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h
  · intro reg hr
    have eq : u.regValue reg = b.regValue reg := by
      rcases (show reg = .rbx ∨ reg = .rbp ∨ reg = .r12 ∨ reg = .r13 ∨ reg = .r14 ∨ reg = .r15
        from by simpa using hr) with rfl|rfl|rfl|rfl|rfl|rfl
      · exact agrees.read (n := 64) (r := 3) (by simp)
      · exact agrees.read (n := 64) (r := 5) (by simp)
      · exact agrees.read (n := 64) (r := 12) (by simp)
      · exact agrees.read (n := 64) (r := 13) (by simp)
      · exact agrees.read (n := 64) (r := 14) (by simp)
      · exact agrees.read (n := 64) (r := 15) (by simp)
    refine eq.trans ((result.calleeSaved reg hr).trans ?_)
    rcases (show reg = .rbx ∨ reg = .rbp ∨ reg = .r12 ∨ reg = .r13 ∨ reg = .r14 ∨ reg = .r15
      from by simpa using hr) with rfl|rfl|rfl|rfl|rfl|rfl
    · exact call.agrees.read (n := 64) (r := 3) (by simp)
    · exact call.agrees.read (n := 64) (r := 5) (by simp)
    · exact call.agrees.read (n := 64) (r := 12) (by simp)
    · exact call.agrees.read (n := 64) (r := 13) (by simp)
    · exact call.agrees.read (n := 64) (r := 14) (by simp)
    · exact call.agrees.read (n := 64) (r := 15) (by simp)

end P256.Proofs.Signing.Core.Iteration.Components
