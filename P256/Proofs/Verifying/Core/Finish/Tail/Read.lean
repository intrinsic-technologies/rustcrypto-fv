import P256.Proofs.Verifying.Core.Finish.Tail.CallPre
import P256.Proofs.Verifying.Core.Finish.Tail.Branch
import P256.Proofs.Verifying.Core.Digest.Read
import P256.Proofs.SignatureFromDer.Model

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar

theorem read [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x r : Nat}
    (hp : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10e109)
    (src : t.regValue .rdi = frameBase s+392) (dst : t.regValue .rdx = frameBase s)
    (count : t.regValue .rsi = 32) (limbs : t.regValue .rcx = 4) (bits : t.regValue .r8 = 256)
    (bound : x < 2^256)
    (bytes : (⟨(frameBase s+392).toNat,32⟩ : MemoryRegion).HasBytes t.external
      (Standards.SECG.ECC.Encoding.natToOctets 32 x))
    (saved : Nat256At t (frameBase s+704) r) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10e116 ∧
      memLoad u.external (frameBase s+384) 64 = memLoad t.external (frameBase s+384) 64 ∧ Nat256At u (frameBase s) x ∧
      Nat256At u (frameBase s+704) r := by
  obtain ⟨a,callRun,readyA,call⟩ := scalar_call hp.toCalleePre (by decide) (by decide)
    state 0xe109 0xaf82 (by decide) (by decide +kernel) (by decide)
    (inProgram_of_textOffset 0x19090 (by decide)) rip
  have stateA := state.after_call hp.toCalleePre (by decide) (by decide) readyA call
  have source : a.regValue .rdi = frameBase s+392 :=
    (call.agrees.read (n := 64) (r := 7) (by simp)).trans src
  have destination : a.regValue .rdx = frameBase s :=
    (call.agrees.read (n := 64) (r := 2) (by simp)).trans dst
  have cp := readBe_pre hp stateA call.rip source destination
    ((call.agrees.read (n := 64) (r := 6) (by simp)).trans count)
    ((call.agrees.read (n := 64) (r := 1) (by simp)).trans limbs)
    ((call.agrees.read (n := 64) (r := 8) (by simp)).trans bits)
    (by change InProgram (stackTop a); rw [(callEffect_stack call).1];
        exact inProgram_of_textOffset 0xe10e (by decide))
  have inputBytes : (registerRegion a .rdi 32).HasBytes a.external
      (Standards.SECG.ECC.Encoding.natToOctets 32 x) := by
    have region : registerRegion a .rdi 32 = (⟨(frameBase s+392).toNat,32⟩ : MemoryRegion) := by
      simp only [registerRegion,source]
    rw [region]
    refine ⟨bytes.1,fun i => ?_⟩
    have hi : i.val < 32 := by simpa only [SecretKeyFromBytes.Encoding.natToOctets_size] using i.isLt
    have addr : frameBase s+392 = stackPtr s-784 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    have old := bytes.2 i
    change a.external[BitVec.ofNat 64 ((frameBase s+392).toNat+i.val)]? = _
    change t.external[BitVec.ofNat 64 ((frameBase s+392).toNat+i.val)]? = _ at old
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,addr] at old ⊢
    exact (scalar_call_byte (frameOffset := 1176) (by decide) state call
      (by decide) (by decide) hi).trans old
  obtain ⟨b,result⟩ := ReadBe.read_be_correct cp inputBytes
  have stateB := Digest.readBe_result_frame hp stateA result destination
  have decoded : Arith.uint (Standards.SECG.ECC.Encoding.natToOctets 32 x) = x := by
    change Standards.SECG.ECC.Encoding.octetsToNat _ = _
    rw [SignatureFromDer.octetsToNat_natToOctets,
      show (256 : Nat)^32 = 2^256 by decide +kernel,Nat.mod_eq_of_lt bound]
  have valueB : Nat256At b (frameBase s) x := by
    apply nat256At_of_memLoad_limbs bound
    · intro i hi
      exact stateB.allocated _ ((stack_sub_readable hp.stack (offset := 1176) (len := 32)
        (by decide) (by decide)).mem i hi)
    · intro j hj
      have h := result.value j hj
      rwa [destination,decoded] at h
  have rA := Digest.call_slot (offset := 704) state call (by decide) saved
  have rB := Digest.readBe_slot hp stateA destination result (by decide) (by decide) rA
  have bxB : memLoad b.external (frameBase s+384) 64 = memLoad t.external (frameBase s+384) 64 := by
    have preserved := prefix_load hp (Digest.readBe_stack hp stateA destination result)
      (offset := 384) (n := 64) (by decide) (by decide)
    apply preserved.trans
    have same := scalar_call_read (frameOffset := 1176) (by decide) state call
      (offset := 792) (n := 64) (by decide) (by decide)
    simpa only [Operand.read,frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,
      BitVec.reduceNeg,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using same
  obtain ⟨u,branchRun,readyU,ripU,agrees⟩ := status
    (readyToStep stateB.machine stateB.bindingsSupported) stateB.loaded
    (result.rip.trans (callEffect_stack call).1) result.status hp.outerBoundary
  have stateU := stateB.after_registers readyU agrees (by simp [Component.Covers]) (by simp)
  have memoryU := agrees.external (by simp [Component.Covers])
  obtain ⟨fuel,run⟩ := result.execution
  refine ⟨1+fuel+2,u,(callRun.trans run).trans branchRun,stateU,ripU,
    (by rw [memoryU]; exact bxB),?_,?_⟩
  · exact ⟨valueB.1,fun i hi => by rw [memoryU]; exact valueB.2 i hi⟩
  · exact ⟨rB.1,fun i hi => by rw [memoryU]; exact rB.2 i hi⟩

end P256.Proofs.Verifying.Core.Finish.Tail
