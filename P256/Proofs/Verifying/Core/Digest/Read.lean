import P256.Proofs.Verifying.Core.Digest.CallPre
import P256.Proofs.Verifying.Core.Digest.Memory
import P256.Proofs.Verifying.Core.Digest.Branch
import P256.Proofs.ReadBe.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Digest

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar (Nat256At nat256At_of_memLoad_limbs)

theorem call_slot [Bindings] {s t u : RamState} {target : RamState → BitVec 64}
    {ret : BitVec 64} {offset x : Nat} (state : Frame s t)
    (effect : (callEffect target ret t).Holds t u) (bound : offset+32 ≤ 1128)
    (value : Nat256At t (frameBase s+BitVec.ofNat 64 offset) x) :
    Nat256At u (frameBase s+BitVec.ofNat 64 offset) x := by
  have addr : frameBase s+BitVec.ofNat 64 offset =
      stackPtr s-BitVec.ofNat 64 (1176-offset) := by
    rw [← scalar_stack_address (frameOffset := 1176) state.rsp (by decide) (by omega)]
    rw [state.rsp]
    rfl
  rw [addr] at value ⊢
  refine ⟨value.1,fun i hi => ?_⟩
  exact (scalar_call_byte (frameOffset := 1176) (by decide) state effect (by omega) (by omega) hi).trans
    (value.2 i hi)

set_option maxHeartbeats 1000000 in
theorem read [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {digest : ByteArray} {r scalarS : Nat}
    (pre : Core.Pre s boundary) (state : Reading s t)
    (bytes : (⟨(frameBase s+424).toNat,32⟩ : MemoryRegion).HasBytes t.external digest)
    (savedR : Nat256At t (frameBase s+704) r)
    (savedS : Nat256At t (frameBase s+736) scalarS) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10dc30 ∧
      Prepare.Pointers s u ∧ Nat256At u (frameBase s) (Arith.uint digest) ∧
      Nat256At u (frameBase s+704) r ∧ Nat256At u (frameBase s+736) scalarS ∧
      MemoryWriteFrame t u (prefixRegions s) := by
  obtain ⟨a,callRun,readyA,call⟩ := scalar_call pre.toCalleePre (by decide) (by decide)
    state.toFrameState 0xdc23 0xb468 (by decide) (by decide +kernel) (by decide)
    (inProgram_of_textOffset 0x19090 (by decide)) state.rip
  change (callEffect (fun _ => 0x119090) 0x10dc28 t).Holds t a at call
  have stateA := state.toFrameState.after_call pre.toCalleePre (by decide) (by decide) readyA call
  have src : a.regValue .rdi = frameBase s+424 :=
    (call.agrees.read (n := 64) (r := 7) (by simp)).trans state.source
  have dst : a.regValue .rdx = frameBase s :=
    (call.agrees.read (n := 64) (r := 2) (by simp)).trans state.destination
  have cp := readBe_pre pre stateA call.rip src dst
    ((call.agrees.read (n := 64) (r := 6) (by simp)).trans state.count)
    ((call.agrees.read (n := 64) (r := 1) (by simp)).trans state.limbs)
    ((call.agrees.read (n := 64) (r := 8) (by simp)).trans state.bits)
    (by change InProgram (stackTop a); rw [(callEffect_stack call).1]; exact inProgram_of_textOffset 0xdc28 (by decide))
  have callMemory := prefix_call pre state.toFrameState call
  have inputBytes : (registerRegion a .rdi 32).HasBytes a.external digest := by
    have region : registerRegion a .rdi 32 = (⟨(frameBase s+424).toNat,32⟩ : MemoryRegion) := by
      simp only [registerRegion,src]
    rw [region]
    exact digest_bytes pre callMemory bytes
  obtain ⟨b,result⟩ := ReadBe.read_be_correct cp inputBytes
  have stateB := readBe_result_frame pre stateA result dst
  have valueB : Nat256At b (frameBase s) (Arith.uint digest) := by
    apply nat256At_of_memLoad_limbs
    · have size : digest.size = 32 := bytes.1
      simpa only [Arith.uint,Arith.decodeBigEndian,size,
        show (256 : Nat)^32 = 2^256 by decide +kernel] using
        SecretKeyFromBytes.Encoding.octetsToNat_lt digest
    · intro i hi
      exact stateB.allocated _ ((stack_sub_readable pre.stack (offset := 1176) (len := 32)
        (by decide) (by decide)).mem i hi)
    · exact dst ▸ result.value
  have rA := call_slot (offset := 704) state.toFrameState call (by decide) savedR
  have sA := call_slot (offset := 736) state.toFrameState call (by decide) savedS
  have rB := readBe_slot pre stateA dst result (by decide) (by decide) rA
  have sB := readBe_slot pre stateA dst result (by decide) (by decide) sA
  have pointersB : Prepare.Pointers s b := by
    refine ⟨?_⟩
    exact (result.calleeSaved .rbx (by simp)).trans
      ((call.agrees.read (n := 64) (r := 3) (by simp)).trans state.signature)
  obtain ⟨u,branchRun,readyU,ripU,agrees⟩ := status
    (readyToStep stateB.machine stateB.bindingsSupported) stateB.loaded
    (result.rip.trans (callEffect_stack call).1) result.status pre.outerBoundary
  have stateU := stateB.after_registers readyU agrees (by simp [Component.Covers]) (by simp)
  have memoryU := agrees.external (by simp [Component.Covers])
  obtain ⟨fuel,run⟩ := result.execution
  refine ⟨1+fuel+2,u,(callRun.trans run).trans branchRun,stateU,ripU,
    pointersB.after agrees (by simp),?_,?_,?_,?_⟩
  · simpa only [Nat256At,memoryU] using valueB
  · exact ⟨rB.1,fun i hi => by rw [memoryU]; exact rB.2 i hi⟩
  · exact ⟨sB.1,fun i hi => by rw [memoryU]; exact sB.2 i hi⟩
  · intro addr outside
    rw [memoryU]
    exact (memoryWriteFrame_trans callMemory (readBe_stack pre stateA dst result)) addr outside

end P256.Proofs.Verifying.Core.Digest
