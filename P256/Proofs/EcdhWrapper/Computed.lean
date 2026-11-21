import P256.Proofs.EcdhWrapper.Peer.Decoded
import P256.Proofs.EcdhWrapper.Peer.Result
import P256.Proofs.EcdhWrapper.Multiply

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem peer_result_word {initial s t : RamState} {offset : Nat}
    (stack : Stack.Valid initial 4104)
    (ag : AgreesExcept (Peer.Result.components initial) s t)
    (range : offset ≤ 48 ∨ offset=464 ∨ offset=472) :
    memLoad t.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
  apply memLoad_agrees_apart ag
  intro address len member
  have cases : (address=stackPtr initial-336 ∧ len=1) ∨
      (address=stackPtr initial-336 ∧ len=72) := by
    simpa [Peer.Result.components] using member
  rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    exact stack_sub_apart stack (a := 336) (b := offset) (by decide)
      (by rcases range with h | rfl | rfl <;> omega) (by decide) (by omega)
      (by rcases range with h | rfl | rfl <;> omega)

theorem computed_of_raw [bindings : Bindings]
    (raw : ∀ (s : RamState) (boundary : ReturnBoundary) (bytes : ByteArray),
      Sec1.AffineDecodePre s boundary bytes → ∃ t, CalleeResult s t boundary 80 3360 ∧
        Sec1.AffineResultAt t (s.regValue .rdi) (Points.decodePoint bytes))
    {initial : RamState} {secret peer : ByteArray} {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices) :
    ∃ t, (∃ fuel, Advances (returnBoundary initial) fuel initial t) ∧
      MachineRamUnitStrideDecodable bindings t ∧
      SupportedIntegerMachineState bindings.processor t ∧ DirectionFlagUnset t ∧
      ProgramLoaded t ∧
      (∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome) ∧
      t.RIP = 0x106bd5 ∧ stackPtr t = stackPtr initial-504 ∧
      (MemoryRegion.mk (stackPtr initial-504).toNat 32).HasBytes t.external
        (P256.Spec.Ecdh.diffieHellman #[secret,peer]) ∧
      MemoryWriteFrame initial t (wrapperRegions ecdhDiffieHellman initial) ∧
      (∀ reg ∈ savedRegisters,
        memLoad t.external (stackPtr initial-BitVec.ofNat 64 reg.2) 64 =
          initial.regValue reg.1) ∧
      memLoad t.external (stackPtr initial) 64 = (returnBoundary initial).rip ∧
      memLoad t.external (stackPtr initial-472) 64 = initial.regValue .rcx ∧
      memLoad t.external (stackPtr initial-464) 64 = initial.regValue .r8 ∧
      t.MXCSR = initial.MXCSR ∧ t.FP87_Control = initial.FP87_Control := by
  obtain ⟨point,s,decoded,⟨n,run⟩,hs,ms,ds,ls,gs,ips,sps,scalar,affine,valid,
    frame,saved,ret,out,cap,mx,fp⟩ := Peer.decoded_of_raw raw hb hm call
  obtain ⟨u,⟨m,step⟩,ipu,spu,rdx,affineU,hu,mu,du,lu,gu,_,mxu,fpu,_,frameU,_,ag⟩ :=
    Peer.Result.correct hb hm call hs ms ds ls gs frame ips sps affine valid
  have scalarU := Peer.scalar_after_padding call.stackAvailable.1
    (Peer.Result.work_frame call.stackAvailable.1 ag) scalar
  obtain ⟨t,⟨k,finish⟩,ipt,spt,bytes,ht,mt,dt,lt,gt,_,mxt,fpt,_,frameT,words⟩ :=
    Multiply.correct hb hm call hu mu du lu gu frameU ipu spu rdx scalarU affineU
  have word (offset : Nat) (range : offset ≤ 48 ∨ offset=464 ∨ offset=472) :
      memLoad t.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64 :=
    (words offset (by rcases range with h | rfl | rfl <;> omega)).trans
      (peer_result_word call.stackAvailable.1 ag range)
  have size : secret.size = 32 := ((arguments_iff secret peer).mp call.argumentsValid).1
  rw [machine_output_of_decoded size decoded] at bytes
  refine ⟨t,⟨n+m+k,(run.trans step).trans finish⟩,ht,mt,dt,lt,gt,ipt,spt,bytes,frameT,
    ?_,?_,(word 472 (.inr (.inr rfl))).trans out,(word 464 (.inr (.inl rfl))).trans cap,
    mxt.trans (mxu.trans mx),fpt.trans (fpu.trans fp)⟩
  · intro reg member
    have bound : reg.2 ≤ 48 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (word reg.2 (.inl bound)).trans (saved reg member)
  · have keep : memLoad t.external (stackPtr initial) 64 =
        memLoad s.external (stackPtr initial) 64 := by
      simpa only [BitVec.sub_zero] using word 0 (.inl (by decide))
    exact keep.trans ret

end P256.Proofs.EcdhWrapper
