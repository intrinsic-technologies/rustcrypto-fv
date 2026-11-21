import P256.Proofs.EcdhWrapper.Peer.Buffer.Run
import P256.Proofs.EcdhWrapper.Peer.Buffer.Preserve
import P256.Proofs.Sec1.EncodedPoint

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Buffer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Sec1.Decode.Prepare.Copy

theorem correct [Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬InProgram (returnBoundary initial).rip) (ready : ReadyToStep s)
    (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rsp : stackPtr s=stackPtr initial-504) (rip : s.RIP=0x106a3d)
    (encoded : Sec1.EncodedPointAt s (stackPtr initial-336) peer) :
    ∃ t, Advances (returnBoundary initial) 45 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP=0x106b70 ∧ stackPtr t=stackPtr initial-504 ∧
      Sec1.EncodedPointAt t (stackPtr initial-264) peer ∧
      CalleeSavedRegistersUnchanged s t ∧
      (∀ off, off≤48 ∨ (464≤off ∧ off≤472) →
        memLoad t.external (stackPtr initial-BitVec.ofNat 64 off) 64=
          memLoad s.external (stackPtr initial-BitVec.ofNat 64 off) 64) ∧
      AgreesExcept (components (stackPtr s)) s t := by
  let f := fun i ↦ memByte s.external (stackPtr s+BitVec.ofNat 64 i)
  have window : Window s f 305 := Bytes.of_isSome
    (by simpa using (readable call grow rsp (off := 0) (len := 305) (by decide)).mem)
  obtain ⟨t,adv,readyT,loadedT,windowT,ripT,ag⟩ :=
    run call outside ready loaded grow rsp rip window
  have same : stackPtr t=stackPtr s := ag.read (n := 64) (r := 4) (by simp [components])
  refine ⟨t,adv,readyT,loadedT,ripT,same.trans rsp,?_,registers_preserved ag,
    fun off bound ↦ word_preserved rsp ag bound,ag⟩
  refine ⟨encoded.1,?_⟩
  intro i hi
  have dest := windowT (240+i) (by omega)
  rw [copiedWindow_eq f hi] at dest
  have src := window (168+i) (by omega)
  have sourceAddress : stackPtr s+BitVec.ofNat 64 (168+i)=
      stackPtr initial-336+BitVec.ofNat 64 i := by
    rw [BitVec.ofNat_add,←BitVec.add_assoc,address rsp (by decide)]
    rfl
  have destinationAddress : stackPtr t+BitVec.ofNat 64 (240+i)=
      stackPtr initial-264+BitVec.ofNat 64 i := by
    rw [same,BitVec.ofNat_add,←BitVec.add_assoc,address rsp (by decide)]
    rfl
  rw [destinationAddress] at dest
  rw [sourceAddress] at src
  exact dest.trans (src.symm.trans (encoded.2 i hi))

end P256.Proofs.EcdhWrapper.Peer.Buffer
