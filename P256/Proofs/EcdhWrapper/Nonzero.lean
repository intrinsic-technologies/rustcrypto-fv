import P256.Proofs.EcdhWrapper.Nonzero.Clear
import P256.Proofs.EcdhWrapper.Nonzero.Arguments
import P256.Proofs.EcdhWrapper.Nonzero.Zero
import P256.Proofs.EcdhWrapper.Nonzero.Choice
import P256.Proofs.EcdhWrapper.Model
import P256.Proofs.Program.CallPre

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Nonzero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar (Nat256At)

theorem correct [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (hbi : MachineRamUnitStrideDecodable bindings initial)
    (hmi : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (direction : DirectionFlagUnset s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rip : s.RIP = 0x1068d7) (rsp : stackPtr s = stackPtr initial-504)
    (r14 : s.regValue .r14 = stackPtr initial-264)
    (scalar : Nat256At s (stackPtr initial-264) (Arith.uint secret)) :
    ∃ u, (∃ fuel, Advances (returnBoundary initial) fuel s u) ∧
      u.RIP = 0x106923 ∧ stackPtr u = stackPtr initial-504 ∧
      (u.regValue .rax).setWidth 8 = 1 ∧
      Nat256At u (stackPtr initial-264) (Arith.uint secret) ∧
      CalleeSavedRegistersUnchanged s u ∧
      MachineRamUnitStrideDecodable bindings u ∧
      SupportedIntegerMachineState bindings.processor u ∧ DirectionFlagUnset u ∧
      ProgramLoaded u ∧
      (∀ a : BitVec 64, (initial.external[a]?).isSome → (u.external[a]?).isSome) ∧
      u.MXCSR = s.MXCSR ∧ u.FP87_Control = s.FP87_Control ∧
      MemoryWriteFrame s u #v[ScalarFrame.Work.region initial 4104 304] ∧
      AgreesExcept (clobbers initial) s u := by
  have outside := outer_boundary call hmi hbi
  have positive : 0 < Arith.uint secret := ((arguments_iff secret peer).mp call.argumentsValid).2.1
  obtain ⟨na,a,ra,readyA,ripA,spA,zeroA,ga⟩ := clear call outside
    (readyToStep hm hb) loaded grow rip rsp
  have loadedA := loaded_after call ga loaded
  obtain ⟨b,rb,readyB,ripB,diB,siB,gb⟩ := arguments outside readyA loadedA ripA
  have gab : AgreesExcept (clobbers initial) s b := (ga.trans gb).mono (by simp [clobbers])
  have spB : stackPtr b = stackPtr initial-504 :=
    (gb.read (n := 64) (r := 4) (by simp)).trans spA
  have di : b.regValue .rdi = stackPtr initial-264 :=
    diB.trans ((ga.read (n := 64) (r := 14) (by simp [clobbers])).trans r14)
  have si : b.regValue .rsi = stackPtr initial-336 := by
    rw [siB,spA]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have memB := gb.external (by simp [Component.Covers])
  have zeroB : Nat256At b (stackPtr initial-336) 0 := by
    simpa only [Nat256At,memB] using zeroA
  obtain ⟨c,⟨nc,rc⟩,readyC,ripC,spC,valueC,gc⟩ := zero_call call outside
    (bindingsSupported_of_ready_agrees hb readyB gab)
    (supportedMachine_of_ready_agrees hm readyB gab)
    (gab.directionFlagClear (by simp [clobbers]) direction) (loaded_after call gab loaded)
    (fun a ha => gab.grow a (grow a ha)) ripB spB di si
    (scalar_preserved call.stackAvailable.1 gab scalar) zeroB
  have gac : AgreesExcept (clobbers initial) s c := (gab.trans gc).mono (by simp)
  have value : (c.regValue .rax).setWidth 8 = 0 := by
    simpa only [ite_eq_right (by omega : Arith.uint secret ≠ 0)] using valueC
  obtain ⟨d,rd,readyD,ripD,valueD,gd⟩ := invert outside readyC
    (loaded_after call gac loaded) ripC value
  have gad : AgreesExcept (clobbers initial) s d := (gac.trans gd).mono (by simp [clobbers])
  have spD : stackPtr d = stackPtr initial-504 :=
    (gd.read (n := 64) (r := 4) (by simp)).trans spC
  obtain ⟨u,ru,readyU,ripU,spU,valueU,gu⟩ := choice call outside readyD
    (loaded_after call gad loaded) (fun a ha => gad.grow a (grow a ha)) ripD spD
  have total : AgreesExcept (clobbers initial) s u := (gad.trans gu).mono (by simp [clobbers])
  refine ⟨u,⟨_,((((ra.trans rb).trans rc).trans rd).trans ru)⟩,ripU,spU.trans spD,?_,
    scalar_preserved call.stackAvailable.1 total scalar,?_,
    bindingsSupported_of_ready_agrees hb readyU total,
    supportedMachine_of_ready_agrees hm readyU total,
    total.directionFlagClear (by simp [clobbers]) direction,loaded_after call total loaded,
    (fun a ha => total.grow a (grow a ha)),total.mxcsr (by simp [clobbers]),
    total.fcw (by simp [clobbers]),total.memoryWriteFrame (writes call.stackAvailable.1),total⟩
  · rw [valueU,valueD]; rfl
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact total.read (n := 64) (r := 3) (by simp [clobbers])
    · exact total.read (n := 64) (r := 5) (by simp [clobbers])
    · exact total.read (n := 64) (r := 12) (by simp [clobbers])
    · exact total.read (n := 64) (r := 13) (by simp [clobbers])
    · exact total.read (n := 64) (r := 14) (by simp [clobbers])
    · exact total.read (n := 64) (r := 15) (by simp [clobbers])

end P256.Proofs.EcdhWrapper.Nonzero
