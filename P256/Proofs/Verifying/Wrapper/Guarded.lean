import P256.Proofs.Verifying.Wrapper.Initialize
import P256.Proofs.Verifying.Wrapper.Inputs
import P256.Proofs.Verifying.Wrapper.Guards
import P256.Proofs.Verifying.Wrapper.ReturnState

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure KeyReady [Bindings] (initial s : RamState) (key : ByteArray) : Prop
    extends ReturnState initial s where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  frame : MemoryWriteFrame initial s (wrapperRegions verifyingKeyVerify initial)
  rip : s.RIP = 0x103088
  output : s.regValue .r12 = initial.regValue .rcx
  capacity : s.regValue .r13 = initial.regValue .r8
  pointers : s.regValue .r14 = initial.regValue .rdi
  lengths : s.regValue .rbx = initial.regValue .rdx
  count : s.regValue .r15 = 3
  source : s.regValue .rdx = memLoad initial.external (initial.regValue .rdi) 64
  nonzero : s.regValue .rdx ≠ 0
  bounded : (registerRegion s .rdx key.size).Bounded
  bytes : (registerRegion s .rdx key.size).HasBytes s.external key
  keySize : key.size = 65

theorem guards_correct [bindings : Bindings] {initial : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices) :
    ∃ t, KeyReady initial t key := by
  obtain ⟨s, hs⟩ := initialize_correct hb hm call
  have state : ReturnState initial s := by
    refine ⟨bindingsSupported_of_ready_agrees hb hs.ready hs.agrees,
      supportedMachine_of_ready_agrees hm hs.ready hs.agrees, hs.loaded,
      hs.agrees.directionFlagClear ?_ call.directionFlagUnset, hs.rsp, hs.saved, hs.returnAddress,
      hs.agrees.read (n := 64) (r := 5) ?_, hs.agrees.grow⟩
    all_goals simp [saveComponents, pushSequenceFrame, arenaComponents]
  have count : initial.regValue .rsi = 3 := BitVec.eq_of_toNat_eq call.countArgumentMatchesInputs
  have countS : s.regValue .rsi = 3 :=
    (hs.agrees.read (n := 64) (r := 6)
      (by simp [saveComponents, pushSequenceFrame, arenaComponents])).trans count
  have outside := outer_boundary call hm hb
  obtain ⟨a, ha, ra, ripA, agA⟩ := count_guard hs.ready hs.loaded outside hs.rip countS
  have stateA := state.after_registers ra agA (by simp [Component.Covers]) (by simp) (by simp)
  have memA := agA.external (by simp [Component.Covers])
  have frameA : MemoryWriteFrame initial a (wrapperRegions verifyingKeyVerify initial) := by
    intro addr away
    rw [memA]
    exact hs.frame addr away
  have fullA := hs.agrees.trans agA
  obtain ⟨address, original, nonzero, bounded, bytes, readableP, readableL, pointer, length⟩ :=
    preserved_key_input call frameA
  have rdiA : a.regValue .rdi = initial.regValue .rdi :=
    fullA.read (n := 64) (r := 7) (by simp [saveComponents, pushSequenceFrame, arenaComponents])
  have rdxA : a.regValue .rdx = initial.regValue .rdx :=
    fullA.read (n := 64) (r := 2) (by simp [saveComponents, pushSequenceFrame, arenaComponents])
  obtain ⟨nb, b, runB, readyB, _, effectB⟩ := load_arguments (returnBoundary initial) outside a ra
    (programText_slice (programLoaded_codeIn stateA.loaded) 0x3060 loadArgumentsBytes
      (by decide) (by decide +kernel))
    ⟨ripA, by rw [rdiA]; exact readableP, by rw [rdxA]; exact readableL⟩
  have agB : AgreesExcept [.reg 3,.reg 14,.reg 2,.reg 0,.rip] a b := by
    simpa only [loadArgumentsEffect, Effect.components, Write.component, Operand.component,
      List.map, List.cons_append, List.nil_append] using effectB.agrees
  have stateB := stateA.after_registers readyB agB (by simp [Component.Covers]) (by simp) (by simp)
  have values : b.regValue .rbx = a.regValue .rdx ∧ b.regValue .r14 = a.regValue .rdi ∧
      b.regValue .rdx = memLoad a.external (a.regValue .rdi) 64 ∧
      b.regValue .rax = memLoad a.external (a.regValue .rdx) 64 := effectB.writes
  have inputB : b.regValue .rdx = address := values.2.2.1.trans (rdiA ▸ pointer)
  have lengthB : b.regValue .rax = BitVec.ofNat 64 key.size := values.2.2.2.trans (rdxA ▸ length)
  obtain ⟨c, hc, readyC, ripC, agC⟩ := input_guard readyB stateB.loaded outside effectB.rip
    (by rw [inputB]; exact nonzero)
  have stateC := stateB.after_registers readyC agC (by simp [Component.Covers]) (by simp) (by simp)
  obtain ⟨point, r, scalarS, _, _, size, _⟩ := verifying_arguments_decoded call.argumentsValid
  have lengthC : c.regValue .rax = 65 := by
    have h : c.regValue .rax = BitVec.ofNat 64 key.size :=
      (agC.read (n := 64) (r := 0) (by simp)).trans lengthB
    exact h.trans (by rw [size]; rfl)
  obtain ⟨d, hd, readyD, ripD, agD⟩ := length_guard readyC stateC.loaded outside ripC lengthC
  have stateD := stateC.after_registers readyD agD (by simp [Component.Covers]) (by simp) (by simp)
  obtain ⟨nt, t, runT, readyT, _, effectT⟩ := save_arguments (returnBoundary initial) outside d readyD
    (programText_slice (programLoaded_codeIn stateD.loaded) 0x307f saveArgumentsBytes
      (by decide) (by decide +kernel)) ripD
  have agT : AgreesExcept [.reg 15,.reg 12,.reg 13,.rip] d t := by
    simpa only [saveArgumentsEffect, Effect.components, Write.component, Operand.component,
      List.map, List.cons_append, List.nil_append] using effectT.agrees
  have stateT := stateD.after_registers readyT agT (by simp [Component.Covers]) (by simp) (by simp)
  have tail := (((agA.trans agB).trans agC).trans agD).trans agT
  have tailMemory := tail.external (by simp [Component.Covers])
  have afterB := (agC.trans agD).trans agT
  have beforeD := ((fullA.trans agB).trans agC).trans agD
  have saved : t.regValue .r15 = d.regValue .rsi ∧ t.regValue .r12 = d.regValue .rcx ∧
      t.regValue .r13 = d.regValue .r8 := effectT.writes
  have inputT : t.regValue .rdx = address :=
    (afterB.read (n := 64) (r := 2) (by simp)).trans inputB
  obtain ⟨n, run⟩ := hs.execution
  refine ⟨t, ⟨stateT, ⟨_, ((((run.trans ha).trans runB).trans hc).trans hd).trans runT⟩,
    ?_, effectT.rip, ?_, ?_, ?_, ?_, ?_, inputT.trans original.symm, ?_, ?_, ?_, size⟩⟩
  · intro addr away
    rw [tailMemory]
    exact hs.frame addr away
  · exact saved.2.1.trans (beforeD.read (n := 64) (r := 1)
      (by simp [saveComponents, pushSequenceFrame, arenaComponents]))
  · exact saved.2.2.trans (beforeD.read (n := 64) (r := 8)
      (by simp [saveComponents, pushSequenceFrame, arenaComponents]))
  · exact (afterB.read (n := 64) (r := 14) (by simp)).trans (values.2.1.trans rdiA)
  · exact (afterB.read (n := 64) (r := 3) (by simp)).trans (values.1.trans rdxA)
  · exact saved.1.trans ((beforeD.read (n := 64) (r := 6)
      (by simp [saveComponents, pushSequenceFrame, arenaComponents])).trans count)
  · rw [inputT]
    exact nonzero
  · change (MemoryRegion.mk (t.regValue .rdx).toNat key.size).Bounded
    rw [inputT]
    exact bounded
  · change (MemoryRegion.mk (t.regValue .rdx).toNat key.size).HasBytes t.external key
    rw [inputT, ((agB.trans agC).trans agD |>.trans agT).external (by simp [Component.Covers])]
    exact bytes

end P256.Proofs.Verifying.Wrapper
