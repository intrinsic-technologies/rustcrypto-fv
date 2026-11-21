import P256.Proofs.Signing.Wrapper.Entry.Initialize
import P256.Proofs.Program.WrapperFirstInput
import P256.Proofs.Signing.Wrapper.Entry.Guards
import P256.Proofs.Signing.Wrapper.Entry.Input
import P256.Proofs.Signing.Wrapper.Entry.Arguments
import P256.Proofs.Program.State

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def guardComponents : List Component := [.reg 0, .reg 5, .reg 12, .reg 15, .flags, .rip]

structure GuardedEntry [Bindings] (initial s : RamState) (secret : ByteArray) : Prop extends
    State initial s 520 where
  rip : s.RIP = 0x1023c0
  pointers : s.regValue .r12 = initial.regValue .rdi
  lengths : s.regValue .r15 = initial.regValue .rdx
  count : s.regValue .rsi = 2
  sourceAddress : s.regValue .rax = memLoad initial.external (initial.regValue .rdi) 64
  sourceNonzero : s.regValue .rax ≠ 0
  sourceBounded : (registerRegion s .rax secret.size).Bounded
  sourceBytes : (registerRegion s .rax secret.size).HasBytes s.external secret
  length : s.regValue .rbp = BitVec.ofNat 64 secret.size
  output : s.regValue .rcx = initial.regValue .rcx
  capacity : s.regValue .r8 = initial.regValue .r8

theorem guards_correct [bindings : Bindings] {initial : RamState} {input message : ByteArray}
    {slices : Array Input} (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (hcall : ValidCallWithSlices signingKeyTrySign initial [input, message] slices) :
    ∃ t, GuardedEntry initial t input := by
  obtain ⟨s, hs⟩ := initialize_correct hb hm hcall
  have hcount : s.regValue .rsi = 2 := by
    have hi : initial.regValue .rsi = 2 := by
      have hc := hcall.countArgumentMatchesInputs
      apply BitVec.eq_of_toNat_eq
      exact hc
    exact (hs.agrees.read (n := 64) (r := 6) (by simp [saveComponents,
      pushSequenceFrame, arenaComponents])).trans hi
  have hout := outer_boundary hcall hm hb
  obtain ⟨a, ha, ra, ipa, fa⟩ := count_guard hs.ready hs.loaded hout hs.rip hcount
  have ma := fa.external (by simp [Component.Covers])
  have loadedA : ProgramLoaded a := by simpa only [ProgramLoaded, ma] using hs.loaded
  have frameA : MemoryWriteFrame initial a (wrapperRegions signingKeyTrySign initial) := by
    intro address hr
    rw [ma]
    exact hs.frame address hr
  have agA := hs.agrees.trans fa
  obtain ⟨address, originalPointer, hn, hbound, hbytes, hp, hl, mp, ml⟩ := preserved_first_input hcall frameA
  have rdiA : a.regValue .rdi = initial.regValue .rdi :=
    agA.read (n := 64) (r := 7) (by simp [saveComponents,
      pushSequenceFrame, arenaComponents])
  have rdxA : a.regValue .rdx = initial.regValue .rdx :=
    agA.read (n := 64) (r := 2) (by simp [saveComponents,
      pushSequenceFrame, arenaComponents])
  obtain ⟨n, b, hab, rb, _, eb⟩ :=
    load_arguments (returnBoundary initial) hout a ra
      (programText_slice (programLoaded_codeIn loadedA) 0x23a1 loadArgumentsBytes
        (by decide +kernel) (by decide +kernel))
      ⟨ipa, by rw [rdiA]; exact hp, by rw [rdxA]; exact hl⟩
  have fb : AgreesExcept [.reg 15, .reg 12, .reg 0, .reg 5, .rip] a b := by
    simpa [loadArgumentsEffect, Effect.components, Write.component, Operand.component] using eb.agrees
  have mb := fb.external (by simp [Component.Covers])
  have loadedB : ProgramLoaded b := by simpa only [ProgramLoaded, mb] using loadedA
  have values : b.regValue .r15 = a.regValue .rdx ∧ b.regValue .r12 = a.regValue .rdi ∧
      b.regValue .rax = memLoad a.external (a.regValue .rdi) 64 ∧
      b.regValue .rbp = memLoad a.external (a.regValue .rdx) 64 := eb.writes
  have hrax : b.regValue .rax = address := by
    exact values.2.2.1.trans (rdiA ▸ mp)
  have hrbp : b.regValue .rbp = BitVec.ofNat 64 input.size := by
    exact values.2.2.2.trans (rdxA ▸ ml)
  obtain ⟨u, hbu, ru, ipu, fu⟩ := input_guard rb loadedB hout eb.rip
    (by rw [hrax]; exact hn)
  have mu := fu.external (by simp [Component.Covers])
  have loadedU : ProgramLoaded u := by simpa only [ProgramLoaded, mu] using loadedB
  have inputSize : input.size = 32 :=
    ((arguments_iff input message).mp hcall.argumentsValid).1
  have sizeU : u.regValue .rbp = 32 := by
    exact (fu.read (n := 64) (r := 5) (by simp)).trans (hrbp.trans (by rw [inputSize]; rfl))
  obtain ⟨t, hut, rt, ipt, fut⟩ := length_guard ru loadedU hout ipu sizeU
  have hbt : Advances (returnBoundary initial) 4 b t := hbu.trans hut
  have ft : AgreesExcept [.flags, .rip] b t := (fu.trans fut).mono (by simp)
  have mt := ft.external (by simp [Component.Covers])
  have loadedT : ProgramLoaded t := by simpa only [ProgramLoaded, mt] using loadedB
  have tailAgrees : AgreesExcept guardComponents s t :=
    ((fa.trans fb).trans ft).mono (by simp [guardComponents])
  have tailMemory := tailAgrees.external (by simp [guardComponents, Component.Covers])
  have fullAgrees := hs.agrees.trans tailAgrees
  have raxT : t.regValue .rax = address :=
    (ft.read (n := 64) (r := 0) (by simp)).trans hrax
  obtain ⟨fuel, run⟩ := hs.execution
  have state : State initial t 520 := by
    refine ⟨⟨fuel + 2 + n + 4, ((run.trans ha).trans hab).trans hbt⟩,
      bindingsSupported_of_ready_agrees hb rt fullAgrees,
      supportedMachine_of_ready_agrees hm rt fullAgrees, loadedT,
      fullAgrees.directionFlagClear ?_ hcall.directionFlagUnset, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, fullAgrees.grow, ?_⟩
    · simp [saveComponents, pushSequenceFrame, arenaComponents, guardComponents]
    · exact (tailAgrees.read (n := 64) (r := 4) (by simp [guardComponents])).trans hs.rsp
    · simpa only [Prod.snd, BitVec.ofNat_eq_ofNat, tailMemory] using
        hs.saved (.rbx, 48) (by simp [savedRegisters])
    · simpa only [Prod.snd, BitVec.ofNat_eq_ofNat, tailMemory] using
        hs.saved (.r12, 40) (by simp [savedRegisters])
    · simpa only [Prod.snd, BitVec.ofNat_eq_ofNat, tailMemory] using
        hs.saved (.r13, 32) (by simp [savedRegisters])
    · simpa only [Prod.snd, BitVec.ofNat_eq_ofNat, tailMemory] using
        hs.saved (.r14, 24) (by simp [savedRegisters])
    · simpa only [Prod.snd, BitVec.ofNat_eq_ofNat, tailMemory] using
        hs.saved (.r15, 16) (by simp [savedRegisters])
    · simpa only [Prod.snd, BitVec.ofNat_eq_ofNat, tailMemory] using
        hs.saved (.rbp, 8) (by simp [savedRegisters])
    · simpa only [tailMemory] using hs.returnAddress
    · intro addr haddr
      rw [mt, mb]
      exact frameA addr haddr
  refine ⟨t, ⟨state, ipt, ?_, ?_, ?_, raxT.trans originalPointer.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (ft.read (n := 64) (r := 12) (by simp)).trans (values.2.1.trans rdiA)
  · exact (ft.read (n := 64) (r := 15) (by simp)).trans (values.1.trans rdxA)
  · exact (tailAgrees.read (n := 64) (r := 6) (by simp [guardComponents])).trans hcount
  · rw [raxT]
    exact hn
  · change (MemoryRegion.mk (t.regValue .rax).toNat input.size).Bounded
    rw [raxT]
    exact hbound
  · change (MemoryRegion.mk (t.regValue .rax).toNat input.size).HasBytes t.external input
    rw [raxT, mt, mb]
    exact hbytes
  · exact (ft.read (n := 64) (r := 5) (by simp)).trans hrbp
  · exact fullAgrees.read (n := 64) (r := 1) (by simp [saveComponents,
      pushSequenceFrame, arenaComponents, guardComponents])
  · exact fullAgrees.read (n := 64) (r := 8) (by simp [saveComponents,
      pushSequenceFrame, arenaComponents, guardComponents])

end P256.Proofs.Signing.Wrapper.Entry
