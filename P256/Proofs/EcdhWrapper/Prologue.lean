import P256.Proofs.EcdhWrapper.Initialize
import P256.Proofs.EcdhWrapper.Guards
import P256.Proofs.EcdhWrapper.Model
import P256.Proofs.Program.WrapperFirstInput

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def guardComponents : List Component := [.reg 15, .reg 12, .reg 0, .reg 5, .flags, .rip]

structure GuardedEntry [Bindings] (initial s : RamState) (input : ByteArray) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x106830
  rsp : stackPtr s = stackPtr initial - 504
  output : s.regValue .rcx = initial.regValue .rcx
  capacity : s.regValue .r8 = initial.regValue .r8
  count : s.regValue .rsi = 2
  pointers : s.regValue .r12 = initial.regValue .rdi
  lengths : s.regValue .r15 = initial.regValue .rdx
  sourceAddress : s.regValue .rax = memLoad initial.external (initial.regValue .rdi) 64
  sourceNonzero : s.regValue .rax ≠ 0
  sourceBounded : (registerRegion s .rax input.size).Bounded
  sourceBytes : (registerRegion s .rax input.size).HasBytes s.external input
  length : s.regValue .rbp = BitVec.ofNat 64 input.size
  saved : ∀ entry ∈ savedRegisters,
    memLoad s.external (stackPtr initial - BitVec.ofNat 64 entry.2) 64 =
      initial.regValue entry.1
  returnAddress : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip
  heapBase : memLoad s.external 0x300000 64 = initial.regValue .r9
  heapCapacity : memLoad s.external 0x300008 64 =
    memLoad initial.external (stackPtr initial+8) 64
  heapUsed : memLoad s.external 0x300010 64 = 0
  agrees : AgreesExcept (((saveFrame initial ++ [.reg 4, .flags, .rip]) ++
    arenaComponents) ++ guardComponents) initial s
  frame : MemoryWriteFrame initial s (wrapperRegions ecdhDiffieHellman initial)

theorem guards_correct [bindings : Bindings] {initial : RamState} {secret peer : ByteArray}
    {slices : Array Input} (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (hcall : ValidCallWithSlices ecdhDiffieHellman initial [secret, peer] slices) :
    ∃ t, GuardedEntry initial t secret := by
  obtain ⟨s, hs⟩ := initialize_correct hb hm hcall
  have hcount : s.regValue .rsi = 2 := by
    have hi : initial.regValue .rsi = 2 := by
      apply BitVec.eq_of_toNat_eq
      exact hcall.countArgumentMatchesInputs
    exact (hs.agrees.read (n := 64) (r := 6)
      (by simp [saveFrame, arenaComponents])).trans hi
  have hout := outer_boundary hcall hm hb
  obtain ⟨a, ha, ra, ipa, fa⟩ := count_guard hs.ready hs.loaded hout hs.rip hcount
  have ma := fa.external (by simp [Component.Covers])
  have loadedA : ProgramLoaded a := by simpa only [ProgramLoaded, ma] using hs.loaded
  have frameA : MemoryWriteFrame initial a (wrapperRegions ecdhDiffieHellman initial) := by
    intro address hr
    rw [ma]
    exact hs.frame address hr
  have agA := hs.agrees.trans fa
  obtain ⟨address, originalPointer, hn, hbound, hbytes, hp, hl, mp, ml⟩ :=
    preserved_first_input hcall frameA
  have rdiA : a.regValue .rdi = initial.regValue .rdi :=
    agA.read (n := 64) (r := 7) (by simp [saveFrame, arenaComponents])
  have rdxA : a.regValue .rdx = initial.regValue .rdx :=
    agA.read (n := 64) (r := 2) (by simp [saveFrame, arenaComponents])
  obtain ⟨n, b, hab, rb, _, eb⟩ :=
    load_arguments (returnBoundary initial) hout a ra
      (programText_slice (programLoaded_codeIn loadedA) 0x6811 loadArgumentsBytes
        (by decide +kernel) (by decide +kernel))
      ⟨ipa, by rw [rdiA]; exact hp, by rw [rdxA]; exact hl⟩
  have fb : AgreesExcept [.reg 15, .reg 12, .reg 0, .reg 5, .rip] a b := by
    simpa [loadArgumentsEffect, Effect.components, Write.component, Operand.component]
      using eb.agrees
  have mb := fb.external (by simp [Component.Covers])
  have loadedB : ProgramLoaded b := by simpa only [ProgramLoaded, mb] using loadedA
  have hw : b.regValue .r15 = a.regValue .rdx ∧ b.regValue .r12 = a.regValue .rdi ∧
      b.regValue .rax = memLoad a.external (a.regValue .rdi) 64 ∧
      b.regValue .rbp = memLoad a.external (a.regValue .rdx) 64 := eb.writes
  have hrax : b.regValue .rax = address := hw.2.2.1.trans (rdiA ▸ mp)
  have hrbp : b.regValue .rbp = BitVec.ofNat 64 secret.size := hw.2.2.2.trans (rdxA ▸ ml)
  obtain ⟨u, hbu, ru, ipu, fu⟩ := input_guard rb loadedB hout eb.rip
    (by rw [hrax]; exact hn)
  have mu := fu.external (by simp [Component.Covers])
  have loadedU : ProgramLoaded u := by simpa only [ProgramLoaded, mu] using loadedB
  have inputSize : secret.size = 32 := ((arguments_iff secret peer).mp hcall.argumentsValid).1
  have sizeU : u.regValue .rbp = 32 := by
    exact (fu.read (n := 64) (r := 5) (by simp)).trans
      (hrbp.trans (by rw [inputSize]; rfl))
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
  refine ⟨t, {
    execution := ⟨fuel + 2 + n + 4, ((run.trans ha).trans hab).trans hbt⟩
    ready := rt
    loaded := loadedT
    rip := ipt
    rsp := (tailAgrees.read (n := 64) (r := 4) (by simp [guardComponents])).trans hs.rsp
    output := fullAgrees.read (n := 64) (r := 1)
      (by simp [saveFrame, arenaComponents, guardComponents])
    capacity := fullAgrees.read (n := 64) (r := 8)
      (by simp [saveFrame, arenaComponents, guardComponents])
    count := (tailAgrees.read (n := 64) (r := 6) (by simp [guardComponents])).trans hcount
    pointers := (ft.read (n := 64) (r := 12) (by simp)).trans (hw.2.1.trans rdiA)
    lengths := (ft.read (n := 64) (r := 15) (by simp)).trans (hw.1.trans rdxA)
    sourceAddress := raxT.trans originalPointer.symm
    sourceNonzero := by rw [raxT]; exact hn
    sourceBounded := by
      change (MemoryRegion.mk (t.regValue .rax).toNat secret.size).Bounded
      rw [raxT]
      exact hbound
    sourceBytes := by
      change (MemoryRegion.mk (t.regValue .rax).toNat secret.size).HasBytes t.external secret
      rw [raxT, mt, mb]
      exact hbytes
    length := (ft.read (n := 64) (r := 5) (by simp)).trans hrbp
    saved := by simpa only [tailMemory] using hs.saved
    returnAddress := by simpa only [tailMemory] using hs.returnAddress
    heapBase := by simpa only [tailMemory] using hs.heapBase
    heapCapacity := by simpa only [tailMemory] using hs.heapCapacity
    heapUsed := by simpa only [tailMemory] using hs.heapUsed
    agrees := fullAgrees
    frame := by
      intro addr haddr
      rw [mt, mb]
      exact frameA addr haddr }⟩

end P256.Proofs.EcdhWrapper
