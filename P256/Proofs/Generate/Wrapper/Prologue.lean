import P256.Proofs.Generate.Wrapper.Initialize
import P256.Proofs.Program.WrapperInput
import P256.Proofs.Generate.Wrapper.Guards

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.Pkcs8 (saveMemory saveComponents)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def guardComponents : List Component := [.reg 0, .reg 1, .reg 3, .reg 14, .flags, .rip]

structure GuardedEntry [Bindings] (initial s : RamState) (input : ByteArray) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x106d91
  rsp : stackPtr s = stackPtr initial - 264
  output : s.regValue .r14 = initial.regValue .rcx
  capacity : s.regValue .rbx = initial.regValue .r8
  sourceAddress : s.regValue .rcx = memLoad initial.external (initial.regValue .rdi) 64
  sourceNonzero : s.regValue .rcx ≠ 0
  sourceBounded : (registerRegion s .rcx input.size).Bounded
  sourceBytes : (registerRegion s .rcx input.size).HasBytes s.external input
  length : s.regValue .rax = BitVec.ofNat 64 input.size
  savedRbx : memLoad s.external (stackPtr initial - 24) 64 = initial.regValue .rbx
  savedR14 : memLoad s.external (stackPtr initial - 16) 64 = initial.regValue .r14
  savedR15 : memLoad s.external (stackPtr initial - 8) 64 = initial.regValue .r15
  returnAddress : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip
  heapBase : memLoad s.external 0x300000 64 = initial.regValue .r9
  heapCapacity : memLoad s.external 0x300008 64 =
    memLoad initial.external (stackPtr initial+8) 64
  heapUsed : memLoad s.external 0x300010 64 = 0
  agrees : AgreesExcept (saveComponents initial ++ arenaComponents ++ guardComponents) initial s
  frame : MemoryWriteFrame initial s (wrapperRegions signingKeyGenerateFromRng initial)

theorem guards_correct [bindings : Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (hcall : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices) :
    ∃ t, GuardedEntry initial t input := by
  obtain ⟨s, hs⟩ := initialize_correct hb hm hcall
  have hcount : s.regValue .rsi = 1 := by
    have hi : initial.regValue .rsi = 1 := by
      have hc := hcall.countArgumentMatchesInputs
      apply BitVec.eq_of_toNat_eq
      exact hc
    exact (hs.agrees.read (n := 64) (r := 6) (by simp [saveComponents, arenaComponents])).trans hi
  have hout := outer_boundary hcall hm hb
  obtain ⟨a, ha, ra, ipa, fa⟩ := count_guard hs.ready hs.loaded hout hs.rip hcount
  have ma := fa.external (by simp [Component.Covers])
  have loadedA : ProgramLoaded a := by simpa only [ProgramLoaded, ma] using hs.loaded
  have frameA : MemoryWriteFrame initial a (wrapperRegions signingKeyGenerateFromRng initial) := by
    intro address hr
    rw [ma]
    exact hs.frame address hr
  have agA := hs.agrees.trans fa
  obtain ⟨address, originalPointer, hn, hbound, hbytes, hp, hl, mp, ml⟩ := preserved_input hcall frameA
  have rdiA : a.regValue .rdi = initial.regValue .rdi :=
    agA.read (n := 64) (r := 7) (by simp [saveComponents, arenaComponents])
  have rdxA : a.regValue .rdx = initial.regValue .rdx :=
    agA.read (n := 64) (r := 2) (by simp [saveComponents, arenaComponents])
  obtain ⟨n, b, hab, rb, _, eb⟩ :=
    load_arguments (returnBoundary initial) hout a ra
      (programText_slice (programLoaded_codeIn loadedA) 0x6d7c loadArgumentsBytes
        (by decide +kernel) (by decide +kernel))
      ⟨ipa, by rw [rdiA]; exact hp, by rw [rdxA]; exact hl⟩
  have fb : AgreesExcept [.reg 3, .reg 14, .reg 1, .reg 0, .rip] a b := by
    simpa [loadArgumentsEffect, Effect.components, Write.component, Operand.component] using eb.agrees
  have mb := fb.external (by simp [Component.Covers])
  have loadedB : ProgramLoaded b := by simpa only [ProgramLoaded, mb] using loadedA
  have hrcx : b.regValue .rcx = address := by
    have hw : b.regValue .rbx = a.regValue .r8 ∧ b.regValue .r14 = a.regValue .rcx ∧
        b.regValue .rcx = memLoad a.external (a.regValue .rdi) 64 ∧
        b.regValue .rax = memLoad a.external (a.regValue .rdx) 64 := eb.writes
    exact hw.2.2.1.trans (rdiA ▸ mp)
  have hrax : b.regValue .rax = BitVec.ofNat 64 input.size := by
    have hw : b.regValue .rbx = a.regValue .r8 ∧ b.regValue .r14 = a.regValue .rcx ∧
        b.regValue .rcx = memLoad a.external (a.regValue .rdi) 64 ∧
        b.regValue .rax = memLoad a.external (a.regValue .rdx) 64 := eb.writes
    exact hw.2.2.2.trans (rdxA ▸ ml)
  obtain ⟨t, hbt, rt, ipt, ft⟩ := input_guard rb loadedB hout eb.rip
    (by rw [hrcx]; exact hn)
  have mt := ft.external (by simp [Component.Covers])
  have loadedT : ProgramLoaded t := by simpa only [ProgramLoaded, mt] using loadedB
  have tailAgrees : AgreesExcept guardComponents s t :=
    ((fa.trans fb).trans ft).mono (by simp [guardComponents])
  have tailMemory := tailAgrees.external (by simp [guardComponents, Component.Covers])
  have fullAgrees := hs.agrees.trans tailAgrees
  have rcxT : t.regValue .rcx = address :=
    (ft.read (n := 64) (r := 1) (by simp)).trans hrcx
  obtain ⟨fuel, run⟩ := hs.execution
  refine ⟨t, ⟨⟨fuel + 2 + n + 2, ((run.trans ha).trans hab).trans hbt⟩, rt, loadedT, ipt,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (tailAgrees.read (n := 64) (r := 4) (by simp [guardComponents])).trans hs.rsp
  · have hw : b.regValue .rbx = a.regValue .r8 ∧ b.regValue .r14 = a.regValue .rcx ∧
        b.regValue .rcx = memLoad a.external (a.regValue .rdi) 64 ∧
        b.regValue .rax = memLoad a.external (a.regValue .rdx) 64 := eb.writes
    exact (ft.read (n := 64) (r := 14) (by simp)).trans (hw.2.1.trans
      (agA.read (n := 64) (r := 1) (by simp [saveComponents, arenaComponents])))
  · have hw : b.regValue .rbx = a.regValue .r8 ∧ b.regValue .r14 = a.regValue .rcx ∧
        b.regValue .rcx = memLoad a.external (a.regValue .rdi) 64 ∧
        b.regValue .rax = memLoad a.external (a.regValue .rdx) 64 := eb.writes
    exact (ft.read (n := 64) (r := 3) (by simp)).trans (hw.1.trans
      (agA.read (n := 64) (r := 8) (by simp [saveComponents, arenaComponents])))
  · exact rcxT.trans originalPointer.symm
  · rw [rcxT]
    exact hn
  · change (MemoryRegion.mk (t.regValue .rcx).toNat input.size).Bounded
    rw [rcxT]
    exact hbound
  · change (MemoryRegion.mk (t.regValue .rcx).toNat input.size).HasBytes t.external input
    rw [rcxT, mt, mb]
    exact hbytes
  · exact (ft.read (n := 64) (r := 0) (by simp)).trans hrax
  · simpa only [tailMemory] using hs.savedRbx
  · simpa only [tailMemory] using hs.savedR14
  · simpa only [tailMemory] using hs.savedR15
  · simpa only [tailMemory] using hs.returnAddress
  · simpa only [tailMemory] using hs.heapBase
  · simpa only [tailMemory] using hs.heapCapacity
  · simpa only [tailMemory] using hs.heapUsed
  · simpa only [List.append_assoc] using fullAgrees
  · intro addr haddr
    rw [mt, mb]
    exact frameA addr haddr

end P256.Proofs.Generate.Wrapper
