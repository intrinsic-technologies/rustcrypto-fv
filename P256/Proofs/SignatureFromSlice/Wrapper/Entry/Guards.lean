import P256.Proofs.SignatureFromSlice.Wrapper.Entry.Initialize
import P256.Proofs.Program.WrapperInput
import P256.Proofs.SignatureFromSlice.Wrapper.Guards

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open SavePair
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def guardComponents : List Component := [.reg 0, .reg 6, .reg 3, .reg 14, .flags, .rip]

structure GuardedEntry [Bindings] (initial s : RamState) (input : ByteArray) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x102275
  rsp : stackPtr s = stackPtr initial - 88
  output : s.regValue .rbx = initial.regValue .rcx
  capacity : s.regValue .r14 = initial.regValue .r8
  sourceAddress : s.regValue .rsi = memLoad initial.external (initial.regValue .rdi) 64
  sourceNonzero : s.regValue .rsi ≠ 0
  sourceBounded : (registerRegion s .rsi input.size).Bounded
  sourceBytes : (registerRegion s .rsi input.size).HasBytes s.external input
  length : s.regValue .rax = BitVec.ofNat 64 input.size
  savedRbx : memLoad s.external (stackPtr initial - 16) 64 = initial.regValue .rbx
  savedR14 : memLoad s.external (stackPtr initial - 8) 64 = initial.regValue .r14
  returnAddress : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip
  agrees : AgreesExcept (saveComponents initial ++ arenaComponents ++ guardComponents) initial s
  frame : MemoryWriteFrame initial s (wrapperRegions signatureFromSlice initial)

theorem guards_correct [bindings : Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (hcall : ValidCallWithSlices signatureFromSlice initial [input] slices) :
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
  have frameA : MemoryWriteFrame initial a (wrapperRegions signatureFromSlice initial) := by
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
      (programText_slice (programLoaded_codeIn loadedA) 0x2264 loadArgumentsBytes
        (by decide +kernel) (by decide +kernel))
      ⟨ipa, by rw [rdiA]; exact hp, by rw [rdxA]; exact hl⟩
  have fb : AgreesExcept [.reg 6, .reg 0, .rip] a b := by
    simpa [loadArgumentsEffect, Effect.components, Write.component, Operand.component] using eb.agrees
  have mb := fb.external (by simp [Component.Covers])
  have loadedB : ProgramLoaded b := by simpa only [ProgramLoaded, mb] using loadedA
  have hrsi : b.regValue .rsi = address := eb.writes.1.trans (rdiA ▸ mp)
  have hrax : b.regValue .rax = BitVec.ofNat 64 input.size := eb.writes.2.trans (rdxA ▸ ml)
  obtain ⟨t, hbt, rt, ipt, outT, capT, ft⟩ := input_guard rb loadedB hout eb.rip
    (by rw [hrsi]; exact hn)
  have mt := ft.external (by simp [Component.Covers])
  have loadedT : ProgramLoaded t := by simpa only [ProgramLoaded, mt] using loadedB
  have tailAgrees : AgreesExcept guardComponents s t :=
    ((fa.trans fb).trans ft).mono (by simp [guardComponents])
  have tailMemory := tailAgrees.external (by simp [guardComponents, Component.Covers])
  have fullAgrees := hs.agrees.trans tailAgrees
  have rsiT : t.regValue .rsi = address :=
    (ft.read (n := 64) (r := 6) (by simp)).trans hrsi
  obtain ⟨fuel, run⟩ := hs.execution
  refine ⟨t, ⟨⟨fuel + 2 + n + 4, ((run.trans ha).trans hab).trans hbt⟩, rt, loadedT, ipt,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (tailAgrees.read (n := 64) (r := 4) (by simp [guardComponents])).trans hs.rsp
  · exact outT.trans ((agA.trans fb).read (n := 64) (r := 1) (by simp [saveComponents, arenaComponents]))
  · exact capT.trans ((agA.trans fb).read (n := 64) (r := 8) (by simp [saveComponents, arenaComponents]))
  · exact rsiT.trans originalPointer.symm
  · rw [rsiT]
    exact hn
  · change (MemoryRegion.mk (t.regValue .rsi).toNat input.size).Bounded
    rw [rsiT]
    exact hbound
  · change (MemoryRegion.mk (t.regValue .rsi).toNat input.size).HasBytes t.external input
    rw [rsiT, mt, mb]
    exact hbytes
  · exact (ft.read (n := 64) (r := 0) (by simp)).trans hrax
  · simpa only [tailMemory] using hs.savedRbx
  · simpa only [tailMemory] using hs.savedR14
  · simpa only [tailMemory] using hs.returnAddress
  · simpa only [List.append_assoc] using fullAgrees
  · intro addr haddr
    rw [mt, mb]
    exact frameA addr haddr

end P256.Proofs.SignatureFromSlice.Wrapper
