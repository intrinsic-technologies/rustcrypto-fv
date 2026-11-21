import Hkdf.Proofs.NewExpand.Extract.Initialize.Assemble
import Hkdf.Proofs.NewExpand.Extract.Initialize.Pads.Chaining
import Hkdf.Proofs.NewExpand.Extract.Initialize.Pads.Xor
import Hkdf.Proofs.NewExpand.Extract.Initialize.Pads.Setup

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.SHA256
open Hkdf.Proofs.Common.CallFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Initialize.Pads

private theorem preserve_inner {initial padded compressed s : RamState}
    (stack : Stack.Valid initial 2264)
    (padFrame : MemoryWriteFrame s padded #v[padRegion initial])
    (hashFrame : MemoryWriteFrame padded compressed (chainingRegions initial true)) :
    (Component.mem (slot initial 456) 40).Agrees s compressed := by
  have first := slot_agrees stack padFrame (offset := 456) (size := 40) (by decide)
    (by decide) (by
      intro r hr
      have eq : r = padRegion initial := by simpa only [Vector.mem_singleton] using hr
      rw [eq]
      exact slotRegion_disjoint stack (by decide) (by decide) (.inr (by decide)))
  have second := slot_agrees stack hashFrame (offset := 456) (size := 40) (by decide)
    (by decide) (by
      intro r hr
      have choices : r = slotRegion initial 416 40 ∨ r = slotRegion initial 800 344 := by
        simpa only [chainingRegions, hashOffset, ite_true, Vector.mem_mk, List.mem_toArray,
          List.mem_cons, List.not_mem_nil, or_false] using hr
      rcases choices with rfl | rfl
      · exact slotRegion_disjoint stack (by decide) (by decide) (.inr (by decide))
      · exact slotRegion_disjoint stack (by decide) (by decide) (.inl (by decide)))
  exact first.trans second

theorem initialize_hmac [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray}
    (pre : ExtractPre initial boundary salt ikm)
    (state : Normalized initial s boundary salt) :
    ∃ t, Initialized initial t boundary salt := by
  have padAddress : base initial + 120 = slot initial 336 :=
    base_add initial (offset := 120) (by decide)
  have padBytes : (padRegion initial).HasBytes s.external
      (HMAC.keyBlock (salt.getD (RFC5869.defaultSalt .sha256))) := by
    simpa only [padAddress] using state.block
  obtain ⟨innerPad, innerPadFrame, innerPadRip, innerBytes, innerPadAgrees, _⟩ :=
    padding false pre state.toFrame state.rip padBytes
  obtain ⟨fuelI, innerSetup, innerRun, innerReady, innerRip, innerSetupAgrees,
    innerDest, innerSource, innerN, innerIV, innerCount, iv⟩ :=
    Initialize.Pads.setup false pre innerPadFrame innerPadRip (by intro h; contradiction)
  obtain ⟨inner, innerFrame, innerRet, innerABI, _, padded, innerHash, innerBlocks⟩ :=
    chaining false pre innerPadFrame innerBytes innerRun innerReady innerRip innerSetupAgrees
      innerDest innerSource innerN innerIV innerCount
  obtain ⟨outerPad, outerPadFrame, outerPadRip, outerBytes, outerPadAgrees, padMemory⟩ :=
    padding true pre innerFrame innerRet padded
  have padIV : IVRegisters outerPad := by
    rcases iv with ⟨r12, r13, rbp, rbx⟩
    exact ⟨
      (outerPadAgrees.read (n := 64) (r := 12) (by simp [Pad.components])).trans
        ((innerABI.1 .r12 (by simp)).trans r12),
      (outerPadAgrees.read (n := 64) (r := 13) (by simp [Pad.components])).trans
        ((innerABI.1 .r13 (by simp)).trans r13),
      (outerPadAgrees.read (n := 64) (r := 5) (by simp [Pad.components])).trans
        ((innerABI.1 .rbp (by simp)).trans rbp),
      (outerPadAgrees.read (n := 64) (r := 3) (by simp [Pad.components])).trans
        ((innerABI.1 .rbx (by simp)).trans rbx)⟩
  simp only [Bool.false_eq_true, ite_false, ite_true, xorPad_inner_to_outer] at outerBytes
  obtain ⟨fuelO, outerSetup, outerRun, outerReady, outerRip, outerSetupAgrees,
    outerDest, outerSource, outerN, outerIV, outerCount, _⟩ :=
    Initialize.Pads.setup true pre outerPadFrame outerPadRip (fun _ ↦ padIV)
  obtain ⟨outer, outerFrame, outerRet, outerABI, hashMemory, _, outerHash, outerBlocks⟩ :=
    chaining true pre outerPadFrame outerBytes outerRun outerReady outerRip outerSetupAgrees
      outerDest outerSource outerN outerIV outerCount
  have ikmPtr : outer.regValue .r15 = initial.regValue .rcx := calc
    _ = outerSetup.regValue .r15 := outerABI.1 .r15 (by simp)
    _ = outerPad.regValue .r15 := outerSetupAgrees.read (n := 64) (r := 15) (by simp)
    _ = inner.regValue .r15 := outerPadAgrees.read (n := 64) (r := 15) (by simp [Pad.components])
    _ = innerSetup.regValue .r15 := innerABI.1 .r15 (by simp)
    _ = innerPad.regValue .r15 := innerSetupAgrees.read (n := 64) (r := 15) (by simp)
    _ = s.regValue .r15 := innerPadAgrees.read (n := 64) (r := 15) (by simp [Pad.components])
    _ = initial.regValue .rcx := state.ikmPtr
  have ikmLen : outer.regValue .r14 = initial.regValue .r8 := calc
    _ = outerSetup.regValue .r14 := outerABI.1 .r14 (by simp)
    _ = outerPad.regValue .r14 := outerSetupAgrees.read (n := 64) (r := 14) (by simp)
    _ = inner.regValue .r14 := outerPadAgrees.read (n := 64) (r := 14) (by simp [Pad.components])
    _ = innerSetup.regValue .r14 := innerABI.1 .r14 (by simp)
    _ = innerPad.regValue .r14 := innerSetupAgrees.read (n := 64) (r := 14) (by simp)
    _ = s.regValue .r14 := innerPadAgrees.read (n := 64) (r := 14) (by simp [Pad.components])
    _ = initial.regValue .r8 := state.ikmLen
  have same := preserve_inner pre.call.stack padMemory hashMemory
  have hashI := hashState_of_bytes innerHash (show (Component.mem (slot initial 456) 32).Agrees
    inner outer from fun i hi ↦ same i (by omega))
  have sameCount : (Component.mem (slot initial 456 + 32) 8).Agrees inner outer := by
    intro i hi
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using same (32 + i) (by omega)
  have addrI : slot initial 456 + 32 = slot initial 424 :=
    slot_add initial (offset := 456) (delta := 32) (by decide)
  have countI : loadBytes outer.external (base initial + 32) 8 = .ok 1 := by
    change loadBytes outer.external (slot initial 456 + 32) 8 = _
    rw [agrees_loadBytes sameCount, addrI]
    exact innerBlocks
  have addrO : base initial + 40 = slot initial 416 := base_add initial (offset := 40) (by decide)
  have countO : base initial + 72 = slot initial 384 := base_add initial (offset := 72) (by decide)
  apply Initialize.assemble pre outerFrame outerRet ikmPtr ikmLen hashI countI
  · rw [addrO]
    exact outerHash
  · rw [countO]
    exact outerBlocks

end Hkdf.Proofs.NewExpand.Extract
