import Sha3.Spec.Program
import X86Proofs.Program.Agrees

namespace X86Proofs

open X86.Machine

@[simp] def scalarClobber : Component → Bool
  | .reg _ | .flags | .rip | .mem _ _ | .xmm _ => true
  | _ => false

@[ext] structure ScalarFrame where
  rest : RamState
  direction : BitVec 1
  mxcsr : BitVec 32
  fpr : BitVec 3 → BitVec 80
  fsw : BitVec 16
  fcc : BitVec 4
  ftw : BitVec 16
  fcw : BitVec 16
  fpuPtr : BitVec 171

def scalarFrame (s : RamState) : ScalarFrame where
  rest := fixedPart s
  direction := dfBit s.RFLAGS
  mxcsr := s.MXCSR
  fpr := fun r => s.FP87[fprIndex r]
  fsw := fswRest s.FP87_Status
  fcc := fswCC s.FP87_Status
  ftw := s.FP87_Tag_Word
  fcw := s.FP87_Control
  fpuPtr := fpuPtrOf s

theorem AgreesExcept.scalarFrame_eq {cs : List Component} {s t : RamState}
    (h : AgreesExcept cs s t) (hcs : cs.all scalarClobber = true) :
    scalarFrame t = scalarFrame s := by
  have apart (c : Component) (hc : scalarClobber c = false) : c ∉ cs := by
    intro hmem
    exact Bool.noConfusion (hc.symm.trans (List.all_eq_true.mp hcs c hmem))
  apply ScalarFrame.ext
  · exact h.rest
  · exact h.df (apart _ rfl)
  · exact h.mxcsr (apart _ rfl)
  · exact funext fun r => h.fpr (apart (.fpr r) rfl)
  · exact h.fsw (apart _ rfl)
  · exact h.fcc (apart _ rfl)
  · exact h.ftw (apart _ rfl)
  · exact h.fcw (apart _ rfl)
  · exact h.fpuPtr (apart _ rfl)

end X86Proofs

namespace Sha3.Proofs

open Sha3.Spec.Program Prelude X86

theorem memoryWriteFrame_refl (s : Machine.RamState) (regions : Vector MemoryRegion n) :
    MemoryWriteFrame s s regions := by
  intro address h
  rfl

theorem memoryWriteFrame_trans {a b c : Machine.RamState} {regions : Vector MemoryRegion n}
    (hab : MemoryWriteFrame a b regions) (hbc : MemoryWriteFrame b c regions) :
    MemoryWriteFrame a c regions := by
  intro address h
  exact (hbc address h).trans (hab address h)

theorem memoryWriteFrame_eq_of_avoids {a b : Machine.RamState}
    {regions : Vector MemoryRegion n} {forbidden : BitVec 64 → Prop}
    (hframe : MemoryWriteFrame a b regions)
    (havoid : ∀ region ∈ regions, region.Avoids forbidden)
    {address : BitVec 64} (haddress : forbidden address) :
    b.external[address]? = a.external[address]? := by
  apply hframe address
  intro region hregion hcontains
  exact havoid region hregion address hcontains haddress

theorem programLoaded_of_memoryWriteFrame {a b : Machine.RamState}
    {regions : Vector MemoryRegion n}
    (hframe : MemoryWriteFrame a b regions)
    (havoid : ∀ region ∈ regions, region.Avoids InProgram)
    (hloaded : ProgramLoaded a) : ProgramLoaded b := by
  intro address byte hbyte
  rw [memoryWriteFrame_eq_of_avoids hframe havoid ⟨byte, hbyte⟩]
  exact hloaded address byte hbyte

theorem inPageTables_root (i : Fin 8) :
    InPageTables (BitVec.ofNat 64 (0x1000 + i.val)) := by
  refine ⟨⟨0x1000, 8⟩, by simp, ?_⟩
  simp only [MemoryRegion.Contains, BitVec.toNat_ofNat]
  have := i.isLt
  constructor <;> omega

theorem inPageTables_leaf (page : Fin 4) (i : Fin 8) :
    InPageTables (BitVec.ofNat 64 (0x2000 + 8 * page.val + i.val)) := by
  refine ⟨⟨0x2000, 32⟩, by simp, ?_⟩
  simp only [MemoryRegion.Contains, BitVec.toNat_ofNat]
  have := i.isLt
  have := page.isLt
  constructor <;> omega

theorem identityMappedMemory_of_memoryWriteFrame {a b : Machine.RamState}
    {regions : Vector MemoryRegion n}
    (hframe : MemoryWriteFrame a b regions)
    (havoid : ∀ region ∈ regions, region.Avoids InPageTables)
    (hcr3 : b.CR3 = a.CR3) (hmemory : IdentityMappedMemory a) :
    IdentityMappedMemory b := by
  refine ⟨hcr3.trans hmemory.cr3, ?_, ?_⟩
  · intro i
    rw [memoryWriteFrame_eq_of_avoids hframe havoid (inPageTables_root i)]
    exact hmemory.tables.1 i
  · intro page i
    rw [memoryWriteFrame_eq_of_avoids hframe havoid (inPageTables_leaf page i)]
    exact hmemory.tables.2 page i

theorem memoryWriteFrame_mono {a b : Machine.RamState}
    {regions : Vector MemoryRegion n} {larger : Vector MemoryRegion m}
    (hframe : MemoryWriteFrame a b regions)
    (hcover : ∀ region ∈ regions, ∀ address, region.Contains address →
      ∃ target ∈ larger, target.Contains address) : MemoryWriteFrame a b larger := by
  intro address hout
  apply hframe address
  intro region hr hin
  obtain ⟨target, ht, hcontains⟩ := hcover region hr address.toNat hin
  exact hout target ht hcontains

theorem hasBytes_of_memoryWriteFrame {a b : Machine.RamState}
    {regions : Vector MemoryRegion n} {region : MemoryRegion} {bytes : ByteArray}
    (hframe : MemoryWriteFrame a b regions) (hbytes : region.HasBytes a.external bytes)
    (hrange : region.start + bytes.size ≤ 2^64)
    (hdisjoint : ∀ target ∈ regions, region.Disjoint target) :
    region.HasBytes b.external bytes := by
  refine ⟨hbytes.1, fun i ↦ ?_⟩
  rw [hframe]
  · exact hbytes.2 i
  · intro target ht
    apply hdisjoint target ht
    have hi := i.isLt
    have hsize : bytes.size = region.size := hbytes.1
    simp only [MemoryRegion.Contains, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    constructor <;> omega

theorem input_hasBytes_of_memoryWriteFrame {initial final : Machine.RamState}
    {inputs : Array Input} {i : Fin inputs.size} {writable : Vector MemoryRegion n}
    (hinput : ValidInputSlice initial inputs i) (hsep : MemorySeparation (readRegions initial inputs) writable)
    (hframe : MemoryWriteFrame initial final writable) :
    inputs[i].region.HasBytes final.external inputs[i].bytes := by
  refine hasBytes_of_memoryWriteFrame hframe hinput.2.2.2.2 ?_ ?_
  · have hb := hinput.2.2.2.1
    change inputs[i].address.toNat + inputs[i].bytes.size < 2 ^ 32 at hb
    change inputs[i].address.toNat + inputs[i].bytes.size ≤ 2 ^ 64
    omega
  · intro target ht
    apply (hsep.2 target ht).1
    simp only [readRegions, List.mem_cons, Array.mem_toList_iff]
    exact Or.inr (Or.inr (Array.mem_map.mpr ⟨inputs[i], Array.getElem_mem _, rfl⟩))

end Sha3.Proofs
