import Prelude.Memory
import K256.Proofs.Common.Refine.Lemma.Region
import K256.Proofs.Common.Refine.Lemma.Frame
import K256.Proofs.Common.Lift.Simulation
namespace K256.Proofs.Refine

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift Prelude

theorem exists_mem_toCodeMap {sections : ImageSections} {s : ImageSection} (hs : s ∈ sections)
    {a : BitVec 64} (h₁ : s.address.toNat ≤ a.toNat)
    (h₂ : a.toNat < s.address.toNat + s.bytes.size) : ∃ b, (a, b) ∈ sections.toCodeMap := by
  have hi : a.toNat - s.address.toNat < s.bytes.toList.length := by
    rw [chunked_toList_length]
    omega
  have ha : s.address + BitVec.ofNat 64 (a.toNat - s.address.toNat) = a := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := a.isLt
    rw [Nat.mod_eq_of_lt (a := a.toNat - s.address.toNat) (by omega)]
    rw [show s.address.toNat + (a.toNat - s.address.toNat) = a.toNat by omega,
      Nat.mod_eq_of_lt this]
  have h := mem_codeRange s.address s.bytes.toList _ hi
  rw [ha] at h
  exact ⟨_, List.mem_flatMap.2 ⟨s, hs, h⟩⟩

namespace FrameInfo

def callSlotBytes (m : FrameInfo) : CodeMap :=
  m.callSlots.flatMap fun c => codeRange c.1 (wordBytes c.2)

theorem mem_callSlotBytes {m : FrameInfo} {c : BitVec 64 × BitVec 64} (hc : c ∈ m.callSlots)
    {i : Nat} (hi : i < 8) : (c.1 + BitVec.ofNat 64 i, storedByte c.2 i) ∈ m.callSlotBytes := by
  refine List.mem_flatMap.2 ⟨c, hc, ?_⟩
  have := mem_codeRange c.1 (wordBytes c.2) i (by simp only [wordBytes, List.length_ofFn]; omega)
  simpa only [wordBytes, List.getElem_ofFn] using this

theorem callSlots_of_loaded {m : FrameInfo} {mem : Ram}
    (hloaded : ∀ x ∈ m.callSlotBytes, mem[x.1]? = some x.2)
    (hlow : ∀ c ∈ m.callSlots, c.1.toNat + 8 ≤ 2 ^ 32) :
    ∀ c ∈ m.callSlots, Readable mem c.1 8 ∧ memLoad mem c.1 64 = c.2 := by
  intro c hc
  have hb : Bytes mem c.1 (64 / 8) (storedByte c.2) := fun i hi =>
    hloaded _ (mem_callSlotBytes hc (by omega))
  exact ⟨⟨hlow c hc, fun i hi => by rw [hb i (by omega)]; rfl⟩,
    hb.memLoad (by decide) (by decide)⟩

def CallSlotsIn (m : FrameInfo) (s : ImageSection) : Prop :=
  ∀ c ∈ m.callSlots, c.1.toNat + 8 ≤ 2 ^ 32 ∧ s.address.toNat ≤ c.1.toNat ∧
    8 ≤ s.bytes.chunkSize ∧ c.1.toNat - s.address.toNat + 8 ≤ s.bytes.size ∧
    chunkedRead s.bytes (c.1.toNat - s.address.toNat) 8 = wordBytes c.2

instance (m : FrameInfo) (s : ImageSection) : Decidable (m.CallSlotsIn s) := by
  unfold CallSlotsIn
  infer_instance

theorem callSlotBytes_sub {m : FrameInfo} {sections : ImageSections} {s : ImageSection}
    (hs : s ∈ sections) (h : m.CallSlotsIn s) : ∀ x ∈ m.callSlotBytes, x ∈ sections.toCodeMap := by
  intro x hx
  obtain ⟨c, hc, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨-, hge, hcs, hle, hread⟩ := h c hc
  have hp : s.address + BitVec.ofNat 64 (c.1.toNat - s.address.toNat) = c.1 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := c.1.isLt
    rw [Nat.mod_eq_of_lt (a := c.1.toNat - s.address.toNat) (by omega),
      show s.address.toNat + (c.1.toNat - s.address.toNat) = c.1.toNat by omega,
      Nat.mod_eq_of_lt this]
  exact codeRange_sub_section hs _ 8 hread hcs hle hp x hx

theorem callSlots_of_section {m : FrameInfo} {sections : ImageSections} {s : ImageSection}
    (hs : s ∈ sections) (h : m.CallSlotsIn s) {mem : Ram}
    (hloaded : ∀ x ∈ sections.toCodeMap, mem[x.1]? = some x.2) :
    ∀ c ∈ m.callSlots, Readable mem c.1 8 ∧ memLoad mem c.1 64 = c.2 :=
  callSlots_of_loaded (fun x hx => hloaded x (callSlotBytes_sub hs h x hx)) fun c hc => (h c hc).1

def CallSlotSpanIn (m : FrameInfo) (s : ImageSection) : Prop :=
  s.address.toNat ≤ slotsLow m.callSlots ∧
    slotsHigh m.callSlots ≤ s.address.toNat + s.bytes.size

instance (m : FrameInfo) (s : ImageSection) : Decidable (m.CallSlotSpanIn s) := by
  unfold CallSlotSpanIn
  infer_instance

theorem callSlotSpan_of_section {m : FrameInfo} {sections : ImageSections} {s : ImageSection}
    (hs : s ∈ sections) (h : m.CallSlotSpanIn s) :
    ∀ a : BitVec 64, slotsLow m.callSlots ≤ a.toNat → a.toNat < slotsHigh m.callSlots →
      ∃ b, (a, b) ∈ sections.toCodeMap :=
  fun _ h₁ h₂ => exists_mem_toCodeMap hs (by have := h.1; omega) (by have := h.2; omega)

theorem slotsLow_lt_slotsHigh {cs : List (BitVec 64 × BitVec 64)} (h : cs ≠ []) :
    slotsLow cs < slotsHigh cs := by
  cases cs with
  | nil => exact absurd rfl h
  | cons c rest =>
    simp only [slotsLow, slotsHigh, List.map_cons, List.foldr_cons]
    omega

theorem slotsHigh_le {cs : List (BitVec 64 × BitVec 64)} {b : Nat}
    (h : ∀ c ∈ cs, c.1.toNat + 8 ≤ b) : slotsHigh cs ≤ b := by
  induction cs with
  | nil => exact Nat.zero_le _
  | cons c rest ih =>
    simp only [slotsHigh, List.map_cons, List.foldr_cons] at ih ⊢
    have := h c List.mem_cons_self
    have := ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    omega

end FrameInfo

def Activation.ofEntry (s : RamState) (stackBytes : Nat) (ret : BitVec 64) : Activation where
  original := s.external
  rsp := s.regValue .rsp
  ret := ret
  low := BitVec.ofNat 64 ((s.regValue .rsp).toNat - stackBytes)
  rbx := s.regValue .rbx
  rbp := s.regValue .rbp
  r12 := s.regValue .r12
  r13 := s.regValue .r13
  r14 := s.regValue .r14
  r15 := s.regValue .r15
  rdi := s.regValue .rdi
  rsi := s.regValue .rsi
  rdx := s.regValue .rdx
  rcx := s.regValue .rcx
  r8 := s.regValue .r8
  r9 := s.regValue .r9
  mxcsr := (Operand.mxcsr : Operand 32).read s
  ftw := (Operand.ftw : Operand 16).read s
  fcw := (Operand.fcw : Operand 16).read s
  fs := s.FS

namespace Activation

variable {s : RamState} {stackBytes : Nat} {ret : BitVec 64}

theorem ofEntry_regs : ∀ r ∈ entryNumbers,
    (Reg.ofIndex r).read s = ⟨64, (ofEntry s stackBytes ret).entryReg r⟩ := by
  intro r hr
  simp only [entryNumbers, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

theorem ofEntry_low_toNat :
    (ofEntry s stackBytes ret).low.toNat = (s.regValue .rsp).toNat - stackBytes := by
  change (BitVec.ofNat 64 ((s.regValue .rsp).toNat - stackBytes)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.regValue .rsp).isLt; omega)]

end Activation

private theorem stack_start (s : RamState) (n : Nat) :
    (Stack.region s n).start = (s.regValue .rsp).toNat - n := rfl

private theorem stack_end (s : RamState) (n : Nat) :
    (Stack.region s n).start + (Stack.region s n).size = (s.regValue .rsp).toNat + 8 := by
  change (s.regValue .rsp).toNat - n + ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - n))
    = _
  omega

theorem memLoad_returnSlot {s : RamState} {ret : BitVec 64}
    (h : (Stack.returnSlot s).Word64At s.external ret) :
    memLoad s.external (s.regValue .rsp) 64 = ret := by
  have h' := memLoad_of_word64At h
  rwa [show (Stack.returnSlot s).start = (s.regValue .rsp).toNat from rfl, BitVec.ofNat_toNat,
    BitVec.setWidth_eq] at h'

theorem FrameInfo.Pre.of_sysV {m : FrameInfo} {code : CodeMap} {s : RamState} {stackBytes : Nat}
    {ret : BitVec 64} {forbidden : BitVec 64 → Prop}
    (hrip : s.RIP = m.entry)
    (hstack : Stack.Valid s stackBytes) (hwindow : m.window ≤ stackBytes)
    (havoid : (Stack.region s stackBytes).Avoids forbidden)
    (hcode : ∀ x ∈ code, forbidden x.1)
    (htables : ∀ b : BitVec 64, ¬ PageTableEntriesApart b.toNat 1 → forbidden b)
    (hret : memLoad s.external (s.regValue .rsp) 64 = ret)
    (hretLow : ret.toNat < 2 ^ 32) (hretOutside : ∀ x ∈ code, x.1 ≠ ret)
    (hslots : ∀ c ∈ m.callSlots, Readable s.external c.1 8 ∧ memLoad s.external c.1 64 = c.2)
    (hspan : m.callSlots ≠ [] → ∀ a : BitVec 64, slotsLow m.callSlots ≤ a.toNat →
      a.toNat < slotsHigh m.callSlots → forbidden a)
    (hdf : RFLAGS.DirectionFlagClear s.RFLAGS) :
    m.Pre code (Activation.ofEntry s stackBytes ret) s := by
  have hbound : (Stack.region s stackBytes).Bounded := hstack.1
  have halloc : (Stack.region s stackBytes).Allocated s.external := hstack.2.1
  have hnu : stackBytes ≤ (s.regValue .rsp).toNat := hstack.2.2.1
  have hstart := stack_start s stackBytes
  have hend := stack_end s stackBytes
  have hrsp := (s.regValue .rsp).isLt
  refine
    { rip := hrip
      original := rfl
      regs := Activation.ofEntry_regs
      ret := hret
      retLow := hretLow
      retOutside := hretOutside
      slot := ?_
      window := fun hpos => ?_
      room := ?_
      align := hstack.2.2.2
      callSlots := hslots
      callSlotsApart := fun hne => ?_
      df := hdf
      mxcsr := rfl
      ftw := rfl
      fcw := rfl
      fs := rfl }
  · change Readable s.external (s.regValue .rsp) 8
    exact Readable.of_allocated hbound halloc (by rw [hstart]; omega) (by omega)
  · change Writable code s.external (s.regValue .rsp - BitVec.ofNat 64 m.window) m.window
    have hle : BitVec.ofNat 64 m.window ≤ s.regValue .rsp := by
      rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hw : (s.regValue .rsp - BitVec.ofNat 64 m.window).toNat =
        (s.regValue .rsp).toNat - m.window := by
      rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Writable.of_avoids hbound halloc havoid hcode htables (by rw [hw, hstart]; omega)
      (by rw [hw]; omega) hpos
  · change (Activation.ofEntry s stackBytes ret).low.toNat + m.window ≤ (s.regValue .rsp).toNat
    rw [Activation.ofEntry_low_toNat]
    omega
  · have hhi : slotsHigh m.callSlots ≤ 2 ^ 32 :=
      FrameInfo.slotsHigh_le fun c hc => (hslots c hc).1.low
    have hlt := FrameInfo.slotsLow_lt_slotsHigh hne
    have h := apart_of_avoids havoid (hspan hne) (by omega) hlt (by omega)
    change slotsHigh m.callSlots + m.window ≤ (s.regValue .rsp).toNat ∨
      (s.regValue .rsp).toNat ≤ slotsLow m.callSlots
    omega

end K256.Proofs.Refine
