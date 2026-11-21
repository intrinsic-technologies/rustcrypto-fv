import Sha3.Proofs.Wrapper.Finish.Plain.Code
import Sha3.Proofs.Wrapper.Finish.Arguments
import Sha3.Proofs.Wrapper.Setup.Basic
import Sha3.Proofs.Wrapper.Frame
import Sha3.Proofs.Wrapper.Finish.Code
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

namespace Sha3.Proofs.Wrapper.Finish.Plain

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

structure CopyPre [bindings : Bindings] (initial : RamState) (v : Variant)
    (inputs : Array Input) (split : Nat) (out : BitVec 64)
    (digest : Vector UInt8 v.digestBytes) (s : RamState) (keccak : Bool := false) (mode : Mode := .plain) : Prop where
  invocation : ValidInvocation bindings v mode initial inputs split keccak
  invariant : Invariant initial v mode s keccak
  saved : SavedFrame initial s mode
  rip : s.RIP = callAddress mode v keccak + (5 : BitVec 64)
  rsp : stackPtr s = frameBase initial v mode keccak
  pointer : (outputOperand initial v mode keccak).read s = out
  outputValid : ValidOutput initial ⟨out.toNat, v.digestBytes⟩
  outputMember : (⟨out.toNat, v.digestBytes⟩ : MemoryRegion) ∈ writeRegions initial v mode keccak
  outputApart : (⟨out.toNat, v.digestBytes⟩ : MemoryRegion).Disjoint
    (Stack.region initial (mode.entry v keccak).minStackBytes)
  digestBytes : ∀ i : Fin v.digestBytes,
    s.external[frameBase initial v mode keccak + BitVec.ofNat 64 (digestOffset mode + i.val)]? = some digest[i]
  mode : mode = .plain ∨ mode = .digest

def CopyPost [Bindings] (initial : RamState) (v : Variant) (out : BitVec 64)
    (digest : Vector UInt8 v.digestBytes) (s t : RamState) (keccak : Bool := false) (mode : Mode := .plain) : Prop :=
  Invariant initial v mode t keccak ∧ SavedFrame initial t mode ∧
    t.RIP = epilogueAddress mode v keccak ∧ stackPtr t = frameBase initial v mode keccak ∧
    (∀ i : Fin v.digestBytes, t.external[out + BitVec.ofNat 64 i.val]? = some digest[i]) ∧
    MemoryWriteFrame s t #v[Stack.region initial (mode.entry v keccak).minStackBytes,
      ⟨out.toNat, v.digestBytes⟩] ∧ CalleeSavedRegistersUnchanged s t

def copySteps (v : Variant) (mode : Mode := .plain) : Nat :=
  (match v with | .sha224 | .sha256 => 13 | .sha384 => 19 | .sha512 => 25) -
    if mode = .digest then 1 else 0

def copyOffset (v : Variant) (offset : Nat) (mode : Mode := .plain) : Nat :=
  if mode = .digest then
    offset + (if (match v with | .sha224 => 22 | .sha256 => 24 | .sha384 => 44 | .sha512 => 67) ≤ offset then 1 else 0) -
      (if (match v with | .sha224 => 42 | .sha256 => 44 | .sha384 => 64 | .sha512 => 87) ≤ offset then 5 else 0)
  else offset

theorem copy_end (v : Variant) (keccak : Bool := false) (mode : Mode := .plain)
    (hMode : mode = .plain ∨ mode = .digest := by exact Or.inl rfl) :
    callAddress mode v keccak + 5 + BitVec.ofNat 64 (copyBytes v mode).length =
      epilogueAddress mode v keccak := by
  rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel

def copyWrites (initial : RamState) (v : Variant) (out : BitVec 64) (keccak : Bool := false)
    (mode : Mode := .plain) :
    Vector MemoryRegion 2 :=
  #v[⟨(frameBase initial v mode keccak).toNat + Mode.plain.outputSlotOffset v keccak + 8,
    v.digestBytes⟩, ⟨out.toNat, v.digestBytes⟩]

theorem copyWrites_cover {keccak : Bool} {mode : Mode} {initial : RamState} {v : Variant} {out : BitVec 64}
    (hMode : mode = .plain ∨ mode = .digest)
    (hStack : Stack.Valid initial (mode.entry v keccak).minStackBytes) :
    ∀ region ∈ copyWrites initial v out keccak mode, ∀ address, region.Contains address →
      ∃ target ∈ #v[Stack.region initial (mode.entry v keccak).minStackBytes,
        (⟨out.toNat, v.digestBytes⟩ : MemoryRegion)], target.Contains address := by
  intro region hr address ha
  obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp hr
  have he : i = 0 ∨ i = 1 := by omega
  rcases he with rfl | rfl
  · refine ⟨_, Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, ?_⟩
    have hb : mode.frameSize v keccak ≤ (mode.entry v keccak).minStackBytes := by
      rw [Mode.stackBudget mode v keccak]; omega
    obtain ⟨hl, hu⟩ := frameBase_bounds hStack hb
    have hd : Mode.plain.outputSlotOffset v keccak + 8 + v.digestBytes ≤ mode.frameSize v keccak := by
      rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
    change (Stack.region initial (mode.entry v keccak).minStackBytes).start ≤ address ∧
      address < (Stack.region initial (mode.entry v keccak).minStackBytes).start +
        (Stack.region initial (mode.entry v keccak).minStackBytes).size
    change (frameBase initial v mode keccak).toNat + Mode.plain.outputSlotOffset v keccak + 8 ≤ address ∧
      address < (frameBase initial v mode keccak).toNat + Mode.plain.outputSlotOffset v keccak + 8 +
        v.digestBytes at ha
    constructor <;> omega
  · exact ⟨_, Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩, ha⟩

theorem copyMemory_saved {keccak : Bool} {mode : Mode} {initial s t : RamState} {v : Variant} {out : BitVec 64}
    (hMode : mode = .plain ∨ mode = .digest)
    (hStack : Stack.Valid initial (mode.entry v keccak).minStackBytes)
    (hApart : (⟨out.toNat, v.digestBytes⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry v keccak).minStackBytes))
    (hMemory : MemoryWriteFrame s t (copyWrites initial v out keccak mode))
    (hSaved : SavedFrame initial s mode) : SavedFrame initial t mode := by
  have hb : mode.frameSize v keccak ≤ (mode.entry v keccak).minStackBytes := by
    rw [Mode.stackBudget mode v keccak]; omega
  have hf : (frameBase initial v mode keccak).toNat =
      (initial.regValue .rsp).toNat - mode.frameSize v keccak :=
    stack_sub_toNat hStack.2.2.1 hb
  have hUnder := hStack.2.2.1
  change (mode.entry v keccak).minStackBytes ≤ (initial.regValue .rsp).toNat at hUnder
  have hSize : (mode.savedBytes) ≤ mode.frameSize v keccak := by rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
  have hLow : (initial.regValue .rsp).toNat + 8 < 2^32 := by
    have hh := hStack.1
    simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Bounded,
      userAddressLimit] at hh
    omega
  have hd : Mode.plain.outputSlotOffset v keccak + 8 + v.digestBytes ≤ mode.frameSize v keccak - (mode.savedBytes) := by
    rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
  have hBytes : ∀ j < (mode.savedBytes + 8),
      t.external[initial.regValue .rsp - BitVec.ofNat 64 mode.savedBytes + BitVec.ofNat 64 j]? =
        s.external[initial.regValue .rsp - BitVec.ofNat 64 mode.savedBytes + BitVec.ofNat 64 j]? := by
    intro j hj
    apply hMemory
    intro region hr ha
    have hAddr : (initial.regValue .rsp - BitVec.ofNat 64 mode.savedBytes + BitVec.ofNat 64 j).toNat =
        (initial.regValue .rsp).toNat - (mode.savedBytes) + j := by
      rw [BitVec.toNat_add, stack_sub_toNat hStack.2.2.1 (by omega), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp hr
    have he : i = 0 ∨ i = 1 := by omega
    rcases he with rfl | rfl
    · change (MemoryRegion.mk _ v.digestBytes).Contains _ at ha
      simp only [MemoryRegion.Contains, hAddr, hf] at ha
      omega
    · apply hApart _ ha
      simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains, hAddr]
      constructor <;> omega
  constructor
  · intro i
    rw [← hSaved.saved i]
    apply memLoad_congr
    intro j hj
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    change t.external[initial.regValue .rsp - BitVec.ofNat 64 mode.savedBytes + BitVec.ofNat 64 (8 * i.val) +
        BitVec.ofNat 64 j]? = s.external[initial.regValue .rsp - BitVec.ofNat 64 mode.savedBytes +
        BitVec.ofNat 64 (8 * i.val) + BitVec.ofNat 64 j]?
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hBytes (8 * i.val + j) (by
      have hi := i.isLt
      simp only [Mode.savedBytes]
      omega)
  · rw [← hSaved.returnSlot]
    apply memLoad_congr
    intro j hj
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    have he : initial.regValue .rsp + BitVec.ofNat 64 j =
        initial.regValue .rsp - BitVec.ofNat 64 mode.savedBytes + BitVec.ofNat 64 ((mode.savedBytes) + j) := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    change t.external[initial.regValue .rsp + BitVec.ofNat 64 j]? = s.external[_]?
    rw [he]
    exact hBytes _ (by omega)

theorem copy_effect_advance [bindings : Bindings]
    {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode} {inputs : Array Input} {split : Nat}
    {out p : BitVec 64} {bytes : List UInt8} {pre : RamState → Prop}
    {effect : RamState → Effect}
    (hMode : mode = .plain ∨ mode = .digest)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak)
    (hInv : Invariant initial v mode s keccak) (hSaved : SavedFrame initial s mode)
    (hMember : (⟨out.toNat, v.digestBytes⟩ : MemoryRegion) ∈ writeRegions initial v mode keccak)
    (hApart : (⟨out.toNat, v.digestBytes⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry v keccak).minStackBytes))
    (step : StepEffect pre (codeRange p bytes) effect) (image : ImageAt p bytes)
    (hWrites : WritesWithin (effect s).components (copyWrites initial v out keccak mode))
    (hNoRsp : Component.reg 4 ∉ (effect s).components)
    (hRsp : stackPtr s = frameBase initial v mode keccak) (hp : pre s)
    (hd : Component.df ∉ (effect s).components := by exact of_decide_eq_true rfl) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ Invariant initial v mode t keccak ∧
      SavedFrame initial t mode ∧ stackPtr t = frameBase initial v mode keccak ∧
      (effect s).Holds s t ∧ MemoryWriteFrame s t (copyWrites initial v out keccak mode) := by
  obtain ⟨t, ht, hr, he⟩ := step s hInv.ready (image.code hInv.loaded) hp
  have hMem := he.agrees.memoryWriteFrame hWrites
  have hSp : stackPtr t = frameBase initial v mode keccak :=
    (he.agrees.read (n := 64) hNoRsp).trans hRsp
  have hCover : WritesWithin (effect s).components (writeRegions initial v mode keccak) := by
    intro c hc address ha
    obtain ⟨r, hregion, hcontains⟩ := hWrites c hc address ha
    obtain ⟨target, htarget, hcontains⟩ :=
      copyWrites_cover hMode hCall.stackAvailable r hregion address.toNat hcontains
    refine ⟨target, ?_, hcontains⟩
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp htarget
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · exact stack_mem_writeRegions initial v mode keccak
    · exact hMember
  refine ⟨t, Advances.of_step ht (.inr ?_),
    hInv.of_agreesExcept hCall hr he.agrees hCover hd,
    copyMemory_saved hMode hCall.stackAvailable hApart hMem hSaved, hSp, he, hMem⟩
  change stackPtr t ≠ _
  rw [hSp]
  exact stackSub_ne_returnBoundary initial _ (by rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> decide)

namespace CopyPre

variable [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
  {inputs : Array Input} {split : Nat} {out : BitVec 64} {digest : Vector UInt8 v.digestBytes}
  (h : CopyPre initial v inputs split out digest s keccak mode)
include h

theorem stackRead (offset n : Nat) (hr : offset + n ≤ mode.frameSize v keccak + 8) :
    MemReadable s (frameBase initial v mode keccak + BitVec.ofNat 64 offset) n :=
  h.invariant.frameReadable h.invocation.stackAvailable hr

theorem outputOffset_toNat (offset : Nat) (hr : offset ≤ v.digestBytes) :
    (out + BitVec.ofNat 64 offset).toNat = out.toNat + offset := by
  have hb : out.toNat + v.digestBytes < 2^32 := h.outputValid.2.1
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem outputRead (offset n : Nat) (hr : offset + n ≤ v.digestBytes) :
    MemReadable s (out + BitVec.ofNat 64 offset) n := by
  apply memReadable_of_region h.outputValid.2.1
  · intro address ha
    exact Option.isSome_iff_exists.mp
      (h.invariant.grows address (Option.isSome_iff_exists.mpr (h.outputValid.2.2 address ha)))
  · change out.toNat ≤ _
    rw [h.outputOffset_toNat offset (by omega)]
    omega
  · change (out + BitVec.ofNat 64 offset).toNat + n ≤ out.toNat + v.digestBytes
    rw [h.outputOffset_toNat offset (by omega)]
    omega

theorem stack_avoid (offset : Nat) (hr : offset < mode.frameSize v keccak + 8) :
    ¬ (InProgram (frameBase initial v mode keccak + BitVec.ofNat 64 offset) ∨
      InPageTables (frameBase initial v mode keccak + BitVec.ofNat 64 offset)) := by
  apply writeRegions_avoid h.invocation _ (stack_mem_writeRegions initial v mode keccak)
  exact frameAddress_contains h.invocation.stackAvailable (by rw [Mode.stackBudget mode v keccak]; omega) hr

theorem output_avoid (offset : Nat) (hr : offset < v.digestBytes) :
    ¬ (InProgram (out + BitVec.ofNat 64 offset) ∨ InPageTables (out + BitVec.ofNat 64 offset)) := by
  apply writeRegions_avoid h.invocation _ h.outputMember
  change out.toNat ≤ (out + BitVec.ofNat 64 offset).toNat ∧
    (out + BitVec.ofNat 64 offset).toNat < out.toNat + v.digestBytes
  rw [h.outputOffset_toNat offset (by omega)]
  constructor <;> omega

end CopyPre

namespace CopyPre

variable [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
  {inputs : Array Input} {split : Nat} {out : BitVec 64} {digest : Vector UInt8 v.digestBytes}
  (h : CopyPre initial v inputs split out digest s keccak mode)

include h

theorem ne_returnBoundary {address : BitVec 64} (ha : InProgram address) :
    address ≠ (returnBoundary initial).rip := by
  obtain ⟨a, hw, _, hn⟩ := h.invocation.returnAddress
  rw [returnBoundary_rip_of_word64At hw]
  intro he
  exact hn (he ▸ ha)

theorem stack_tables (offset n : Nat) (hr : offset + n ≤ mode.frameSize v keccak + 8) :
    ∀ i < n, ¬ InPageTables (frameBase initial v mode keccak + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) := by
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact fun ht ↦ h.stack_avoid (offset + i) (by omega) (.inr ht)

theorem output_tables (offset n : Nat) (hr : offset + n ≤ v.digestBytes) :
    ∀ i < n, ¬ InPageTables (out + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) := by
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact fun ht ↦ h.output_avoid (offset + i) (by omega) (.inr ht)

theorem stack_store_avoids (offset : Nat) {n : Nat} (value : BitVec n) (next : BitVec 64)
    (hr : offset + n / 8 ≤ mode.frameSize v keccak + 8) :
    (Effect.mk next [⟨(Operand.mem (frameBase initial v mode keccak + BitVec.ofNat 64 offset) : Operand n),
      value⟩] none).Avoids Extracted.programImage := by
  intro x hx c hc
  simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem,
    List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · rintro ⟨i, hi, he⟩
    apply h.stack_avoid (offset + i) (by omega)
    left
    refine ⟨x.2, ?_⟩
    have hh : frameBase initial v mode keccak + BitVec.ofNat 64 (offset + i) = x.1 := by
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he.symm
    rw [hh]
    exact hx
  · exact id

theorem output_store_avoids (offset : Nat) {n : Nat} (value : BitVec n) (next : BitVec 64)
    (hr : offset + n / 8 ≤ v.digestBytes) :
    (Effect.mk next [⟨(Operand.mem (out + BitVec.ofNat 64 offset) : Operand n), value⟩] none).Avoids
      Extracted.programImage := by
  intro x hx c hc
  simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem,
    List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · rintro ⟨i, hi, he⟩
    apply h.output_avoid (offset + i) (by omega)
    left
    refine ⟨x.2, ?_⟩
    have hh : out + BitVec.ofNat 64 (offset + i) = x.1 := by
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he.symm
    rw [hh]
    exact hx
  · exact id

end CopyPre

namespace CopyPre

variable [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
  {inputs : Array Input} {split : Nat} {out : BitVec 64} {digest : Vector UInt8 v.digestBytes}
  (h : CopyPre initial v inputs split out digest s keccak mode)

include h

theorem byte_of_load_eq {t : RamState}
    (hgrows : ∀ address : BitVec 64, (s.external[address]?).isSome → (t.external[address]?).isSome)
    (offset width : Nat) (hr : offset + width / 8 ≤ v.digestBytes)
    (hload : memLoad t.external (out + BitVec.ofNat 64 offset) width =
      memLoad s.external (frameBase initial v mode keccak + BitVec.ofNat 64 (digestOffset mode + offset)) width)
    (i : Nat) (hi : i < width / 8) :
    t.external[out + BitVec.ofNat 64 (offset + i)]? =
      some (digest[offset + i]'(by omega)) := by
  have hall := h.outputRead 0 v.digestBytes (by omega)
  simp only [BitVec.add_zero] at hall
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
    (hgrows _ (hall.mem (offset + i) (by omega)))
  have hh := memByte_of_memLoad_eq hload i hi
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc] at hh
  change (t.external[out + BitVec.ofNat 64 (offset + i)]?).getD 0 =
    (s.external[frameBase initial v mode keccak + BitVec.ofNat 64 (digestOffset mode + (offset + i))]?).getD 0 at hh
  rw [hb, h.digestBytes ⟨offset + i, by omega⟩] at hh
  rw [hb]
  simpa only [Option.getD_some, Fin.getElem_fin] using congrArg some hh

theorem post_of_effect {t : RamState} {effect : Effect}
    (hReady : ReadyToStep t) (he : effect.Holds s t)
    (hWrites : WritesWithin effect.components (copyWrites initial v out keccak mode))
    (hNoRsp : Component.reg 4 ∉ effect.components)
    (hKeep : ∀ register ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
      Component.reg (BitVec.ofNat 5 register.fin.val) ∉ effect.components)
    (hRip : effect.rip = epilogueAddress mode v keccak)
    (hOutput : ∀ i : Fin v.digestBytes, t.external[out + BitVec.ofNat 64 i.val]? = some digest[i])
    (hd : Component.df ∉ effect.components := by exact of_decide_eq_true rfl) :
    CopyPost initial v out digest s t keccak mode := by
  have hMem := he.agrees.memoryWriteFrame hWrites
  have hCover : WritesWithin effect.components (writeRegions initial v mode keccak) := by
    intro c hc address ha
    obtain ⟨r, hregion, hcontains⟩ := hWrites c hc address ha
    obtain ⟨target, htarget, hcontains⟩ :=
      copyWrites_cover h.mode h.invocation.stackAvailable r hregion address.toNat hcontains
    refine ⟨target, ?_, hcontains⟩
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp htarget
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · exact stack_mem_writeRegions initial v mode keccak
    · exact h.outputMember
  exact ⟨h.invariant.of_agreesExcept h.invocation hReady he.agrees hCover hd,
    copyMemory_saved h.mode h.invocation.stackAvailable h.outputApart hMem h.saved,
    he.rip.trans hRip, (he.agrees.read (n := 64) hNoRsp).trans h.rsp,
    hOutput, memoryWriteFrame_mono hMem (copyWrites_cover h.mode h.invocation.stackAvailable),
    calleeSavedRegistersUnchanged_of_agreesExcept he.agrees hKeep⟩

end CopyPre
namespace CopyPre

variable [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
  {inputs : Array Input} {split : Nat} {out : BitVec 64} {digest : Vector UInt8 v.digestBytes}
  (h : CopyPre initial v inputs split out digest s keccak mode)

include h

theorem stack_write {offset count : Nat} {address : BitVec 64}
    (hl : Mode.plain.outputSlotOffset v keccak + 8 ≤ offset)
    (hu : offset + count ≤ Mode.plain.outputSlotOffset v keccak + 8 + v.digestBytes)
    (hc : (Component.mem (frameBase initial v mode keccak + BitVec.ofNat 64 offset) count).Covers address) :
    ∃ region ∈ copyWrites initial v out keccak mode, region.Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hc
  refine ⟨_, Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, ?_⟩
  rw [BitVec.add_assoc, ← BitVec.ofNat_add,
    frameAddress_toNat h.invocation.stackAvailable
      (by rw [Mode.stackBudget mode v keccak]; omega) ?_]
  · change (frameBase initial v mode keccak).toNat + Mode.plain.outputSlotOffset v keccak + 8 ≤
        (frameBase initial v mode keccak).toNat + (offset + i) ∧
      (frameBase initial v mode keccak).toNat + (offset + i) <
        (frameBase initial v mode keccak).toNat + Mode.plain.outputSlotOffset v keccak + 8 + v.digestBytes
    constructor <;> omega
  · have hb : Mode.plain.outputSlotOffset v keccak + 8 + v.digestBytes ≤ mode.frameSize v keccak := by
      rcases h.mode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
    omega

theorem output_write {offset count : Nat} {address : BitVec 64}
    (hu : offset + count ≤ v.digestBytes)
    (hc : (Component.mem (out + BitVec.ofNat 64 offset) count).Covers address) :
    ∃ region ∈ copyWrites initial v out keccak mode, region.Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hc
  refine ⟨_, Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩, ?_⟩
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.outputOffset_toNat (offset + i) (by omega)]
  change out.toNat ≤ out.toNat + (offset + i) ∧
    out.toNat + (offset + i) < out.toNat + v.digestBytes
  constructor <;> omega

end CopyPre

namespace CopyPre

variable [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
  {inputs : Array Input} {split : Nat} {out : BitVec 64} {digest : Vector UInt8 v.digestBytes}
  (h : CopyPre initial v inputs split out digest s keccak mode)

include h

theorem load_output_store (memory : Ram) (offset sourceOffset : BitVec 64)
    {n : Nat} (value : BitVec n) (width : Nat)
    (houtput : offset.toNat + n / 8 ≤ v.digestBytes)
    (hsource : sourceOffset.toNat + width / 8 ≤ mode.frameSize v keccak + 8) :
    memLoad (memStore memory (out + offset) value)
      (frameBase initial v mode keccak + sourceOffset) width =
      memLoad memory (frameBase initial v mode keccak + sourceOffset) width := by
  apply memLoad_congr
  intro j hj
  simp only [memByte, PhysicalMemory.read]
  rw [memStore_getElem?_of_ne]
  intro i hi he
  have he' : out + BitVec.ofNat 64 (offset.toNat + i) =
      frameBase initial v mode keccak + BitVec.ofNat 64 (sourceOffset.toNat + j) := by
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      ← BitVec.add_assoc] using he
  apply h.outputApart (out + BitVec.ofNat 64 (offset.toNat + i)).toNat
  · change out.toNat ≤ (out + BitVec.ofNat 64 (offset.toNat + i)).toNat ∧
      (out + BitVec.ofNat 64 (offset.toNat + i)).toNat < out.toNat + v.digestBytes
    rw [h.outputOffset_toNat _ (by omega)]
    constructor <;> omega
  · rw [he']
    exact frameAddress_contains h.invocation.stackAvailable
      (by rw [Mode.stackBudget mode v keccak]; omega) (by omega)

theorem load_output_store_zero (memory : Ram) (sourceOffset : BitVec 64)
    {n : Nat} (value : BitVec n) (width : Nat)
    (houtput : n / 8 ≤ v.digestBytes)
    (hsource : sourceOffset.toNat + width / 8 ≤ mode.frameSize v keccak + 8) :
    memLoad (memStore memory out value) (frameBase initial v mode keccak + sourceOffset) width =
      memLoad memory (frameBase initial v mode keccak + sourceOffset) width := by
  simpa using
    h.load_output_store memory 0 sourceOffset value width (by simpa using houtput) hsource

end CopyPre

end Sha3.Proofs.Wrapper.Finish.Plain
