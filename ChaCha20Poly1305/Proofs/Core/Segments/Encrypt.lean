import ChaCha20Poly1305.Proofs.Core.Cuts
import ChaCha20Poly1305.Proofs.Callee100a80
import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Code
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Test.Generated.R8.Triple
import X86Proofs.Instructions.Branch.Triple
import ChaCha20Poly1305.Proofs.Common.Refine.Lemma.Region
import X86Proofs.Step.Sse

namespace ChaCha20Poly1305.Proofs.Core.Encrypt

open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CoreContract
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

abbrev rd (u : RamState) (n : BitVec 5) : BitVec 64 := (Operand.reg n : Operand 64).read u

def Same (W : Nat → Prop) (a b : RamState) : Prop :=
  ∀ x : BitVec 64, ¬ W x.toNat → b.external[x]? = a.external[x]?

theorem Same.refl (W : Nat → Prop) (a : RamState) : Same W a a := fun _ _ => rfl

theorem Same.trans {W : Nat → Prop} {a b c : RamState} (h₁ : Same W a b) (h₂ : Same W b c) :
    Same W a c := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Same.mono {W W' : Nat → Prop} {a b : RamState} (h : Same W a b)
    (hw : ∀ x, W x → W' x) : Same W' a b := fun x hx => h x fun hW => hx (hw _ hW)

theorem Same.of_agrees {W : Nat → Prop} {cs : List Component} {a b : RamState}
    (h : AgreesExcept cs a b) (hw : ∀ c ∈ cs, ∀ x, c.Covers x → W x.toNat) : Same W a b :=
  fun x hx => h.byte fun c hc hcov => hx (hw c hc x hcov)

theorem Same.load {W : Nat → Prop} {a b : RamState} (h : Same W a b) {x : BitVec 64} {n : Nat}
    (hx : ∀ i < n / 8, ¬ W (x + BitVec.ofNat 64 i).toNat) :
    memLoad b.external x n = memLoad a.external x n := by
  apply memLoad_congr
  intro i hi
  simp only [memByte]
  exact congrArg (fun o => Option.getD o 0) (h _ (hx i hi))

theorem Same.hasBytes {W : Nat → Prop} {a b : RamState} (h : Same W a b) {r : MemoryRegion}
    {bytes : ByteArray} (hr : r.HasBytes a.external bytes) (hlow : r.start + r.size < 2 ^ 64)
    (hw : ∀ x, r.start ≤ x → x < r.start + r.size → ¬ W x) : r.HasBytes b.external bytes := by
  refine ⟨hr.1, fun i => ?_⟩
  have hi : i.val < r.size := by have := i.isLt; have := hr.1; unfold MemoryRegion.HasLength at this; omega
  rw [h _ ?_]
  · exact hr.2 i
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hw _ (by omega) (by omega)

theorem Same.word64At {W : Nat → Prop} {a b : RamState} (h : Same W a b) {r : MemoryRegion}
    {value : BitVec 64} (hr : r.Word64At a.external value) (hlow : r.start + 8 < 2 ^ 64)
    (hw : ∀ x, r.start ≤ x → x < r.start + 8 → ¬ W x) : r.Word64At b.external value := by
  refine ⟨hr.1, Bytes.loadBytes64 fun i hi => ?_⟩
  rw [h _ ?_]
  · exact Refine.bytes_of_word64At hr i hi
  · rw [← ofNat_toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := r.start) (by omega), Nat.mod_eq_of_lt (by omega)]
    exact hw _ (by omega) (by omega)

theorem word64At_of_load {m : Ram} {r : MemoryRegion} {value : BitVec 64} (hsize : r.size = 8)
    (hload : memLoad m (BitVec.ofNat 64 r.start) 64 = value)
    (hsome : ∀ i < 8, (m[BitVec.ofNat 64 r.start + BitVec.ofNat 64 i]?).isSome) :
    r.Word64At m value := by
  refine ⟨hsize.symm, Bytes.loadBytes64 ?_⟩
  have hb := Bytes.of_memLoad (n := 64) (m := m) (a := BitVec.ofNat 64 r.start) hsome
  rw [hload] at hb
  exact hb

theorem code_inProgram (off len : Nat) (h : off + len ≤ 11759) :
    ∀ j < len, InProgram (BitVec.ofNat 64 (0x100000 + off) + BitVec.ofNat 64 j) := by
  intro j hj
  have hs : Extracted.textBytes.size = 11759 := by decide
  have hp := text_address_in_program (off + j) (by omega)
  have he : BitVec.ofNat 64 (0x100000 + off) + BitVec.ofNat 64 j =
      Extracted.textAddress + BitVec.ofNat 64 (off + j) := by
    apply BitVec.eq_of_toNat_eq
    have h0 : (1048576 : BitVec 64).toNat = 1048576 := rfl
    simp only [Extracted.textAddress, BitVec.toNat_add, BitVec.toNat_ofNat, h0]
    omega
  rw [he]
  exact hp

theorem inProgram_of_toNat {a : BitVec 64} (h₁ : 0x100000 ≤ a.toNat)
    (h₂ : a.toNat < 0x100000 + 11759) : InProgram a := by
  have hs : Extracted.textBytes.size = 11759 := by decide
  have hp := text_address_in_program (a.toNat - 0x100000) (by omega)
  have he : Extracted.textAddress + BitVec.ofNat 64 (a.toNat - 0x100000) = a := by
    apply BitVec.eq_of_toNat_eq
    have h0 : Extracted.textAddress.toNat = 1048576 := rfl
    rw [BitVec.toNat_add, h0, BitVec.toNat_ofNat]
    omega
  rwa [he] at hp

theorem ne_boundary {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip)
    (a : BitVec 64) (h : 0x100000 ≤ a.toNat ∧ a.toNat < 0x100000 + 11759) : a ≠ boundary.rip := by
  intro he
  exact hOut (he ▸ inProgram_of_toNat h.1 h.2)

theorem step_run [Machine.Bindings] {pre : RamState → Prop} {e : RamState → Effect}
    {boundary : ReturnBoundary} {p : BitVec 64} {bytes : List UInt8}
    (hStep : StepEffect pre (codeRange p bytes) e) {u : RamState} (hr : ReadyToStep u)
    (hc : CodeIn Extracted.programImage u) (hbytes : CodeIn (codeRange p bytes) u)
    (hpre : pre u) (hne : (e u).rip ≠ boundary.rip)
    (hav : ∀ c ∈ (e u).components, ∀ a, c.Covers a → ¬ InProgram a) :
    ∃ v, Advances boundary 1 u v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      (e u).Holds u v := by
  obtain ⟨v, ha, hr', he⟩ := hStep.advances hr hbytes hpre hne
  refine ⟨v, ha, hr', he.codeIn ?_ hc, he⟩
  intro x hx c hcm hcov
  exact hav c hcm x.1 hcov (inProgram_of_mem hx)

theorem nonmem_not_covers {c : Component} (h : c.isMem = false) (x : BitVec 64) :
    ¬ c.Covers x := by
  cases c <;> simp_all [Component.Covers, Component.isMem]

theorem regs_av {cs : List Component} (h : ∀ c ∈ cs, c.isMem = false) :
    ∀ c ∈ cs, ∀ a, c.Covers a → ¬ InProgram a :=
  fun c hc a hcov => absurd hcov (nonmem_not_covers (h c hc) a)

theorem regs_within {W : Nat → Prop} {cs : List Component} (h : ∀ c ∈ cs, c.isMem = false) :
    ∀ c ∈ cs, ∀ x, c.Covers x → W x.toNat :=
  fun c hc a hcov => absurd hcov (nonmem_not_covers (h c hc) a)

theorem toNat_add_ofNat {a : BitVec 64} {k : Nat} (h : a.toNat + k < 2 ^ 64) :
    (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt h]

theorem toNat_sub_ofNat {a : BitVec 64} {k : Nat} (h : k ≤ a.toNat) :
    (a - BitVec.ofNat 64 k).toNat = a.toNat - k := by
  have hk : k < 2 ^ 64 := by have := a.isLt; omega
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  omega

theorem mem_within {W : Nat → Prop} {a : BitVec 64} {n : Nat} (ha : a.toNat + n < 2 ^ 64)
    (hw : ∀ j < n, W (a.toNat + j)) :
    ∀ x, (Component.mem a n).Covers x → W x.toNat := by
  rintro x ⟨j, hj, rfl⟩
  rw [toNat_add_ofNat (by omega)]
  exact hw j hj

theorem mem_av {a : BitVec 64} {n : Nat} (ha : a.toNat + n < 2 ^ 64)
    (hw : ∀ x : BitVec 64, a.toNat ≤ x.toNat → x.toNat < a.toNat + n → ¬ InProgram x) :
    ∀ x, (Component.mem a n).Covers x → ¬ InProgram x := by
  rintro x ⟨j, hj, rfl⟩
  apply hw <;> rw [toNat_add_ofNat (by omega)] <;> omega


theorem sib_rsp_addr (u : RamState) (d : Disp) (x : BitVec 64) :
    (AddrMode.sib 4 none 0 d).addr u x = stackPtr u + d.value := by
  simp only [AddrMode.addr, AddrMode.reg64]
  rw [stackPtr_eq_read]
  rfl

theorem base_addr (u : RamState) (b : BitVec 4) (d : Disp) (x : BitVec 64) :
    (AddrMode.base b d).addr u x = rd u (b.setWidth 5) + d.value := rfl

section Frame

variable {s : RamState}

structure StackFacts (s : RamState) : Prop where
  room : 992 ≤ (stackPtr s).toNat
  top : (stackPtr s).toNat + 8 < 2 ^ 32
  outside : ∀ a : BitVec 64, (stackPtr s).toNat - 992 ≤ a.toNat →
    a.toNat < (stackPtr s).toNat + 8 → ¬ InProgram a
  tables : (stackPtr s).toNat + 8 ≤ 0x1000 ∨ 0x2020 ≤ (stackPtr s).toNat - 992

theorem stack_contains {x : Nat} :
    (Stack.region s coreStackBytes).Contains x ↔
      (stackPtr s).toNat - 992 ≤ x ∧ x < (stackPtr s).toNat + 8 := by
  have hsp : s.regValue .rsp = stackPtr s := rfl
  simp only [MemoryRegion.Contains, Stack.region, hsp, coreStackBytes, Stack.returnAddressBytes]
  omega

theorem stack_facts [Machine.Bindings] {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) : StackFacts s := by
  obtain ⟨hb, -, hn, -⟩ := hPre.stack
  have hav := hPre.separation.2.2 (Stack.region s coreStackBytes) (by simp [coreWritten])
  have hsp : s.regValue .rsp = stackPtr s := rfl
  simp only [Stack.region, MemoryRegion.Bounded, userAddressLimit, Stack.NoUnderflow,
    Stack.returnAddressBytes, hsp, coreStackBytes] at hb hn
  have hav' : ∀ a : BitVec 64, (stackPtr s).toNat - 992 ≤ a.toNat →
      a.toNat < (stackPtr s).toNat + 8 → ¬ (InProgram a ∨ pageTables.Contains a.toNat) :=
    fun a h₁ h₂ => hav a (stack_contains.mpr ⟨h₁, h₂⟩)
  refine ⟨hn, by omega, fun a h₁ h₂ hp => hav' a h₁ h₂ (.inl hp), ?_⟩
  refine Classical.byContradiction fun hc => ?_
  let x : Nat := max ((stackPtr s).toNat - 992) 0x1000
  have hx : x < 2 ^ 64 := by omega
  apply hav' (BitVec.ofNat 64 x)
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]; omega
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]; omega
  · right
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
    simp only [pageTables, MemoryRegion.Contains]
    omega

theorem framePointer_toNat (hS : StackFacts s) : (framePointer s).toNat = frameBase s := by
  have := hS.room
  unfold framePointer frameBase frameBytes
  exact toNat_sub_ofNat (by omega)

theorem framePointer_add_toNat (hS : StackFacts s) {k : Nat} (hk : k ≤ 0x1c0) :
    (framePointer s + BitVec.ofNat 64 k).toNat = frameBase s + k := by
  have := hS.room
  have := hS.top
  rw [toNat_add_ofNat] <;> rw [framePointer_toNat hS] <;> unfold frameBase frameBytes <;> omega

theorem framePointer_sub_toNat (hS : StackFacts s) {k : Nat} (hk : k ≤ 0x228) :
    (framePointer s - BitVec.ofNat 64 k).toNat = frameBase s - k := by
  have := hS.room
  rw [toNat_sub_ofNat] <;> rw [framePointer_toNat hS] <;> unfold frameBase frameBytes <;> omega

theorem framePointer_add_eq (hS : StackFacts s) {k : Nat} (hk : k ≤ 0x1c0) :
    framePointer s + BitVec.ofNat 64 k = BitVec.ofNat 64 (frameBase s + k) := by
  apply BitVec.eq_of_toNat_eq
  rw [framePointer_add_toNat hS hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := hS.top
  unfold frameBase frameBytes
  omega

def preW (s : RamState) (x : Nat) : Prop :=
  (frameBase s - 8 ≤ x ∧ x < frameBase s) ∨ (frameBase s + 0x18 ≤ x ∧ x < frameBase s + 0x30)

theorem machineRamUnitStrideDecodable_of_ready [bindings : Machine.Bindings] {u : RamState}
    (h : ReadyToStep u) (hstride : UnitStringStride bindings) :
    MachineRamUnitStrideDecodable bindings u :=
  ⟨h.smrr, h.memoryType, hstride, h.features.lzcnt⟩

theorem ready_of_inv [bindings : Machine.Bindings] {t : RamState} {outPtr : BitVec 64}
    {length : Nat} (h : Inv s t outPtr length) : ReadyToStep t :=
  ReadyToStep.of_supported h.machine h.environment.smrr h.environment.memoryType
    (DecoderFeatures.of_supported h.machine h.environment.leadingZeroCount)

theorem stack_allocated [Machine.Bindings] {t : RamState} {outPtr : BitVec 64} {length : Nat}
    (h : Inv s t outPtr length) (a : BitVec 64) (h₁ : (stackPtr s).toNat - 992 ≤ a.toNat)
    (h₂ : a.toNat < (stackPtr s).toNat + 8) : (t.external[a]?).isSome := by
  obtain ⟨b, hb⟩ := h.allocated (Stack.region s coreStackBytes) (by simp [coreWritten]) a
    (stack_contains.mpr ⟨h₁, h₂⟩)
  simp [hb]

end Frame


theorem ext_of_regs {cs : List Component} {a b : RamState} (h : AgreesExcept cs a b)
    (hcs : ∀ c ∈ cs, c.isMem = false) : b.external = a.external :=
  h.external fun c hc x => nonmem_not_covers (hcs c hc) x

theorem same_of_regs {W : Nat → Prop} {cs : List Component} {a b : RamState}
    (h : AgreesExcept cs a b) (hcs : ∀ c ∈ cs, c.isMem = false) : Same W a b :=
  fun x _ => by rw [ext_of_regs h hcs]

theorem same_of_store {cs : List Component} {a b : RamState} (h : AgreesExcept cs a b)
    {addr : BitVec 64} {n : Nat} (hcs : cs = [.mem addr n, .rip]) (hlow : addr.toNat + n < 2 ^ 64) :
    Same (fun x => addr.toNat ≤ x ∧ x < addr.toNat + n) a b := by
  subst hcs
  apply Same.of_agrees h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact mem_within (W := fun x => addr.toNat ≤ x ∧ x < addr.toNat + n) hlow
      fun j hj => ⟨by omega, by omega⟩
  · exact fun x hx => absurd hx (nonmem_not_covers rfl x)

theorem memReadable_of_word {u : RamState} {r : MemoryRegion} {v : BitVec 64}
    (h : r.Word64At u.external v) (hb : r.start + 8 ≤ 2 ^ 32) :
    MemReadable u (BitVec.ofNat 64 r.start) 8 :=
  ⟨by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega,
    fun i hi => by rw [Refine.bytes_of_word64At h i hi]; rfl⟩

theorem allHold_single {s' : RamState} {w : Write} (h : Write.AllHold s' [w]) :
    w.dst.read s' = w.val := h

theorem mem_read_eq (u : RamState) (a : BitVec 64) :
    (Operand.mem a : Operand 64).read u = memLoad u.external a 64 := rfl

section Steps

variable [bindings : Machine.Bindings] {s : RamState}

omit bindings in
theorem stack_storePre (hS : StackFacts s) {u : RamState}
    (halloc : ∀ a : BitVec 64, (stackPtr s).toNat - 992 ≤ a.toNat →
      a.toNat < (stackPtr s).toNat + 8 → (u.external[a]?).isSome)
    {a : BitVec 64} (ha₁ : (stackPtr s).toNat - 992 ≤ a.toNat)
    (ha₂ : a.toNat + 8 ≤ (stackPtr s).toNat + 8) {p : BitVec 64} {len off : Nat}
    (hrip : u.RIP = p) (hp : p = BitVec.ofNat 64 (0x100000 + off)) (hoff : off + len ≤ 11759)
    {addr : RamState → BitVec 64} (haddr : addr u = a) : StorePre p len addr 8 u := by
  have htop := hS.top
  have htab := hS.tables
  refine ⟨hrip, haddr ▸ ⟨by omega, fun i hi => halloc _ ?_ ?_, by
    unfold PageTableEntriesApart; omega⟩, haddr ▸ ?_⟩
  · rw [toNat_add_ofNat (by omega)]; omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · intro i hi j hj he
    apply hS.outside (a + BitVec.ofNat 64 i)
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [he, hp]
      exact code_inProgram off len hoff j hj

structure AtCall (s t v : RamState) (length : Nat) (inPtr outPtr : BitVec 64) : Prop where
  ready : ReadyToStep v
  code : CodeIn Extracted.programImage v
  rip : v.RIP = 0x100a80
  rsp : stackPtr v = framePointer s - BitVec.ofNat 64 8
  rdi : rd v 7 = framePointer s + BitVec.ofNat 64 0xd0
  rsi : rd v 6 = framePointer s + BitVec.ofNat 64 0x18
  r12 : rd v 12 = outPtr
  r14 : rd v 14 = BitVec.ofNat 64 length
  r15 : rd v 15 = rd t 15
  rbx : rd v 3 = rd t 3
  df : DirectionFlagUnset v
  sse : SupportedSSE bindings.processor v
  grow : ∀ x : BitVec 64, (t.external[x]?).isSome → (v.external[x]?).isSome
  same : Same (preW s) t v
  inSlot : memLoad v.external (framePointer s + BitVec.ofNat 64 0x18) 64 = inPtr
  outSlot : memLoad v.external (framePointer s + BitVec.ofNat 64 0x20) 64 = outPtr
  lengthSlot : memLoad v.external (framePointer s + BitVec.ofNat 64 0x28) 64 =
    BitVec.ofNat 64 length
  ret : memLoad v.external (framePointer s - BitVec.ofNat 64 8) 64 = 0x10090e

theorem precall {t : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}
    (boundary : ReturnBoundary) (hOut : ¬ InProgram boundary.rip)
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hCut : Cut2 s t key nonce associatedData plaintext inPtr outPtr) :
    ∃ fuel v, Advances boundary fuel t v ∧ AtCall s t v plaintext.size inPtr outPtr := by
  have hS := stack_facts hPre
  have hroom := hS.room
  have htop := hS.top
  have hFB : frameBase s = (stackPtr s).toNat - 0x1b8 := rfl
  have r0 := ready_of_inv hCut.toInv
  have c0 := hCut.code
  have hsp0 : stackPtr t = framePointer s := hCut.rsp
  have hall0 := stack_allocated hCut.toInv
  have hSD : Same (fun x => ¬ (descriptorRegion s).Contains x) s t := fun x hx =>
    read_unchanged hPre hCut.frame (region := descriptorRegion s) (by simp [coreRead]) x
      (Classical.not_not.mp hx)
  have hDB : (s.regValue .r9).toNat + 24 < 2 ^ 32 := hPre.descriptorBounded
  have hInW : (descriptorWord s 0).Word64At t.external inPtr :=
    hSD.word64At hPre.inPointer (by simp [descriptorWord]; omega) fun x h₁ h₂ hn =>
      hn (by simp only [descriptorRegion, descriptorWord, registerRegion,
        MemoryRegion.Contains] at h₁ h₂ ⊢; omega)
  have hOutW : (descriptorWord s 1).Word64At t.external outPtr :=
    hSD.word64At hPre.outPointer (by simp [descriptorWord]; omega) fun x h₁ h₂ hn =>
      hn (by simp only [descriptorRegion, descriptorWord, registerRegion,
        MemoryRegion.Contains] at h₁ h₂ ⊢; omega)
  have hA1 : (AddrMode.sib 4 none 0 (.d32 0xa8)).addr t
      (0x1008d9 + BitVec.ofNat 64 (movLoadLen (.sib 4 none 0 (.d32 0xa8)))) =
      BitVec.ofNat 64 (slot s 0xa8).start := by
    rw [sib_rsp_addr, hsp0]
    exact framePointer_add_eq hS (k := 0xa8) (by decide)
  have hRd1 : MemReadable t ((AddrMode.sib 4 none 0 (.d32 0xa8)).addr t
      (0x1008d9 + BitVec.ofNat 64 (movLoadLen (.sib 4 none 0 (.d32 0xa8))))) 8 := by
    rw [hA1]
    exact memReadable_of_word hCut.descriptorSlot (by simp only [slot]; omega)
  obtain ⟨s1, a1, r1, c1, e1⟩ := step_run (boundary := boundary)
    (mov_r64_m64_effect_step 0x1008d9 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide))
    r0 c0 (program_text_slice c0 0x8d9 8 (by decide +kernel))
    ⟨hCut.rip, hRd1⟩
    (ne_boundary hOut 0x1008e1 ⟨by decide, by decide⟩) (regs_av (by simp [Component.isMem]))
  change (movR64M64Effect 0x1008d9 1 (.sib 4 none 0 (.d32 0xa8)) t).Holds t s1 at e1
  have hx1 : s1.external = t.external := ext_of_regs e1.agrees (by simp [Component.isMem])
  have hrcx1 : rd s1 1 = s.regValue .r9 := by
    have hw : rd s1 1 = memLoad t.external (BitVec.ofNat 64 (slot s 0xa8).start) 64 := by
      rw [← hA1]; exact e1.writes
    rw [hw]
    exact Refine.memLoad_of_word64At hCut.descriptorSlot
  have hA2 : (AddrMode.base 1 .none).addr s1
      (0x1008e1 + BitVec.ofNat 64 (movLoadLen (.base 1 .none))) =
      BitVec.ofNat 64 (descriptorWord s 0).start := by
    rw [base_addr]
    change rd s1 1 + 0 = _
    rw [hrcx1]
    apply BitVec.eq_of_toNat_eq
    simp [descriptorWord]
  obtain ⟨s2, a2, r2, c2, e2⟩ := step_run (boundary := boundary)
    (mov_r64_m64_effect_step 0x1008e1 0x48 (by unfold RexWPrefix; decide) 0
      (.base 1 .none) (by decide) (by decide) (by decide))
    r1 c1 (program_text_slice c1 0x8e1 3 (by decide +kernel))
    ⟨e1.rip, by
      rw [hA2]
      exact memReadable_of_word (hx1 ▸ hInW) (by simp [descriptorWord]; omega)⟩
    (ne_boundary hOut 0x1008e4 ⟨by decide, by decide⟩) (regs_av (by simp [Component.isMem]))
  change (movR64M64Effect 0x1008e1 0 (.base 1 .none) s1).Holds s1 s2 at e2
  have hx2 : s2.external = t.external :=
    (ext_of_regs e2.agrees (by simp [Component.isMem])).trans hx1
  have hrax2 : rd s2 0 = inPtr := by
    have hw : rd s2 0 = memLoad s1.external (BitVec.ofNat 64 (descriptorWord s 0).start) 64 := by
      rw [← hA2]; exact e2.writes
    rw [hw, hx1]
    exact Refine.memLoad_of_word64At hInW
  have hrcx2 : rd s2 1 = s.regValue .r9 := by
    rw [rd, e2.agrees.read (by simp)]; exact hrcx1
  have hA3 : (AddrMode.base 1 (.d8 8)).addr s2
      (0x1008e4 + BitVec.ofNat 64 (movLoadLen (.base 1 (.d8 8)))) =
      BitVec.ofNat 64 (descriptorWord s 1).start := by
    rw [base_addr]
    change rd s2 1 + (8 : BitVec 8).signExtend 64 = _
    rw [hrcx2]
    apply BitVec.eq_of_toNat_eq
    simp only [descriptorWord, BitVec.toNat_add, BitVec.toNat_ofNat]
    have : ((8 : BitVec 8).signExtend 64).toNat = 8 := by decide
    rw [this]
  obtain ⟨s3, a3, r3, c3, e3⟩ := step_run (boundary := boundary)
    (mov_r64_m64_effect_step 0x1008e4 0x4c (by unfold RexWPrefix; decide) 4
      (.base 1 (.d8 8)) (by decide) (by decide) (by decide))
    r2 c2 (program_text_slice c2 0x8e4 4 (by decide +kernel))
    ⟨e2.rip, by
      rw [hA3]
      exact memReadable_of_word (hx2 ▸ hOutW) (by simp [descriptorWord]; omega)⟩
    (ne_boundary hOut 0x1008e8 ⟨by decide, by decide⟩) (regs_av (by simp [Component.isMem]))
  change (movR64M64Effect 0x1008e4 12 (.base 1 (.d8 8)) s2).Holds s2 s3 at e3
  have hx3 : s3.external = t.external :=
    (ext_of_regs e3.agrees (by simp [Component.isMem])).trans hx2
  have hr12_3 : rd s3 12 = outPtr := by
    have hw : rd s3 12 = memLoad s2.external (BitVec.ofNat 64 (descriptorWord s 1).start) 64 := by
      rw [← hA3]; exact e3.writes
    rw [hw, hx2]
    exact Refine.memLoad_of_word64At hOutW
  have hrax3 : rd s3 0 = inPtr := by
    rw [rd, e3.agrees.read (by simp)]; exact hrax2
  have hsp3 : stackPtr s3 = framePointer s := by
    rw [stackPtr_eq_read, (e1.agrees.trans (e2.agrees.trans e3.agrees)).read (by simp),
      ← stackPtr_eq_read, hsp0]
  have hall3 : ∀ a : BitVec 64, (stackPtr s).toNat - 992 ≤ a.toNat →
      a.toNat < (stackPtr s).toNat + 8 → (s3.external[a]?).isSome := by
    intro a h₁ h₂; rw [hx3]; exact hall0 a h₁ h₂
  have hA4 : storeAddrAt 0x1008e8 (.sib 4 none 0 (.d8 0x18)) (3 + (AddrMode.sib 4 none 0
      (.d8 0x18)).tail.length) s3 = framePointer s + BitVec.ofNat 64 0x18 := by
    rw [storeAddrAt, sib_rsp_addr, hsp3]; rfl
  have hT4 := framePointer_add_toNat hS (k := 0x18) (by decide)
  obtain ⟨s4, a4, r4, c4, e4⟩ := step_run (boundary := boundary)
    (mov_m64_r64_effect_step 0x1008e8 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide))
    r3 c3 (program_text_slice c3 0x8e8 5 (by decide +kernel))
    (stack_storePre hS hall3 (by rw [hT4]; omega) (by rw [hT4]; omega) e3.rip
      (off := 0x8e8) rfl (by decide) hA4)
    (ne_boundary hOut 0x1008ed ⟨by decide, by decide⟩) (by
      simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl)
      · rw [hA4]
        exact mem_av (by omega) fun x h₁ h₂ => hS.outside x (by omega) (by omega)
      · exact fun x hx => absurd hx (nonmem_not_covers rfl x))
  change (movM64R64Effect 0x1008e8 0 (.sib 4 none 0 (.d8 0x18)) s3).Holds s3 s4 at e4
  have hm4 : Same (fun x => frameBase s + 0x18 ≤ x ∧ x < frameBase s + 0x18 + 8) s3 s4 := by
    have := same_of_store e4.agrees (addr := framePointer s + BitVec.ofNat 64 0x18) (n := 8)
      (by simp only [movM64R64Effect_components, hA4]) (by omega)
    rwa [hT4] at this
  have hslot4 : memLoad s4.external (framePointer s + BitVec.ofNat 64 0x18) 64 = inPtr := by
    have hw : (Operand.mem (framePointer s + BitVec.ofNat 64 0x18) : Operand 64).read s4 =
        rd s3 0 := by rw [← hA4]; exact e4.writes
    rw [← mem_read_eq, hw]; exact hrax3
  have hsp4 : stackPtr s4 = framePointer s := by
    rw [stackPtr_eq_read, e4.agrees.read (by simp), ← stackPtr_eq_read, hsp3]
  have hall4 : ∀ a : BitVec 64, (stackPtr s).toNat - 992 ≤ a.toNat →
      a.toNat < (stackPtr s).toNat + 8 → (s4.external[a]?).isSome :=
    fun a h₁ h₂ => e4.agrees.grow a (hall3 a h₁ h₂)
  have hr12_4 : rd s4 12 = outPtr := by rw [rd, e4.agrees.read (by simp)]; exact hr12_3
  have hA5 : storeAddrAt 0x1008ed (.sib 4 none 0 (.d8 0x20)) (3 + (AddrMode.sib 4 none 0
      (.d8 0x20)).tail.length) s4 = framePointer s + BitVec.ofNat 64 0x20 := by
    rw [storeAddrAt, sib_rsp_addr, hsp4]; rfl
  have hT5 := framePointer_add_toNat hS (k := 0x20) (by decide)
  obtain ⟨s5, a5, r5, c5, e5⟩ := step_run (boundary := boundary)
    (mov_m64_r64_effect_step 0x1008ed 0x4c (by unfold RexWPrefix; decide) 4
      (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide))
    r4 c4 (program_text_slice c4 0x8ed 5 (by decide +kernel))
    (stack_storePre hS hall4 (by rw [hT5]; omega) (by rw [hT5]; omega) e4.rip
      (off := 0x8ed) rfl (by decide) hA5)
    (ne_boundary hOut 0x1008f2 ⟨by decide, by decide⟩) (by
      simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl)
      · rw [hA5]
        exact mem_av (by omega) fun x h₁ h₂ => hS.outside x (by omega) (by omega)
      · exact fun x hx => absurd hx (nonmem_not_covers rfl x))
  change (movM64R64Effect 0x1008ed 12 (.sib 4 none 0 (.d8 0x20)) s4).Holds s4 s5 at e5
  have hm5 : Same (fun x => frameBase s + 0x20 ≤ x ∧ x < frameBase s + 0x20 + 8) s4 s5 := by
    have := same_of_store e5.agrees (addr := framePointer s + BitVec.ofNat 64 0x20) (n := 8)
      (by simp only [movM64R64Effect_components, hA5]) (by omega)
    rwa [hT5] at this
  have hslot5 : memLoad s5.external (framePointer s + BitVec.ofNat 64 0x20) 64 = outPtr := by
    have hw : (Operand.mem (framePointer s + BitVec.ofNat 64 0x20) : Operand 64).read s5 =
        rd s4 12 := by rw [← hA5]; exact e5.writes
    rw [← mem_read_eq, hw]; exact hr12_4
  have hsp5 : stackPtr s5 = framePointer s := by
    rw [stackPtr_eq_read, e5.agrees.read (by simp), ← stackPtr_eq_read, hsp4]
  have hA6 : (AddrMode.sib 4 none 0 (.d8 0x10)).addr s5
      (0x1008f2 + BitVec.ofNat 64 (movLoadLen (.sib 4 none 0 (.d8 0x10)))) =
      BitVec.ofNat 64 (slot s 0x10).start := by
    rw [sib_rsp_addr, hsp5]
    exact framePointer_add_eq hS (k := 0x10) (by decide)
  have hm45 : Same (preW s) t s5 :=
    ((same_of_regs (e1.agrees.trans (e2.agrees.trans e3.agrees))
      (by simp [Component.isMem])).trans
      ((hm4.mono fun x hx => by unfold preW; omega).trans
        (hm5.mono fun x hx => by unfold preW; omega)))
  have hLen5 : (slot s 0x10).Word64At s5.external (BitVec.ofNat 64 plaintext.size) :=
    hm45.word64At hCut.lengthSlot (by simp only [slot]; omega) fun x h₁ h₂ => by
      simp only [slot] at h₁ h₂; unfold preW; omega
  obtain ⟨s6, a6, r6, c6, e6⟩ := step_run (boundary := boundary)
    (mov_r64_m64_effect_step 0x1008f2 0x4c (by unfold RexWPrefix; decide) 6
      (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide))
    r5 c5 (program_text_slice c5 0x8f2 5 (by decide +kernel))
    ⟨e5.rip, by rw [hA6]; exact memReadable_of_word hLen5 (by simp only [slot]; omega)⟩
    (ne_boundary hOut 0x1008f7 ⟨by decide, by decide⟩) (regs_av (by simp [Component.isMem]))
  change (movR64M64Effect 0x1008f2 14 (.sib 4 none 0 (.d8 0x10)) s5).Holds s5 s6 at e6
  have hx6 : s6.external = s5.external := ext_of_regs e6.agrees (by simp [Component.isMem])
  have hr14_6 : rd s6 14 = BitVec.ofNat 64 plaintext.size := by
    have hw : rd s6 14 = memLoad s5.external (BitVec.ofNat 64 (slot s 0x10).start) 64 := by
      rw [← hA6]; exact e6.writes
    rw [hw]
    exact Refine.memLoad_of_word64At hLen5
  have hsp6 : stackPtr s6 = framePointer s := by
    rw [stackPtr_eq_read, e6.agrees.read (by simp), ← stackPtr_eq_read, hsp5]
  have hall6 : ∀ a : BitVec 64, (stackPtr s).toNat - 992 ≤ a.toNat →
      a.toNat < (stackPtr s).toNat + 8 → (s6.external[a]?).isSome :=
    fun a h₁ h₂ => e6.agrees.grow a (e5.agrees.grow a (hall4 a h₁ h₂))
  have hA7 : storeAddrAt 0x1008f7 (.sib 4 none 0 (.d8 0x28)) (3 + (AddrMode.sib 4 none 0
      (.d8 0x28)).tail.length) s6 = framePointer s + BitVec.ofNat 64 0x28 := by
    rw [storeAddrAt, sib_rsp_addr, hsp6]; rfl
  have hT7 := framePointer_add_toNat hS (k := 0x28) (by decide)
  obtain ⟨s7, a7, r7, c7, e7⟩ := step_run (boundary := boundary)
    (mov_m64_r64_effect_step 0x1008f7 0x4c (by unfold RexWPrefix; decide) 6
      (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide))
    r6 c6 (program_text_slice c6 0x8f7 5 (by decide +kernel))
    (stack_storePre hS hall6 (by rw [hT7]; omega) (by rw [hT7]; omega) e6.rip
      (off := 0x8f7) rfl (by decide) hA7)
    (ne_boundary hOut 0x1008fc ⟨by decide, by decide⟩) (by
      simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl)
      · rw [hA7]
        exact mem_av (by omega) fun x h₁ h₂ => hS.outside x (by omega) (by omega)
      · exact fun x hx => absurd hx (nonmem_not_covers rfl x))
  change (movM64R64Effect 0x1008f7 14 (.sib 4 none 0 (.d8 0x28)) s6).Holds s6 s7 at e7
  have hm7 : Same (fun x => frameBase s + 0x28 ≤ x ∧ x < frameBase s + 0x28 + 8) s6 s7 := by
    have := same_of_store e7.agrees (addr := framePointer s + BitVec.ofNat 64 0x28) (n := 8)
      (by simp only [movM64R64Effect_components, hA7]) (by omega)
    rwa [hT7] at this
  have hslot7 : memLoad s7.external (framePointer s + BitVec.ofNat 64 0x28) 64 =
      BitVec.ofNat 64 plaintext.size := by
    have hw : (Operand.mem (framePointer s + BitVec.ofNat 64 0x28) : Operand 64).read s7 =
        rd s6 14 := by rw [← hA7]; exact e7.writes
    rw [← mem_read_eq, hw]; exact hr14_6
  have hsp7 : stackPtr s7 = framePointer s := by
    rw [stackPtr_eq_read, e7.agrees.read (by simp), ← stackPtr_eq_read, hsp6]
  obtain ⟨s8, a8, r8, c8, e8⟩ := step_run (boundary := boundary)
    (lea_r64_effect_step 0x1008fc 0x48 (by unfold RexWPrefix; decide) 7
      (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide))
    r7 c7 (program_text_slice c7 0x8fc 8 (by decide +kernel)) e7.rip
    (ne_boundary hOut 0x100904 ⟨by decide, by decide⟩) (regs_av (by simp [Component.isMem]))
  change (leaR64Effect 0x1008fc 7 (.sib 4 none 0 (.d32 0xd0)) s7).Holds s7 s8 at e8
  have hrdi8 : rd s8 7 = framePointer s + BitVec.ofNat 64 0xd0 := by
    have hw : rd s8 7 = (AddrMode.sib 4 none 0 (.d32 0xd0)).addr s7
        (0x1008fc + BitVec.ofNat 64 (leaLen (.sib 4 none 0 (.d32 0xd0)))) := e8.writes
    rw [hw, sib_rsp_addr, hsp7]; rfl
  have hsp8 : stackPtr s8 = framePointer s := by
    rw [stackPtr_eq_read, e8.agrees.read (by simp), ← stackPtr_eq_read, hsp7]
  obtain ⟨s9, a9, r9, c9, e9⟩ := step_run (boundary := boundary)
    (lea_r64_effect_step 0x100904 0x48 (by unfold RexWPrefix; decide) 6
      (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide))
    r8 c8 (program_text_slice c8 0x904 5 (by decide +kernel)) e8.rip
    (ne_boundary hOut 0x100909 ⟨by decide, by decide⟩) (regs_av (by simp [Component.isMem]))
  change (leaR64Effect 0x100904 6 (.sib 4 none 0 (.d8 0x18)) s8).Holds s8 s9 at e9
  have hrsi9 : rd s9 6 = framePointer s + BitVec.ofNat 64 0x18 := by
    have hw : rd s9 6 = (AddrMode.sib 4 none 0 (.d8 0x18)).addr s8
        (0x100904 + BitVec.ofNat 64 (leaLen (.sib 4 none 0 (.d8 0x18)))) := e9.writes
    rw [hw, sib_rsp_addr, hsp8]; rfl
  have hsp9 : stackPtr s9 = framePointer s := by
    rw [stackPtr_eq_read, e9.agrees.read (by simp), ← stackPtr_eq_read, hsp8]
  have hall9 : ∀ a : BitVec 64, (stackPtr s).toNat - 992 ≤ a.toNat →
      a.toNat < (stackPtr s).toNat + 8 → (s9.external[a]?).isSome :=
    fun a h₁ h₂ => e9.agrees.grow a (e8.agrees.grow a (e7.agrees.grow a (hall6 a h₁ h₂)))
  have hpa : pushAddr s9 = framePointer s - BitVec.ofNat 64 8 := by rw [pushAddr, hsp9]; rfl
  have hT10 := framePointer_sub_toNat hS (k := 8) (by decide)
  obtain ⟨v, a10, r10, c10, e10⟩ := step_run (boundary := boundary)
    (call_rel32_effect_step 0x100909 0x172 (by decide))
    r9 c9 (program_text_slice c9 0x909 5 (by decide +kernel))
    (stack_storePre hS hall9 (by rw [hT10]; unfold frameBase frameBytes; omega)
      (by rw [hT10]; unfold frameBase frameBytes; omega) e9.rip
      (off := 0x909) rfl (by decide) hpa)
    (ne_boundary hOut 0x100a80 ⟨by decide, by decide⟩) (by
      simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl | rfl)
      · exact fun x hx => absurd hx (nonmem_not_covers rfl x)
      · rw [hpa]
        refine mem_av (by omega) fun x h₁ h₂ => hS.outside x ?_ ?_
        · rw [hT10] at h₁; omega
        · rw [hT10] at h₂; omega
      · exact fun x hx => absurd hx (nonmem_not_covers rfl x))
  have hm10 : Same (fun x => frameBase s - 8 ≤ x ∧ x < frameBase s - 8 + 8) s9 v := by
    apply Same.of_agrees e10.agrees
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl)
    · exact fun x hx => absurd hx (nonmem_not_covers rfl x)
    · rw [hpa]
      exact mem_within (W := fun x => frameBase s - 8 ≤ x ∧ x < frameBase s - 8 + 8)
        (by omega) fun j hj => by rw [hT10]; omega
    · exact fun x hx => absurd hx (nonmem_not_covers rfl x)
  have hag := e1.agrees.trans (e2.agrees.trans (e3.agrees.trans (e4.agrees.trans
    (e5.agrees.trans (e6.agrees.trans (e7.agrees.trans (e8.agrees.trans
    (e9.agrees.trans e10.agrees))))))))
  have hag4 := e4.agrees.trans (e5.agrees.trans (e6.agrees.trans (e7.agrees.trans
    (e8.agrees.trans (e9.agrees.trans e10.agrees)))))
  have hag7 := e7.agrees.trans (e8.agrees.trans (e9.agrees.trans e10.agrees))
  have hr03 : Same (fun _ => False) t s3 :=
    same_of_regs (e1.agrees.trans (e2.agrees.trans e3.agrees)) (by simp [Component.isMem])
  have hr56 : Same (fun _ => False) s5 s6 := same_of_regs e6.agrees (by simp [Component.isMem])
  have hr79 : Same (fun _ => False) s7 s9 :=
    same_of_regs (e8.agrees.trans e9.agrees) (by simp [Component.isMem])
  have hFB8 : 8 ≤ frameBase s := by unfold frameBase frameBytes; omega
  have hTail : Same (fun x => (frameBase s + 0x20 ≤ x ∧ x < frameBase s + 0x30) ∨
      (frameBase s - 8 ≤ x ∧ x < frameBase s)) s4 v :=
    (hm5.mono fun x hx => by omega).trans ((hr56.mono fun x hx => hx.elim).trans
      ((hm7.mono fun x hx => by omega).trans ((hr79.mono fun x hx => hx.elim).trans
        (hm10.mono fun x hx => by omega))))
  have hTail7 : Same (fun x => frameBase s - 8 ≤ x ∧ x < frameBase s) s7 v :=
    (hr79.mono fun x hx => hx.elim).trans (hm10.mono fun x hx => by omega)
  have hTail5 : Same (fun x => (frameBase s + 0x28 ≤ x ∧ x < frameBase s + 0x30) ∨
      (frameBase s - 8 ≤ x ∧ x < frameBase s)) s5 v :=
    (hr56.mono fun x hx => hx.elim).trans ((hm7.mono fun x hx => by omega).trans
      (hTail7.mono fun x hx => by omega))
  have hoff (k i : Nat) (hk : k ≤ 0x1b0) (hi : i < 8) :
      (framePointer s + BitVec.ofNat 64 k + BitVec.ofNat 64 i).toNat = frameBase s + k + i := by
    rw [toNat_add_ofNat, framePointer_add_toNat hS (by omega)] <;>
      rw [framePointer_add_toNat hS (by omega)] <;> unfold frameBase frameBytes <;> omega
  refine ⟨_, v, a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans
    (a8.trans (a9.trans a10)))))))), r10, c10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hag.directionFlagClear (by simp) hCut.directionFlagUnset,
    SupportedSSE.of_agreesExcept hag hCut.machine.sse, hag.grow, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e10.rip]; rfl
  · rw [stackPtr_eq_read, e10.writes.1, hpa]
  · rw [rd, e10.agrees.read (by simp), e9.agrees.read (by simp)]; exact hrdi8
  · rw [rd, e10.agrees.read (by simp)]; exact hrsi9
  · rw [rd, hag4.read (by simp)]; exact hr12_3
  · rw [rd, hag7.read (by simp)]; exact hr14_6
  · exact hag.read (by simp)
  · exact hag.read (by simp)
  · exact (hr03.mono fun x hx => hx.elim).trans ((hm4.mono fun x hx => by unfold preW; omega).trans
      (hTail.mono fun x hx => by unfold preW; omega))
  · rw [hTail.load (n := 64) fun i hi => by rw [hoff 0x18 i (by decide) (by omega)]; omega]
    exact hslot4
  · rw [hTail5.load (n := 64) fun i hi => by rw [hoff 0x20 i (by decide) (by omega)]; omega]
    exact hslot5
  · rw [hTail7.load (n := 64) fun i hi => by rw [hoff 0x28 i (by decide) (by omega)]; omega]
    exact hslot7
  · have hw : (Operand.mem (pushAddr s9) : Operand 64).read v = 0x100909 + BitVec.ofNat 64 5 :=
      e10.writes.2
    rw [hpa, mem_read_eq] at hw
    rw [hw]; rfl


omit bindings in
theorem disjoint_symm {r r' : MemoryRegion} (h : r.Disjoint r') : r'.Disjoint r :=
  fun x h₁ h₂ => h x h₂ h₁

omit bindings in
theorem disjoint_of_sub {r big r' : MemoryRegion} (h : r.Disjoint big)
    (hs : ∀ x, r'.Contains x → big.Contains x) : r.Disjoint r' :=
  fun x h₁ h₂ => h x h₁ (hs x h₂)

section Regions

variable {key : Vector UInt8 32} {nonce : Vector UInt8 12}
  {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}

theorem out_stack (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) :
    (messageRegion outPtr plaintext.size).Disjoint (Stack.region s coreStackBytes) := by
  have h := hPre.separation.1
  simp only [coreWritten, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at h
  exact h.2.1

theorem in_stack (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) :
    (messageRegion inPtr plaintext.size).Disjoint (Stack.region s coreStackBytes) := by
  by_cases he : inPtr = outPtr
  · subst he; exact out_stack hPre
  · apply disjoint_symm
    apply hPre.separation.2.1 _ (by simp [coreWritten])
    simp [coreRead, he]

theorem out_avoids (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) :
    (messageRegion outPtr plaintext.size).Avoids
      (fun a => InProgram a ∨ pageTables.Contains a.toNat) :=
  hPre.separation.2.2 _ (by simp [coreWritten])

theorem stack_avoids (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) :
    (Stack.region s coreStackBytes).Avoids
      (fun a => InProgram a ∨ pageTables.Contains a.toNat) :=
  hPre.separation.2.2 _ (by simp [coreWritten])

theorem stack_writable {t v : RamState}
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hInv : Inv s t outPtr plaintext.size)
    (hgrow : ∀ x : BitVec 64, (t.external[x]?).isSome → (v.external[x]?).isSome)
    {r : MemoryRegion} (h₁ : (stackPtr s).toNat - 992 ≤ r.start)
    (h₂ : r.start + r.size ≤ (stackPtr s).toNat + 8) : Callee100a80.Writable v r := by
  have hS := stack_facts hPre
  have := hS.top
  refine ⟨by omega, fun i hi => hgrow _ (stack_allocated hInv _ ?_ ?_), fun a ha => ?_⟩
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  · exact stack_avoids hPre a (stack_contains.mpr ⟨by
      simp only [MemoryRegion.Contains] at ha; omega, by
      simp only [MemoryRegion.Contains] at ha; omega⟩)

theorem in_preW (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) {x : Nat}
    (hx : (messageRegion inPtr plaintext.size).Contains x) : ¬ preW s x := by
  have hS := stack_facts hPre
  have := hS.room
  intro hw
  apply in_stack hPre x hx
  rw [stack_contains]
  unfold preW frameBase frameBytes at hw
  omega

theorem callPre {t v : RamState}
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hCut : Cut2 s t key nonce associatedData plaintext inPtr outPtr)
    (hA : AtCall s t v plaintext.size inPtr outPtr) :
    Callee100a80.CallPre v key 1 nonce inPtr outPtr plaintext := by
  have hS := stack_facts hPre
  have hroom := hS.room
  have htop := hS.top
  have hF := framePointer_toNat hS
  have hFB : frameBase s = (stackPtr s).toNat - 0x1b8 := rfl
  have hspv : (stackPtr v).toNat = frameBase s - 8 := by
    rw [hA.rsp]; exact framePointer_sub_toNat hS (by decide)
  have hrdi : (rdi.read v).toNat = frameBase s + 0xd0 := by
    rw [show rdi.read v = rd v 7 from rfl, hA.rdi]; exact framePointer_add_toNat hS (by decide)
  have hrsi : (rsi.read v).toNat = frameBase s + 0x18 := by
    rw [show rsi.read v = rd v 6 from rfl, hA.rsi]; exact framePointer_add_toNat hS (by decide)
  have hInB : inPtr.toNat + plaintext.size < 2 ^ 32 := hPre.messageInMemory.1
  have hOutB : outPtr.toNat + plaintext.size < 2 ^ 32 := hPre.outputInMemory.1
  have hOS := out_stack hPre
  have hIS := in_stack hPre
  have hsub (r : MemoryRegion) (h₁ : (stackPtr s).toNat - 992 ≤ r.start)
      (h₂ : r.start + r.size ≤ (stackPtr s).toNat + 8) :
      ∀ x, r.Contains x → (Stack.region s coreStackBytes).Contains x := fun x hx => by
    rw [stack_contains]; simp only [MemoryRegion.Contains] at hx; omega
  have hsome (a : BitVec 64) (h₁ : (stackPtr s).toNat - 992 ≤ a.toNat)
      (h₂ : a.toNat < (stackPtr s).toNat + 8) : (v.external[a]?).isSome :=
    hA.grow a (stack_allocated hCut.toInv a h₁ h₂)
  have hword (a : BitVec 64) (k : Nat) (ha : a.toNat = frameBase s + k) (hk : k ≤ 0x1b0)
      {w : BitVec 64} (hw : memLoad v.external a 64 = w) :
      (⟨a.toNat, 8⟩ : MemoryRegion).Word64At v.external w := by
    apply word64At_of_load rfl
    · rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hw
    · intro i hi
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      apply hsome <;> rw [toNat_add_ofNat (by omega), ha] <;> unfold frameBase frameBytes <;>
        omega
  refine ⟨hA.ready, hA.code, hA.rip, hA.df, ?stackLow, ?stack, ?cipher, ?words, ?position,
    ?buf, ?inPtr, ?outPtr, ?length, ?messageBytes, by omega, ?out, hPre.inPlaceOrApart,
    ?inputCipher, ?inputStack, ?outCipher, ?outStack, ?outBuf, ?cipherStack, ?cipherBuf,
    ?bufStack, ?returnLow, ?returnOutside⟩
  case stackLow =>
    unfold Callee100a80.frameBytes; rw [hspv]; unfold frameBase frameBytes; omega
  case stack =>
    apply stack_writable hPre hCut.toInv hA.grow <;>
      simp only [Callee100a80.stackRegion, Callee100a80.frameBytes, hspv] <;>
      unfold frameBase frameBytes <;> omega
  case cipher =>
    apply stack_writable hPre hCut.toInv hA.grow <;>
      simp only [Callee100a80.cipherRegion, Callee100a80.cipherBytes, hrdi] <;>
      unfold frameBase frameBytes <;> omega
  case words =>
    have h := hA.same.hasBytes hCut.cipher (by simp only [cipherOffset]; omega)
      fun x h₁ h₂ => by simp only [cipherOffset] at h₁ h₂; unfold preW; omega
    simp only [Callee100a80.wordsRegion, hrdi]
    exact h
  case position =>
    have h := hA.same.hasBytes hCut.position (by simp only [cipherOffset]; omega)
      fun x h₁ h₂ => by simp only [cipherOffset] at h₁ h₂; unfold preW; omega
    simp only [Callee100a80.positionRegion, hrdi]
    exact h
  case buf =>
    refine ⟨by rw [hrsi]; omega, fun i hi => hsome _ ?_ ?_⟩ <;>
      rw [toNat_add_ofNat (by omega), hrsi] <;> unfold frameBase frameBytes <;> omega
  case inPtr =>
    simp only [Callee100a80.inPtrSlot]
    exact hword _ 0x18 hrsi (by decide) (by
      rw [show rsi.read v = rd v 6 from rfl, hA.rsi]; exact hA.inSlot)
  case outPtr =>
    simp only [Callee100a80.outPtrSlot]
    have h := hword (framePointer s + BitVec.ofNat 64 0x20) 0x20
      (framePointer_add_toNat hS (by decide)) (by decide) hA.outSlot
    rw [framePointer_add_toNat hS (by decide)] at h
    rw [hrsi, show frameBase s + 0x18 + 8 = frameBase s + 0x20 by omega]
    exact h
  case length =>
    simp only [Callee100a80.lengthSlot]
    have h := hword (framePointer s + BitVec.ofNat 64 0x28) 0x28
      (framePointer_add_toNat hS (by decide)) (by decide) hA.lengthSlot
    rw [framePointer_add_toNat hS (by decide)] at h
    rw [hrsi, show frameBase s + 0x18 + 16 = frameBase s + 0x28 by omega]
    exact h
  case messageBytes =>
    exact hA.same.hasBytes (r := messageRegion inPtr plaintext.size) hCut.message (by simp only [messageRegion]; omega)
      fun x h₁ h₂ => in_preW hPre ⟨h₁, h₂⟩
  case out =>
    refine ⟨by simp only [Callee100a80.outputRegion]; omega, fun i hi => hA.grow _ ?_,
      fun a ha => out_avoids hPre a ha⟩
    obtain ⟨b, hb⟩ := hCut.allocated (messageRegion outPtr plaintext.size)
      (by simp [coreWritten]) (BitVec.ofNat 64 (outPtr.toNat + i)) (by
        simp only [messageRegion, MemoryRegion.Contains, BitVec.toNat_ofNat]
        simp only [Callee100a80.outputRegion] at hi
        rw [Nat.mod_eq_of_lt (by omega)]; omega)
    simp only [Callee100a80.outputRegion]
    rw [hb]; rfl
  case inputCipher =>
    exact disjoint_of_sub hIS (hsub _ (by simp only [Callee100a80.cipherRegion, hrdi]; omega)
      (by simp only [Callee100a80.cipherRegion, Callee100a80.cipherBytes, hrdi]; omega))
  case inputStack =>
    exact disjoint_of_sub hIS (hsub _
      (by simp only [Callee100a80.stackRegion, Callee100a80.frameBytes, hspv]; omega)
      (by simp only [Callee100a80.stackRegion, Callee100a80.frameBytes, hspv]; omega))
  case outCipher =>
    exact disjoint_of_sub hOS (hsub _ (by simp only [Callee100a80.cipherRegion, hrdi]; omega)
      (by simp only [Callee100a80.cipherRegion, Callee100a80.cipherBytes, hrdi]; omega))
  case outStack =>
    exact disjoint_of_sub hOS (hsub _
      (by simp only [Callee100a80.stackRegion, Callee100a80.frameBytes, hspv]; omega)
      (by simp only [Callee100a80.stackRegion, Callee100a80.frameBytes, hspv]; omega))
  case outBuf =>
    exact disjoint_of_sub hOS (hsub _ (by simp only [Callee100a80.bufRegion, hrsi]; omega)
      (by simp only [Callee100a80.bufRegion, hrsi]; omega))
  case cipherStack =>
    intro x h₁ h₂
    simp only [Callee100a80.cipherRegion, Callee100a80.stackRegion, Callee100a80.cipherBytes,
      Callee100a80.frameBytes, MemoryRegion.Contains, hrdi, hspv] at h₁ h₂
    omega
  case cipherBuf =>
    intro x h₁ h₂
    simp only [Callee100a80.cipherRegion, Callee100a80.bufRegion, Callee100a80.cipherBytes,
      MemoryRegion.Contains, hrdi, hrsi] at h₁ h₂
    omega
  case bufStack =>
    intro x h₁ h₂
    simp only [Callee100a80.bufRegion, Callee100a80.stackRegion, Callee100a80.frameBytes,
      MemoryRegion.Contains, hrsi, hspv] at h₁ h₂
    omega
  case returnLow =>
    simp only [returnBoundary]
    rw [mem_read_eq, hA.rsp, hA.ret]; decide
  case returnOutside =>
    left
    simp only [returnBoundary]
    rw [mem_read_eq, hA.rsp, hA.ret]; decide

end Regions


section Poly

open ChaCha20Poly1305.Proofs.Poly1305State

omit bindings in
theorem word32_same {W : Nat → Prop} {a b : RamState} (h : Same W a b) {addr : BitVec 64}
    (hw : ∀ i < 4, ¬ W (addr + BitVec.ofNat 64 i).toNat) : word32 b addr = word32 a addr :=
  h.load (n := 32) hw

omit bindings in
theorem polyState_same {W : Nat → Prop} {a b : RamState} (h : Same W a b) {base : BitVec 64}
    (hlow : base.toNat + 0x38 < 2 ^ 64) (hw : ∀ k < 0x38, ¬ W (base.toNat + k))
    {otk : Vector UInt8 32} {acc : Nat} (hp : Core.PolyState a base otk acc) :
    Core.PolyState b base otk acc := by
  have hword (c : Nat) (hc : c ≤ 0x24) (i : Fin 5) (hi : c + 4 * i.val + 4 ≤ 0x38) :
      word32 b (base + BitVec.ofNat 64 c + BitVec.ofNat 64 (4 * i.val)) =
        word32 a (base + BitVec.ofNat 64 c + BitVec.ofNat 64 (4 * i.val)) := by
    apply word32_same h
    intro j hj
    have := hw (c + 4 * i.val + j) (by omega)
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hi5 := i.isLt
    rwa [Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (a := 4 * i.val) (by omega),
      Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.add_assoc, Nat.add_assoc,
      ← Nat.add_assoc c]
  have hpad : padWords b base = padWords a base := by
    funext i
    have := hword 0 (by decide) ⟨i.val, by omega⟩ (by have := i.isLt; simp; omega)
    simpa [padWords] using this
  have hr : rLimbs b base = rLimbs a base := by
    funext i
    exact hword 0x10 (by decide) i (by have := i.isLt; omega)
  have hh : hLimbs b base = hLimbs a base := by
    funext i
    exact hword 0x24 (by decide) i (by have := i.isLt; omega)
  exact ⟨hpad ▸ hp.pad, hr ▸ hp.rClamped, hr ▸ hp.rValue, hh ▸ hp.hBounded, hh ▸ hp.hValue⟩

end Poly

def CalleeAdvances [Machine.Bindings] : Prop :=
  ∀ {s : RamState} {key : Vector UInt8 32} {counter : UInt32} {nonce : Vector UInt8 12}
    {input output : BitVec 64} {message : ByteArray} (boundary : ReturnBoundary),
    (boundary.rip.toNat < Callee100a80.entry.toNat ∨
      Callee100a80.codeEnd ≤ boundary.rip.toNat) →
    Callee100a80.CallPre s key counter nonce input output message →
    (returnBoundary s).rip ≠ boundary.rip →
    ∃ fuel t, Advances boundary fuel s t ∧
      Callee100a80.CallResult s t key counter nonce output message

theorem calleeAdvances : CalleeAdvances :=
  fun boundary hb h hne => Callee100a80.call_advances boundary hb h hne

def postW (s : RamState) (outPtr : BitVec 64) (length : Nat) (x : Nat) : Prop :=
  (frameBase s - 0x1a8 ≤ x ∧ x < frameBase s) ∨
    (frameBase s + 0x100 ≤ x ∧ x < frameBase s + 0x150) ∨
    (messageRegion outPtr length).Contains x

omit bindings in
theorem callee_same {v w : RamState} (hS : StackFacts s) {outPtr : BitVec 64} {length : Nat}
    (hOutB : outPtr.toNat + length < 2 ^ 32)
    (hrdi : (rdi.read v).toNat = frameBase s + 0xd0) (hspv : (stackPtr v).toNat = frameBase s - 8)
    (hag : AgreesExcept (Callee100a80.callChanges v outPtr length) v w) :
    Same (postW s outPtr length) v w := by
  have := hS.room
  have := hS.top
  have hFB : frameBase s = (stackPtr s).toNat - 0x1b8 := rfl
  have h30 : (0x30 : BitVec 64).toNat = 0x30 := rfl
  have h40 : (0x40 : BitVec 64).toNat = 0x40 := rfl
  apply Same.of_agrees hag
  intro c hc
  simp only [Callee100a80.callChanges, Callee100a80.frameBytes, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  any_goals exact fun x hx => absurd hx (nonmem_not_covers rfl x)
  all_goals rintro x ⟨j, hj, rfl⟩
  all_goals simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, hrdi, hspv,
    h30, h40]
  all_goals unfold postW messageRegion MemoryRegion.Contains
  all_goals dsimp only
  all_goals unfold frameBase frameBytes at *
  all_goals omega


attribute [local simp] jccEffect in
theorem encrypt_of_call (hCall : CalleeAdvances) {t : RamState} {key : Vector UInt8 32}
    {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}
    (boundary : ReturnBoundary)
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hOut : ¬ InProgram boundary.rip)
    (hCut : Cut2 s t key nonce associatedData plaintext inPtr outPtr) :
    ∃ fuel u, Advances boundary fuel t u ∧
      Cut3 s u key nonce associatedData plaintext outPtr := by
  have hS := stack_facts hPre
  have hroom := hS.room
  have htop := hS.top
  have hFB : frameBase s = (stackPtr s).toNat - 0x1b8 := rfl
  obtain ⟨f1, v, a1, hA⟩ := precall boundary hOut hPre hCut
  have hCP := callPre hPre hCut hA
  have hRet : (returnBoundary v).rip = 0x10090e := by
    simp only [returnBoundary]; rw [mem_read_eq, hA.rsp, hA.ret]
  have hb : boundary.rip.toNat < Callee100a80.entry.toNat ∨
      Callee100a80.codeEnd ≤ boundary.rip.toNat := by
    have he : Callee100a80.entry.toNat = 0x100a80 := rfl
    rw [he]
    refine Classical.byContradiction fun h => hOut (inProgram_of_toNat ?_ ?_) <;>
      simp only [Callee100a80.codeEnd] at h <;> omega
  obtain ⟨f2, w, a2, hR⟩ := hCall boundary hb hCP
    (by rw [hRet]; exact ne_boundary hOut _ ⟨by decide, by decide⟩)
  have hInB : inPtr.toNat + plaintext.size < 2 ^ 32 := hPre.messageInMemory.1
  have hOutB : outPtr.toNat + plaintext.size < 2 ^ 32 := hPre.outputInMemory.1
  have hAcc : Callee100a80.Accepted 1 plaintext.size := by
    unfold Callee100a80.Accepted; simp only [UInt32.toNat_one]; omega
  have hst := hR.status
  simp only [hAcc, ↓reduceIte] at hst
  obtain ⟨hal, hct⟩ := hst
  obtain ⟨w1, b1, rw1, cw1, g1⟩ := step_run (boundary := boundary)
    (test_r8_r8_effect_step 0x10090e 0xc0 (by decide) (by decide) (by decide))
    hR.ready hR.code (program_text_slice hR.code 0x90e 2 (by decide +kernel))
    (hR.rip.trans hRet) (ne_boundary hOut 0x100910 ⟨by decide, by decide⟩)
    (regs_av (by simp [Component.isMem]))
  change (testR8R8Effect 0x10090e 2 0 0 w).Holds w w1 at g1
  have hZF : (StatusFlags.ofRFLAGS w1.RFLAGS).ZF = true := by
    obtain ⟨-, -, -, hZ, -⟩ := g1.flags
    have h0 : (Operand.reg 0 : Operand 8).read w = 0 := hal
    simp only [testFlags, FlagAllows, h0] at hZ
    rw [hZ]; rfl
  have hj : (jccEffect 0x100910 6 5 ((0x121 : BitVec 32).signExtend 64) w1).rip = 0x100916 := by
    simp only [jccEffect, branchEffect, condHolds_5, hZF]; rfl
  obtain ⟨u, b2, rw2, cw2, g2⟩ := step_run (boundary := boundary)
    (jcc_rel32_effect_step 0x100910 5 0x121)
    rw1 cw1 (program_text_slice cw1 0x910 6 (by decide +kernel))
    ⟨g1.rip, fun h => by rw [condHolds_5, hZF] at h; exact absurd h (by decide)⟩
    (by rw [hj]; exact ne_boundary hOut 0x100916 ⟨by decide, by decide⟩)
    (regs_av (by simp [Component.isMem, jccEffect]))
  have hagU := hR.agrees.trans (g1.agrees.trans g2.agrees)
  have hagW := g1.agrees.trans g2.agrees
  have hxU : u.external = w.external :=
    ext_of_regs hagW (by simp [Component.isMem, jccEffect])
  have hrdi : (rdi.read v).toNat = frameBase s + 0xd0 := by
    rw [show rdi.read v = rd v 7 from rfl, hA.rdi]; exact framePointer_add_toNat hS (by decide)
  have hspv : (stackPtr v).toNat = frameBase s - 8 := by
    rw [hA.rsp]; exact framePointer_sub_toNat hS (by decide)
  have hSame : Same (fun x => preW s x ∨ postW s outPtr plaintext.size x) t u :=
    (hA.same.mono fun x hx => .inl hx).trans
      (((callee_same hS hOutB hrdi hspv hR.agrees).trans
        (fun x _ => by rw [hxU])).mono fun x hx => .inr hx)
  have hOS := out_stack hPre
  have hkeep (k hi : Nat) (hk : hi ≤ 0x1c0) (hk' : hi ≤ 0x18 ∨ (0x30 ≤ k ∧ hi ≤ 0x100) ∨
      0x150 ≤ k) (x : Nat) (h₁ : frameBase s + k ≤ x) (h₂ : x < frameBase s + hi) :
      ¬ (preW s x ∨ postW s outPtr plaintext.size x) := by
    rintro (h | h | h | h)
    · unfold preW at h; omega
    · omega
    · omega
    · exact hOS x h (stack_contains.mpr ⟨by omega, by omega⟩)
  have hslot (k : Nat) (hk : k ≤ 0x1b8) (hk' : k + 8 ≤ 0x18 ∨ (0x30 ≤ k ∧ k + 8 ≤ 0x100) ∨
      0x150 ≤ k) {val : BitVec 64} (h : (slot s k).Word64At t.external val) :
      (slot s k).Word64At u.external val :=
    hSame.word64At h (by simp only [slot]; omega) fun x h₁ h₂ =>
      hkeep k (k + 8) (by omega) hk' x h₁ (by simp only [slot] at h₂; omega)
  have hgrow : ∀ x : BitVec 64, (t.external[x]?).isSome → (u.external[x]?).isSome :=
    fun x h => hagU.grow x (hA.grow x h)
  have hreg (r : BitVec 5) (hr : Component.reg r ∉ Callee100a80.callChanges v outPtr
      plaintext.size) : rd u r = rd v r := by
    rw [rd, hagU.read (by simp only [List.mem_append]; simp at hr ⊢; exact hr)]
  refine ⟨_, u, a1.trans (a2.trans (b1.trans b2)), ⟨machineRamUnitStrideDecodable_of_ready rw2 hCut.environment.stringStride,
    ⟨rw2.cpu, SupportedSSE.of_agreesExcept hagU hA.sse, rw2.memory, rw2.ready⟩, cw2,
    hagU.directionFlagClear (by simp [Callee100a80.callChanges]) hA.df, ?rsp, ?frame,
    ?allocated, ?saved, ?returnAddress⟩, ?rip, ?r12, ?r14, ?r15, ?rbx,
    hslot 0x10 (by decide) (by decide) hCut.lengthSlot,
    hslot 0x98 (by decide) (by decide) hCut.adLengthSlot,
    hslot 0xa0 (by decide) (by decide) hCut.resultSlot, ?ciphertext, ?poly⟩
  case rsp =>
    rw [stackPtr_eq_read, hagW.read (by simp), ← stackPtr_eq_read, hR.rsp, hA.rsp]
    exact BitVec.sub_add_cancel _ _
  case frame =>
    intro x hx
    rw [hSame x ?_]
    · exact hCut.frame x hx
    · have h₁ := hx (Stack.region s coreStackBytes) (by simp)
      have h₂ := hx (messageRegion outPtr plaintext.size) (by simp)
      rw [stack_contains] at h₁
      rintro (h | h | h | h)
      · unfold preW at h; omega
      · omega
      · omega
      · exact h₂ h
  case allocated =>
    intro region hr a ha
    obtain ⟨b, hb⟩ := hCut.allocated region hr a ha
    exact Option.isSome_iff_exists.mp (hgrow a (by simp [hb]))
  case saved =>
    intro e he
    have h := hCut.saved e he
    simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hslot _ (by decide) (by decide) h
  case returnAddress =>
    have h := hCut.returnAddress
    have hsp : s.regValue .rsp = stackPtr s := rfl
    refine hSame.word64At h (by simp only [Stack.returnSlot, hsp]; omega) fun x h₁ h₂ => ?_
    simp only [Stack.returnSlot, hsp] at h₁ h₂
    exact hkeep 0x1b8 0x1c0 (by decide) (by decide) x (by unfold frameBase frameBytes; omega)
      (by unfold frameBase frameBytes; omega)
  case rip => rw [g2.rip]; exact hj
  case r12 =>
    show rd u 12 = outPtr
    rw [hreg 12 (by simp [Callee100a80.callChanges])]; exact hA.r12
  case r14 =>
    show rd u 14 = _
    rw [hreg 14 (by simp [Callee100a80.callChanges])]; exact hA.r14
  case r15 =>
    show rd u 15 = _
    rw [hreg 15 (by simp [Callee100a80.callChanges]), hA.r15]; exact hCut.r15
  case rbx =>
    show rd u 3 = _
    rw [hreg 3 (by simp [Callee100a80.callChanges]), hA.rbx]; exact hCut.rbx
  case ciphertext =>
    show (messageRegion outPtr plaintext.size).HasBytes u.external
      (chacha20Encrypt key 1 nonce plaintext)
    rw [hxU]; exact hct
  case poly =>
    have hpb : (polyBase s).toNat = frameBase s + 0x150 :=
      framePointer_add_toNat hS (k := polyOffset) (by decide)
    exact polyState_same hSame (by omega) (fun k hk => by
      rw [hpb]; exact hkeep 0x150 0x188 (by decide) (by decide) _ (by omega) (by omega))
      hCut.poly


theorem encrypt (hCall : CalleeAdvances) {t : RamState} {key : Vector UInt8 32}
    {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}
    (boundary : ReturnBoundary)
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hBoundaryOutside : ¬ InProgram boundary.rip)
    (_hBoundaryDifferent : boundary.rip ≠ (returnBoundary s).rip)
    (hCut : Cut2 s t key nonce associatedData plaintext inPtr outPtr) :
    ∃ fuel u, Advances boundary fuel t u ∧
      Cut3 s u key nonce associatedData plaintext outPtr :=
  encrypt_of_call hCall boundary hPre hBoundaryOutside hCut

theorem encrypt_segment {t : RamState} {key : Vector UInt8 32}
    {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}
    (boundary : ReturnBoundary)
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hBoundaryOutside : ¬ InProgram boundary.rip)
    (_hBoundaryDifferent : boundary.rip ≠ (returnBoundary s).rip)
    (hCut : Cut2 s t key nonce associatedData plaintext inPtr outPtr) :
    ∃ fuel u, Advances boundary fuel t u ∧
      Cut3 s u key nonce associatedData plaintext outPtr :=
  encrypt_of_call calleeAdvances boundary hPre hBoundaryOutside hCut

end Steps

end ChaCha20Poly1305.Proofs.Core.Encrypt
