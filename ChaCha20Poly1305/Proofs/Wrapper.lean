import ChaCha20Poly1305.Spec
import ChaCha20Poly1305.Proofs.CoreContract
import ChaCha20Poly1305.Proofs.Core.Call
import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Code
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Cmov.Generated.RR.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Program.Entry
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Setcc.Generated.R8.Triple
import X86Proofs.Instructions.Or.Generated.R8.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Pop.Triple

namespace ChaCha20Poly1305.Proofs.Wrapper

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine
open ChaCha20Poly1305.Proofs.CoreContract

def wrapperFrameBytes : Nat := 112

def wrapperFrame (initial : RamState) : MemoryRegion :=
  ⟨(stackPtr initial).toNat - wrapperFrameBytes, wrapperFrameBytes⟩

def savedSlot (initial : RamState) (offset : Nat) : MemoryRegion :=
  ⟨(stackPtr initial).toNat - offset, 8⟩

private theorem loadBytes_loop_isSome {memory : Machine.Ram} {address : BitVec 64}
    {remaining current shift accumulator : Nat} {value : BitVec 64}
    (h : Machine.loadBytes.loop memory address remaining current shift accumulator = .ok value) :
    ∀ i < remaining, (memory[address + BitVec.ofNat 64 (current + i)]?).isSome := by
  induction remaining generalizing current shift accumulator with
  | zero => intro i hi; omega
  | succ remaining ih =>
    cases hbyte : memory[Machine.addAddress address current]? with
    | none => simp only [Machine.loadBytes.loop, hbyte] at h; cases h
    | some byte =>
      simp only [Machine.loadBytes.loop, hbyte] at h
      intro i hi
      cases i with
      | zero =>
        change memory[address + BitVec.ofNat 64 current]? = some byte at hbyte
        simpa only [Nat.add_zero, hbyte] using (show (some byte).isSome = true from rfl)
      | succ i =>
        have hb := ih h i (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hb

theorem loadBytes_isSome {memory : Machine.Ram} {address : BitVec 64} {count : Nat}
    {value : BitVec 64} (h : Machine.loadBytes memory address count = .ok value) :
    ∀ i < count, (memory[address + BitVec.ofNat 64 i]?).isSome := by
  simpa only [Nat.zero_add] using loadBytes_loop_isSome h


theorem word64At_memLoad {region : MemoryRegion} {memory : Machine.Ram} {value : BitVec 64}
    (h : region.Word64At memory value) :
    memLoad memory (BitVec.ofNat 64 region.start) 64 = value := by
  have hb : Bytes memory (BitVec.ofNat 64 region.start) 8
      (storedByte (memLoad memory (BitVec.ofNat 64 region.start) 64)) :=
    Bytes.of_memLoad (n := 64) (loadBytes_isSome h.2)
  exact Except.ok.inj (hb.loadBytes64.symm.trans h.2)

private theorem memReadable_of_allocated {s : Machine.RamState} {region : MemoryRegion}
    {addr : BitVec 64} {len : Nat} (h : region.Allocated s.external)
    (hlow : addr.toNat + len ≤ userAddressLimit)
    (hstart : region.start ≤ addr.toNat)
    (hend : addr.toNat + len ≤ region.start + region.size) :
    MemReadable s addr len := by
  refine ⟨hlow, ?_⟩
  intro i hi
  apply Option.isSome_iff_exists.mpr
  apply h
  have hi64 : i < 2 ^ 64 := by
    unfold userAddressLimit at hlow
    omega
  have hsum : addr.toNat + i < 2 ^ 64 := by
    unfold userAddressLimit at hlow
    omega
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hsum]
  omega

theorem stack_return_readable {s : Machine.RamState} {bytes : Nat}
    (h : Stack.Valid s bytes) : MemReadable s (stackPtr s) 8 := by
  rcases h with ⟨hb, ha, hn, _⟩
  have hstart : (Stack.region s bytes).start ≤ (stackPtr s).toNat := by
    change (s.regValue .rsp).toNat - bytes ≤ (s.regValue .rsp).toNat
    omega
  have hend : (Stack.region s bytes).start + (Stack.region s bytes).size =
      (stackPtr s).toNat + 8 := by
    change ((s.regValue .rsp).toNat - bytes) +
      ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - bytes)) =
      (s.regValue .rsp).toNat + 8
    omega
  apply memReadable_of_allocated ha
  · change (Stack.region s bytes).start + (Stack.region s bytes).size < userAddressLimit at hb
    omega
  · exact hstart
  · omega

theorem chunked_get?_of_lt (d : Prelude.Bytes.Chunked) {i : Nat} (hi : i < d.toList.length) :
    d.get? i = some d.toList[i] := by
  rw [chunked_toList_length] at hi
  simp only [Prelude.Bytes.Chunked.toList, Prelude.Bytes.Chunked.toListFrom, List.getElem_map,
    List.getElem_range', Prelude.Bytes.Chunked.getD, Nat.zero_add]
  unfold Prelude.Bytes.Chunked.get?
  simp [hi]

theorem section_fetchByte_of_mem {s : ImageSection} {a : BitVec 64} {b : UInt8}
    (h : (a, b) ∈ s.toCodeMap) (hs : s.bytes.size < 2 ^ 64) :
    s.fetchByte a = some b ∧ ∃ i < s.bytes.size, a = s.address + BitVec.ofNat 64 i := by
  obtain ⟨⟨i, hi⟩, he⟩ := (mem_codeRange_iff _ _ _).mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hi' : i < s.bytes.size := by rwa [chunked_toList_length] at hi
  refine ⟨?_, i, hi', rfl⟩
  unfold ImageSection.fetchByte
  rw [show s.address + BitVec.ofNat 64 i - s.address = BitVec.ofNat 64 i by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact chunked_get?_of_lt _ hi

theorem fetchByte_of_mem_programImage {a : BitVec 64} {b : UInt8}
    (h : (a, b) ∈ Extracted.programImage) :
    Extracted.programSections.fetchByte a = some b := by
  have htext : Extracted.textBytes.size = 11759 := by decide
  have hro : Extracted.rodataBytes.size = 5128 := by decide
  simp only [Extracted.programImage, Extracted.programSections, ImageSections.toCodeMap,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at h
  simp only [Extracted.programSections, ImageSections.fetchByte]
  rcases h with h | h
  · obtain ⟨hf, -⟩ := section_fetchByte_of_mem h (by simp only [htext]; omega)
    rw [hf]; rfl
  · obtain ⟨hf, i, hi, rfl⟩ := section_fetchByte_of_mem h (by simp only [hro]; omega)
    rw [hf]
    have hnone : ImageSection.fetchByte ⟨Extracted.textAddress, Extracted.textBytes⟩
        (Extracted.rodataAddress + BitVec.ofNat 64 i) = none := by
      simp only [hro] at hi
      unfold ImageSection.fetchByte Prelude.Bytes.Chunked.get?
      simp only [htext]
      split
      · rename_i hlt
        simp only [Extracted.textAddress, Extracted.rodataAddress] at hlt
        rw [show (0x200000 : BitVec 64) + BitVec.ofNat 64 i - 0x100000 =
          BitVec.ofNat 64 (0x100000 + i) by
            apply BitVec.eq_of_toNat_eq; simp; omega] at hlt
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt
        omega
      · rfl
    rw [hnone]; rfl

theorem codeIn_of_programLoaded {s : Machine.RamState} (h : ProgramLoaded s) :
    ∀ a b, (a, b) ∈ Extracted.programImage → s.external[a]? = some b :=
  fun a b hm => h a b (fetchByte_of_mem_programImage hm)

theorem entry_ready (bindings : Machine.Bindings) {s : Machine.RamState}
    (hBindings : MachineRamUnitStrideDecodable bindings s)
    (hMachine : SupportedIntegerMachineState bindings.processor s)
    (hLoaded : ProgramLoaded s) :
    @EntryReady bindings Extracted.programImage s := by
  letI := bindings
  exact EntryReady.of_sections hMachine hBindings.smrr hBindings.memoryType
    hBindings.leadingZeroCount (codeIn_of_programLoaded hLoaded) (by decide +kernel)

structure AtCoreCall (initial s : RamState) : Prop where
  rsp : stackPtr s = stackPtr initial - 112
  returnAddress : (returnBoundary s).rip = coreReturnAddressInPlace
  rdi : s.regValue .rdi = stackPtr s + 0x27
  rbx : s.regValue .rbx = initial.regValue .r9
  r14 : s.regValue .r14 = initial.regValue .rcx
  r15 : (stackArgumentSlot initial 0).Word64At initial.external (s.regValue .r15)
  rbp : s.regValue .rbp = initial.regValue .rbp
  r12 : s.regValue .r12 = initial.regValue .r12
  r13 : s.regValue .r13 = initial.regValue .r13
  savedR15 : (savedSlot initial 8).Word64At s.external (initial.regValue .r15)
  savedR14 : (savedSlot initial 16).Word64At s.external (initial.regValue .r14)
  savedRbx : (savedSlot initial 24).Word64At s.external (initial.regValue .rbx)
  frame : MemoryWriteFrame initial s #v[wrapperFrame initial]
  grows : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome

theorem entry_boundary [bindings : Machine.Bindings] {initial : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall encryptInPlace initial [key, nonce, associatedData, plaintext]) :
    nearReturn64Boundary initial = .ok (returnBoundary initial) ∧
      ¬ InProgram (returnBoundary initial).rip := by
  have hEntry := entry_ready bindings hBindings hMachine hCall.programLoaded
  refine ⟨nearReturn64Boundary_eq initial hEntry.ready.dataReady hMachine.integer.ss
    (stack_return_readable hCall.stackAvailable), ?_⟩
  obtain ⟨address, hSlot, -, hOutside⟩ := hCall.returnAddress
  have hRead := word64At_memLoad hSlot
  have hRip : (returnBoundary initial).rip = address := by
    simp only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hRead
    exact hRead
  rw [hRip]
  exact hOutside

theorem coreReturnAddress_inProgram : InProgram coreReturnAddressInPlace :=
  ⟨0x80, by decide +kernel⟩

structure EntryStack (initial : RamState) : Prop where
  top : (stackPtr initial).toNat + 8 < 2 ^ 32
  room : 1104 ≤ (stackPtr initial).toNat
  allocated : ∀ a : BitVec 64, (stackPtr initial).toNat - 1104 ≤ a.toNat →
    a.toNat < (stackPtr initial).toNat + 8 → (initial.external[a]?).isSome
  outside : ∀ a : BitVec 64, (stackPtr initial).toNat - 1104 ≤ a.toNat →
    a.toNat < (stackPtr initial).toNat + 8 → ¬ InProgram a
  tables : 0x2020 ≤ (stackPtr initial).toNat - 1104 ∨ (stackPtr initial).toNat + 8 ≤ 0x1000

theorem stack_mem_written {initial : RamState} {inputs : List ByteArray} :
    Stack.region initial 1104 ∈ writtenRegions encryptInPlace initial inputs := by
  simp [writtenRegions, encryptInPlace]

theorem entry_stack {initial : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    (hCall : ValidCall encryptInPlace initial [key, nonce, associatedData, plaintext]) :
    EntryStack initial := by
  have hv : Stack.Valid initial 1104 := hCall.stackAvailable
  obtain ⟨hb, ha, hn, -⟩ := hv
  have hav := hCall.separation.2.2 _ stack_mem_written
  simp only [Stack.region, MemoryRegion.Bounded, userAddressLimit, MemoryRegion.Allocated,
    MemoryRegion.Contains, Stack.NoUnderflow, Stack.returnAddressBytes] at hb ha hn
  simp only [MemoryRegion.Avoids, Stack.region, MemoryRegion.Contains, pageTables,
    Stack.returnAddressBytes] at hav
  have hsp : initial.regValue .rsp = stackPtr initial := rfl
  rw [hsp] at hb ha hn hav
  refine ⟨by omega, hn, ?_, ?_, ?_⟩
  · intro a h1 h2
    obtain ⟨b, hb⟩ := ha a ⟨h1, by change _ < _ + (_ + 8 - _); omega⟩
    simp [hb]
  · intro a h1 h2 hp
    exact hav a ⟨h1, by change _ < _ + (_ + 8 - _); omega⟩ (.inl hp)
  · refine Classical.byContradiction fun hc => ?_
    let x : Nat := max ((stackPtr initial).toNat - 1104) 0x1000
    have hx : x < 2 ^ 64 := by omega
    apply hav (BitVec.ofNat 64 x)
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
      constructor <;> omega
    · right
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
      constructor <;> omega

def Grows (initial u : RamState) : Prop :=
  ∀ a : BitVec 64, (initial.external[a]?).isSome → (u.external[a]?).isSome

theorem Grows.step {initial u v : RamState} {cs : List Component} (h : Grows initial u)
    (he : AgreesExcept cs u v) : Grows initial v :=
  fun a ha => he.grow a (h a ha)

theorem slot_toNat {I : BitVec 64} {k i : Nat} (hk : k ≤ I.toNat) (hI : I.toNat + 8 < 2 ^ 32)
    (hi : i < k + 8) :
    (I - BitVec.ofNat 64 k + BitVec.ofNat 64 i).toNat = I.toNat - k + i := by
  have hk64 : k < 2 ^ 64 := by omega
  have hi64 : i < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt hi64]
  omega

theorem slot_toNat0 {I : BitVec 64} {k : Nat} (hk : k ≤ I.toNat) :
    (I - BitVec.ofNat 64 k).toNat = I.toNat - k := by
  have hk64 : k < 2 ^ 64 := by have := I.isLt; omega
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  omega

theorem slot_writable {initial u : RamState} (hS : EntryStack initial) (hg : Grows initial u)
    {k : Nat} (hk8 : 8 ≤ k) (hk : k ≤ 1104) :
    MemWritable u (stackPtr initial - BitVec.ofNat 64 k) 8 := by
  have hroom := hS.room
  have htop := hS.top
  refine ⟨?_, ?_, ?_⟩
  · rw [slot_toNat0 (by omega)]; omega
  · intro i hi
    apply hg
    apply hS.allocated <;> rw [slot_toNat (by omega) htop (by omega)] <;> omega
  · rw [slot_toNat0 (by omega)]
    have := hS.tables
    unfold PageTableEntriesApart
    omega

theorem slot_apart {initial : RamState} (hS : EntryStack initial) {k : Nat} (hk8 : 8 ≤ k)
    (hk : k ≤ 1104) {p : BitVec 64} {len : Nat}
    (hp : ∀ j < len, InProgram (p + BitVec.ofNat 64 j)) :
    RangeApart (stackPtr initial - BitVec.ofNat 64 k) 8 p len := by
  intro i hi j hj he
  have hroom := hS.room
  have htop := hS.top
  apply hS.outside (stackPtr initial - BitVec.ofNat 64 k + BitVec.ofNat 64 i)
  · rw [slot_toNat (by omega) htop (by omega)]; omega
  · rw [slot_toNat (by omega) htop (by omega)]; omega
  · rw [he]; exact hp j hj

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

theorem code_ne_boundary {boundary : ReturnBoundary} (hOutside : ¬ InProgram boundary.rip)
    (off : Nat) (h : off < 11759) : BitVec.ofNat 64 (0x100000 + off) ≠ boundary.rip := by
  intro he
  apply hOutside
  rw [← he]
  have := code_inProgram off 1 (by omega) 0 (by omega)
  simpa using this

theorem slot_not_covers {I : BitVec 64} {k k' i : Nat} (hi : i < 8)
    (h : k + 8 ≤ k' ∨ k' + 8 ≤ k) (hk : k ≤ 1104) (hk' : k' ≤ 1104) :
    ¬ (Component.mem (I - BitVec.ofNat 64 k') 8).Covers (I - BitVec.ofNat 64 k + BitVec.ofNat 64 i) := by
  rintro ⟨j, hj, he⟩
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at this
  have := I.isLt
  omega

theorem step_run [Bindings] {pre : RamState → Prop} {e : RamState → Effect}
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

theorem slot_av {initial : RamState} (hS : EntryStack initial) {k : Nat} (hk8 : 8 ≤ k)
    (hk : k ≤ 1104) {cs : List Component}
    (hcs : ∀ c ∈ cs, c = .mem (stackPtr initial - BitVec.ofNat 64 k) 8 ∨ ∀ a, ¬ c.Covers a) :
    ∀ c ∈ cs, ∀ a, c.Covers a → ¬ InProgram a := by
  intro c hc a hcov
  rcases hcs c hc with rfl | h
  · obtain ⟨i, hi, rfl⟩ := hcov
    have hroom := hS.room
    have htop := hS.top
    apply hS.outside <;> rw [slot_toNat (by omega) htop (by omega)] <;> omega
  · exact absurd hcov (h a)

theorem noMem_av {cs : List Component} (hcs : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) :
    ∀ c ∈ cs, ∀ a, c.Covers a → ¬ InProgram a :=
  fun c hc a hcov => absurd hcov (hcs c hc a)

theorem regs_av {cs : List Component} (h : ∀ c ∈ cs, c.isMem = false) :
    ∀ c ∈ cs, ∀ a, c.Covers a → ¬ InProgram a := by
  intro c hc a hcov
  have := h c hc
  cases c <;> simp_all [Component.Covers, Component.isMem]

macro "reg_av" : tactic => `(tactic| (apply regs_av; simp [Component.isMem]))

theorem storePre_slot {initial u : RamState} (hS : EntryStack initial) (hg : Grows initial u)
    {p : BitVec 64} {len k : Nat} {addr : RamState → BitVec 64} (hrip : u.RIP = p)
    (haddr : addr u = stackPtr initial - BitVec.ofNat 64 k) (hk8 : 8 ≤ k) (hk : k ≤ 1104)
    (hp : ∀ j < len, InProgram (p + BitVec.ofNat 64 j)) : StorePre p len addr 8 u :=
  ⟨hrip, haddr ▸ slot_writable hS hg hk8 hk, haddr ▸ slot_apart hS hk8 hk hp⟩

theorem sub_sub_ofNat (I : BitVec 64) (a b : Nat) :
    I - BitVec.ofNat 64 a - BitVec.ofNat 64 b = I - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

theorem sub_add_ofNat (I : BitVec 64) {a b : Nat} (h : b ≤ a) :
    I - BitVec.ofNat 64 a + BitVec.ofNat 64 b = I - BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := I.isLt
  omega

theorem mem_not_covers {a x : BitVec 64} {n : Nat}
    (h : x.toNat < a.toNat ∨ a.toNat + n ≤ x.toNat) (ha : a.toNat + n < 2 ^ 64) :
    ¬ (Component.mem a n).Covers x := by
  rintro ⟨j, hj, rfl⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)] at h
  omega

theorem nonmem_not_covers {c : Component} (h : c.isMem = false) (x : BitVec 64) :
    ¬ c.Covers x := by
  cases c <;> simp_all [Component.Covers, Component.isMem]

macro "not_cover" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, $ls,*]
  repeat' apply And.intro
  all_goals first
    | exact nonmem_not_covers rfl _
    | (apply mem_not_covers <;>
        simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega)))

theorem regValue_read (s : RamState) :
    s.regValue .rdi = (Operand.reg 7 : Operand 64).read s ∧
    s.regValue .rsi = (Operand.reg 6 : Operand 64).read s ∧
    s.regValue .rdx = (Operand.reg 2 : Operand 64).read s ∧
    s.regValue .rcx = (Operand.reg 1 : Operand 64).read s ∧
    s.regValue .r8 = (Operand.reg 8 : Operand 64).read s ∧
    s.regValue .r9 = (Operand.reg 9 : Operand 64).read s ∧
    s.regValue .rbx = (Operand.reg 3 : Operand 64).read s ∧
    s.regValue .rbp = (Operand.reg 5 : Operand 64).read s ∧
    s.regValue .r12 = (Operand.reg 12 : Operand 64).read s ∧
    s.regValue .r13 = (Operand.reg 13 : Operand 64).read s ∧
    s.regValue .r14 = (Operand.reg 14 : Operand 64).read s ∧
    s.regValue .r15 = (Operand.reg 15 : Operand 64).read s ∧
    s.regValue .rsp = (Operand.reg 4 : Operand 64).read s := by
  simp only [Operand.read_reg64]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem region_sep {r r' : MemoryRegion} (h : r.Disjoint r') (hr : 0 < r.size)
    (hr' : 0 < r'.size) : r.start + r.size ≤ r'.start ∨ r'.start + r'.size ≤ r.start := by
  refine Classical.byContradiction fun hc => ?_
  exact h (max r.start r'.start) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩

theorem sp_keep {cs : List Component} {u v : RamState} {x : BitVec 64}
    (he : AgreesExcept cs u v) (h : Component.reg 4 ∉ cs) (hu : stackPtr u = x) :
    stackPtr v = x := by
  rw [stackPtr_eq_read, he.read h, ← stackPtr_eq_read, hu]

theorem rsp_addr {u : RamState} {I : BitVec 64} {k : Nat} (hu : stackPtr u = I - BitVec.ofNat 64 k)
    (dd : BitVec 8) (d : Nat) (hd : dd.signExtend 64 = BitVec.ofNat 64 d) (hdk : d ≤ k)
    (x : BitVec 64) :
    (AddrMode.sib 4 none 0 (.d8 dd)).addr u x = I - BitVec.ofNat 64 (k - d) := by
  simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
  rw [show ((4 : BitVec 4).setWidth 5) = (4 : BitVec 5) from rfl, ← stackPtr_eq_read, hu, hd,
    sub_add_ofNat _ hdk]

theorem rsp_addr0 {u : RamState} {I : BitVec 64} {k : Nat}
    (hu : stackPtr u = I - BitVec.ofNat 64 k) (x : BitVec 64) :
    (AddrMode.sib 4 none 0 .none).addr u x = I - BitVec.ofNat 64 k := by
  simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
  rw [show ((4 : BitVec 4).setWidth 5) = (4 : BitVec 5) from rfl, ← stackPtr_eq_read, hu]
  exact BitVec.add_zero _

theorem rdi_addr {u : RamState} {K : BitVec 64} (hu : (Operand.reg 7 : Operand 64).read u = K)
    (dd : BitVec 8) (d : Nat) (hd : dd.signExtend 64 = BitVec.ofNat 64 d) (x : BitVec 64) :
    (AddrMode.base 7 (.d8 dd)).addr u x = K + BitVec.ofNat 64 d := by
  simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
  rw [show ((7 : BitVec 4).setWidth 5) = (7 : BitVec 5) from rfl, hu, hd]

theorem rdi_addr0 {u : RamState} {K : BitVec 64} (hu : (Operand.reg 7 : Operand 64).read u = K)
    (x : BitVec 64) : (AddrMode.base 7 .none).addr u x = K + BitVec.ofNat 64 0 := by
  simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
  rw [show ((7 : BitVec 4).setWidth 5) = (7 : BitVec 5) from rfl, hu]
  rfl

theorem add_ofNat_toNat {K : BitVec 64} {j : Nat} (_h : K.toNat + j < 2 ^ 64) :
    K + BitVec.ofNat 64 j = BitVec.ofNat 64 (K.toNat + j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem key_readable {initial u : RamState} {K : BitVec 64} (hg : Grows initial u)
    (hB : K.toNat + 32 < 2 ^ 32)
    (hbytes : ∀ j < 32, (initial.external[K + BitVec.ofNat 64 j]?).isSome) (d : Nat)
    (hd : d + 8 ≤ 32) : MemReadable u (K + BitVec.ofNat 64 d) 8 := by
  refine ⟨?_, fun i hi => hg _ ?_⟩
  · rw [add_ofNat_toNat (by omega), BitVec.toNat_ofNat]; omega
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact hbytes _ (by omega)

theorem writes_slot {initial : RamState} (hS : EntryStack initial) {k : Nat} (hk8 : 8 ≤ k)
    (hk : k ≤ 112) {cs : List Component}
    (hcs : ∀ c ∈ cs, c = .mem (stackPtr initial - BitVec.ofNat 64 k) 8 ∨ ∀ a, ¬ c.Covers a) :
    WritesWithin cs #v[wrapperFrame initial] := by
  intro c hc a hcov
  refine ⟨wrapperFrame initial, by simp, ?_⟩
  rcases hcs c hc with rfl | h
  · obtain ⟨i, hi, rfl⟩ := hcov
    have hroom := hS.room
    have htop := hS.top
    simp only [wrapperFrame, wrapperFrameBytes, MemoryRegion.Contains]
    rw [slot_toNat (by omega) htop (by omega)]
    omega
  · exact absurd hcov (h a)

theorem writes_regs {initial : RamState} {cs : List Component}
    (h : ∀ c ∈ cs, c.isMem = false) : WritesWithin cs #v[wrapperFrame initial] := by
  intro c hc a hcov
  exact absurd hcov (nonmem_not_covers (h c hc) a)

theorem frame_step {initial u v : RamState} {cs : List Component}
    (hF : MemoryWriteFrame initial u #v[wrapperFrame initial]) (he : AgreesExcept cs u v)
    (hw : WritesWithin cs #v[wrapperFrame initial]) :
    MemoryWriteFrame initial v #v[wrapperFrame initial] :=
  memoryWriteFrame_trans hF (he.memoryWriteFrame hw)

theorem load_outside {initial u : RamState}
    (hF : MemoryWriteFrame initial u #v[wrapperFrame initial]) {a : BitVec 64}
    (h : ∀ i < 8, ¬ (wrapperFrame initial).Contains (a + BitVec.ofNat 64 i).toNat) :
    memLoad u.external a 64 = memLoad initial.external a 64 := by
  apply memLoad_congr
  intro i hi
  simp only [memByte]
  congr 1
  exact hF _ (by simpa using h i hi)

macro "frame_regs" : tactic => `(tactic| (apply writes_regs; simp [Component.isMem]))

syntax "slot_cs" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| slot_cs [$ls,*]) => `(tactic| (
    simp only [pushR64Effect_components, movM64R64Effect_components, pushEffect_components,
      storeAddrAt, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true, true_or, $ls,*]
    repeat' apply And.intro
    all_goals first
      | trivial
      | exact .inl rfl
      | exact .inr (fun _ => nonmem_not_covers rfl _)
      | exact (fun _ => nonmem_not_covers rfl _)))

theorem be_holds {f : StatusFlags} {a b : BitVec 64}
    (hf : (StatusFlagsOutcome.ofStatusFlags (cmpSpec a b)).Allows f) (h : a.toNat ≤ b.toNat) :
    condHolds 6 f = true := by
  obtain ⟨hCF, -, -, hZF, -⟩ := hf
  change f.CF = (cmpSpec a b).CF at hCF
  change f.ZF = (cmpSpec a b).ZF at hZF
  rw [condHolds_6, hCF, hZF, cmpSpec_ZF]
  change (decide (a.toNat < b.toNat) || (a == b)) = true
  by_cases hl : a.toNat < b.toNat
  · simp [hl]
  · have : a = b := BitVec.eq_of_toNat_eq (by omega)
    simp [this]

theorem flags_keep {cs : List Component} {u v : RamState} (he : AgreesExcept cs u v)
    (h : Component.flags ∉ cs) :
    StatusFlags.ofRFLAGS v.RFLAGS = StatusFlags.ofRFLAGS u.RFLAGS :=
  he.agree _ h rfl

def changes (initial : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 6, .reg 7, .reg 9, .reg 14, .reg 15, .flags, .rip,
    .mem (stackPtr initial - BitVec.ofNat 64 112) 112]

structure Track [Machine.Bindings] (initial u : RamState) : Prop where
  ready : ReadyToStep u
  code : CodeIn Extracted.programImage u
  agrees : AgreesExcept (changes initial) initial u

def StepWrites (initial : RamState) (k : Nat) (cs : List Component) : Prop :=
  ∀ c ∈ cs, (c.isMem = false ∧ c ∈ changes initial) ∨
    (8 ≤ k ∧ k ≤ 112 ∧ c = .mem (stackPtr initial - BitVec.ofNat 64 k) 8)

theorem frame_covers {initial : RamState} (hS : EntryStack initial) {k i : Nat} (hk8 : 8 ≤ k)
    (hk : k ≤ 112) (hi : i < 8) :
    (Component.mem (stackPtr initial - BitVec.ofNat 64 112) 112).Covers
      (stackPtr initial - BitVec.ofNat 64 k + BitVec.ofNat 64 i) := by
  refine ⟨112 - k + i, by omega, ?_⟩
  have := hS.room
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem StepWrites.av {initial : RamState} (hS : EntryStack initial) {k : Nat}
    {cs : List Component} (h : StepWrites initial k cs) :
    ∀ c ∈ cs, ∀ a, c.Covers a → ¬ InProgram a := by
  intro c hc a hcov
  rcases h c hc with ⟨hm, -⟩ | ⟨hk8, hk, rfl⟩
  · exact absurd hcov (nonmem_not_covers hm a)
  · obtain ⟨i, hi, rfl⟩ := hcov
    have hroom := hS.room
    have htop := hS.top
    apply hS.outside <;> rw [slot_toNat (by omega) htop (by omega)] <;> omega

theorem StepWrites.widen {initial u v : RamState} (hS : EntryStack initial) {k : Nat}
    {cs : List Component} (h : StepWrites initial k cs) (he : AgreesExcept cs u v) :
    AgreesExcept (changes initial) u v := by
  refine ⟨fun c hc hm => he.agree c (fun hcs => ?_) hm, fun x hx => he.memory x ?_,
    he.rest, he.grow⟩
  · rcases h c hcs with ⟨-, h1⟩ | ⟨-, -, rfl⟩
    · exact hc h1
    · simp [Component.isMem] at hm
  · intro c hcs hcov
    rcases h c hcs with ⟨-, h1⟩ | ⟨hk8, hk, rfl⟩
    · exact hx c h1 hcov
    · obtain ⟨i, hi, rfl⟩ := hcov
      exact hx _ (by simp [changes]) (frame_covers hS hk8 hk hi)

theorem StepWrites.keep {initial u v : RamState} {k : Nat} {cs : List Component}
    (h : StepWrites initial k cs) (he : AgreesExcept cs u v) {k' : Nat}
    (hkk : k = 0 ∨ k + 8 ≤ k' ∨ k' + 8 ≤ k) (hk' : k' ≤ 1104) :
    (Operand.mem (stackPtr initial - BitVec.ofNat 64 k') : Operand 64).read v =
      (Operand.mem (stackPtr initial - BitVec.ofNat 64 k') : Operand 64).read u := by
  apply memLoad_congr
  intro i hi
  change i < 8 at hi
  simp only [memByte]
  congr 1
  apply he.byte
  intro c hc
  rcases h c hc with ⟨hm, -⟩ | ⟨hk8, hk, rfl⟩
  · exact nonmem_not_covers hm _
  · exact slot_not_covers hi (by omega) (by omega) (by omega)

theorem Track.frame [Machine.Bindings] {initial u : RamState} (hS : EntryStack initial)
    (hT : Track initial u) : MemoryWriteFrame initial u #v[wrapperFrame initial] := by
  apply hT.agrees.memoryWriteFrame
  intro c hc a hcov
  refine ⟨wrapperFrame initial, by simp, ?_⟩
  simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Component.Covers] at hcov
  obtain ⟨i, hi, rfl⟩ := hcov
  have := hS.room
  simp only [wrapperFrame, wrapperFrameBytes, MemoryRegion.Contains, BitVec.toNat_add,
    BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem Track.grows [Machine.Bindings] {initial u : RamState} (hT : Track initial u) :
    Grows initial u :=
  hT.agrees.grow

theorem track_step [Machine.Bindings] {initial : RamState} (hS : EntryStack initial)
    {pre : RamState → Prop} {e : RamState → Effect} {p : BitVec 64} {bytes : List UInt8}
    {k : Nat} (hStep : StepEffect pre (codeRange p bytes) e) {u : RamState}
    (hT : Track initial u) (hbytes : CodeIn (codeRange p bytes) u) (hpre : pre u)
    (hne : (e u).rip ≠ (returnBoundary initial).rip)
    (hw : StepWrites initial k (e u).components) :
    ∃ v, Advances (returnBoundary initial) 1 u v ∧ Track initial v ∧ (e u).Holds u v := by
  obtain ⟨v, ha, hr, hc, he⟩ := step_run hStep hT.ready hT.code hbytes hpre hne (hw.av hS)
  refine ⟨v, ha, ⟨hr, hc, (hT.agrees.trans (hw.widen hS he.agrees)).mono ?_⟩, he⟩
  intro c hc
  simp only [List.mem_append, or_self] at hc
  exact hc

syntax "step_writes" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| step_writes [$ls,*]) => `(tactic| (
    simp only [StepWrites, pushR64Effect_components, movM64R64Effect_components,
      pushEffect_components, subR64Imm8Effect_components, movR64R64Effect_components,
      movR64M64Effect_components, xorR32R32Effect_components, cmpR64R64Effect_components,
      cmovR64R64Effect_components, leaR64Effect_components, movR32Imm32Effect_components,
      storeAddrAt, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true, $ls,*]
    repeat' apply And.intro
    all_goals first
      | exact .inl ⟨rfl, by simp [changes]⟩
      | (apply Or.inr; repeat' apply And.intro; all_goals first | rfl | omega)))

theorem mem_keep {u v : RamState} {cs : List Component} (he : AgreesExcept cs u v)
    (h : ∀ c ∈ cs, c.isMem = false) (a : BitVec 64) :
    (Operand.mem a : Operand 64).read v = (Operand.mem a : Operand 64).read u := by
  change memLoad v.external a 64 = memLoad u.external a 64
  rw [he.external (fun c hc x => nonmem_not_covers (h c hc) x)]

abbrev rd (u : RamState) (n : BitVec 5) : BitVec 64 := (Operand.reg n : Operand 64).read u

abbrev wd (u : RamState) (a : BitVec 64) : BitVec 64 := (Operand.mem a : Operand 64).read u

theorem phase_a [Machine.Bindings] {initial : RamState} (hS : EntryStack initial)
    (hOut : ¬ InProgram (returnBoundary initial).rip) (T0 : Track initial initial)
    (hRip : initial.RIP = 0x101930) (hArgB : (stackPtr initial).toNat + 16 < 2 ^ 32)
    (hArgSome : ∀ i < 8, (initial.external[stackPtr initial + 8 + BitVec.ofNat 64 i]?).isSome) :
    ∃ n u, Advances (returnBoundary initial) n initial u ∧ Track initial u ∧
      u.RIP = 0x10194a ∧ stackPtr u = stackPtr initial - BitVec.ofNat 64 104 ∧
      rd u 15 = memLoad initial.external (stackPtr initial + 8) 64 ∧
      rd u 3 = rd initial 9 ∧ rd u 14 = rd initial 1 ∧ rd u 1 = rd initial 2 ∧
      rd u 2 = rd initial 6 ∧ rd u 7 = rd initial 7 ∧ rd u 9 = rd initial 9 ∧
      wd u (stackPtr initial - BitVec.ofNat 64 8) = rd initial 15 ∧
      wd u (stackPtr initial - BitVec.ofNat 64 16) = rd initial 14 ∧
      wd u (stackPtr initial - BitVec.ofNat 64 24) = rd initial 3 := by
  have hpa0 : pushAddr initial = stackPtr initial - BitVec.ofNat 64 8 := rfl
  have hw1 : StepWrites initial 8 (pushR64Effect 0x101930 2 15 initial).components := by
    step_writes [hpa0]
  obtain ⟨s1, a1, T1, e1⟩ := track_step hS
    (push_r64_rex_effect_step 0x101930 0x41 0x57 (by unfold RexPrefix; decide) (by decide))
    T0 (program_text_slice T0.code 0x1930 2 (by decide +kernel))
    (storePre_slot hS T0.grows hRip hpa0 (by omega) (by omega) (code_inProgram 0x1930 2 (by omega))) (code_ne_boundary hOut 0x1932 (by omega)) hw1
  change (pushR64Effect 0x101930 2 15 initial).Holds initial s1 at e1
  have hsp1 : stackPtr s1 = stackPtr initial - BitVec.ofNat 64 8 := e1.writes.1
  have hpa1 : pushAddr s1 = stackPtr initial - BitVec.ofNat 64 16 := by rw [pushAddr, hsp1]; bv_omega
  have hw2 : StepWrites initial 16 (pushR64Effect 0x101932 2 14 s1).components := by
    step_writes [hpa1]
  obtain ⟨s2, a2, T2, e2⟩ := track_step hS
    (push_r64_rex_effect_step 0x101932 0x41 0x56 (by unfold RexPrefix; decide) (by decide))
    T1 (program_text_slice T1.code 0x1932 2 (by decide +kernel))
    (storePre_slot hS T1.grows e1.rip hpa1 (by omega) (by omega) (code_inProgram 0x1932 2 (by omega))) (code_ne_boundary hOut 0x1934 (by omega)) hw2
  change (pushR64Effect 0x101932 2 14 s1).Holds s1 s2 at e2
  have hsp2 : stackPtr s2 = stackPtr initial - BitVec.ofNat 64 16 := by
    rw [show stackPtr s2 = pushAddr s1 from e2.writes.1, hpa1]
  have hpa2 : pushAddr s2 = stackPtr initial - BitVec.ofNat 64 24 := by rw [pushAddr, hsp2]; bv_omega
  have hw3 : StepWrites initial 24 (pushR64Effect 0x101934 1 3 s2).components := by
    step_writes [hpa2]
  obtain ⟨s3, a3, T3, e3⟩ := track_step hS
    (push_r64_effect_step 0x101934 0x53 (by decide))
    T2 (program_text_slice T2.code 0x1934 1 (by decide +kernel))
    (storePre_slot hS T2.grows e2.rip hpa2 (by omega) (by omega) (code_inProgram 0x1934 1 (by omega))) (code_ne_boundary hOut 0x1935 (by omega)) hw3
  change (pushR64Effect 0x101934 1 3 s2).Holds s2 s3 at e3
  have hsp3 : stackPtr s3 = stackPtr initial - BitVec.ofNat 64 24 := by
    rw [show stackPtr s3 = pushAddr s2 from e3.writes.1, hpa2]
  have hw4 : StepWrites initial 0 (subR64Imm8Effect 0x101935 4 0x50 s3).components := by
    step_writes []
  obtain ⟨s4, a4, T4, e4⟩ := track_step hS
    (sub_r64_imm8_effect_step 0x101935 0x48 0xec 0x50 (by unfold RexWPrefix; decide)
      (by decide) (by decide))
    T3 (program_text_slice T3.code 0x1935 4 (by decide +kernel))
    e3.rip (code_ne_boundary hOut 0x1939 (by omega)) hw4
  change (subR64Imm8Effect 0x101935 4 0x50 s3).Holds s3 s4 at e4
  have hsp4 : stackPtr s4 = stackPtr initial - BitVec.ofNat 64 104 := by
    have h : stackPtr s4 = stackPtr s3 - (0x50 : BitVec 8).signExtend 64 := e4.writes
    rw [h, hsp3, show (0x50 : BitVec 8).signExtend 64 = 0x50 from rfl]
    bv_omega
  have hw5 : StepWrites initial 0 (movR64R64Effect 0x101939 3 9 s4).components := by
    step_writes []
  obtain ⟨s5, a5, T5, e5⟩ := track_step hS
    (mov_r64_r64_effect_step 0x101939 0x4c 0xcb (by unfold RexWPrefix; decide) (by decide))
    T4 (program_text_slice T4.code 0x1939 3 (by decide +kernel))
    e4.rip (code_ne_boundary hOut 0x193c (by omega)) hw5
  change (movR64R64Effect 0x101939 3 9 s4).Holds s4 s5 at e5
  have hw6 : StepWrites initial 0 (movR64R64Effect 0x10193c 14 1 s5).components := by
    step_writes []
  obtain ⟨s6, a6, T6, e6⟩ := track_step hS
    (mov_r64_r64_effect_step 0x10193c 0x49 0xce (by unfold RexWPrefix; decide) (by decide))
    T5 (program_text_slice T5.code 0x193c 3 (by decide +kernel))
    e5.rip (code_ne_boundary hOut 0x193f (by omega)) hw6
  change (movR64R64Effect 0x10193c 14 1 s5).Holds s5 s6 at e6
  have hw7 : StepWrites initial 0 (movR64R64Effect 0x10193f 1 2 s6).components := by
    step_writes []
  obtain ⟨s7, a7, T7, e7⟩ := track_step hS
    (mov_r64_r64_effect_step 0x10193f 0x48 0xd1 (by unfold RexWPrefix; decide) (by decide))
    T6 (program_text_slice T6.code 0x193f 3 (by decide +kernel))
    e6.rip (code_ne_boundary hOut 0x1942 (by omega)) hw7
  change (movR64R64Effect 0x10193f 1 2 s6).Holds s6 s7 at e7
  have hw8 : StepWrites initial 0 (movR64R64Effect 0x101942 2 6 s7).components := by
    step_writes []
  obtain ⟨s8, a8, T8, e8⟩ := track_step hS
    (mov_r64_r64_effect_step 0x101942 0x48 0xf2 (by unfold RexWPrefix; decide) (by decide))
    T7 (program_text_slice T7.code 0x1942 3 (by decide +kernel))
    e7.rip (code_ne_boundary hOut 0x1945 (by omega)) hw8
  change (movR64R64Effect 0x101942 2 6 s7).Holds s7 s8 at e8
  have hsp8 : stackPtr s8 = stackPtr initial - BitVec.ofNat 64 104 := by
    rw [stackPtr_eq_read, (((e5.agrees.trans e6.agrees).trans e7.agrees).trans e8.agrees).read (by simp), ← stackPtr_eq_read, hsp4]
  have hA9 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x70)).addr s8 x = stackPtr initial + 8 := by
    intro x
    simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
    rw [show ((4 : BitVec 4).setWidth 5) = (4 : BitVec 5) from rfl, ← stackPtr_eq_read, hsp8,
      show (0x70 : BitVec 8).signExtend 64 = 0x70 from rfl]
    bv_omega
  have hw9 : StepWrites initial 0 (movR64M64Effect 0x101945 15 (.sib 4 none 0 (.d8 0x70)) s8).components := by
    step_writes []
  obtain ⟨s9, a9, T9, e9⟩ := track_step hS
    (mov_r64_m64_effect_step 0x101945 0x4c (by unfold RexWPrefix; decide) 7
      (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide))
    T8 (program_text_slice T8.code 0x1945 5 (by decide +kernel))
    ⟨e8.rip, by
      rw [hA9]
      have := hS.top
      refine ⟨?_, fun i hi => T8.grows _ (hArgSome i hi)⟩
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega⟩ (code_ne_boundary hOut 0x194a (by omega)) hw9
  change (movR64M64Effect 0x101945 15 (.sib 4 none 0 (.d8 0x70)) s8).Holds s8 s9 at e9
  refine ⟨_, s9, ((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9), T9, e9.rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stackPtr_eq_read, e9.agrees.read (by simp), ← stackPtr_eq_read, hsp8]
  · show (Operand.reg 15 : Operand 64).read s9 = _
    rw [e9.writes]
    change memLoad s8.external _ 64 = _
    rw [hA9]
    apply load_outside (T8.frame hS)
    intro i hi
    have := hS.room
    have := hS.top
    simp only [wrapperFrame, wrapperFrameBytes, MemoryRegion.Contains, BitVec.ofNat_eq_ofNat,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · show (Operand.reg 3 : Operand 64).read s9 = _
    rw [(((e6.agrees.trans e7.agrees).trans e8.agrees).trans e9.agrees).read (by simp), e5.writes, (((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).read (by simp)]
  · show (Operand.reg 14 : Operand 64).read s9 = _
    rw [((e7.agrees.trans e8.agrees).trans e9.agrees).read (by simp), e6.writes, ((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).read (by simp)]
  · show (Operand.reg 1 : Operand 64).read s9 = _
    rw [(e8.agrees.trans e9.agrees).read (by simp), e7.writes, (((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).read (by simp)]
  · show (Operand.reg 2 : Operand 64).read s9 = _
    rw [e9.agrees.read (by simp), e8.writes, ((((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).read (by simp)]
  · exact ((((((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).read (by simp)
  · exact ((((((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).read (by simp)
  · exact Eq.trans (Eq.trans (hw9.keep e9.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw8.keep e8.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw7.keep e7.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw6.keep e6.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw5.keep e5.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw4.keep e4.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw3.keep e3.agrees (k' := 8) (by omega) (by omega)) (hw2.keep e2.agrees (k' := 8) (by omega) (by omega))))))))) e1.writes.2
  · exact Eq.trans (Eq.trans (hw9.keep e9.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw8.keep e8.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw7.keep e7.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw6.keep e6.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw5.keep e5.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw4.keep e4.agrees (k' := 16) (by omega) (by omega)) (hw3.keep e3.agrees (k' := 16) (by omega) (by omega)))))))) (hpa1 ▸ (e2.writes.2.trans (e1.agrees.read (by simp))))
  · exact Eq.trans (Eq.trans (hw9.keep e9.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw8.keep e8.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw7.keep e7.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw6.keep e6.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw5.keep e5.agrees (k' := 24) (by omega) (by omega)) (hw4.keep e4.agrees (k' := 24) (by omega) (by omega))))))) (hpa2 ▸ (e3.writes.2.trans ((e1.agrees.trans e2.agrees).read (by simp))))

theorem phase_b [Machine.Bindings] {initial s9 : RamState} (hS : EntryStack initial)
    (hOut : ¬ InProgram (returnBoundary initial).rip) (T9 : Track initial s9)
    (hrip : s9.RIP = 0x10194a) (hsp9 : stackPtr s9 = stackPtr initial - BitVec.ofNat 64 104)
    {K : BitVec 64} (hK9 : rd s9 7 = K) (hKeyB : K.toNat + 32 < 2 ^ 32)
    (hKeySome : ∀ j < 32, (initial.external[K + BitVec.ofNat 64 j]?).isSome)
    (hKeySep : (stackPtr initial).toNat + 8 ≤ K.toNat ∨ K.toNat + 32 ≤ (stackPtr initial).toNat - 1104) :
    ∃ n v, Advances (returnBoundary initial) n s9 v ∧ Track initial v ∧
      v.RIP = 0x101968 ∧ stackPtr v = stackPtr initial - BitVec.ofNat 64 104 ∧
      rd v 0 = memLoad initial.external (K + BitVec.ofNat 64 0) 64 ∧
      wd v (stackPtr initial - BitVec.ofNat 64 32) = memLoad initial.external (K + BitVec.ofNat 64 24) 64 ∧
      wd v (stackPtr initial - BitVec.ofNat 64 40) = memLoad initial.external (K + BitVec.ofNat 64 16) 64 ∧
      wd v (stackPtr initial - BitVec.ofNat 64 48) = memLoad initial.external (K + BitVec.ofNat 64 8) 64 ∧
      rd v 3 = rd s9 3 ∧ rd v 14 = rd s9 14 ∧ rd v 1 = rd s9 1 ∧ rd v 2 = rd s9 2 ∧
      rd v 9 = rd s9 9 ∧ rd v 15 = rd s9 15 ∧
      wd v (stackPtr initial - BitVec.ofNat 64 8) = wd s9 (stackPtr initial - BitVec.ofNat 64 8) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 16) = wd s9 (stackPtr initial - BitVec.ofNat 64 16) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 24) = wd s9 (stackPtr initial - BitVec.ofNat 64 24) := by
  have hKeyOut : ∀ d, d + 8 ≤ 32 → ∀ i < 8,
      ¬ (wrapperFrame initial).Contains (K + BitVec.ofNat 64 d + BitVec.ofNat 64 i).toNat := by
    intro d hd i hi
    have := hS.room
    simp only [wrapperFrame, wrapperFrameBytes, MemoryRegion.Contains, BitVec.toNat_add,
      BitVec.toNat_ofNat]
    omega
  have hw10 : StepWrites initial 0 (movR64M64Effect 0x10194a 0 (.base 7 (.d8 0x18)) s9).components := by
    step_writes []
  obtain ⟨s10, a10, T10, e10⟩ := track_step hS
    (mov_r64_m64_effect_step 0x10194a 0x48 (by unfold RexWPrefix; decide) 0
      (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide))
    T9 (program_text_slice T9.code 0x194a 4 (by decide +kernel))
    ⟨hrip, by rw [rdi_addr hK9 0x18 24 rfl]; exact key_readable T9.grows hKeyB hKeySome 24 (by omega)⟩ (code_ne_boundary hOut 0x194e (by omega)) hw10
  change (movR64M64Effect 0x10194a 0 (.base 7 (.d8 0x18)) s9).Holds s9 s10 at e10
  have hld10 : (Operand.reg 0 : Operand 64).read s10 =
      memLoad initial.external (K + BitVec.ofNat 64 24) 64 := by
    rw [e10.writes]
    change memLoad s9.external _ 64 = _
    rw [rdi_addr hK9 0x18 24 rfl]
    exact load_outside (T9.frame hS) (hKeyOut 24 (by omega))
  have hsp10 := sp_keep e10.agrees (by simp) hsp9
  have hK10 : (Operand.reg 7 : Operand 64).read s10 = K :=
    (e10.agrees.read (by simp)).trans hK9
  have hA11 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x48)).addr s10 x =
      stackPtr initial - BitVec.ofNat 64 32 := rsp_addr hsp10 0x48 72 rfl (by omega)
  have hw11 : StepWrites initial 32 (movM64R64Effect 0x10194e 0 (.sib 4 none 0 (.d8 0x48)) s10).components := by
    step_writes [hA11]
  obtain ⟨s11, a11, T11, e11⟩ := track_step hS
    (mov_m64_r64_effect_step 0x10194e 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide))
    T10 (program_text_slice T10.code 0x194e 5 (by decide +kernel))
    (storePre_slot hS T10.grows e10.rip (hA11 _) (by omega) (by omega)
      (code_inProgram 0x194e 5 (by omega))) (code_ne_boundary hOut 0x1953 (by omega)) hw11
  change (movM64R64Effect 0x10194e 0 (.sib 4 none 0 (.d8 0x48)) s10).Holds s10 s11 at e11
  have hm11 : (Operand.mem (stackPtr initial - BitVec.ofNat 64 32) : Operand 64).read s11 =
      (Operand.reg 0 : Operand 64).read s10 := by
    rw [← hA11 (0x10194e + BitVec.ofNat 64 5)]
    exact e11.writes
  have hsp11 := sp_keep e11.agrees (by simp) hsp10
  have hK11 : (Operand.reg 7 : Operand 64).read s11 = K :=
    (e11.agrees.read (by simp)).trans hK10
  have hw12 : StepWrites initial 0 (movR64M64Effect 0x101953 0 (.base 7 (.d8 0x10)) s11).components := by
    step_writes []
  obtain ⟨s12, a12, T12, e12⟩ := track_step hS
    (mov_r64_m64_effect_step 0x101953 0x48 (by unfold RexWPrefix; decide) 0
      (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide))
    T11 (program_text_slice T11.code 0x1953 4 (by decide +kernel))
    ⟨e11.rip, by rw [rdi_addr hK11 0x10 16 rfl]; exact key_readable T11.grows hKeyB hKeySome 16 (by omega)⟩ (code_ne_boundary hOut 0x1957 (by omega)) hw12
  change (movR64M64Effect 0x101953 0 (.base 7 (.d8 0x10)) s11).Holds s11 s12 at e12
  have hld12 : (Operand.reg 0 : Operand 64).read s12 =
      memLoad initial.external (K + BitVec.ofNat 64 16) 64 := by
    rw [e12.writes]
    change memLoad s11.external _ 64 = _
    rw [rdi_addr hK11 0x10 16 rfl]
    exact load_outside (T11.frame hS) (hKeyOut 16 (by omega))
  have hsp12 := sp_keep e12.agrees (by simp) hsp11
  have hK12 : (Operand.reg 7 : Operand 64).read s12 = K :=
    (e12.agrees.read (by simp)).trans hK11
  have hA13 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x40)).addr s12 x =
      stackPtr initial - BitVec.ofNat 64 40 := rsp_addr hsp12 0x40 64 rfl (by omega)
  have hw13 : StepWrites initial 40 (movM64R64Effect 0x101957 0 (.sib 4 none 0 (.d8 0x40)) s12).components := by
    step_writes [hA13]
  obtain ⟨s13, a13, T13, e13⟩ := track_step hS
    (mov_m64_r64_effect_step 0x101957 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide))
    T12 (program_text_slice T12.code 0x1957 5 (by decide +kernel))
    (storePre_slot hS T12.grows e12.rip (hA13 _) (by omega) (by omega)
      (code_inProgram 0x1957 5 (by omega))) (code_ne_boundary hOut 0x195c (by omega)) hw13
  change (movM64R64Effect 0x101957 0 (.sib 4 none 0 (.d8 0x40)) s12).Holds s12 s13 at e13
  have hm13 : (Operand.mem (stackPtr initial - BitVec.ofNat 64 40) : Operand 64).read s13 =
      (Operand.reg 0 : Operand 64).read s12 := by
    rw [← hA13 (0x101957 + BitVec.ofNat 64 5)]
    exact e13.writes
  have hsp13 := sp_keep e13.agrees (by simp) hsp12
  have hK13 : (Operand.reg 7 : Operand 64).read s13 = K :=
    (e13.agrees.read (by simp)).trans hK12
  have hw14 : StepWrites initial 0 (movR64M64Effect 0x10195c 0 (.base 7 .none) s13).components := by
    step_writes []
  obtain ⟨s14, a14, T14, e14⟩ := track_step hS
    (mov_r64_m64_effect_step 0x10195c 0x48 (by unfold RexWPrefix; decide) 0
      (.base 7 .none) (by decide) (by decide) (by decide))
    T13 (program_text_slice T13.code 0x195c 3 (by decide +kernel))
    ⟨e13.rip, by rw [rdi_addr0 hK13]; exact key_readable T13.grows hKeyB hKeySome 0 (by omega)⟩ (code_ne_boundary hOut 0x195f (by omega)) hw14
  change (movR64M64Effect 0x10195c 0 (.base 7 .none) s13).Holds s13 s14 at e14
  have hld14 : (Operand.reg 0 : Operand 64).read s14 =
      memLoad initial.external (K + BitVec.ofNat 64 0) 64 := by
    rw [e14.writes]
    change memLoad s13.external _ 64 = _
    rw [rdi_addr0 hK13]
    exact load_outside (T13.frame hS) (hKeyOut 0 (by omega))
  have hsp14 := sp_keep e14.agrees (by simp) hsp13
  have hK14 : (Operand.reg 7 : Operand 64).read s14 = K :=
    (e14.agrees.read (by simp)).trans hK13
  have hw15 : StepWrites initial 0 (movR64M64Effect 0x10195f 6 (.base 7 (.d8 0x8)) s14).components := by
    step_writes []
  obtain ⟨s15, a15, T15, e15⟩ := track_step hS
    (mov_r64_m64_effect_step 0x10195f 0x48 (by unfold RexWPrefix; decide) 6
      (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide))
    T14 (program_text_slice T14.code 0x195f 4 (by decide +kernel))
    ⟨e14.rip, by rw [rdi_addr hK14 0x8 8 rfl]; exact key_readable T14.grows hKeyB hKeySome 8 (by omega)⟩ (code_ne_boundary hOut 0x1963 (by omega)) hw15
  change (movR64M64Effect 0x10195f 6 (.base 7 (.d8 0x8)) s14).Holds s14 s15 at e15
  have hld15 : (Operand.reg 6 : Operand 64).read s15 =
      memLoad initial.external (K + BitVec.ofNat 64 8) 64 := by
    rw [e15.writes]
    change memLoad s14.external _ 64 = _
    rw [rdi_addr hK14 0x8 8 rfl]
    exact load_outside (T14.frame hS) (hKeyOut 8 (by omega))
  have hsp15 := sp_keep e15.agrees (by simp) hsp14
  have hK15 : (Operand.reg 7 : Operand 64).read s15 = K :=
    (e15.agrees.read (by simp)).trans hK14
  have hA16 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x38)).addr s15 x =
      stackPtr initial - BitVec.ofNat 64 48 := rsp_addr hsp15 0x38 56 rfl (by omega)
  have hw16 : StepWrites initial 48 (movM64R64Effect 0x101963 6 (.sib 4 none 0 (.d8 0x38)) s15).components := by
    step_writes [hA16]
  obtain ⟨s16, a16, T16, e16⟩ := track_step hS
    (mov_m64_r64_effect_step 0x101963 0x48 (by unfold RexWPrefix; decide) 6
      (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide))
    T15 (program_text_slice T15.code 0x1963 5 (by decide +kernel))
    (storePre_slot hS T15.grows e15.rip (hA16 _) (by omega) (by omega)
      (code_inProgram 0x1963 5 (by omega))) (code_ne_boundary hOut 0x1968 (by omega)) hw16
  change (movM64R64Effect 0x101963 6 (.sib 4 none 0 (.d8 0x38)) s15).Holds s15 s16 at e16
  have hm16 : (Operand.mem (stackPtr initial - BitVec.ofNat 64 48) : Operand 64).read s16 =
      (Operand.reg 6 : Operand 64).read s15 := by
    rw [← hA16 (0x101963 + BitVec.ofNat 64 5)]
    exact e16.writes
  have hsp16 := sp_keep e16.agrees (by simp) hsp15
  have hK16 : (Operand.reg 7 : Operand 64).read s16 = K :=
    (e16.agrees.read (by simp)).trans hK15
  refine ⟨_, s16, ((((((a10.trans a11).trans a12).trans a13).trans a14).trans a15).trans a16), T16, e16.rip, hsp16, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((e15.agrees.trans e16.agrees).read (by simp)).trans hld14
  · exact Eq.trans (Eq.trans (hw16.keep e16.agrees (k' := 32) (by omega) (by omega)) (Eq.trans (hw15.keep e15.agrees (k' := 32) (by omega) (by omega)) (Eq.trans (hw14.keep e14.agrees (k' := 32) (by omega) (by omega)) (Eq.trans (hw13.keep e13.agrees (k' := 32) (by omega) (by omega)) (hw12.keep e12.agrees (k' := 32) (by omega) (by omega)))))) (hm11.trans hld10)
  · exact Eq.trans (Eq.trans (hw16.keep e16.agrees (k' := 40) (by omega) (by omega)) (Eq.trans (hw15.keep e15.agrees (k' := 40) (by omega) (by omega)) (hw14.keep e14.agrees (k' := 40) (by omega) (by omega)))) (hm13.trans hld12)
  · exact hm16.trans hld15
  · exact ((((((e10.agrees.trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).read (by simp)
  · exact ((((((e10.agrees.trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).read (by simp)
  · exact ((((((e10.agrees.trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).read (by simp)
  · exact ((((((e10.agrees.trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).read (by simp)
  · exact ((((((e10.agrees.trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).read (by simp)
  · exact ((((((e10.agrees.trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).read (by simp)
  · exact (Eq.trans (hw16.keep e16.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw15.keep e15.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw14.keep e14.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw13.keep e13.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw12.keep e12.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw11.keep e11.agrees (k' := 8) (by omega) (by omega)) (hw10.keep e10.agrees (k' := 8) (by omega) (by omega))))))))
  · exact (Eq.trans (hw16.keep e16.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw15.keep e15.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw14.keep e14.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw13.keep e13.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw12.keep e12.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw11.keep e11.agrees (k' := 16) (by omega) (by omega)) (hw10.keep e10.agrees (k' := 16) (by omega) (by omega))))))))
  · exact (Eq.trans (hw16.keep e16.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw15.keep e15.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw14.keep e14.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw13.keep e13.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw12.keep e12.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw11.keep e11.agrees (k' := 24) (by omega) (by omega)) (hw10.keep e10.agrees (k' := 24) (by omega) (by omega))))))))

theorem phase_c [Machine.Bindings] {initial s16 : RamState} (hS : EntryStack initial)
    (hOut : ¬ InProgram (returnBoundary initial).rip) (T16 : Track initial s16)
    (hrip : s16.RIP = 0x101968) (hsp16 : stackPtr s16 = stackPtr initial - BitVec.ofNat 64 104)
    (hle : (rd s16 9).toNat ≤ (rd s16 15).toNat) :
    ∃ n v, Advances (returnBoundary initial) n s16 v ∧ Track initial v ∧
      v.RIP = 0x10198d ∧ stackPtr v = stackPtr initial - BitVec.ofNat 64 104 ∧
      wd v (stackPtr initial - BitVec.ofNat 64 56) = rd s16 0 ∧
      wd v (stackPtr initial - BitVec.ofNat 64 104) = rd s16 14 ∧
      wd v (stackPtr initial - BitVec.ofNat 64 96) = rd s16 14 ∧
      wd v (stackPtr initial - BitVec.ofNat 64 88) = rd s16 9 ∧
      rd v 3 = rd s16 3 ∧ rd v 14 = rd s16 14 ∧ rd v 1 = rd s16 1 ∧ rd v 2 = rd s16 2 ∧
      rd v 15 = rd s16 15 ∧
      wd v (stackPtr initial - BitVec.ofNat 64 8) = wd s16 (stackPtr initial - BitVec.ofNat 64 8) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 16) = wd s16 (stackPtr initial - BitVec.ofNat 64 16) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 24) = wd s16 (stackPtr initial - BitVec.ofNat 64 24) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 32) = wd s16 (stackPtr initial - BitVec.ofNat 64 32) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 40) = wd s16 (stackPtr initial - BitVec.ofNat 64 40) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 48) = wd s16 (stackPtr initial - BitVec.ofNat 64 48) := by
  have hw17 : StepWrites initial 0 (xorR32R32Effect 0x101968 2 6 6 s16).components := by
    step_writes []
  obtain ⟨s17, a17, T17, e17⟩ := track_step hS
    (xor_r32_r32_effect_step 0x101968 0xf6 (by decide))
    T16 (program_text_slice T16.code 0x1968 2 (by decide +kernel))
    hrip (code_ne_boundary hOut 0x196a (by omega)) hw17
  change (xorR32R32Effect 0x101968 2 6 6 s16).Holds s16 s17 at e17
  have hsp17 := sp_keep e17.agrees (by simp) hsp16
  have hw18 : StepWrites initial 0 (cmpR64R64Effect 0x10196a 9 15 s17).components := by
    step_writes []
  obtain ⟨s18, a18, T18, e18⟩ := track_step hS
    (cmp_r64_r64_effect_step 0x10196a 0x4d 0xf9 (by unfold RexWPrefix; decide) (by decide))
    T17 (program_text_slice T17.code 0x196a 3 (by decide +kernel))
    e17.rip (code_ne_boundary hOut 0x196d (by omega)) hw18
  change (cmpR64R64Effect 0x10196a 9 15 s17).Holds s17 s18 at e18
  have hsp18 := sp_keep e18.agrees (by simp) hsp17
  have hbe18 : condHolds 6 (StatusFlags.ofRFLAGS s18.RFLAGS) = true := by
    have hf := e18.flags
    simp only [Effect.FlagsHold, cmpR64R64Effect] at hf
    rw [e17.agrees.read (by simp), e17.agrees.read (r := 15) (by simp)] at hf
    exact be_holds hf hle
  have hw19 : StepWrites initial 0 (cmovR64R64Effect 0x10196d 4 6 9 true s18).components := by
    step_writes []
  obtain ⟨s19, a19, T19, e19⟩ := track_step hS
    (cmov_r64_r64_effect_step 0x10196d 6 0x49 (by unfold RexWPrefix; decide) 0xf1 (by decide)
      true)
    T18 (program_text_slice T18.code 0x196d 4 (by decide +kernel))
    ⟨e18.rip, hbe18⟩ (code_ne_boundary hOut 0x1971 (by omega)) hw19
  change (cmovR64R64Effect 0x10196d 4 6 9 true s18).Holds s18 s19 at e19
  have hsp19 := sp_keep e19.agrees (by simp) hsp18
  have hw20 : StepWrites initial 0 (movR32Imm32Effect 0x101971 5 7 1 s19).components := by
    step_writes []
  obtain ⟨s20, a20, T20, e20⟩ := track_step hS
    (mov_r32_imm32_effect_step 0x101971 0xbf (by decide) 1)
    T19 (program_text_slice T19.code 0x1971 5 (by decide +kernel))
    e19.rip (code_ne_boundary hOut 0x1976 (by omega)) hw20
  change (movR32Imm32Effect 0x101971 5 7 1 s19).Holds s19 s20 at e20
  have hsp20 := sp_keep e20.agrees (by simp) hsp19
  have hbe20 : condHolds 6 (StatusFlags.ofRFLAGS s20.RFLAGS) = true := by
    rw [flags_keep e20.agrees (by simp), flags_keep e19.agrees (by simp)]
    exact hbe18
  have hw21 : StepWrites initial 0 (cmovR64R64Effect 0x101976 4 7 14 true s20).components := by
    step_writes []
  obtain ⟨s21, a21, T21, e21⟩ := track_step hS
    (cmov_r64_r64_effect_step 0x101976 6 0x49 (by unfold RexWPrefix; decide) 0xfe (by decide)
      true)
    T20 (program_text_slice T20.code 0x1976 4 (by decide +kernel))
    ⟨e20.rip, hbe20⟩ (code_ne_boundary hOut 0x197a (by omega)) hw21
  change (cmovR64R64Effect 0x101976 4 7 14 true s20).Holds s20 s21 at e21
  have hsp21 := sp_keep e21.agrees (by simp) hsp20
  have hA22 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x30)).addr s21 x =
      stackPtr initial - BitVec.ofNat 64 56 := rsp_addr hsp21 0x30 48 rfl (by omega)
  have hw22 : StepWrites initial 56 (movM64R64Effect 0x10197a 0 (.sib 4 none 0 (.d8 0x30)) s21).components := by
    step_writes [hA22]
  obtain ⟨s22, a22, T22, e22⟩ := track_step hS
    (mov_m64_r64_effect_step 0x10197a 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide))
    T21 (program_text_slice T21.code 0x197a 5 (by decide +kernel))
    (storePre_slot hS T21.grows e21.rip (hA22 _) (by omega) (by omega)
      (code_inProgram 0x197a 5 (by omega))) (code_ne_boundary hOut 0x197f (by omega)) hw22
  change (movM64R64Effect 0x10197a 0 (.sib 4 none 0 (.d8 0x30)) s21).Holds s21 s22 at e22
  have hm22 : (Operand.mem (stackPtr initial - BitVec.ofNat 64 56) : Operand 64).read s22 =
      (Operand.reg 0 : Operand 64).read s21 := by
    rw [← hA22 (0x10197a + BitVec.ofNat 64 5)]
    exact e22.writes
  have hsp22 := sp_keep e22.agrees (by simp) hsp21
  have hA23 : ∀ x, (AddrMode.sib 4 none 0 .none).addr s22 x =
      stackPtr initial - BitVec.ofNat 64 104 := rsp_addr0 hsp22
  have hw23 : StepWrites initial 104 (movM64R64Effect 0x10197f 7 (.sib 4 none 0 .none) s22).components := by
    step_writes [hA23]
  obtain ⟨s23, a23, T23, e23⟩ := track_step hS
    (mov_m64_r64_effect_step 0x10197f 0x48 (by unfold RexWPrefix; decide) 7
      (.sib 4 none 0 .none) (by decide) (by decide) (by decide))
    T22 (program_text_slice T22.code 0x197f 4 (by decide +kernel))
    (storePre_slot hS T22.grows e22.rip (hA23 _) (by omega) (by omega)
      (code_inProgram 0x197f 4 (by omega))) (code_ne_boundary hOut 0x1983 (by omega)) hw23
  change (movM64R64Effect 0x10197f 7 (.sib 4 none 0 .none) s22).Holds s22 s23 at e23
  have hm23 : (Operand.mem (stackPtr initial - BitVec.ofNat 64 104) : Operand 64).read s23 =
      (Operand.reg 7 : Operand 64).read s22 := by
    rw [← hA23 (0x10197f + BitVec.ofNat 64 4)]
    exact e23.writes
  have hsp23 := sp_keep e23.agrees (by simp) hsp22
  have hA24 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x8)).addr s23 x =
      stackPtr initial - BitVec.ofNat 64 96 := rsp_addr hsp23 0x8 8 rfl (by omega)
  have hw24 : StepWrites initial 96 (movM64R64Effect 0x101983 7 (.sib 4 none 0 (.d8 0x8)) s23).components := by
    step_writes [hA24]
  obtain ⟨s24, a24, T24, e24⟩ := track_step hS
    (mov_m64_r64_effect_step 0x101983 0x48 (by unfold RexWPrefix; decide) 7
      (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide))
    T23 (program_text_slice T23.code 0x1983 5 (by decide +kernel))
    (storePre_slot hS T23.grows e23.rip (hA24 _) (by omega) (by omega)
      (code_inProgram 0x1983 5 (by omega))) (code_ne_boundary hOut 0x1988 (by omega)) hw24
  change (movM64R64Effect 0x101983 7 (.sib 4 none 0 (.d8 0x8)) s23).Holds s23 s24 at e24
  have hm24 : (Operand.mem (stackPtr initial - BitVec.ofNat 64 96) : Operand 64).read s24 =
      (Operand.reg 7 : Operand 64).read s23 := by
    rw [← hA24 (0x101983 + BitVec.ofNat 64 5)]
    exact e24.writes
  have hsp24 := sp_keep e24.agrees (by simp) hsp23
  have hA25 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x10)).addr s24 x =
      stackPtr initial - BitVec.ofNat 64 88 := rsp_addr hsp24 0x10 16 rfl (by omega)
  have hw25 : StepWrites initial 88 (movM64R64Effect 0x101988 6 (.sib 4 none 0 (.d8 0x10)) s24).components := by
    step_writes [hA25]
  obtain ⟨s25, a25, T25, e25⟩ := track_step hS
    (mov_m64_r64_effect_step 0x101988 0x48 (by unfold RexWPrefix; decide) 6
      (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide))
    T24 (program_text_slice T24.code 0x1988 5 (by decide +kernel))
    (storePre_slot hS T24.grows e24.rip (hA25 _) (by omega) (by omega)
      (code_inProgram 0x1988 5 (by omega))) (code_ne_boundary hOut 0x198d (by omega)) hw25
  change (movM64R64Effect 0x101988 6 (.sib 4 none 0 (.d8 0x10)) s24).Holds s24 s25 at e25
  have hm25 : (Operand.mem (stackPtr initial - BitVec.ofNat 64 88) : Operand 64).read s25 =
      (Operand.reg 6 : Operand 64).read s24 := by
    rw [← hA25 (0x101988 + BitVec.ofNat 64 5)]
    exact e25.writes
  have hsp25 := sp_keep e25.agrees (by simp) hsp24
  have hrdi21 : rd s21 7 = rd s16 14 := by
    show (Operand.reg 7 : Operand 64).read s21 = (Operand.reg 14 : Operand 64).read s16
    rw [e21.writes]
    exact ((((e17.agrees.trans e18.agrees).trans e19.agrees).trans e20.agrees).read (by simp))
  have hrsi19 : rd s19 6 = rd s16 9 := by
    show (Operand.reg 6 : Operand 64).read s19 = (Operand.reg 9 : Operand 64).read s16
    rw [e19.writes]
    exact ((e17.agrees.trans e18.agrees).read (by simp))
  refine ⟨_, s25, ((((((((a17.trans a18).trans a19).trans a20).trans a21).trans a22).trans a23).trans a24).trans a25), T25, e25.rip, hsp25, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Eq.trans (Eq.trans (hw25.keep e25.agrees (k' := 56) (by omega) (by omega)) (Eq.trans (hw24.keep e24.agrees (k' := 56) (by omega) (by omega)) (hw23.keep e23.agrees (k' := 56) (by omega) (by omega)))) (hm22.trans (((((e17.agrees.trans e18.agrees).trans e19.agrees).trans e20.agrees).trans e21.agrees).read (by simp)))
  · exact Eq.trans (Eq.trans (hw25.keep e25.agrees (k' := 104) (by omega) (by omega)) (hw24.keep e24.agrees (k' := 104) (by omega) (by omega))) (hm23.trans ((e22.agrees.read (by simp)).trans hrdi21))
  · exact Eq.trans (hw25.keep e25.agrees (k' := 96) (by omega) (by omega)) (hm24.trans ((e22.agrees.trans e23.agrees).read (by simp) |>.trans hrdi21))
  · exact hm25.trans ((((((e20.agrees.trans e21.agrees).trans e22.agrees).trans e23.agrees).trans e24.agrees).read (by simp)).trans hrsi19)
  · exact ((((((((e17.agrees.trans e18.agrees).trans e19.agrees).trans e20.agrees).trans e21.agrees).trans e22.agrees).trans e23.agrees).trans e24.agrees).trans e25.agrees).read (by simp)
  · exact ((((((((e17.agrees.trans e18.agrees).trans e19.agrees).trans e20.agrees).trans e21.agrees).trans e22.agrees).trans e23.agrees).trans e24.agrees).trans e25.agrees).read (by simp)
  · exact ((((((((e17.agrees.trans e18.agrees).trans e19.agrees).trans e20.agrees).trans e21.agrees).trans e22.agrees).trans e23.agrees).trans e24.agrees).trans e25.agrees).read (by simp)
  · exact ((((((((e17.agrees.trans e18.agrees).trans e19.agrees).trans e20.agrees).trans e21.agrees).trans e22.agrees).trans e23.agrees).trans e24.agrees).trans e25.agrees).read (by simp)
  · exact ((((((((e17.agrees.trans e18.agrees).trans e19.agrees).trans e20.agrees).trans e21.agrees).trans e22.agrees).trans e23.agrees).trans e24.agrees).trans e25.agrees).read (by simp)
  · exact (Eq.trans (hw25.keep e25.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw24.keep e24.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw23.keep e23.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw22.keep e22.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw21.keep e21.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw20.keep e20.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw19.keep e19.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw18.keep e18.agrees (k' := 8) (by omega) (by omega)) (hw17.keep e17.agrees (k' := 8) (by omega) (by omega))))))))))
  · exact (Eq.trans (hw25.keep e25.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw24.keep e24.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw23.keep e23.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw22.keep e22.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw21.keep e21.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw20.keep e20.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw19.keep e19.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw18.keep e18.agrees (k' := 16) (by omega) (by omega)) (hw17.keep e17.agrees (k' := 16) (by omega) (by omega))))))))))
  · exact (Eq.trans (hw25.keep e25.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw24.keep e24.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw23.keep e23.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw22.keep e22.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw21.keep e21.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw20.keep e20.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw19.keep e19.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw18.keep e18.agrees (k' := 24) (by omega) (by omega)) (hw17.keep e17.agrees (k' := 24) (by omega) (by omega))))))))))
  · exact (Eq.trans (hw25.keep e25.agrees (k' := 32) (by omega) (by omega)) (Eq.trans (hw24.keep e24.agrees (k' := 32) (by omega) (by omega)) (Eq.trans (hw23.keep e23.agrees (k' := 32) (by omega) (by omega)) (Eq.trans (hw22.keep e22.agrees (k' := 32) (by omega) (by omega)) (Eq.trans (hw21.keep e21.agrees (k' := 32) (by omega) (by omega)) (Eq.trans (hw20.keep e20.agrees (k' := 32) (by omega) (by omega)) (Eq.trans (hw19.keep e19.agrees (k' := 32) (by omega) (by omega)) (Eq.trans (hw18.keep e18.agrees (k' := 32) (by omega) (by omega)) (hw17.keep e17.agrees (k' := 32) (by omega) (by omega))))))))))
  · exact (Eq.trans (hw25.keep e25.agrees (k' := 40) (by omega) (by omega)) (Eq.trans (hw24.keep e24.agrees (k' := 40) (by omega) (by omega)) (Eq.trans (hw23.keep e23.agrees (k' := 40) (by omega) (by omega)) (Eq.trans (hw22.keep e22.agrees (k' := 40) (by omega) (by omega)) (Eq.trans (hw21.keep e21.agrees (k' := 40) (by omega) (by omega)) (Eq.trans (hw20.keep e20.agrees (k' := 40) (by omega) (by omega)) (Eq.trans (hw19.keep e19.agrees (k' := 40) (by omega) (by omega)) (Eq.trans (hw18.keep e18.agrees (k' := 40) (by omega) (by omega)) (hw17.keep e17.agrees (k' := 40) (by omega) (by omega))))))))))
  · exact (Eq.trans (hw25.keep e25.agrees (k' := 48) (by omega) (by omega)) (Eq.trans (hw24.keep e24.agrees (k' := 48) (by omega) (by omega)) (Eq.trans (hw23.keep e23.agrees (k' := 48) (by omega) (by omega)) (Eq.trans (hw22.keep e22.agrees (k' := 48) (by omega) (by omega)) (Eq.trans (hw21.keep e21.agrees (k' := 48) (by omega) (by omega)) (Eq.trans (hw20.keep e20.agrees (k' := 48) (by omega) (by omega)) (Eq.trans (hw19.keep e19.agrees (k' := 48) (by omega) (by omega)) (Eq.trans (hw18.keep e18.agrees (k' := 48) (by omega) (by omega)) (hw17.keep e17.agrees (k' := 48) (by omega) (by omega))))))))))

theorem phase_d [Machine.Bindings] {initial s25 : RamState} (hS : EntryStack initial)
    (hOut : ¬ InProgram (returnBoundary initial).rip) (T25 : Track initial s25)
    (hrip : s25.RIP = 0x10198d) (hsp25 : stackPtr s25 = stackPtr initial - BitVec.ofNat 64 104) :
    ∃ n v, Advances (returnBoundary initial) n s25 v ∧ Track initial v ∧
      v.RIP = 0x100650 ∧ stackPtr v = stackPtr initial - BitVec.ofNat 64 112 ∧
      rd v 7 = stackPtr initial - BitVec.ofNat 64 73 ∧ rd v 6 = stackPtr initial - BitVec.ofNat 64 56 ∧
      rd v 9 = stackPtr initial - BitVec.ofNat 64 104 ∧
      wd v (stackPtr initial - BitVec.ofNat 64 112) = 0x10199f ∧
      rd v 3 = rd s25 3 ∧ rd v 14 = rd s25 14 ∧ rd v 1 = rd s25 1 ∧ rd v 2 = rd s25 2 ∧
      rd v 15 = rd s25 15 ∧
      wd v (stackPtr initial - BitVec.ofNat 64 8) = wd s25 (stackPtr initial - BitVec.ofNat 64 8) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 16) = wd s25 (stackPtr initial - BitVec.ofNat 64 16) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 24) = wd s25 (stackPtr initial - BitVec.ofNat 64 24) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 32) = wd s25 (stackPtr initial - BitVec.ofNat 64 32) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 40) = wd s25 (stackPtr initial - BitVec.ofNat 64 40) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 48) = wd s25 (stackPtr initial - BitVec.ofNat 64 48) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 56) = wd s25 (stackPtr initial - BitVec.ofNat 64 56) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 88) = wd s25 (stackPtr initial - BitVec.ofNat 64 88) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 96) = wd s25 (stackPtr initial - BitVec.ofNat 64 96) ∧
      wd v (stackPtr initial - BitVec.ofNat 64 104) = wd s25 (stackPtr initial - BitVec.ofNat 64 104) := by
  have hw26 : StepWrites initial 0 (leaR64Effect 0x10198d 7 (.sib 4 none 0 (.d8 0x1f)) s25).components := by
    step_writes []
  obtain ⟨s26, a26, T26, e26⟩ := track_step hS
    (lea_r64_effect_step 0x10198d 0x48 (by unfold RexWPrefix; decide) 7
      (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide))
    T25 (program_text_slice T25.code 0x198d 5 (by decide +kernel))
    hrip (code_ne_boundary hOut 0x1992 (by omega)) hw26
  change (leaR64Effect 0x10198d 7 (.sib 4 none 0 (.d8 0x1f)) s25).Holds s25 s26 at e26
  have hsp26 := sp_keep e26.agrees (by simp) hsp25
  have hw27 : StepWrites initial 0 (leaR64Effect 0x101992 6 (.sib 4 none 0 (.d8 0x30)) s26).components := by
    step_writes []
  obtain ⟨s27, a27, T27, e27⟩ := track_step hS
    (lea_r64_effect_step 0x101992 0x48 (by unfold RexWPrefix; decide) 6
      (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide))
    T26 (program_text_slice T26.code 0x1992 5 (by decide +kernel))
    e26.rip (code_ne_boundary hOut 0x1997 (by omega)) hw27
  change (leaR64Effect 0x101992 6 (.sib 4 none 0 (.d8 0x30)) s26).Holds s26 s27 at e27
  have hsp27 := sp_keep e27.agrees (by simp) hsp26
  have hw28 : StepWrites initial 0 (movR64R64Effect 0x101997 9 4 s27).components := by
    step_writes []
  obtain ⟨s28, a28, T28, e28⟩ := track_step hS
    (mov_r64_r64_effect_step 0x101997 0x49 0xe1 (by unfold RexWPrefix; decide) (by decide))
    T27 (program_text_slice T27.code 0x1997 3 (by decide +kernel))
    e27.rip (code_ne_boundary hOut 0x199a (by omega)) hw28
  change (movR64R64Effect 0x101997 9 4 s27).Holds s27 s28 at e28
  have hsp28 := sp_keep e28.agrees (by simp) hsp27
  have hpa28 : pushAddr s28 = stackPtr initial - BitVec.ofNat 64 112 := by
    rw [pushAddr, hsp28]; bv_omega
  have hw29 : StepWrites initial 112 (callEffect (fun _ => branchTarget 0x10199a 5 ((0xffffecb1 : BitVec 32).signExtend 64))
      (0x10199a + BitVec.ofNat 64 5) s28).components := by
    step_writes [callEffect, hpa28]
  obtain ⟨s29, a29, T29, e29⟩ := track_step hS
    (call_rel32_effect_step 0x10199a 0xffffecb1 (by decide))
    T28 (program_text_slice T28.code 0x199a 5 (by decide +kernel))
    (storePre_slot hS T28.grows e28.rip hpa28 (by omega) (by omega)
      (code_inProgram 0x199a 5 (by omega))) (code_ne_boundary hOut 0x650 (by omega)) hw29
  change (callEffect (fun _ => branchTarget 0x10199a 5 ((0xffffecb1 : BitVec 32).signExtend 64))
      (0x10199a + BitVec.ofNat 64 5) s28).Holds s28 s29 at e29
  refine ⟨_, s29, (((a26.trans a27).trans a28).trans a29), T29, e29.rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (show stackPtr s29 = pushAddr s28 from e29.writes.1).trans hpa28
  · show (Operand.reg 7 : Operand 64).read s29 = _
    rw [((e27.agrees.trans e28.agrees).trans e29.agrees).read (by simp), e26.writes]
    exact rsp_addr hsp25 0x1f 31 rfl (by omega) (0x10198d + BitVec.ofNat 64 5)
  · show (Operand.reg 6 : Operand 64).read s29 = _
    rw [(e28.agrees.trans e29.agrees).read (by simp), e27.writes]
    exact rsp_addr hsp26 0x30 48 rfl (by omega) (0x101992 + BitVec.ofNat 64 5)
  · show (Operand.reg 9 : Operand 64).read s29 = _
    rw [e29.agrees.read (by simp), e28.writes, ← stackPtr_eq_read, hsp27]
  · exact (show wd s29 (pushAddr s28) = 0x10199f from e29.writes.2) ▸ hpa28 ▸ rfl
  · exact (((e26.agrees.trans e27.agrees).trans e28.agrees).trans e29.agrees).read (by simp)
  · exact (((e26.agrees.trans e27.agrees).trans e28.agrees).trans e29.agrees).read (by simp)
  · exact (((e26.agrees.trans e27.agrees).trans e28.agrees).trans e29.agrees).read (by simp)
  · exact (((e26.agrees.trans e27.agrees).trans e28.agrees).trans e29.agrees).read (by simp)
  · exact (((e26.agrees.trans e27.agrees).trans e28.agrees).trans e29.agrees).read (by simp)
  · exact (Eq.trans (hw29.keep e29.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw28.keep e28.agrees (k' := 8) (by omega) (by omega)) (Eq.trans (hw27.keep e27.agrees (k' := 8) (by omega) (by omega)) (hw26.keep e26.agrees (k' := 8) (by omega) (by omega)))))
  · exact (Eq.trans (hw29.keep e29.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw28.keep e28.agrees (k' := 16) (by omega) (by omega)) (Eq.trans (hw27.keep e27.agrees (k' := 16) (by omega) (by omega)) (hw26.keep e26.agrees (k' := 16) (by omega) (by omega)))))
  · exact (Eq.trans (hw29.keep e29.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw28.keep e28.agrees (k' := 24) (by omega) (by omega)) (Eq.trans (hw27.keep e27.agrees (k' := 24) (by omega) (by omega)) (hw26.keep e26.agrees (k' := 24) (by omega) (by omega)))))
  · exact (Eq.trans (hw29.keep e29.agrees (k' := 32) (by omega) (by omega)) (Eq.trans (hw28.keep e28.agrees (k' := 32) (by omega) (by omega)) (Eq.trans (hw27.keep e27.agrees (k' := 32) (by omega) (by omega)) (hw26.keep e26.agrees (k' := 32) (by omega) (by omega)))))
  · exact (Eq.trans (hw29.keep e29.agrees (k' := 40) (by omega) (by omega)) (Eq.trans (hw28.keep e28.agrees (k' := 40) (by omega) (by omega)) (Eq.trans (hw27.keep e27.agrees (k' := 40) (by omega) (by omega)) (hw26.keep e26.agrees (k' := 40) (by omega) (by omega)))))
  · exact (Eq.trans (hw29.keep e29.agrees (k' := 48) (by omega) (by omega)) (Eq.trans (hw28.keep e28.agrees (k' := 48) (by omega) (by omega)) (Eq.trans (hw27.keep e27.agrees (k' := 48) (by omega) (by omega)) (hw26.keep e26.agrees (k' := 48) (by omega) (by omega)))))
  · exact (Eq.trans (hw29.keep e29.agrees (k' := 56) (by omega) (by omega)) (Eq.trans (hw28.keep e28.agrees (k' := 56) (by omega) (by omega)) (Eq.trans (hw27.keep e27.agrees (k' := 56) (by omega) (by omega)) (hw26.keep e26.agrees (k' := 56) (by omega) (by omega)))))
  · exact (Eq.trans (hw29.keep e29.agrees (k' := 88) (by omega) (by omega)) (Eq.trans (hw28.keep e28.agrees (k' := 88) (by omega) (by omega)) (Eq.trans (hw27.keep e27.agrees (k' := 88) (by omega) (by omega)) (hw26.keep e26.agrees (k' := 88) (by omega) (by omega)))))
  · exact (Eq.trans (hw29.keep e29.agrees (k' := 96) (by omega) (by omega)) (Eq.trans (hw28.keep e28.agrees (k' := 96) (by omega) (by omega)) (Eq.trans (hw27.keep e27.agrees (k' := 96) (by omega) (by omega)) (hw26.keep e26.agrees (k' := 96) (by omega) (by omega)))))
  · exact (Eq.trans (hw29.keep e29.agrees (k' := 104) (by omega) (by omega)) (Eq.trans (hw28.keep e28.agrees (k' := 104) (by omega) (by omega)) (Eq.trans (hw27.keep e27.agrees (k' := 104) (by omega) (by omega)) (hw26.keep e26.agrees (k' := 104) (by omega) (by omega)))))

theorem word64At_of_memLoad {m : Ram} {a v : BitVec 64}
    (hsome : ∀ i < 8, (m[a + BitVec.ofNat 64 i]?).isSome) (hv : memLoad m a 64 = v)
    {start : Nat} (ha : BitVec.ofNat 64 start = a) :
    (⟨start, 8⟩ : MemoryRegion).Word64At m v :=
  ⟨rfl, by rw [ha, ← hv]; exact (Bytes.of_memLoad (n := 64) hsome).loadBytes64⟩

theorem copied_byte {m mi : Ram} {a src : BitVec 64}
    (hsome : ∀ o < 8, (m[a + BitVec.ofNat 64 o]?).isSome)
    (hv : memLoad m a 64 = memLoad mi src 64) {o : Nat} (ho : o < 8) {b : UInt8}
    (hb : mi[src + BitVec.ofNat 64 o]? = some b) : m[a + BitVec.ofNat 64 o]? = some b := by
  rw [Bytes.of_memLoad (n := 64) hsome o ho, hv, storedByte_memLoad _ _ _ (by omega)]
  simp only [memByte]
  change some ((mi[src + BitVec.ofNat 64 o]?).getD 0) = some b
  rw [hb]
  rfl

theorem disjoint_of_sep {a b : MemoryRegion}
    (h : a.start + a.size ≤ b.start ∨ b.start + b.size ≤ a.start) : a.Disjoint b :=
  fun _ h1 h2 => by simp only [MemoryRegion.Contains] at h1 h2; omega

theorem disjoint_mono {a b a' b' : MemoryRegion} (h : a.Disjoint b)
    (ha : ∀ x, a'.Contains x → a.Contains x) (hb : ∀ x, b'.Contains x → b.Contains x) :
    a'.Disjoint b' :=
  fun x h1 h2 => h x (ha x h1) (hb x h2)

theorem avoids_mono {a a' : MemoryRegion} {f : BitVec 64 → Prop} (h : a.Avoids f)
    (ha : ∀ x, a'.Contains x → a.Contains x) : a'.Avoids f :=
  fun x hx => h x (ha x.toNat hx)

theorem input_kept {initial s : RamState} (hS : EntryStack initial)
    (hF : MemoryWriteFrame initial s #v[wrapperFrame initial]) {region : MemoryRegion}
    {bytes : ByteArray} (hsep : (⟨(stackPtr initial).toNat - 1104, 1112⟩ : MemoryRegion).Disjoint region)
    (h : ValidInput initial region bytes) : ValidInput s region bytes := by
  refine ⟨h.1, h.2.1, fun i => ?_⟩
  have hb := h.1
  have hl := h.2.1
  simp only [MemoryRegion.Bounded, userAddressLimit, MemoryRegion.HasLength] at hb hl
  have hi := i.isLt
  rw [hF _ ?_]
  · exact h.2.2 i
  intro r hr hc
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  have hn : (BitVec.ofNat 64 (region.start + i.val)).toNat = region.start + i.val := by
    rw [BitVec.toNat_ofNat]; omega
  rw [hn] at hc
  simp only [wrapperFrame, wrapperFrameBytes, MemoryRegion.Contains] at hc
  have := hS.room
  exact hsep (region.start + i.val) ⟨by simp only; omega, by simp only; omega⟩
    ⟨by omega, by omega⟩

theorem allocated_kept {initial s : RamState} (hg : Grows initial s) {region : MemoryRegion}
    (h : region.Allocated initial.external) : region.Allocated s.external := by
  intro a ha
  obtain ⟨b, hb⟩ := h a ha
  exact Option.isSome_iff_exists.mp (hg a (by simp [hb]))

theorem stack_allocated {initial s : RamState} (hS : EntryStack initial) (hg : Grows initial s)
    {region : MemoryRegion} (h1 : (stackPtr initial).toNat - 1104 ≤ region.start)
    (h2 : region.start + region.size ≤ (stackPtr initial).toNat + 8) :
    region.Allocated s.external := by
  intro a ha
  exact Option.isSome_iff_exists.mp (hg a (hS.allocated a (by simp only [MemoryRegion.Contains] at ha; omega)
    (by simp only [MemoryRegion.Contains] at ha; omega)))

theorem stack_region_eq (s : RamState) (n : Nat) (h : n ≤ (stackPtr s).toNat) :
    Stack.region s n = ⟨(stackPtr s).toNat - n, n + 8⟩ := by
  simp only [Stack.region, Stack.returnAddressBytes]
  rw [show s.regValue .rsp = stackPtr s from rfl]
  congr 1
  omega

theorem entry_sep {initial : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData plaintext : ByteArray}
    (hCall : ValidCall encryptInPlace initial [key, nonce, associatedData, plaintext])
    (hS : EntryStack initial) {cap : BitVec 64}
    (hcapW : (stackArgumentSlot initial 0).Word64At initial.external cap) :
    let St : MemoryRegion := ⟨(stackPtr initial).toNat - 1104, 1112⟩
    let Buf : MemoryRegion := ⟨(initial.regValue .rcx).toNat, cap.toNat⟩
    St.Disjoint ⟨(initial.regValue .rdi).toNat, 32⟩ ∧
    St.Disjoint ⟨(initial.regValue .rsi).toNat, 12⟩ ∧
    St.Disjoint ⟨(initial.regValue .rdx).toNat, associatedData.size⟩ ∧
    Buf.Disjoint St ∧
    Buf.Disjoint ⟨(initial.regValue .rsi).toNat, 12⟩ ∧
    Buf.Disjoint ⟨(initial.regValue .rdx).toNat, associatedData.size⟩ ∧
    St.Avoids (fun a => InProgram a ∨ pageTables.Contains a.toNat) ∧
    Buf.Avoids (fun a => InProgram a ∨ pageTables.Contains a.toNat) := by
  intro St Buf
  have hSt : Stack.region initial 1104 = St := by
    rw [stack_region_eq _ _ hS.room]
  have hBuf : bufferRegion encryptInPlace initial = Buf := by
    simp only [bufferRegion, bufferBytes, encryptInPlace, argumentValue, hcapW.2, registerRegion]
    rfl
  have hW : ∀ r, r ∈ writtenRegions encryptInPlace initial
      [key, nonce, associatedData, plaintext] ↔ r = Buf ∨ r = St := by
    intro r
    simp [writtenRegions, encryptInPlace, Routine.needsOutput, hSt.symm, hBuf.symm]
  have hR : ∀ r, r = ⟨(initial.regValue .rdi).toNat, 32⟩ ∨
      r = ⟨(initial.regValue .rsi).toNat, 12⟩ ∨
      r = ⟨(initial.regValue .rdx).toNat, associatedData.size⟩ →
      r ∈ readRegions encryptInPlace initial [key, nonce, associatedData, plaintext] := by
    intro r hr
    simp only [readRegions, encryptInPlace, inputRegion, registerRegion]
    rcases hr with rfl | rfl | rfl <;> simp
  have hsep := hCall.separation
  refine ⟨hsep.2.1 St ((hW St).2 (.inr rfl)) _ (hR _ (.inl rfl)),
    hsep.2.1 St ((hW St).2 (.inr rfl)) _ (hR _ (.inr (.inl rfl))),
    hsep.2.1 St ((hW St).2 (.inr rfl)) _ (hR _ (.inr (.inr rfl))), ?_,
    hsep.2.1 Buf ((hW Buf).2 (.inl rfl)) _ (hR _ (.inr (.inl rfl))),
    hsep.2.1 Buf ((hW Buf).2 (.inl rfl)) _ (hR _ (.inr (.inr rfl))),
    hsep.2.2 St ((hW St).2 (.inr rfl)), hsep.2.2 Buf ((hW Buf).2 (.inl rfl))⟩
  have hp := hsep.1
  have hwl : writtenRegions encryptInPlace initial [key, nonce, associatedData, plaintext] =
      [bufferRegion encryptInPlace initial, Stack.region initial 1104] := rfl
  rw [hwl, hSt, hBuf] at hp
  exact List.pairwise_pair.mp hp

theorem key_copied {initial s : RamState} (hS : EntryStack initial) (hg : Grows initial s)
    {K : BitVec 64} (hKeyByte : ∀ j < 32, ∃ b, initial.external[K + BitVec.ofNat 64 j]? = some b)
    (hk0 : wd s (stackPtr initial - BitVec.ofNat 64 56) = memLoad initial.external (K + BitVec.ofNat 64 0) 64)
    (hk8 : wd s (stackPtr initial - BitVec.ofNat 64 48) = memLoad initial.external (K + BitVec.ofNat 64 8) 64)
    (hk16 : wd s (stackPtr initial - BitVec.ofNat 64 40) = memLoad initial.external (K + BitVec.ofNat 64 16) 64)
    (hk24 : wd s (stackPtr initial - BitVec.ofNat 64 32) = memLoad initial.external (K + BitVec.ofNat 64 24) 64)
    (i : Nat) (hi : i < 32) :
    s.external[stackPtr initial - BitVec.ofNat 64 56 + BitVec.ofNat 64 i]? =
      initial.external[K + BitVec.ofNat 64 i]? := by
  have hroom := hS.room
  have htop := hS.top
  have hsome : ∀ k, 8 ≤ k → k ≤ 1104 → ∀ o < 8,
      (s.external[stackPtr initial - BitVec.ofNat 64 k + BitVec.ofNat 64 o]?).isSome := by
    intro k hk1 hk2 o ho
    apply hg
    apply hS.allocated <;> rw [slot_toNat (by omega) htop (by omega)] <;> omega
  have hcase : ∀ j, j < 4 → ∀ o < 8, 8 * j + o = i →
      wd s (stackPtr initial - BitVec.ofNat 64 (56 - 8 * j)) =
        memLoad initial.external (K + BitVec.ofNat 64 (8 * j)) 64 →
      s.external[stackPtr initial - BitVec.ofNat 64 56 + BitVec.ofNat 64 i]? =
        initial.external[K + BitVec.ofNat 64 i]? := by
    intro j hj o ho hji hv
    obtain ⟨b, hb⟩ := hKeyByte i hi
    rw [hb]
    have ha : stackPtr initial - BitVec.ofNat 64 56 + BitVec.ofNat 64 i =
        stackPtr initial - BitVec.ofNat 64 (56 - 8 * j) + BitVec.ofNat 64 o := by
      apply BitVec.eq_of_toNat_eq
      rw [slot_toNat (by omega) htop (by omega), slot_toNat (by omega) htop (by omega)]
      omega
    have hb' : initial.external[K + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 o]? = some b := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, hji]; exact hb
    rw [ha]
    exact copied_byte (hsome _ (by omega) (by omega)) hv ho hb'
  by_cases h1 : i < 8
  · exact hcase 0 (by omega) i h1 (by omega) hk0
  by_cases h2 : i < 16
  · exact hcase 1 (by omega) (i - 8) (by omega) (by omega) hk8
  by_cases h3 : i < 24
  · exact hcase 2 (by omega) (i - 16) (by omega) (by omega) hk16
  · exact hcase 3 (by omega) (i - 24) (by omega) (by omega) hk24

theorem slot_word {initial s : RamState} (hS : EntryStack initial) (hg : Grows initial s)
    {k : Nat} (hk1 : 8 ≤ k) (hk2 : k ≤ 1104) {v : BitVec 64}
    (hv : wd s (stackPtr initial - BitVec.ofNat 64 k) = v) {start : Nat}
    (hstart : start = (stackPtr initial).toNat - k) :
    (⟨start, 8⟩ : MemoryRegion).Word64At s.external v := by
  have hroom := hS.room
  have htop := hS.top
  refine word64At_of_memLoad (fun o ho => ?_) hv ?_
  · apply hg
    apply hS.allocated <;> rw [slot_toNat (by omega) htop (by omega)] <;> omega
  · apply BitVec.eq_of_toNat_eq
    rw [slot_toNat0 (by omega), BitVec.toNat_ofNat]
    omega

theorem core_pre_of [bindings : Machine.Bindings] {initial s : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall encryptInPlace initial [key, nonce, associatedData, plaintext])
    (hS : EntryStack initial) {cap : BitVec 64}
    (hcapW : (stackArgumentSlot initial 0).Word64At initial.external cap)
    (hcapLe : (initial.regValue .r9).toNat ≤ cap.toNat)
    (T : Track initial s) (hrip : s.RIP = 0x100650)
    (hsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 112)
    (hrdi : rd s 7 = stackPtr initial - BitVec.ofNat 64 73)
    (hrsi : rd s 6 = stackPtr initial - BitVec.ofNat 64 56)
    (hrdx : rd s 2 = rd initial 6) (hrcx : rd s 1 = rd initial 2)
    (hr9 : rd s 9 = stackPtr initial - BitVec.ofNat 64 104)
    (hk0 : wd s (stackPtr initial - BitVec.ofNat 64 56) =
      memLoad initial.external (rd initial 7 + BitVec.ofNat 64 0) 64)
    (hk8 : wd s (stackPtr initial - BitVec.ofNat 64 48) =
      memLoad initial.external (rd initial 7 + BitVec.ofNat 64 8) 64)
    (hk16 : wd s (stackPtr initial - BitVec.ofNat 64 40) =
      memLoad initial.external (rd initial 7 + BitVec.ofNat 64 16) 64)
    (hk24 : wd s (stackPtr initial - BitVec.ofNat 64 32) =
      memLoad initial.external (rd initial 7 + BitVec.ofNat 64 24) 64)
    (hd0 : wd s (stackPtr initial - BitVec.ofNat 64 104) = rd initial 1)
    (hd8 : wd s (stackPtr initial - BitVec.ofNat 64 96) = rd initial 1)
    (hd16 : wd s (stackPtr initial - BitVec.ofNat 64 88) = rd initial 9) :
    CorePre s key nonce associatedData plaintext (initial.regValue .rcx)
      (initial.regValue .rcx) := by
  have hroom := hS.room
  have htop := hS.top
  have hg := T.grows
  have hF := T.frame hS
  obtain ⟨hStKey, hStNonce, hStAD, hBufSt, hBufNonce, hBufAD, hAvSt, hAvBuf⟩ :=
    entry_sep hCall hS hcapW
  obtain ⟨hKeyIn, hNonceIn, hADIn, hPtIn, -⟩ := hCall.inputsInMemory
  obtain ⟨-, -, hADLen, hPtLen, -⟩ := hCall.lengthArgumentsMatchInputs
  have hADLen' : (initial.regValue .r8).toNat = associatedData.size := hADLen
  have hPtLen' : (initial.regValue .r9).toNat = plaintext.size := hPtLen
  have hOutIn := hCall.outputInMemory rfl
  have hbuf : bufferRegion encryptInPlace initial = ⟨(initial.regValue .rcx).toNat, cap.toNat⟩ := by
    simp only [bufferRegion, bufferBytes, encryptInPlace, argumentValue, hcapW.2,
      registerRegion] <;> rfl
  rw [hbuf] at hOutIn
  simp only [rd, wd] at hrdi hrsi hrdx hrcx hr9 hk0 hk8 hk16 hk24 hd0 hd8 hd16
  have hRs := regValue_read s
  have hRi := regValue_read initial
  have hr8 : s.regValue .r8 = initial.regValue .r8 := by
    rw [hRs.2.2.2.2.1, hRi.2.2.2.2.1]; exact T.agrees.read (by simp [changes])
  have hIs : (s.regValue .rsp).toNat = (stackPtr initial).toNat - 112 := by
    rw [show s.regValue .rsp = stackPtr s from rfl, hsp, slot_toNat0 (by omega)]
  have hrdiN : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 73 := by
    rw [hRs.1, hrdi, slot_toNat0 (by omega)]
  have hrsiN : (s.regValue .rsi).toNat = (stackPtr initial).toNat - 56 := by
    rw [hRs.2.1, hrsi, slot_toNat0 (by omega)]
  have hr9N : (s.regValue .r9).toNat = (stackPtr initial).toNat - 104 := by
    rw [hRs.2.2.2.2.2.1, hr9, slot_toNat0 (by omega)]
  have hrdx' : s.regValue .rdx = initial.regValue .rsi := by
    rw [hRs.2.2.1, hRi.2.1]; exact hrdx
  have hrcx' : s.regValue .rcx = initial.regValue .rdx := by
    rw [hRs.2.2.2.1, hRi.2.2.1]; exact hrcx
  have hKB : (initial.regValue .rdi).toNat + 32 < 2 ^ 32 := hKeyIn.1
  have hPB : (initial.regValue .rcx).toNat + cap.toNat < 2 ^ 32 := hOutIn.1
  have hStKey' := hStKey
  simp only [MemoryRegion.Disjoint, MemoryRegion.Contains] at hStKey'
  have hKeyByte : ∀ j (hj : j < 32),
      initial.external[initial.regValue .rdi + BitVec.ofNat 64 j]? =
        some (key.toArray[j]'(by simp; exact hj)) := by
    intro j hj
    rw [add_ofNat_toNat (by omega)]
    exact hKeyIn.2.2 ⟨j, by show j < key.toArray.size; simp; exact hj⟩
  have hMsgSub : ∀ x, (messageRegion (initial.regValue .rcx) plaintext.size).Contains x →
      (⟨(initial.regValue .rcx).toNat, cap.toNat⟩ : MemoryRegion).Contains x := by
    intro x hx
    simp only [messageRegion, MemoryRegion.Contains] at hx ⊢
    omega
  have hSubSt : ∀ (r : MemoryRegion), (stackPtr initial).toNat - 1104 ≤ r.start →
      r.start + r.size ≤ (stackPtr initial).toNat + 8 →
      ∀ x, r.Contains x → (⟨(stackPtr initial).toNat - 1104, 1112⟩ : MemoryRegion).Contains x := by
    intro r h1 h2 x hx
    simp only [MemoryRegion.Contains] at hx ⊢
    omega
  have hStS : Stack.region s coreStackBytes = ⟨(stackPtr initial).toNat - 1104, 1000⟩ := by
    simp only [Stack.region, Stack.returnAddressBytes, coreStackBytes, hIs, MemoryRegion.mk.injEq]
    constructor <;> omega
  have hRes : resultRegion s = ⟨(stackPtr initial).toNat - 73, 17⟩ := by
    simp only [resultRegion, registerRegion, resultBytes, hrdiN]
  have hKeyR : keyRegion s = ⟨(stackPtr initial).toNat - 56, 32⟩ := by
    simp only [keyRegion, registerRegion, hrsiN]
  have hNonceR : nonceRegion s = ⟨(initial.regValue .rsi).toNat, 12⟩ := by
    simp only [nonceRegion, registerRegion, hrdx']
  have hADR : associatedDataRegion s = ⟨(initial.regValue .rdx).toNat, associatedData.size⟩ := by
    simp only [associatedDataRegion, registerRegion, hrcx', hr8, hADLen']
  have hDescR : descriptorRegion s = ⟨(stackPtr initial).toNat - 104, 24⟩ := by
    simp only [descriptorRegion, registerRegion, hr9N]
  refine
    { environment := ⟨T.ready.smrr, T.ready.memoryType, hBindings.stringStride,
        T.ready.features.lzcnt⟩
      machine := ⟨T.ready.cpu, SupportedSSE.of_agreesExcept T.agrees hMachine.sse,
        T.ready.memory, T.ready.ready⟩
      code := T.code
      entry := hrip
      directionFlagUnset := T.agrees.directionFlagClear (by simp [changes])
        hCall.directionFlagUnset
      stack := ?_
      keyInMemory := ?_
      nonceInMemory := ?_
      associatedDataLength := by rw [hr8]; exact hADLen'
      associatedDataInMemory := ?_
      descriptorBounded := ?_
      inPointer := ?_
      outPointer := ?_
      messageLength := ?_
      messageInMemory := ?_
      outputInMemory := ?_
      inPlaceOrApart := .inl rfl
      resultInMemory := ?_
      separation := ?_ }
  ·
    have hAl := hCall.stackAvailable.2.2.2
    simp only [Stack.returnSlot, MemoryRegion.Aligned, Stack.callAlignment,
      Stack.returnAddressBytes] at hAl
    rw [show initial.regValue .rsp = stackPtr initial from rfl] at hAl
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (Stack.region s coreStackBytes).Bounded
      rw [hStS]; simp only [MemoryRegion.Bounded, userAddressLimit]; omega
    · change (Stack.region s coreStackBytes).Allocated s.external
      rw [hStS]; exact stack_allocated hS hg (by simp only; omega) (by simp only; omega)
    · simp only [Stack.NoUnderflow]; rw [hIs]; unfold coreStackBytes; omega
    · simp only [Stack.returnSlot, MemoryRegion.Aligned, Stack.callAlignment,
        Stack.returnAddressBytes]
      rw [hIs]; omega
  ·
    have hlen : (ByteArray.mk key.toArray).size = 32 := by simp [ByteArray.size]
    rw [hKeyR]
    refine ⟨by simp only [MemoryRegion.Bounded, userAddressLimit]; omega,
      hlen, fun i => ?_⟩
    have hi : i.val < 32 := Nat.lt_of_lt_of_eq i.isLt hlen
    have hc := key_copied hS hg (K := initial.regValue .rdi)
      (fun j hj => ⟨_, hKeyByte j hj⟩) (by rw [hRi.1]; exact hk0) (by rw [hRi.1]; exact hk8)
      (by rw [hRi.1]; exact hk16) (by rw [hRi.1]; exact hk24) i.val hi
    have ha : BitVec.ofNat 64 ((stackPtr initial).toNat - 56 + i.val) =
        stackPtr initial - BitVec.ofNat 64 56 + BitVec.ofNat 64 i.val := by
      apply BitVec.eq_of_toNat_eq
      rw [slot_toNat (by omega) htop (by omega), BitVec.toNat_ofNat]
      omega
    simp only
    rw [ha, hc]
    exact hKeyByte i.val hi
  ·
    rw [hNonceR]; exact input_kept hS hF hStNonce hNonceIn
  ·
    rw [hADR]; exact input_kept hS hF hStAD hADIn
  ·
    rw [hDescR]; simp only [MemoryRegion.Bounded, userAddressLimit]; omega
  · rw [hRi.2.2.2.1]
    exact slot_word hS hg (k := 104) (by omega) (by omega) hd0
      (by simp only [hr9N]; omega)
  · rw [hRi.2.2.2.1]
    exact slot_word hS hg (k := 96) (by omega) (by omega) hd8
      (by simp only [hr9N]; omega)
  · have hv : (Operand.reg 9 : Operand 64).read initial = BitVec.ofNat 64 plaintext.size := by
      rw [← hRi.2.2.2.2.2.1, ← hPtLen', BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact slot_word hS hg (k := 88) (by omega) (by omega) (hd16.trans hv)
      (by simp only [hr9N]; omega)
  ·
    refine input_kept hS hF ?_ hPtIn
    exact disjoint_mono (fun x h1 h2 => hBufSt x h2 h1) (fun x hx => hx) hMsgSub
  ·
    refine ⟨?_, allocated_kept hg ?_⟩
    · simp only [messageRegion, MemoryRegion.Bounded, userAddressLimit]; omega
    · intro a ha; exact hOutIn.2 a (hMsgSub _ ha)
  ·
    rw [hRes]
    exact ⟨by simp only [MemoryRegion.Bounded, userAddressLimit]; omega,
      stack_allocated hS hg (by simp only; omega) (by simp only; omega)⟩
  ·
    have sR := hSubSt ⟨(stackPtr initial).toNat - 73, 17⟩ (by simp only; omega)
      (by simp only; omega)
    have sS := hSubSt ⟨(stackPtr initial).toNat - 1104, 1000⟩ (by simp only; omega)
      (by simp only; omega)
    have sK := hSubSt ⟨(stackPtr initial).toNat - 56, 32⟩ (by simp only; omega)
      (by simp only; omega)
    have sD := hSubSt ⟨(stackPtr initial).toNat - 104, 24⟩ (by simp only; omega)
      (by simp only; omega)
    have hStBuf : (⟨(stackPtr initial).toNat - 1104, 1112⟩ : MemoryRegion).Disjoint
        ⟨(initial.regValue .rcx).toNat, cap.toNat⟩ := fun x h1 h2 => hBufSt x h2 h1
    have hid : ∀ (r : MemoryRegion) x, r.Contains x → r.Contains x := fun _ _ h => h
    simp only [MemorySeparation, coreWritten, coreRead, ite_true, List.append_nil, hRes,
      hStS, hKeyR, hNonceR, hADR, hDescR]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
      exact ⟨⟨disjoint_mono hStBuf sR hMsgSub,
        disjoint_of_sep (by simp only; omega)⟩, disjoint_mono hBufSt hMsgSub sS,
        fun _ h => h.elim⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨⟨disjoint_of_sep (by simp only; omega), disjoint_mono hStNonce sR (hid _),
        disjoint_mono hStAD sR (hid _), disjoint_of_sep (by simp only; omega)⟩,
        ⟨disjoint_mono hBufSt hMsgSub sK, disjoint_mono hBufNonce hMsgSub (hid _),
        disjoint_mono hBufAD hMsgSub (hid _), disjoint_mono hBufSt hMsgSub sD⟩,
        ⟨disjoint_of_sep (by simp only; omega), disjoint_mono hStNonce sS (hid _),
        disjoint_mono hStAD sS (hid _), disjoint_of_sep (by simp only; omega)⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨avoids_mono hAvSt sR, avoids_mono hAvBuf hMsgSub, avoids_mono hAvSt sS⟩

theorem entry_to_core [bindings : Machine.Bindings] {initial : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall encryptInPlace initial [key, nonce, associatedData, plaintext]) :
    ∃ fuel s, Advances (returnBoundary initial) fuel initial s ∧
      CorePre s key nonce associatedData plaintext (initial.regValue .rcx)
        (initial.regValue .rcx) ∧
      AtCoreCall initial s := by
  have hS := entry_stack hCall
  have hroom := hS.room
  have htop := hS.top
  have hEntry := entry_ready bindings hBindings hMachine hCall.programLoaded
  have T0 : Track initial initial := ⟨hEntry.ready, hEntry.code, AgreesExcept.refl _ _⟩
  have hOut := (entry_boundary hBindings hMachine hCall).2
  obtain ⟨cap, ⟨hcapB, hcapW⟩, hcapLe⟩ :=
    hCall.capacityArgumentCoversMessage (.stack 0) rfl
  have hRi := regValue_read initial
  have e7 : rd initial 7 = initial.regValue .rdi := hRi.1.symm
  have hslot : BitVec.ofNat 64 (stackArgumentSlot initial 0).start = stackPtr initial + 8 := by
    apply BitVec.eq_of_toNat_eq
    have h8 : (8 : BitVec 64).toNat = 8 := rfl
    simp only [stackArgumentSlot, BitVec.toNat_ofNat, BitVec.toNat_add, h8]
    change ((stackPtr initial).toNat + 8 * (0 + 1)) % 2 ^ 64 = _
    omega
  have hcapM : memLoad initial.external (stackPtr initial + 8) 64 = cap := by
    rw [← hslot]; exact word64At_memLoad hcapW
  have hArgB : (stackPtr initial).toNat + 16 < 2 ^ 32 := by
    simp only [MemoryRegion.Bounded, stackArgumentSlot, userAddressLimit] at hcapB
    change (stackPtr initial).toNat + 8 * (0 + 1) + 8 < 2 ^ 32 at hcapB
    omega
  have hArgSome : ∀ i < 8,
      (initial.external[stackPtr initial + 8 + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    have := loadBytes_isSome hcapW.2 i hi
    rwa [hslot] at this
  obtain ⟨n1, s9, a1, T9, hrip9, hsp9, h15, h3, h14, h1, h2, h7, h9, hsv8, hsv16, hsv24⟩ :=
    phase_a hS hOut T0 hCall.atEntryPoint hArgB hArgSome
  obtain ⟨hKeyIn, -, -, -, -⟩ := hCall.inputsInMemory
  obtain ⟨hStKey, -, -, -, -, -, -, -⟩ := entry_sep hCall hS hcapW
  have hKeyB : (rd initial 7).toNat + 32 < 2 ^ 32 := by
    have := hKeyIn.1
    simp only [inputRegion, registerRegion, MemoryRegion.Bounded, userAddressLimit] at this
    rw [hRi.1] at this
    exact this
  have hKeySome : ∀ j < 32, (initial.external[rd initial 7 + BitVec.ofNat 64 j]?).isSome := by
    intro j hj
    have := hKeyIn.2.2 ⟨j, by show j < key.toArray.size; simp; exact hj⟩
    simp only [inputRegion, registerRegion] at this
    rw [e7, add_ofNat_toNat (by rw [← e7]; omega)]
    simp [this]
  have hKeySep : (stackPtr initial).toNat + 8 ≤ (rd initial 7).toNat ∨
      (rd initial 7).toNat + 32 ≤ (stackPtr initial).toNat - 1104 := by
    have := region_sep hStKey (by simp) (by simp)
    simp only at this
    rw [e7]
    omega
  obtain ⟨n2, s16, a2, T16, hrip16, hsp16, h0', hk24, hk16, hk8, h3', h14', h1', h2', h9', h15',
      hsv8', hsv16', hsv24'⟩ :=
    phase_b hS hOut T9 hrip9 hsp9 h7 hKeyB hKeySome hKeySep
  have hle : (rd s16 9).toNat ≤ (rd s16 15).toNat := by
    rw [h9', h15', h9, h15, hcapM]
    exact hcapLe
  obtain ⟨n3, s25, a3, T25, hrip25, hsp25, hc0, hd0, hd8, hd16, h3'', h14'', h1'', h2'', h15'',
      hsv8'', hsv16'', hsv24'', hk24', hk16', hk8'⟩ :=
    phase_c hS hOut T16 hrip16 hsp16 hle
  obtain ⟨n4, s, a4, T, hrip, hsp, hrdi, hrsi, hr9, hret, h3d, h14d, h1d, h2d, h15d,
      hsv8d, hsv16d, hsv24d, hk24d, hk16d, hk8d, hk0d, hd16d, hd8d, hd0d⟩ :=
    phase_d hS hOut T25 hrip25 hsp25
  have hRs := regValue_read s
  have hr15 : rd s 15 = cap := by rw [h15d, h15'', h15', h15, hcapM]
  refine ⟨_, s, ((a1.trans a2).trans a3).trans a4, ?_, ?_⟩
  · exact core_pre_of hBindings hMachine hCall hS hcapW (by rw [hRi.2.2.2.2.2.1]; exact hcapLe)
      T hrip hsp hrdi hrsi (by rw [h2d, h2'', h2', h2]) (by rw [h1d, h1'', h1', h1])
      hr9 (by rw [hk0d, hc0, h0']) (by rw [hk8d, hk8', hk8]) (by rw [hk16d, hk16', hk16])
      (by rw [hk24d, hk24', hk24]) (by rw [hd0d, hd0, h14', h14])
      (by rw [hd8d, hd8, h14', h14]) (by rw [hd16d, hd16, h9', h9])
  · refine
      { rsp := by rw [hsp]; rfl
        returnAddress := ?_
        rdi := ?_
        rbx := h3d.trans (h3''.trans (h3'.trans h3))
        r14 := h14d.trans (h14''.trans (h14'.trans h14))
        r15 := by
          have : s.regValue .r15 = cap := hr15
          rw [this]; exact hcapW
        rbp := by
          rw [hRs.2.2.2.2.2.2.2.1, (regValue_read initial).2.2.2.2.2.2.2.1]
          exact T.agrees.read (by simp [changes])
        r12 := by
          rw [hRs.2.2.2.2.2.2.2.2.1, (regValue_read initial).2.2.2.2.2.2.2.2.1]
          exact T.agrees.read (by simp [changes])
        r13 := by
          rw [hRs.2.2.2.2.2.2.2.2.2.1, (regValue_read initial).2.2.2.2.2.2.2.2.2.1]
          exact T.agrees.read (by simp [changes])
        savedR15 := slot_word hS T.grows (k := 8) (by omega) (by omega)
          (hsv8d.trans (hsv8''.trans (hsv8'.trans hsv8))) rfl
        savedR14 := slot_word hS T.grows (k := 16) (by omega) (by omega)
          (hsv16d.trans (hsv16''.trans (hsv16'.trans hsv16))) rfl
        savedRbx := slot_word hS T.grows (k := 24) (by omega) (by omega)
          (hsv24d.trans (hsv24''.trans (hsv24'.trans hsv24))) rfl
        frame := T.frame hS
        grows := T.grows }
    · show wd s (stackPtr s) = _
      rw [hsp]; exact hret
    · have : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 73 := hrdi
      rw [this, hsp]
      bv_omega

structure GTrack [Machine.Bindings] (cs : List Component) (b u : RamState) : Prop where
  ready : ReadyToStep u
  code : CodeIn Extracted.programImage u
  agrees : AgreesExcept cs b u

def Fits (cs ds : List Component) : Prop :=
  ∀ c ∈ ds, (c.isMem = false ∧ c ∈ cs) ∨
    (c.isMem = true ∧ ∀ x, c.Covers x → (∃ d ∈ cs, d.Covers x) ∧ ¬ InProgram x)

theorem Fits.widen {cs ds : List Component} {u v : RamState} (h : Fits cs ds)
    (he : AgreesExcept ds u v) : AgreesExcept cs u v := by
  refine ⟨fun c hc hm => he.agree c (fun hds => ?_) hm, fun x hx => he.memory x ?_,
    he.rest, he.grow⟩
  · rcases h c hds with ⟨-, h1⟩ | ⟨h2, -⟩
    · exact hc h1
    · rw [hm] at h2; cases h2
  · intro c hds hcov
    rcases h c hds with ⟨hm, -⟩ | ⟨-, h2⟩
    · exact nonmem_not_covers hm x hcov
    · obtain ⟨⟨d, hd, hdc⟩, -⟩ := h2 x hcov
      exact hx d hd hdc

theorem Fits.av {cs ds : List Component} (h : Fits cs ds) :
    ∀ c ∈ ds, ∀ a, c.Covers a → ¬ InProgram a := by
  intro c hc a hcov
  rcases h c hc with ⟨hm, -⟩ | ⟨-, h2⟩
  · exact absurd hcov (nonmem_not_covers hm a)
  · exact (h2 a hcov).2

theorem gtrack_step [Machine.Bindings] {cs : List Component} {b u : RamState}
    {boundary : ReturnBoundary} {pre : RamState → Prop} {e : RamState → Effect}
    {p : BitVec 64} {bytes : List UInt8}
    (hStep : StepEffect pre (codeRange p bytes) e) (hT : GTrack cs b u)
    (hbytes : CodeIn (codeRange p bytes) u) (hpre : pre u)
    (hne : (e u).rip ≠ boundary.rip) (hw : Fits cs (e u).components) :
    ∃ v, Advances boundary 1 u v ∧ GTrack cs b v ∧ (e u).Holds u v := by
  obtain ⟨v, ha, hr, hc, he⟩ := step_run hStep hT.ready hT.code hbytes hpre hne hw.av
  refine ⟨v, ha, ⟨hr, hc, (hT.agrees.trans (hw.widen he.agrees)).mono ?_⟩, he⟩
  intro c hc
  simp only [List.mem_append, or_self] at hc
  exact hc

theorem byteRegGpr_0 : byteRegGpr 0 = 0 := rfl
theorem byteRegGpr_1 : byteRegGpr 1 = 1 := rfl

syntax "or_rfl" : tactic
macro_rules
  | `(tactic| or_rfl) => `(tactic| first | exact rfl | exact Or.inl rfl | (apply Or.inr; or_rfl))

syntax "fits" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| fits [$ls,*]) => `(tactic| (
    simp only [Fits, movR64M64Effect_components, movM64R64Effect_components,
      cmpM8Imm8Effect_components, jccEffect, branchEffect_components, movR64R64Effect_components,
      subR64Imm8Effect_components, setccR8NoRexEffect_components, cmpR64R64Effect_components,
      orR8R8NoRexEffect_components, movR32Imm32Effect_components, xorR32R32Effect_components,
      addR64Imm8Effect_components, popR64Effect_components, retEffect_components,
      byteRegGpr_0, byteRegGpr_1, storeAddrAt,
      List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, $ls,*]
    repeat' apply And.intro
    all_goals first
      | exact .inl ⟨rfl, by first | (simp [$ls,*]; done) | (simp [$ls,*]; or_rfl)⟩
      | skip))

macro "notin" : tactic => `(tactic| (
  simp only [movR64M64Effect_components, movM64R64Effect_components,
    cmpM8Imm8Effect_components, jccEffect, branchEffect_components, movR64R64Effect_components,
    subR64Imm8Effect_components, setccR8NoRexEffect_components, cmpR64R64Effect_components,
    orR8R8NoRexEffect_components, movR32Imm32Effect_components, xorR32R32Effect_components,
    addR64Imm8Effect_components, popR64Effect_components, retEffect_components,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  decide))

theorem gload {cs : List Component} {u v : RamState} (he : AgreesExcept cs u v) {a : BitVec 64}
    (h : ∀ c ∈ cs, ∀ i < 8, ¬ c.Covers (a + BitVec.ofNat 64 i)) :
    wd v a = wd u a := by
  apply memLoad_congr
  intro i hi
  change i < 8 at hi
  simp only [memByte]
  congr 1
  exact he.byte fun c hc => h c hc i hi

def RetPresent (I : BitVec 64) (u : RamState) : Prop :=
  ∀ j < 112, (u.external[I - BitVec.ofNat 64 104 + BitVec.ofNat 64 j]?).isSome

theorem RetPresent.of_agrees {I : BitVec 64} {cs : List Component} {u v : RamState}
    (h : RetPresent I u) (he : AgreesExcept cs u v) : RetPresent I v :=
  fun j hj => he.grow _ (h j hj)

theorem ret_addr {I : BitVec 64} (hroom : 1104 ≤ I.toNat) (htop : I.toNat + 8 < 2 ^ 32)
    {k i : Nat} (hk : k ≤ 104) (hi : i < k + 8) :
    I - BitVec.ofNat 64 k + BitVec.ofNat 64 i =
      I - BitVec.ofNat 64 104 + BitVec.ofNat 64 (104 - k + i) := by
  apply BitVec.eq_of_toNat_eq
  rw [slot_toNat (by omega) htop hi, slot_toNat (by omega) htop (by omega)]
  omega

theorem ret_readable {I : BitVec 64} {u : RamState} (hroom : 1104 ≤ I.toNat)
    (htop : I.toNat + 8 < 2 ^ 32) (hP : RetPresent I u) {k n : Nat} (hk : k ≤ 104)
    (hn : n ≤ k + 8) : MemReadable u (I - BitVec.ofNat 64 k) n := by
  refine ⟨by rw [slot_toNat0 (by omega)]; omega, fun i hi => ?_⟩
  rw [ret_addr hroom htop hk (by omega)]
  exact hP _ (by omega)

theorem ret_writable {I : BitVec 64} {u : RamState} (hroom : 1104 ≤ I.toNat)
    (htop : I.toNat + 8 < 2 ^ 32)
    (htables : 0x2020 ≤ I.toNat - 1104 ∨ I.toNat + 8 ≤ 0x1000) (hP : RetPresent I u) {k : Nat}
    (hk : k ≤ 104) (hk8 : 8 ≤ k) : MemWritable u (I - BitVec.ofNat 64 k) 8 := by
  refine ⟨by rw [slot_toNat0 (by omega)]; omega, (ret_readable hroom htop hP hk (by omega)).mem,
    ?_⟩
  rw [slot_toNat0 (by omega)]
  unfold PageTableEntriesApart
  omega

theorem ret_slot_apart {I : BitVec 64} (hroom : 1104 ≤ I.toNat) (htop : I.toNat + 8 < 2 ^ 32)
    (hout : ∀ a : BitVec 64, I.toNat - 1104 ≤ a.toNat → a.toNat < I.toNat + 8 → ¬ InProgram a)
    {k : Nat} (hk : k ≤ 104) {p : BitVec 64} {len : Nat}
    (hp : ∀ j < len, InProgram (p + BitVec.ofNat 64 j)) :
    RangeApart (I - BitVec.ofNat 64 k) 8 p len := by
  intro i hi j hj he
  apply hout (I - BitVec.ofNat 64 k + BitVec.ofNat 64 i)
  · rw [slot_toNat (by omega) htop (by omega)]; omega
  · rw [slot_toNat (by omega) htop (by omega)]; omega
  · rw [he]; exact hp j hj

theorem stack_fits {I : BitVec 64} (hroom : 1104 ≤ I.toNat) (htop : I.toNat + 8 < 2 ^ 32)
    (hout : ∀ a : BitVec 64, I.toNat - 1104 ≤ a.toNat → a.toNat < I.toNat + 8 → ¬ InProgram a)
    {cs : List Component} (hm : Component.mem (I - BitVec.ofNat 64 104) 16 ∈ cs) {k : Nat}
    (hk : 96 ≤ k) (hk' : k ≤ 104) :
    ∀ x, (Component.mem (I - BitVec.ofNat 64 k) 8).Covers x →
      (∃ d ∈ cs, d.Covers x) ∧ ¬ InProgram x := by
  rintro x ⟨i, hi, rfl⟩
  refine ⟨⟨_, hm, 104 - k + i, by omega, ret_addr hroom htop hk' (by omega)⟩, ?_⟩
  apply hout <;> rw [slot_toNat (by omega) htop (by omega)] <;> omega

def retCs1 (I : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .flags, .rip, .mem (I - BitVec.ofNat 64 104) 16]

theorem byte_low_merge0 (v : BitVec 8) (x : BitVec 64) :
    (mergeByteReg 0 v x).setWidth 8 = v := by
  simp only [mergeByteReg, show (0 : BitVec 3).toNat < 4 from by decide, ite_true]
  exact setWidth_mergeGPR8 v x

theorem byte_low_merge1 (v : BitVec 8) (x : BitVec 64) :
    (mergeByteReg 1 v x).setWidth 8 = v := by
  simp only [mergeByteReg, show (1 : BitVec 3).toNat < 4 from by decide, ite_true]
  exact setWidth_mergeGPR8 v x

theorem read_byteReg0 (u : RamState) : (Operand.byteReg 0).read u = (rd u 0).setWidth 8 := by
  rw [Operand.read_byteReg]
  simp only [show (0 : BitVec 3).toNat < 4 from by decide, ite_true, byteRegGpr_0,
    Operand.read_reg64]

theorem read_byteReg1 (u : RamState) : (Operand.byteReg 1).read u = (rd u 1).setWidth 8 := by
  rw [Operand.read_byteReg]
  simp only [show (1 : BitVec 3).toNat < 4 from by decide, ite_true, byteRegGpr_1,
    Operand.read_reg64]

theorem ret_prefix [Machine.Bindings] {initial t : RamState} (hS : EntryStack initial)
    (hOut : ¬ InProgram (returnBoundary initial).rip)
    (T0 : GTrack (retCs1 (stackPtr initial)) t t) (hrip : t.RIP = 0x10199f)
    (hsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 104)
    (hP : RetPresent (stackPtr initial) t)
    (hres : t.external[stackPtr initial - BitVec.ofNat 64 73]? = some 0)
    {size cap : Nat} (hsize : size < 2 ^ 32) (hb : rd t 3 = BitVec.ofNat 64 size)
    (hc : (rd t 15).toNat = cap) :
    ∃ n u, Advances (returnBoundary initial) n t u ∧ GTrack (retCs1 (stackPtr initial)) t u ∧
      u.RIP = (if size + 16 ≤ cap then 0x1019d9 else 0x1019ed) ∧
      stackPtr u = stackPtr initial - BitVec.ofNat 64 104 ∧
      rd u 0 = 1 ∧
      wd u (stackPtr initial - BitVec.ofNat 64 104) = wd t (stackPtr initial - BitVec.ofNat 64 72) ∧
      wd u (stackPtr initial - BitVec.ofNat 64 96) = wd t (stackPtr initial - BitVec.ofNat 64 64) := by
  have hroom := hS.room
  have htop := hS.top
  have hout := hS.outside
  have hmem : Component.mem (stackPtr initial - BitVec.ofNat 64 104) 16 ∈
      retCs1 (stackPtr initial) := by simp [retCs1]
  have hA1 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x1f)).addr t x =
      stackPtr initial - BitVec.ofNat 64 73 := rsp_addr hsp 0x1f 31 rfl (by omega)
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step
    (cmp_m8_imm8_effect_step 0x10199f (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide)
      (by decide) 1)
    T0 (program_text_slice T0.code 0x199f 5 (by decide +kernel))
    ⟨hrip, by rw [hA1]; exact ret_readable hroom htop hP (k := 73) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x19a4 (by omega)) (by fits [retCs1])
  change (cmpM8Imm8Effect 0x10199f 5 (.sib 4 none 0 (.d8 0x1f)) 1 t).Holds t u1 at e1
  have hsp1 := sp_keep e1.agrees (by simp) hsp
  have hz1 : condHolds 5 (StatusFlags.ofRFLAGS u1.RFLAGS) = true := by
    have hf := e1.flags
    simp only [Effect.FlagsHold, cmpM8Imm8Effect, hA1] at hf
    obtain ⟨-, -, -, hZF, -⟩ := hf
    change (StatusFlags.ofRFLAGS u1.RFLAGS).ZF = (cmpSpec _ _).ZF at hZF
    rw [condHolds_5, hZF, cmpSpec_ZF]
    change (!(memLoad t.external (stackPtr initial - BitVec.ofNat 64 73) 8 == 1)) = true
    rw [memLoad_8]
    simp only [memByte]
    change (!(((t.external[stackPtr initial - BitVec.ofNat 64 73]?).getD 0).toBitVec == 1)) = true
    rw [hres]
    decide
  have htgt2 : branchTarget 0x1019a4 2 ((0x07 : BitVec 8).signExtend 64) = 0x1019ad := by decide
  obtain ⟨u2, a2, T2, e2⟩ := gtrack_step (jcc_rel8_effect_step 0x1019a4 5 0x07)
    T1 (program_text_slice T1.code 0x19a4 2 (by decide +kernel))
    ⟨e1.rip, fun _ => by rw [htgt2]; decide⟩
    (by
      simp only [jccEffect, branchEffect, hz1, ite_true]
      rw [htgt2]; exact code_ne_boundary hOut 0x19ad (by omega))
    (by fits [retCs1])
  have hrip2 : u2.RIP = 0x1019ad := (jccEffect_taken hz1 e2).rip.trans htgt2
  have hsp2 := sp_keep e2.agrees (by simp [jccEffect]) hsp1
  have hA3 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x20)).addr u2 x =
      stackPtr initial - BitVec.ofNat 64 72 := rsp_addr hsp2 0x20 32 rfl (by omega)
  obtain ⟨u3, a3, T3, e3⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x1019ad 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide))
    T2 (program_text_slice T2.code 0x19ad 5 (by decide +kernel))
    ⟨hrip2, by rw [hA3]; exact ret_readable hroom htop (hP.of_agrees T2.agrees) (k := 72) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x19b2 (by omega)) (by fits [retCs1])
  change (movR64M64Effect 0x1019ad 0 (.sib 4 none 0 (.d8 0x20)) u2).Holds u2 u3 at e3
  have hsp3 := sp_keep e3.agrees (by simp) hsp2
  have v3 : rd u3 0 = wd u2 (stackPtr initial - BitVec.ofNat 64 72) := by
    have := e3.writes
    simp only [movR64M64Effect, hA3] at this
    exact this
  have hA4 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x28)).addr u3 x =
      stackPtr initial - BitVec.ofNat 64 64 := rsp_addr hsp3 0x28 40 rfl (by omega)
  obtain ⟨u4, a4, T4, e4⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x1019b2 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide))
    T3 (program_text_slice T3.code 0x19b2 5 (by decide +kernel))
    ⟨e3.rip, by rw [hA4]; exact ret_readable hroom htop (hP.of_agrees T3.agrees) (k := 64) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x19b7 (by omega)) (by fits [retCs1])
  change (movR64M64Effect 0x1019b2 1 (.sib 4 none 0 (.d8 0x28)) u3).Holds u3 u4 at e4
  have hsp4 := sp_keep e4.agrees (by simp) hsp3
  have v4 : rd u4 1 = wd u3 (stackPtr initial - BitVec.ofNat 64 64) := by
    have := e4.writes
    simp only [movR64M64Effect, hA4] at this
    exact this
  have hA5 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x8)).addr u4 x =
      stackPtr initial - BitVec.ofNat 64 96 := rsp_addr hsp4 0x8 8 rfl (by omega)
  obtain ⟨u5, a5, T5, e5⟩ := gtrack_step
    (mov_m64_r64_effect_step 0x1019b7 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide))
    T4 (program_text_slice T4.code 0x19b7 5 (by decide +kernel))
    ⟨e4.rip,
      by simp only [storeAddrAt, hA5]
         exact ret_writable hroom htop hS.tables (hP.of_agrees T4.agrees) (k := 96) (by omega) (by omega),
      by simp only [storeAddrAt, hA5]
         exact ret_slot_apart hroom htop hout (k := 96) (by omega) (code_inProgram 0x19b7 5 (by omega))⟩
    (code_ne_boundary hOut 0x19bc (by omega))
    (by
      fits [retCs1, hA5]
      exact .inr ⟨rfl, stack_fits hroom htop hout hmem (by omega) (by omega)⟩)
  change (movM64R64Effect 0x1019b7 1 (.sib 4 none 0 (.d8 0x8)) u4).Holds u4 u5 at e5
  have hsp5 := sp_keep e5.agrees (by simp) hsp4
  have w5 : wd u5 (stackPtr initial - BitVec.ofNat 64 96) = rd u4 1 := by
    rw [← hA5 (0x1019b7 + BitVec.ofNat 64 5)]
    exact e5.writes
  have hA6 : ∀ x, (AddrMode.sib 4 none 0 .none).addr u5 x =
      stackPtr initial - BitVec.ofNat 64 104 := rsp_addr0 hsp5
  obtain ⟨u6, a6, T6, e6⟩ := gtrack_step
    (mov_m64_r64_effect_step 0x1019bc 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 .none) (by decide) (by decide) (by decide))
    T5 (program_text_slice T5.code 0x19bc 4 (by decide +kernel))
    ⟨e5.rip,
      by simp only [storeAddrAt, hA6]
         exact ret_writable hroom htop hS.tables (hP.of_agrees T5.agrees) (k := 104) (by omega) (by omega),
      by simp only [storeAddrAt, hA6]
         exact ret_slot_apart hroom htop hout (k := 104) (by omega) (code_inProgram 0x19bc 4 (by omega))⟩
    (code_ne_boundary hOut 0x19c0 (by omega))
    (by
      fits [retCs1, hA6]
      exact .inr ⟨rfl, stack_fits hroom htop hout hmem (by omega) (by omega)⟩)
  change (movM64R64Effect 0x1019bc 0 (.sib 4 none 0 .none) u5).Holds u5 u6 at e6
  have hsp6 := sp_keep e6.agrees (by simp) hsp5
  have w6 : wd u6 (stackPtr initial - BitVec.ofNat 64 104) = rd u5 0 := by
    rw [← hA6 (0x1019bc + BitVec.ofNat 64 4)]
    exact e6.writes
  have k6 : wd u6 (stackPtr initial - BitVec.ofNat 64 96) =
      wd u5 (stackPtr initial - BitVec.ofNat 64 96) := by
    apply gload e6.agrees
    intro c hc i hi
    simp only [movM64R64Effect_components, storeAddrAt, hA6, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl
    · exact slot_not_covers hi (by omega) (by omega) (by omega)
    · exact fun h => h
  obtain ⟨u7, a7, T7, e7⟩ := gtrack_step
    (mov_r64_r64_effect_step 0x1019c0 0x48 0xd8 (by unfold RexWPrefix; decide) (by decide))
    T6 (program_text_slice T6.code 0x19c0 3 (by decide +kernel))
    e6.rip (code_ne_boundary hOut 0x19c3 (by omega)) (by fits [retCs1])
  change (movR64R64Effect 0x1019c0 0 3 u6).Holds u6 u7 at e7
  have v7 : rd u7 0 = BitVec.ofNat 64 size := by
    rw [show rd u7 0 = rd u6 3 from e7.writes, ← hb]
    exact T6.agrees.read (by simp [retCs1])
  obtain ⟨u8, a8, T8, e8⟩ := gtrack_step
    (sub_r64_imm8_effect_step 0x1019c3 0x48 0xe8 0xf0 (by unfold RexWPrefix; decide)
      (by decide) (by decide))
    T7 (program_text_slice T7.code 0x19c3 4 (by decide +kernel))
    e7.rip (code_ne_boundary hOut 0x19c7 (by omega)) (by fits [retCs1])
  change (subR64Imm8Effect 0x1019c3 0 0xf0 u7).Holds u7 u8 at e8
  have v8 : (rd u8 0).toNat = size + 16 := by
    rw [show rd u8 0 = rd u7 0 - (0xf0 : BitVec 8).signExtend 64 from e8.writes, v7]
    have : (0xf0 : BitVec 8).signExtend 64 = 0xfffffffffffffff0 := by decide
    rw [this, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have h2 : (0xfffffffffffffff0 : BitVec 64).toNat = 2 ^ 64 - 16 := rfl
    rw [h2]
    omega
  have hc8 : condHolds 3 (StatusFlags.ofRFLAGS u8.RFLAGS) = false := by
    have hf := e8.flags
    simp only [Effect.FlagsHold, subR64Imm8Effect] at hf
    obtain ⟨hCF, -⟩ := hf
    change (StatusFlags.ofRFLAGS u8.RFLAGS).CF = (subSpec _ _).2.CF at hCF
    rw [condHolds_3, hCF]
    change (!decide ((rd u7 0).toNat < ((0xf0 : BitVec 8).signExtend 64).toNat)) = false
    rw [v7]
    have : ((0xf0 : BitVec 8).signExtend 64).toNat = 2 ^ 64 - 16 := by decide
    rw [this, BitVec.toNat_ofNat]
    simp only [Bool.not_eq_false', decide_eq_true_eq]
    omega
  obtain ⟨u9, a9, T9, e9⟩ := gtrack_step
    (setcc_r8_norex_effect_step 0x1019c7 3 0xc1 (by decide) false)
    T8 (program_text_slice T8.code 0x19c7 3 (by decide +kernel))
    ⟨e8.rip, hc8⟩ (code_ne_boundary hOut 0x19ca (by omega)) (by fits [retCs1])
  change (setccR8NoRexEffect 0x1019c7 3 1 false u8).Holds u8 u9 at e9
  have v9 : (rd u9 1).setWidth 8 = 0 := by
    rw [show rd u9 1 = mergeByteReg 1 (if false then 1 else 0) (rd u8 1) from e9.writes,
      byte_low_merge1]
    rfl
  have v9a : rd u9 0 = rd u8 0 := e9.agrees.read (by notin)
  obtain ⟨u10, a10, T10, e10⟩ := gtrack_step
    (cmp_r64_r64_effect_step 0x1019ca 0x4c 0xf8 (by unfold RexWPrefix; decide) (by decide))
    T9 (program_text_slice T9.code 0x19ca 3 (by decide +kernel))
    e9.rip (code_ne_boundary hOut 0x19cd (by omega)) (by fits [retCs1])
  change (cmpR64R64Effect 0x1019ca 0 15 u9).Holds u9 u10 at e10
  have hc10 : condHolds 7 (StatusFlags.ofRFLAGS u10.RFLAGS) = decide (cap < size + 16) := by
    have hf := e10.flags
    simp only [Effect.FlagsHold, cmpR64R64Effect] at hf
    obtain ⟨hCF, -, -, hZF, -⟩ := hf
    change (StatusFlags.ofRFLAGS u10.RFLAGS).CF = (cmpSpec _ _).CF at hCF
    change (StatusFlags.ofRFLAGS u10.RFLAGS).ZF = (cmpSpec _ _).ZF at hZF
    rw [condHolds_7, hCF, hZF, cmpSpec_ZF]
    change (!(decide ((rd u9 0).toNat < (rd u9 15).toNat) || (rd u9 0 == rd u9 15))) = _
    have h15 : rd u9 15 = rd t 15 := T9.agrees.read (by simp [retCs1])
    have h0 : (rd u9 0).toNat = size + 16 := by rw [v9a]; exact v8
    have key : ∀ a b : BitVec 64, a.toNat = size + 16 → b.toNat = cap →
        (!(decide (a.toNat < b.toNat) || (a == b))) = decide (cap < size + 16) := by
      intro a b ha hb
      have hab : (a == b) = decide (size + 16 = cap) := by
        by_cases h : size + 16 = cap
        · have : a = b := BitVec.eq_of_toNat_eq (by omega)
          simp [this, h]
        · have : a ≠ b := fun e => h (by rw [← ha, ← hb, e])
          simp [this, h]
      rw [hab, ha, hb]
      by_cases h1 : cap < size + 16 <;> by_cases h2 : size + 16 = cap <;> simp [h1, h2] <;> omega
    exact key _ _ h0 (by rw [h15, hc])
  obtain ⟨u11, a11, T11, e11⟩ := gtrack_step
    (setcc_r8_norex_effect_step 0x1019cd 7 0xc0 (by decide) (decide (cap < size + 16)))
    T10 (program_text_slice T10.code 0x19cd 3 (by decide +kernel))
    ⟨e10.rip, hc10⟩ (code_ne_boundary hOut 0x19d0 (by omega)) (by fits [retCs1])
  change (setccR8NoRexEffect 0x1019cd 3 0 (decide (cap < size + 16)) u10).Holds u10 u11 at e11
  have v11 : (rd u11 0).setWidth 8 = if decide (cap < size + 16) then 1 else 0 := by
    rw [show rd u11 0 = mergeByteReg 0 (if decide (cap < size + 16) then 1 else 0) (rd u10 0)
      from e11.writes, byte_low_merge0]
  have v11c : (rd u11 1).setWidth 8 = 0 := by
    rw [show rd u11 1 = rd u9 1 from
      (e10.agrees.trans e11.agrees).read (by notin), v9]
  obtain ⟨u12, a12, T12, e12⟩ := gtrack_step
    (or_r8_r8_norex_effect_step 0x1019d0 0xc8 (by decide))
    T11 (program_text_slice T11.code 0x19d0 2 (by decide +kernel))
    e11.rip (code_ne_boundary hOut 0x19d2 (by omega)) (by fits [retCs1])
  change (orR8R8NoRexEffect 0x1019d0 2 0 1 u11).Holds u11 u12 at e12
  have hz12 : (StatusFlags.ofRFLAGS u12.RFLAGS).ZF = !decide (cap < size + 16) := by
    have hf := e12.flags
    simp only [Effect.FlagsHold, orR8R8NoRexEffect] at hf
    obtain ⟨-, -, -, hZF, -⟩ := hf
    change (StatusFlags.ofRFLAGS u12.RFLAGS).ZF =
      (((Operand.byteReg 0).read u11 ||| (Operand.byteReg 1).read u11) == 0) at hZF
    rw [hZF, read_byteReg0, read_byteReg1, v11, v11c]
    by_cases h : cap < size + 16 <;> simp [h]
  obtain ⟨u13, a13, T13, e13⟩ := gtrack_step
    (mov_r32_imm32_effect_step 0x1019d2 0xb8 (by decide) 1)
    T12 (program_text_slice T12.code 0x19d2 5 (by decide +kernel))
    e12.rip (code_ne_boundary hOut 0x19d7 (by omega)) (by fits [retCs1])
  change (movR32Imm32Effect 0x1019d2 5 0 1 u12).Holds u12 u13 at e13
  have hc13 : condHolds 5 (StatusFlags.ofRFLAGS u13.RFLAGS) = decide (cap < size + 16) := by
    rw [flags_keep e13.agrees (by simp), condHolds_5, hz12, Bool.not_not]
  have htgt14 : branchTarget 0x1019d7 2 ((0x14 : BitVec 8).signExtend 64) = 0x1019ed := by decide
  obtain ⟨u14, a14, T14, e14⟩ := gtrack_step (jcc_rel8_effect_step 0x1019d7 5 0x14)
    T13 (program_text_slice T13.code 0x19d7 2 (by decide +kernel))
    ⟨e13.rip, fun _ => by rw [htgt14]; decide⟩
    (by
      simp only [jccEffect, branchEffect]
      split
      · rw [htgt14]; exact code_ne_boundary hOut 0x19ed (by omega)
      · exact code_ne_boundary hOut 0x19d9 (by omega))
    (by fits [retCs1])
  have hregs : ∀ c ∈ (((((((movR64R64Effect 0x1019c0 0 3 u6).components ++
      (subR64Imm8Effect 0x1019c3 0 0xf0 u7).components) ++
      (setccR8NoRexEffect 0x1019c7 3 1 false u8).components) ++
      (cmpR64R64Effect 0x1019ca 0 15 u9).components) ++
      (setccR8NoRexEffect 0x1019cd 3 0 (decide (cap < size + 16)) u10).components) ++
      (orR8R8NoRexEffect 0x1019d0 2 0 1 u11).components) ++
      (movR32Imm32Effect 0x1019d2 5 0 1 u12).components) ++
      (jccEffect 0x1019d7 2 5 ((0x14 : BitVec 8).signExtend 64) u13).components,
      c.isMem = false := by
    simp [jccEffect, Component.isMem]
  have hagr := (((((((e7.agrees.trans e8.agrees).trans e9.agrees).trans e10.agrees).trans
    e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees)
  have hsp14 : stackPtr u14 = stackPtr initial - BitVec.ofNat 64 104 :=
    sp_keep hagr (by notin) hsp6
  refine ⟨_, u14, a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans
    (a8.trans (a9.trans (a10.trans (a11.trans (a12.trans (a13.trans a14)))))))))))),
    T14, ?_, hsp14, ?_, ?_, ?_⟩
  · rw [e14.rip]
    simp only [jccEffect, branchEffect, hc13, htgt14]
    by_cases h : size + 16 ≤ cap
    · simp [h, show ¬ cap < size + 16 by omega]
    · simp [h, show cap < size + 16 by omega]
  · exact (e14.agrees.read (by notin)).trans e13.writes
  · exact (mem_keep hagr hregs _).trans (w6.trans
      (((e4.agrees.trans e5.agrees).read (by simp [storeAddrAt])).trans (v3.trans
        (mem_keep (e1.agrees.trans e2.agrees) (by simp [jccEffect, Component.isMem]) _))))
  · exact (mem_keep hagr hregs _).trans (k6.trans (w5.trans (v4.trans
      (mem_keep ((e1.agrees.trans e2.agrees).trans e3.agrees)
        (by simp [jccEffect, Component.isMem]) _))))


def retCs2 (T : BitVec 64) : List Component := [.reg 0, .reg 1, .flags, .rip, .mem T 16]

theorem idx_addr {u : RamState} {R : BitVec 64} {n : Nat} (h14 : rd u 14 = R)
    (h3 : rd u 3 = BitVec.ofNat 64 n) (x : BitVec 64) :
    (AddrMode.sib 14 (some 3) 0 (.d8 8)).addr u x = R + BitVec.ofNat 64 n + BitVec.ofNat 64 8 := by
  simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
  rw [show ((14 : BitVec 4).setWidth 5) = (14 : BitVec 5) from rfl,
    show ((3 : BitVec 4).setWidth 5) = (3 : BitVec 5) from rfl]
  change rd u 14 + (rd u 3 <<< (0 : BitVec 2).toNat) + (8 : BitVec 8).signExtend 64 = _
  rw [h14, h3, show (0 : BitVec 2).toNat = 0 from rfl, BitVec.shiftLeft_zero,
    show (8 : BitVec 8).signExtend 64 = BitVec.ofNat 64 8 from by decide]

theorem idx_addr0 {u : RamState} {R : BitVec 64} {n : Nat} (h14 : rd u 14 = R)
    (h3 : rd u 3 = BitVec.ofNat 64 n) (x : BitVec 64) :
    (AddrMode.sib 14 (some 3) 0 .none).addr u x = R + BitVec.ofNat 64 n := by
  simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
  rw [show ((14 : BitVec 4).setWidth 5) = (14 : BitVec 5) from rfl,
    show ((3 : BitVec 4).setWidth 5) = (3 : BitVec 5) from rfl]
  change rd u 14 + (rd u 3 <<< (0 : BitVec 2).toNat) + 0 = _
  rw [h14, h3, show (0 : BitVec 2).toNat = 0 from rfl, BitVec.shiftLeft_zero]
  exact BitVec.add_zero _

theorem tag_toNat {T : BitVec 64} (hT : T.toNat + 16 < 2 ^ 32) {i : Nat} (hi : i < 16) :
    (T + BitVec.ofNat 64 i).toNat = T.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
  omega

theorem tag_writable {T : BitVec 64} {u : RamState} (hT : T.toNat + 16 < 2 ^ 32)
    (htab : T.toNat + 16 ≤ 0x1000 ∨ 0x2020 ≤ T.toNat)
    (hP : ∀ i < 16, (u.external[T + BitVec.ofNat 64 i]?).isSome) {d : Nat} (hd : d ≤ 8) :
    MemWritable u (T + BitVec.ofNat 64 d) 8 := by
  refine ⟨by rw [tag_toNat hT (by omega)]; omega, fun i hi => ?_, ?_⟩
  · rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact hP _ (by omega)
  · rw [tag_toNat hT (by omega)]; unfold PageTableEntriesApart; omega

theorem tag_apart {T : BitVec 64}
    (hprog : ∀ i < 16, ¬ InProgram (T + BitVec.ofNat 64 i)) {d : Nat} (hd : d ≤ 8)
    {p : BitVec 64} {len : Nat} (hp : ∀ j < len, InProgram (p + BitVec.ofNat 64 j)) :
    RangeApart (T + BitVec.ofNat 64 d) 8 p len := by
  intro i hi j hj he
  apply hprog (d + i) (by omega)
  rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, he]
  exact hp j hj

theorem tag_fits {T : BitVec 64} {cs : List Component} (hm : Component.mem T 16 ∈ cs)
    (hprog : ∀ i < 16, ¬ InProgram (T + BitVec.ofNat 64 i)) {d : Nat} (hd : d ≤ 8) :
    ∀ x, (Component.mem (T + BitVec.ofNat 64 d) 8).Covers x →
      (∃ c ∈ cs, c.Covers x) ∧ ¬ InProgram x := by
  rintro x ⟨i, hi, rfl⟩
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact ⟨⟨_, hm, d + i, by omega, rfl⟩, hprog _ (by omega)⟩

theorem ret_room [Machine.Bindings] {initial u : RamState} (hS : EntryStack initial)
    (hOut : ¬ InProgram (returnBoundary initial).rip) {T R : BitVec 64} {size : Nat}
    (T0 : GTrack (retCs2 T) u u) (hrip : u.RIP = 0x1019d9)
    (hsp : stackPtr u = stackPtr initial - BitVec.ofNat 64 104)
    (hP : RetPresent (stackPtr initial) u)
    (h14 : rd u 14 = R) (h3 : rd u 3 = BitVec.ofNat 64 size) (hTR : R + BitVec.ofNat 64 size = T)
    (hT : T.toNat + 16 < 2 ^ 32) (htab : T.toNat + 16 ≤ 0x1000 ∨ 0x2020 ≤ T.toNat)
    (hTP : ∀ i < 16, (u.external[T + BitVec.ofNat 64 i]?).isSome)
    (hprog : ∀ i < 16, ¬ InProgram (T + BitVec.ofNat 64 i)) :
    ∃ n v, Advances (returnBoundary initial) n u v ∧ GTrack (retCs2 T) u v ∧
      v.RIP = 0x1019ed ∧ stackPtr v = stackPtr initial - BitVec.ofNat 64 104 ∧
      rd v 0 = 0 ∧
      wd v T = wd u (stackPtr initial - BitVec.ofNat 64 104) ∧
      wd v (T + BitVec.ofNat 64 8) = wd u (stackPtr initial - BitVec.ofNat 64 96) := by
  have hroom := hS.room
  have htop := hS.top
  have hmem : Component.mem T 16 ∈ retCs2 T := by simp [retCs2]
  have hA1 : ∀ x, (AddrMode.sib 4 none 0 .none).addr u x =
      stackPtr initial - BitVec.ofNat 64 104 := rsp_addr0 hsp
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x1019d9 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 .none) (by decide) (by decide) (by decide))
    T0 (program_text_slice T0.code 0x19d9 4 (by decide +kernel))
    ⟨hrip, by rw [hA1]; exact ret_readable hroom htop hP (k := 104) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x19dd (by omega)) (by fits [retCs2])
  change (movR64M64Effect 0x1019d9 0 (.sib 4 none 0 .none) u).Holds u u1 at e1
  have hsp1 := sp_keep e1.agrees (by simp) hsp
  have v1 : rd u1 0 = wd u (stackPtr initial - BitVec.ofNat 64 104) := by
    have := e1.writes
    simp only [movR64M64Effect, hA1] at this
    exact this
  have hA2 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x8)).addr u1 x =
      stackPtr initial - BitVec.ofNat 64 96 := rsp_addr hsp1 0x8 8 rfl (by omega)
  obtain ⟨u2, a2, T2, e2⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x1019dd 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide))
    T1 (program_text_slice T1.code 0x19dd 5 (by decide +kernel))
    ⟨e1.rip, by rw [hA2]; exact ret_readable hroom htop (hP.of_agrees T1.agrees) (k := 96) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x19e2 (by omega)) (by fits [retCs2])
  change (movR64M64Effect 0x1019dd 1 (.sib 4 none 0 (.d8 0x8)) u1).Holds u1 u2 at e2
  have v2 : rd u2 1 = wd u (stackPtr initial - BitVec.ofNat 64 96) := by
    have := e2.writes
    simp only [movR64M64Effect, hA2] at this
    exact this.trans (mem_keep e1.agrees (by simp [Component.isMem]) _)
  have h14' : rd u2 14 = R := by
    rw [← h14]; exact (e1.agrees.trans e2.agrees).read (by simp)
  have h3' : rd u2 3 = BitVec.ofNat 64 size := by
    rw [← h3]; exact (e1.agrees.trans e2.agrees).read (by simp)
  have hA3 : ∀ x, (AddrMode.sib 14 (some 3) 0 (.d8 8)).addr u2 x = T + BitVec.ofNat 64 8 := by
    intro x; rw [idx_addr h14' h3', hTR]
  have hTP2 : ∀ i < 16, (u2.external[T + BitVec.ofNat 64 i]?).isSome :=
    fun i hi => (e1.agrees.trans e2.agrees).grow _ (hTP i hi)
  obtain ⟨u3, a3, T3, e3⟩ := gtrack_step
    (mov_m64_r64_effect_step 0x1019e2 0x49 (by unfold RexWPrefix; decide) 1
      (.sib 14 (some 3) 0 (.d8 8)) (by decide) (by decide) (by decide))
    T2 (program_text_slice T2.code 0x19e2 5 (by decide +kernel))
    ⟨e2.rip,
      by simp only [storeAddrAt, hA3]; exact tag_writable hT htab hTP2 (by omega),
      by simp only [storeAddrAt, hA3]
         exact tag_apart hprog (by omega) (code_inProgram 0x19e2 5 (by omega))⟩
    (code_ne_boundary hOut 0x19e7 (by omega))
    (by
      fits [retCs2, hA3]
      exact .inr ⟨rfl, tag_fits hmem hprog (by omega)⟩)
  change (movM64R64Effect 0x1019e2 1 (.sib 14 (some 3) 0 (.d8 8)) u2).Holds u2 u3 at e3
  have w3 : wd u3 (T + BitVec.ofNat 64 8) = rd u2 1 := by
    rw [← hA3 (0x1019e2 + BitVec.ofNat 64 5)]
    exact e3.writes
  have h14'' : rd u3 14 = R := by rw [← h14']; exact e3.agrees.read (by simp)
  have h3'' : rd u3 3 = BitVec.ofNat 64 size := by rw [← h3']; exact e3.agrees.read (by simp)
  have hA4 : ∀ x, (AddrMode.sib 14 (some 3) 0 .none).addr u3 x = T := by
    intro x; rw [idx_addr0 h14'' h3'', hTR]
  have hTP3 : ∀ i < 16, (u3.external[T + BitVec.ofNat 64 i]?).isSome :=
    fun i hi => e3.agrees.grow _ (hTP2 i hi)
  obtain ⟨u4, a4, T4, e4⟩ := gtrack_step
    (mov_m64_r64_effect_step 0x1019e7 0x49 (by unfold RexWPrefix; decide) 0
      (.sib 14 (some 3) 0 .none) (by decide) (by decide) (by decide))
    T3 (program_text_slice T3.code 0x19e7 4 (by decide +kernel))
    ⟨e3.rip,
      by simp only [storeAddrAt, hA4]
         have := tag_writable hT htab hTP3 (d := 0) (by omega)
         rwa [BitVec.add_zero] at this,
      by simp only [storeAddrAt, hA4]
         have := tag_apart hprog (d := 0) (by omega) (code_inProgram 0x19e7 4 (by omega))
         rwa [BitVec.add_zero] at this⟩
    (code_ne_boundary hOut 0x19eb (by omega))
    (by
      fits [retCs2, hA4]
      refine .inr ⟨rfl, ?_⟩
      have := tag_fits hmem hprog (d := 0) (by omega)
      rwa [BitVec.add_zero] at this)
  change (movM64R64Effect 0x1019e7 0 (.sib 14 (some 3) 0 .none) u3).Holds u3 u4 at e4
  have w4 : wd u4 T = rd u3 0 := by
    rw [← hA4 (0x1019e7 + BitVec.ofNat 64 4)]
    exact e4.writes
  have k4 : wd u4 (T + BitVec.ofNat 64 8) = wd u3 (T + BitVec.ofNat 64 8) := by
    apply gload e4.agrees
    intro c hc i hi
    simp only [movM64R64Effect_components, storeAddrAt, hA4, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl
    · rintro ⟨j, hj, he⟩
      have := congrArg BitVec.toNat he
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, tag_toNat hT (by omega),
        tag_toNat hT (by omega)] at this
      omega
    · exact fun h => h
  obtain ⟨u5, a5, T5, e5⟩ := gtrack_step
    (xor_r32_r32_effect_step 0x1019eb 0xc0 (by decide))
    T4 (program_text_slice T4.code 0x19eb 2 (by decide +kernel))
    e4.rip (code_ne_boundary hOut 0x19ed (by omega)) (by fits [retCs2])
  change (xorR32R32Effect 0x1019eb 2 0 0 u4).Holds u4 u5 at e5
  have hagr := (e2.agrees.trans e3.agrees).trans (e4.agrees.trans e5.agrees)
  refine ⟨_, u5, a1.trans (a2.trans (a3.trans (a4.trans a5))), T5, e5.rip, ?_, ?_, ?_, ?_⟩
  · exact sp_keep (e1.agrees.trans hagr) (by simp [storeAddrAt]) hsp
  · rw [show rd u5 0 = _ from e5.writes]
    simp
  · exact (mem_keep e5.agrees (by simp [Component.isMem]) _).trans (w4.trans
      (((e2.agrees.trans e3.agrees).read (by simp [storeAddrAt])).trans v1))
  · exact (mem_keep e5.agrees (by simp [Component.isMem]) _).trans (k4.trans (w3.trans v2))

def retCs3 : List Component := [.reg 4, .flags, .rip, .reg 3, .reg 14, .reg 15]

theorem ret_tail [Machine.Bindings] {initial v : RamState} (hS : EntryStack initial)
    (hOut : ¬ InProgram (returnBoundary initial).rip)
    (hLow : (returnBoundary initial).rip.toNat < 2 ^ 32)
    (T0 : GTrack retCs3 v v) (hrip : v.RIP = 0x1019ed)
    (hsp : stackPtr v = stackPtr initial - BitVec.ofNat 64 104)
    (hP : RetPresent (stackPtr initial) v)
    (hret : wd v (stackPtr initial) = (returnBoundary initial).rip) :
    ∃ n fin, Returns (returnBoundary initial) n v fin ∧ ReadyToStep fin ∧
      AgreesExcept retCs3 v fin ∧
      rd fin 3 = wd v (stackPtr initial - BitVec.ofNat 64 24) ∧
      rd fin 14 = wd v (stackPtr initial - BitVec.ofNat 64 16) ∧
      rd fin 15 = wd v (stackPtr initial - BitVec.ofNat 64 8) := by
  have hroom := hS.room
  have htop := hS.top
  obtain ⟨w1, a1, T1, e1⟩ := gtrack_step
    (add_r64_imm8_effect_step 0x1019ed 0x48 0xc4 0x50 (by unfold RexWPrefix; decide)
      (by decide) (by decide))
    T0 (program_text_slice T0.code 0x19ed 4 (by decide +kernel))
    hrip (code_ne_boundary hOut 0x19f1 (by omega)) (by fits [retCs3])
  change (addR64Imm8Effect 0x1019ed 4 0x50 v).Holds v w1 at e1
  have hsp1 : stackPtr w1 = stackPtr initial - BitVec.ofNat 64 24 := by
    rw [stackPtr_eq_read, show (Operand.reg 4 : Operand 64).read w1 = _ from e1.writes,
      ← stackPtr_eq_read, hsp, show (0x50 : BitVec 8).signExtend 64 = BitVec.ofNat 64 80 from by
        decide]
    rw [show (104 : Nat) = 24 + 80 from rfl, ← sub_sub_ofNat, BitVec.sub_add_cancel]
  obtain ⟨w2, a2, T2, e2⟩ := gtrack_step
    (pop_r64_effect_step 0x1019f1 0x5b (by decide) (by decide))
    T1 (program_text_slice T1.code 0x19f1 1 (by decide +kernel))
    ⟨e1.rip, by rw [hsp1]; exact ret_readable hroom htop (hP.of_agrees T1.agrees) (k := 24) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x19f2 (by omega)) (by fits [retCs3])
  change (popR64Effect 0x1019f1 1 3 w1).Holds w1 w2 at e2
  have hsp2 : stackPtr w2 = stackPtr initial - BitVec.ofNat 64 16 := by
    have h := e2.writes.2
    change stackPtr w2 = stackPtr w1 + BitVec.ofNat 64 8 at h
    rw [h, hsp1, sub_add_ofNat _ (by omega)]
  obtain ⟨w3, a3, T3, e3⟩ := gtrack_step
    (pop_r64_rex_effect_step 0x1019f2 0x41 0x5e (by unfold RexPrefix; decide) (by decide)
      (by decide))
    T2 (program_text_slice T2.code 0x19f2 2 (by decide +kernel))
    ⟨e2.rip, by rw [hsp2]; exact ret_readable hroom htop (hP.of_agrees T2.agrees) (k := 16) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x19f4 (by omega)) (by fits [retCs3])
  change (popR64Effect 0x1019f2 2 14 w2).Holds w2 w3 at e3
  have hsp3 : stackPtr w3 = stackPtr initial - BitVec.ofNat 64 8 := by
    have h := e3.writes.2
    change stackPtr w3 = stackPtr w2 + BitVec.ofNat 64 8 at h
    rw [h, hsp2, sub_add_ofNat _ (by omega)]
  obtain ⟨w4, a4, T4, e4⟩ := gtrack_step
    (pop_r64_rex_effect_step 0x1019f4 0x41 0x5f (by unfold RexPrefix; decide) (by decide)
      (by decide))
    T3 (program_text_slice T3.code 0x19f4 2 (by decide +kernel))
    ⟨e3.rip, by rw [hsp3]; exact ret_readable hroom htop (hP.of_agrees T3.agrees) (k := 8) (by omega) (by omega)⟩
    (code_ne_boundary hOut 0x19f6 (by omega)) (by fits [retCs3])
  change (popR64Effect 0x1019f4 2 15 w3).Holds w3 w4 at e4
  have hsp4 : stackPtr w4 = stackPtr initial := by
    have h := e4.writes.2
    change stackPtr w4 = stackPtr w3 + BitVec.ofNat 64 8 at h
    rw [h, hsp3, BitVec.sub_add_cancel]
  have hmem : ∀ a, wd w4 a = wd v a := by
    intro a
    exact (mem_keep e4.agrees (by simp [Component.isMem]) a).trans
      ((mem_keep e3.agrees (by simp [Component.isMem]) a).trans
      ((mem_keep e2.agrees (by simp [Component.isMem]) a).trans
      (mem_keep e1.agrees (by simp [Component.isMem]) a)))
  have hP4 := hP.of_agrees T4.agrees
  obtain ⟨fin, hstep, hready, e5⟩ := ret_effect_step 0x1019f6 w4 T4.ready
    (program_text_slice T4.code 0x19f6 1 (by decide +kernel))
    ⟨⟨e4.rip, by
        rw [hsp4]
        have := ret_readable hroom htop hP4 (k := 0) (n := 8) (by omega) (by omega)
        simpa using this⟩,
      by
        change (wd w4 (stackPtr w4)).toNat < 2 ^ 32
        rw [hsp4, hmem, hret]; exact hLow⟩
  change (retEffect w4).Holds w4 fin at e5
  have hRet : Returns (returnBoundary initial) 1 w4 fin := by
    apply Returns.of_step hstep
    · rw [e5.rip]
      change wd w4 (stackPtr w4) = _
      rw [hsp4, hmem, hret]
    · exact (show (Operand.reg 4 : Operand 64).read fin = stackPtr w4 + 8 from e5.writes).trans
        (by rw [hsp4]; rfl)
  refine ⟨_, fin, (a1.trans (a2.trans (a3.trans a4))).returns hRet, hready,
    (T4.agrees.trans e5.agrees).mono (by
      intro c hc
      simp only [List.mem_append, retEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | rfl | rfl
      · exact hc
      all_goals simp [retCs3]), ?_, ?_, ?_⟩
  · have h := e2.writes.1
    change rd w2 3 = wd w1 (stackPtr w1) at h
    rw [hsp1] at h
    exact ((e5.agrees.read (r := 3) (by simp)).trans
      ((e3.agrees.trans e4.agrees).read (r := 3) (by simp))).trans
      (h.trans (mem_keep e1.agrees (by simp [Component.isMem]) _))
  · have h := e3.writes.1
    change rd w3 14 = wd w2 (stackPtr w2) at h
    rw [hsp2] at h
    exact ((e5.agrees.read (r := 14) (by simp)).trans (e4.agrees.read (r := 14) (by simp))).trans
      (h.trans (mem_keep (e1.agrees.trans e2.agrees) (by simp [Component.isMem]) _))
  · have h := e4.writes.1
    change rd w4 15 = wd w3 (stackPtr w3) at h
    rw [hsp3] at h
    exact (e5.agrees.read (r := 15) (by simp)).trans
      (h.trans (mem_keep ((e1.agrees.trans e2.agrees).trans e3.agrees)
        (by simp [Component.isMem]) _))


theorem foldlM_push {ε : Type} {f : ByteArray → Nat → Except ε ByteArray} {bytes : ByteArray}
    (hf : ∀ acc k (hk : k < bytes.size), f acc k = .ok (acc.push bytes[k])) :
    ∀ k, k ≤ bytes.size → (List.range k).foldlM f ByteArray.empty =
      .ok ⟨bytes.data.extract 0 k⟩ := by
  intro k
  induction k with
  | zero =>
    intro _
    show Except.ok ByteArray.empty = _
    congr 1
    apply ByteArray.ext
    show (#[] : Array UInt8) = _
    simp
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.foldlM_append, ih (by omega)]
    show List.foldlM f ⟨bytes.data.extract 0 k⟩ [k] = _
    simp only [List.foldlM_cons, List.foldlM_nil]
    rw [hf _ k (by omega)]
    show Except.ok (ByteArray.push ⟨bytes.data.extract 0 k⟩ bytes[k]) = _
    congr 1
    have hk' : k < bytes.data.size := hk
    rw [Array.extract_succ_right (by omega) hk']
    rfl

theorem readRegion_of_hasBytes {final : RamState} {r : MemoryRegion} {bytes : ByteArray}
    (h : r.HasBytes final.external bytes) : readRegion final r = .ok bytes := by
  obtain ⟨hlen, hb⟩ := h
  change bytes.size = r.size at hlen
  unfold readRegion
  rw [← hlen]
  rw [foldlM_push (bytes := bytes) (fun acc k hk => by simp only [hb ⟨k, hk⟩]) _ (Nat.le_refl _)]
  congr 1
  show ByteArray.mk (bytes.data.extract 0 bytes.data.size) = bytes
  rw [Array.extract_size]

theorem frame_widen {a b : RamState} {n m : Nat} {R1 : Vector MemoryRegion n}
    {R2 : Vector MemoryRegion m} (h : MemoryWriteFrame a b R1)
    (hsub : ∀ r ∈ R1, ∀ x, r.Contains x → ∃ r' ∈ R2, r'.Contains x) :
    MemoryWriteFrame a b R2 := by
  intro addr hout
  apply h addr
  intro r hr hc
  obtain ⟨r', hr', hc'⟩ := hsub r hr _ hc
  exact hout r' hr' hc'

theorem wd_congr {u v : RamState} {a : BitVec 64}
    (h : ∀ i < 8, v.external[a + BitVec.ofNat 64 i]? = u.external[a + BitVec.ofNat 64 i]?) :
    wd v a = wd u a := by
  apply memLoad_congr
  intro i hi
  change i < 8 at hi
  simp only [memByte]
  congr 1
  exact h i hi

theorem hasBytes_isSome {r : MemoryRegion} {m : Ram} {bytes : ByteArray} (h : r.HasBytes m bytes)
    {i : Nat} (hi : i < r.size) : (m[BitVec.ofNat 64 (r.start + i)]?).isSome := by
  have h1 : bytes.size = r.size := h.1
  rw [h.2 ⟨i, by omega⟩]
  rfl

theorem ofNat_stack {I : BitVec 64} (hroom : 1104 ≤ I.toNat) (htop : I.toNat + 8 < 2 ^ 32)
    {k i : Nat} (hk : k ≤ 104) (hi : i < k + 8) :
    BitVec.ofNat 64 (I.toNat - k + i) = I - BitVec.ofNat 64 k + BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  rw [slot_toNat (by omega) htop hi, BitVec.toNat_ofNat]
  omega

theorem ret_common [bindings : Machine.Bindings] {initial s t fin : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    {CS : List Component}
    (hCall : ValidCall encryptInPlace initial [key, nonce, associatedData, plaintext])
    (hS : EntryStack initial) (hAt : AtCoreCall initial s)
    (hPost : CorePost s t key nonce associatedData plaintext (initial.regValue .rcx))
    (hagT : AgreesExcept CS t fin) (hready : ReadyToStep fin)
    (hdf : Component.df ∉ CS) (h5 : Component.reg 5 ∉ CS) (h12 : Component.reg 12 ∉ CS)
    (h13 : Component.reg 13 ∉ CS)
    (hmemCS : ∀ c ∈ CS, ∀ a, c.Covers a →
      (outputRegion encryptInPlace initial).Contains a.toNat ∨
        (Stack.region initial encryptInPlace.minStackBytes).Contains a.toNat)
    (hrbx : fin.regValue .rbx = initial.regValue .rbx)
    (hr14 : fin.regValue .r14 = initial.regValue .r14)
    (hr15 : fin.regValue .r15 = initial.regValue .r15) :
    SupportedIntegerMachineState bindings.processor fin ∧
      MachineRamUnitStrideDecodable bindings fin ∧
      CalleeSavedRegistersUnchanged initial fin ∧
      DirectionFlagUnset fin ∧
      MemoryWriteFrame initial fin
        #v[outputRegion encryptInPlace initial,
          Stack.region initial encryptInPlace.minStackBytes] := by
  have hroom := hS.room
  have htop := hS.top
  obtain ⟨cap, ⟨-, hcapW⟩, hcapLe⟩ := hCall.capacityArgumentCoversMessage (.stack 0) rfl
  obtain ⟨-, -, -, hBufSt, -, -, -, -⟩ := entry_sep hCall hS hcapW
  obtain ⟨-, -, -, hPtLen, -⟩ := hCall.lengthArgumentsMatchInputs
  have hPtLen' : (initial.regValue .r9).toNat = plaintext.size := hPtLen
  have hsizeLe : plaintext.size ≤ cap.toNat := by rw [← hPtLen']; exact hcapLe
  have hSt : Stack.region initial encryptInPlace.minStackBytes =
      ⟨(stackPtr initial).toNat - 1104, 1112⟩ := stack_region_eq _ _ hroom
  have hcs := hPost.calleeSaved
  refine ⟨⟨hready.cpu, SupportedSSE.of_agreesExcept hagT hPost.machine.sse, hready.memory,
      hready.ready⟩,
    ⟨hready.smrr, hready.memoryType, hPost.environment.stringStride, hready.features.lzcnt⟩,
    ?_, hagT.directionFlagClear hdf hPost.directionFlagUnset, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hrbx
    · have e : (Operand.reg 5 : Operand 64).read fin = (Operand.reg 5 : Operand 64).read t :=
        hagT.read h5
      rw [show fin.regValue .rbp = t.regValue .rbp from e,
        hcs .rbp (by simp), hAt.rbp]
    · have e : (Operand.reg 12 : Operand 64).read fin = (Operand.reg 12 : Operand 64).read t :=
        hagT.read h12
      rw [show fin.regValue .r12 = t.regValue .r12 from e,
        hcs .r12 (by simp), hAt.r12]
    · have e : (Operand.reg 13 : Operand 64).read fin = (Operand.reg 13 : Operand 64).read t :=
        hagT.read h13
      rw [show fin.regValue .r13 = t.regValue .r13 from e,
        hcs .r13 (by simp), hAt.r13]
    · exact hr14
    · exact hr15
  · have hOutC : ∀ x, (messageRegion (initial.regValue .rcx) plaintext.size).Contains x →
        (outputRegion encryptInPlace initial).Contains x := by
      intro x hx
      have hO : outputRegion encryptInPlace initial = ⟨(initial.regValue .rcx).toNat,
          if hasRoom encryptInPlace initial then plaintext.size + 16 else plaintext.size⟩ := by
        unfold outputRegion registerRegion
        rw [show messageBytes encryptInPlace initial = plaintext.size from hPtLen']
        rfl
      simp only [messageRegion, MemoryRegion.Contains] at hx
      rw [hO]
      simp only [MemoryRegion.Contains]
      split <;> omega
    have hspS : (s.regValue .rsp).toNat = (stackPtr initial).toNat - 112 := by
      rw [show s.regValue .rsp = stackPtr s from rfl, hAt.rsp]
      exact slot_toNat0 (k := 112) (by omega)
    have hrdiS : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 73 := by
      rw [hAt.rdi, hAt.rsp, show (0x27 : BitVec 64) = BitVec.ofNat 64 39 from rfl,
        show (112 : BitVec 64) = BitVec.ofNat 64 112 from rfl, sub_add_ofNat _ (by omega)]
      exact slot_toNat0 (k := 73) (by omega)
    have f1 := frame_widen (R2 := #v[outputRegion encryptInPlace initial,
        Stack.region initial encryptInPlace.minStackBytes]) hAt.frame (by
      intro r hr x hx
      simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      refine ⟨Stack.region initial encryptInPlace.minStackBytes, by simp, ?_⟩
      rw [hSt]
      simp only [wrapperFrame, wrapperFrameBytes, MemoryRegion.Contains] at hx ⊢
      omega)
    have f2 := frame_widen (R2 := #v[outputRegion encryptInPlace initial,
        Stack.region initial encryptInPlace.minStackBytes]) hPost.frame (by
      intro r hr x hx
      simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · refine ⟨Stack.region initial encryptInPlace.minStackBytes, by simp, ?_⟩
        rw [hSt]
        simp only [resultRegion, registerRegion, resultBytes, MemoryRegion.Contains, hrdiS] at hx ⊢
        omega
      · exact ⟨outputRegion encryptInPlace initial, by simp, hOutC x hx⟩
      · refine ⟨Stack.region initial encryptInPlace.minStackBytes, by simp, ?_⟩
        rw [hSt]
        have hx' : (s.regValue .rsp).toNat - coreStackBytes ≤ x ∧
            x < (s.regValue .rsp).toNat + 8 := by
          simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains] at hx
          omega
        rw [hspS] at hx'
        have h992 : coreStackBytes = 992 := rfl
        simp only [MemoryRegion.Contains]
        omega)
    have f3 := hagT.memoryWriteFrame (regions := #v[outputRegion encryptInPlace initial,
        Stack.region initial encryptInPlace.minStackBytes]) (by
      intro c hc a hcov
      rcases hmemCS c hc a hcov with h | h
      · exact ⟨outputRegion encryptInPlace initial, by simp, h⟩
      · exact ⟨Stack.region initial encryptInPlace.minStackBytes, by simp, h⟩)
    exact memoryWriteFrame_trans (memoryWriteFrame_trans f1 f2) f3


theorem saved_slot {initial s : RamState} (hS : EntryStack initial) {k : Nat} {v : BitVec 64}
    (h : (savedSlot initial k).Word64At s.external v) (h1 : 8 ≤ k) (h2 : k ≤ 24) :
    wd s (stackPtr initial - BitVec.ofNat 64 k) = v := by
  have hroom := hS.room
  have := word64At_memLoad h
  rw [show BitVec.ofNat 64 (savedSlot initial k).start = stackPtr initial - BitVec.ofNat 64 k from by
    apply BitVec.eq_of_toNat_eq
    simp only [savedSlot]
    rw [BitVec.toNat_ofNat, slot_toNat0 (by omega)]
    have := (stackPtr initial).isLt
    omega] at this
  exact this

theorem ret_finish [bindings : Machine.Bindings] {initial s t v : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    {CS : List Component} {n : Nat}
    (hCall : ValidCall encryptInPlace initial [key, nonce, associatedData, plaintext])
    (hS : EntryStack initial) (hAt : AtCoreCall initial s)
    (hPost : CorePost s t key nonce associatedData plaintext (initial.regValue .rcx))
    (hOutside : ¬ InProgram (returnBoundary initial).rip)
    (hLow : (returnBoundary initial).rip.toNat < 2 ^ 32)
    (hrun : Advances (returnBoundary initial) n t v) (hag : AgreesExcept CS t v)
    (hready : ReadyToStep v) (hcode : CodeIn Extracted.programImage v)
    (hrip : v.RIP = 0x1019ed) (hsp : stackPtr v = stackPtr initial - BitVec.ofNat 64 104)
    (hP : RetPresent (stackPtr initial) v)
    (hret : wd v (stackPtr initial) = (returnBoundary initial).rip)
    (hsv : ∀ k, 8 ≤ k → k ≤ 24 →
      wd v (stackPtr initial - BitVec.ofNat 64 k) = wd s (stackPtr initial - BitVec.ofNat 64 k))
    (hdf : Component.df ∉ CS) (h5 : Component.reg 5 ∉ CS) (h12 : Component.reg 12 ∉ CS)
    (h13 : Component.reg 13 ∉ CS)
    (hmemCS : ∀ c ∈ CS, ∀ a, c.Covers a →
      (outputRegion encryptInPlace initial).Contains a.toNat ∨
        (Stack.region initial encryptInPlace.minStackBytes).Contains a.toNat) :
    ∃ fuel final, Returns (returnBoundary initial) fuel t final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion encryptInPlace initial,
          Stack.region initial encryptInPlace.minStackBytes] ∧
      final.regValue .rax = v.regValue .rax ∧ final.external = v.external := by
  obtain ⟨m, fin, hRet, hreadyF, hagF, hF3, hF14, hF15⟩ :=
    ret_tail hS hOutside hLow ⟨hready, hcode, AgreesExcept.refl _ _⟩ hrip hsp hP hret
  have hagT := hag.trans hagF
  have hnot : ∀ c, c ∉ CS → c ∉ retCs3 → c ∉ CS ++ retCs3 := by
    intro c h1 h2 h
    rcases List.mem_append.mp h with h | h
    · exact h1 h
    · exact h2 h
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := ret_common hCall hS hAt hPost hagT hreadyF
    (hnot _ hdf (by simp [retCs3])) (hnot _ h5 (by simp [retCs3]))
    (hnot _ h12 (by simp [retCs3])) (hnot _ h13 (by simp [retCs3]))
    (by
      intro c hc a hcov
      rcases List.mem_append.mp hc with hc | hc
      · exact hmemCS c hc a hcov
      · simp only [retCs3, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hcov.elim)
    ((hF3.trans (hsv 24 (by omega) (by omega))).trans (saved_slot hS hAt.savedRbx (by omega)
      (by omega)))
    ((hF14.trans (hsv 16 (by omega) (by omega))).trans (saved_slot hS hAt.savedR14 (by omega)
      (by omega)))
    ((hF15.trans (hsv 8 (by omega) (by omega))).trans (saved_slot hS hAt.savedR15 (by omega)
      (by omega)))
  refine ⟨_, fin, hrun.returns hRet, h₁, h₂, h₃, h₄, h₅, ?_, ?_⟩
  · have e : (Operand.reg 0 : Operand 64).read fin = (Operand.reg 0 : Operand 64).read v :=
      hagF.read (by simp [retCs3])
    exact e
  · exact hagF.external (fun c hc x => by
      simp only [retCs3, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact fun h => h)


theorem core_return [bindings : Machine.Bindings] {initial s t : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    (hCall : ValidCall encryptInPlace initial [key, nonce, associatedData, plaintext])
    (hAt : AtCoreCall initial s)
    (hOutside : ¬ InProgram (returnBoundary initial).rip)
    (hPost : CorePost s t key nonce associatedData plaintext (initial.regValue .rcx)) :
    ∃ fuel final, Returns (returnBoundary initial) fuel t final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion encryptInPlace initial,
          Stack.region initial encryptInPlace.minStackBytes] ∧
      (if hasRoom encryptInPlace initial then
        SuccessfulStatus final ∧
        readOutput encryptInPlace initial final =
          .ok (AEAD.encryptWithTag associatedData key nonce plaintext)
      else
        FailureStatus final aeadErrorStatus ∧
        readOutput encryptInPlace initial final =
          .ok (AEAD.encryptWithoutTag associatedData key nonce plaintext)) := by
  have hS := entry_stack hCall
  have hroom := hS.room
  have htop := hS.top
  obtain ⟨cap, ⟨-, hcapW⟩, hcapLe⟩ := hCall.capacityArgumentCoversMessage (.stack 0) rfl
  obtain ⟨-, -, -, hBufSt, -, -, -, hAvBuf⟩ := entry_sep hCall hS hcapW
  obtain ⟨-, -, -, hPtLen, -⟩ := hCall.lengthArgumentsMatchInputs
  have hPtLen' : (initial.regValue .r9).toNat = plaintext.size := hPtLen
  have hsizeLe : plaintext.size ≤ cap.toNat := by rw [← hPtLen']; exact hcapLe
  have hOutIn := hCall.outputInMemory rfl
  have hbuf : bufferRegion encryptInPlace initial =
      ⟨(initial.regValue .rcx).toNat, cap.toNat⟩ := by
    simp only [bufferRegion, bufferBytes, encryptInPlace, argumentValue, hcapW.2,
      registerRegion] <;> rfl
  rw [hbuf] at hOutIn
  have hRB : (initial.regValue .rcx).toNat + cap.toNat < 2 ^ 32 := hOutIn.1
  have hsize32 : plaintext.size < 2 ^ 32 := by omega
  have hRoomIff : hasRoom encryptInPlace initial = decide (plaintext.size + 16 ≤ cap.toNat) := by
    unfold hasRoom
    rw [show bufferBytes encryptInPlace initial = cap.toNat by
        simp only [bufferBytes, encryptInPlace, argumentValue, hcapW.2] <;> rfl,
      show messageBytes encryptInPlace initial = plaintext.size from hPtLen']
    rfl
  have hO : outputRegion encryptInPlace initial = ⟨(initial.regValue .rcx).toNat,
      if hasRoom encryptInPlace initial then plaintext.size + 16 else plaintext.size⟩ := by
    unfold outputRegion registerRegion
    rw [show messageBytes encryptInPlace initial = plaintext.size from hPtLen']
    rfl
  have hSt : Stack.region initial encryptInPlace.minStackBytes =
      ⟨(stackPtr initial).toNat - 1104, 1112⟩ := stack_region_eq _ _ hroom
  have hcs := hPost.calleeSaved
  have hspS : stackPtr s = stackPtr initial - BitVec.ofNat 64 112 := hAt.rsp
  have hspT : stackPtr t = stackPtr initial - BitVec.ofNat 64 104 := by
    rw [hPost.rsp, hspS, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
      sub_add_ofNat _ (by omega)]
  have hripT : t.RIP = 0x10199f := hPost.rip.trans hAt.returnAddress
  have hrspS : (s.regValue .rsp).toNat = (stackPtr initial).toNat - 112 := by
    rw [show s.regValue .rsp = stackPtr s from rfl, hspS]
    exact slot_toNat0 (k := 112) (by omega)
  have hrdiS : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 73 := by
    rw [hAt.rdi, hAt.rsp, show (0x27 : BitVec 64) = BitVec.ofNat 64 39 from rfl,
      show (112 : BitVec 64) = BitVec.ofNat 64 112 from rfl, sub_add_ofNat _ (by omega)]
    exact slot_toNat0 (k := 73) (by omega)
  have h992 : coreStackBytes = 992 := rfl
  have hts : ∀ a : BitVec 64, ¬ (resultRegion s).Contains a.toNat →
      ¬ (messageRegion (initial.regValue .rcx) plaintext.size).Contains a.toNat →
      ¬ (Stack.region s coreStackBytes).Contains a.toNat → t.external[a]? = s.external[a]? := by
    intro a h1 h2 h3
    apply hPost.frame a
    intro r hr hc
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h1 hc
    · exact h2 hc
    · exact h3 hc
  have hnotRes : ∀ x, ¬ ((stackPtr initial).toNat - 73 ≤ x ∧ x < (stackPtr initial).toNat - 56) →
      ¬ (resultRegion s).Contains x := by
    intro x hx hc
    simp only [resultRegion, registerRegion, resultBytes, MemoryRegion.Contains, hrdiS] at hc
    omega
  have hnotCore : ∀ x, (stackPtr initial).toNat - 104 ≤ x →
      ¬ (Stack.region s coreStackBytes).Contains x := by
    intro x hx hc
    simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains] at hc
    rw [hrspS] at hc
    omega
  have hnotMsgSt : ∀ x, (stackPtr initial).toNat - 1104 ≤ x → x < (stackPtr initial).toNat + 8 →
      ¬ (messageRegion (initial.regValue .rcx) plaintext.size).Contains x := by
    intro x h1 h2 hc
    simp only [messageRegion, MemoryRegion.Contains] at hc
    exact hBufSt x (by simp only [MemoryRegion.Contains]; omega)
      (by simp only [MemoryRegion.Contains]; omega)
  have hsP : ∀ a : BitVec 64, (stackPtr initial).toNat - 1104 ≤ a.toNat →
      a.toNat < (stackPtr initial).toNat + 8 → (s.external[a]?).isSome :=
    fun a h1 h2 => hAt.grows a (hS.allocated a h1 h2)
  have hresB : ∀ i < 17,
      (t.external[stackPtr initial - BitVec.ofNat 64 73 + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    by_cases h0 : i = 0
    · subst h0
      have := hasBytes_isSome hPost.resultOk (i := 0) (by simp)
      simp only at this
      rwa [hrdiS, ofNat_stack hroom htop (k := 73) (by omega) (by omega)] at this
    · have := hasBytes_isSome hPost.tag (i := i - 1) (by simp only; omega)
      simp only at this
      rw [hrdiS, show (stackPtr initial).toNat - 73 + 1 + (i - 1) =
        (stackPtr initial).toNat - 73 + i by omega,
        ofNat_stack hroom htop (k := 73) (by omega) (by omega)] at this
      exact this
  have hPT : RetPresent (stackPtr initial) t := by
    intro j hj
    have ha : (stackPtr initial - BitVec.ofNat 64 104 + BitVec.ofNat 64 j).toNat =
        (stackPtr initial).toNat - 104 + j := slot_toNat (by omega) htop (by omega)
    by_cases hr : 31 ≤ j ∧ j < 48
    · have e : stackPtr initial - BitVec.ofNat 64 104 + BitVec.ofNat 64 j =
          stackPtr initial - BitVec.ofNat 64 73 + BitVec.ofNat 64 (j - 31) := by
        apply BitVec.eq_of_toNat_eq
        rw [ha, slot_toNat (by omega) htop (by omega)]
        omega
      rw [e]
      exact hresB _ (by omega)
    · rw [hts _ (hnotRes _ (by rw [ha]; omega)) (hnotMsgSt _ (by rw [ha]; omega) (by rw [ha]; omega))
        (hnotCore _ (by rw [ha]; omega))]
      exact hsP _ (by rw [ha]; omega) (by rw [ha]; omega)
  have hres : t.external[stackPtr initial - BitVec.ofNat 64 73]? = some 0 := by
    have := hPost.resultOk.2 ⟨0, by decide⟩
    simp only at this
    rw [hrdiS, ofNat_stack hroom htop (k := 73) (i := 0) (by omega) (by omega)] at this
    rw [show (ByteArray.mk #[0])[0] = 0 from rfl] at this
    simpa using this
  have hb3 : rd t 3 = BitVec.ofNat 64 plaintext.size := by
    have : t.regValue .rbx = initial.regValue .r9 := (hcs .rbx (by simp)).trans hAt.rbx
    rw [← hPtLen', BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact this
  have hcapS : s.regValue .r15 = cap := Except.ok.inj (hAt.r15.2.symm.trans hcapW.2)
  have hc15 : (rd t 15).toNat = cap.toNat := by
    have : t.regValue .r15 = cap := (hcs .r15 (by simp)).trans hcapS
    exact congrArg BitVec.toNat this
  have h14t : rd t 14 = initial.regValue .rcx := (hcs .r14 (by simp)).trans hAt.r14
  have hReadyT : ReadyToStep t := ReadyToStep.of_supported hPost.machine
    hPost.environment.smrr hPost.environment.memoryType
    (DecoderFeatures.of_supported hPost.machine hPost.environment.leadingZeroCount)
  obtain ⟨n1, u, aU, TU, hripU, hspU, hraxU, hwU1, hwU2⟩ :=
    ret_prefix (size := plaintext.size) (cap := cap.toNat) hS hOutside
      ⟨hReadyT, hPost.code, AgreesExcept.refl _ _⟩ hripT hspT hPT hres hsize32 hb3 hc15
  have hPU := hPT.of_agrees TU.agrees
  obtain ⟨raddr, hSlot, hLowA, -⟩ := hCall.returnAddress
  have hRip : (returnBoundary initial).rip = raddr := by
    have hRead := word64At_memLoad hSlot
    simp only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hRead
    exact hRead
  have hLow : (returnBoundary initial).rip.toNat < 2 ^ 32 := by
    rw [hRip]; exact hLowA
  have hretT : wd t (stackPtr initial) = (returnBoundary initial).rip := by
    show wd t (stackPtr initial) = wd initial (stackPtr initial)
    apply wd_congr
    intro i hi
    have ha : (stackPtr initial + BitVec.ofNat 64 i).toNat = (stackPtr initial).toNat + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [hts _ (hnotRes _ (by rw [ha]; omega)) (hnotMsgSt _ (by rw [ha]; omega) (by rw [ha]; omega))
      (hnotCore _ (by rw [ha]; omega))]
    apply hAt.frame
    intro r hr hc
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp only [wrapperFrame, wrapperFrameBytes, MemoryRegion.Contains] at hc
    rw [ha] at hc
    omega
  have hslotT : ∀ k, 8 ≤ k → k ≤ 24 → wd t (stackPtr initial - BitVec.ofNat 64 k) =
      wd s (stackPtr initial - BitVec.ofNat 64 k) := by
    intro k hk1 hk2
    apply wd_congr
    intro i hi
    have ha := slot_toNat (I := stackPtr initial) (k := k) (i := i) (by omega) htop (by omega)
    exact hts _ (hnotRes _ (by rw [ha]; omega)) (hnotMsgSt _ (by rw [ha]; omega) (by rw [ha]; omega))
      (hnotCore _ (by rw [ha]; omega))
  have hcov1 : ∀ a : BitVec 64, (∀ i < 8, (stackPtr initial).toNat - 88 ≤
      (a + BitVec.ofNat 64 i).toNat) →
      ∀ c ∈ retCs1 (stackPtr initial), ∀ i < 8, ¬ c.Covers (a + BitVec.ofNat 64 i) := by
    intro a ha c hc i hi
    simp only [retCs1, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact fun h => h
    rintro ⟨j, hj, he⟩
    have := congrArg BitVec.toNat he
    rw [slot_toNat (by omega) htop (by omega)] at this
    have := ha i hi
    omega
  have hkeep1 : ∀ k, k ≤ 24 → wd u (stackPtr initial - BitVec.ofNat 64 k) =
      wd t (stackPtr initial - BitVec.ofNat 64 k) := by
    intro k hk
    apply gload TU.agrees
    apply hcov1
    intro i hi
    rw [slot_toNat (by omega) htop (by omega)]
    omega
  have hkeep1I : wd u (stackPtr initial) = wd t (stackPtr initial) := by
    have := hkeep1 0 (by omega)
    simpa using this
  by_cases hR : plaintext.size + 16 ≤ cap.toNat
  ·
    have hRoom : hasRoom encryptInPlace initial = true := by
      rw [hRoomIff]; exact decide_eq_true hR
    have hripU' : u.RIP = 0x1019d9 := by rw [hripU]; simp [hR]
    obtain ⟨T, hTdef⟩ : ∃ T, T = initial.regValue .rcx + BitVec.ofNat 64 plaintext.size :=
      ⟨_, rfl⟩
    have hTn : T.toNat = (initial.regValue .rcx).toNat + plaintext.size := by
      rw [hTdef, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hTi : ∀ i < 16, (T + BitVec.ofNat 64 i).toNat = T.toNat + i :=
      fun i hi => tag_toNat (by omega) hi
    have hTbuf : ∀ i < 16, (⟨(initial.regValue .rcx).toNat, cap.toNat⟩ : MemoryRegion).Contains
        (T + BitVec.ofNat 64 i).toNat := by
      intro i hi
      simp only [MemoryRegion.Contains]
      rw [hTi i hi]
      omega
    have htab : T.toNat + 16 ≤ 0x1000 ∨ 0x2020 ≤ T.toNat := by
      refine Classical.byContradiction fun hc => ?_
      have hx : max T.toNat 0x1000 - T.toNat < 16 := by omega
      apply hAvBuf (T + BitVec.ofNat 64 (max T.toNat 0x1000 - T.toNat)) (hTbuf _ hx)
      right
      simp only [pageTables, MemoryRegion.Contains]
      rw [hTi _ hx]
      omega
    have hprog : ∀ i < 16, ¬ InProgram (T + BitVec.ofNat 64 i) :=
      fun i hi h => hAvBuf _ (hTbuf i hi) (.inl h)
    have hTt : ∀ i < 16, t.external[T + BitVec.ofNat 64 i]? = s.external[T + BitVec.ofNat 64 i]? := by
      intro i hi
      have hx := hTbuf i hi
      simp only [MemoryRegion.Contains] at hx
      apply hts
      · intro hc
        simp only [resultRegion, registerRegion, resultBytes, MemoryRegion.Contains, hrdiS] at hc
        exact hBufSt _ (by simp only [MemoryRegion.Contains]; omega)
          (by simp only [MemoryRegion.Contains]; omega)
      · intro hc
        simp only [messageRegion, MemoryRegion.Contains] at hc
        rw [hTi i hi] at hc
        omega
      · intro hc
        simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains] at hc
        rw [hrspS] at hc
        exact hBufSt _ (by simp only [MemoryRegion.Contains]; omega)
          (by simp only [MemoryRegion.Contains]; omega)
    have hTP : ∀ i < 16, (u.external[T + BitVec.ofNat 64 i]?).isSome := by
      intro i hi
      apply TU.agrees.grow
      rw [hTt i hi]
      apply hAt.grows
      obtain ⟨b, hb⟩ := hOutIn.2 _ (hTbuf i hi)
      simp [hb]
    have h14u : rd u 14 = initial.regValue .rcx :=
      (TU.agrees.read (by simp [retCs1])).trans h14t
    have h3u : rd u 3 = BitVec.ofNat 64 plaintext.size :=
      (TU.agrees.read (by simp [retCs1])).trans hb3
    obtain ⟨n2, v, aV, TV, hripV, hspV, hraxV, hwV1, hwV2⟩ :=
      ret_room hS hOutside ⟨TU.ready, TU.code, AgreesExcept.refl _ _⟩ hripU' hspU hPU h14u h3u
        hTdef.symm (by omega) htab hTP hprog
    have hcov2 : ∀ a : BitVec 64, (∀ i < 8, (stackPtr initial).toNat - 1104 ≤
        (a + BitVec.ofNat 64 i).toNat ∧ (a + BitVec.ofNat 64 i).toNat < (stackPtr initial).toNat + 8) →
        ∀ c ∈ retCs2 T, ∀ i < 8, ¬ c.Covers (a + BitVec.ofNat 64 i) := by
      intro a ha c hc i hi
      simp only [retCs2, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact fun h => h
      rintro ⟨j, hj, he⟩
      have h1 := hTbuf j hj
      rw [← he] at h1
      exact hBufSt _ h1 (by simp only [MemoryRegion.Contains]; have := ha i hi; omega)
    have hkeep2 : ∀ k, k ≤ 24 → wd v (stackPtr initial - BitVec.ofNat 64 k) =
        wd u (stackPtr initial - BitVec.ofNat 64 k) := by
      intro k hk
      apply gload TV.agrees
      apply hcov2
      intro i hi
      rw [slot_toNat (by omega) htop (by omega)]
      omega
    have hkeep2I : wd v (stackPtr initial) = wd u (stackPtr initial) := by
      have := hkeep2 0 (by omega)
      simpa using this
    have hag := TU.agrees.trans TV.agrees
    obtain ⟨fuel, fin, hRet, h₁, h₂, h₃, h₄, h₅, hrax, hext⟩ :=
      ret_finish hCall hS hAt hPost hOutside hLow (aU.trans aV) hag TV.ready TV.code hripV hspV
        (hPU.of_agrees TV.agrees) (hkeep2I.trans (hkeep1I.trans hretT))
        (fun k h1 h2 => (hkeep2 k h2).trans ((hkeep1 k h2).trans (hslotT k h1 h2)))
        (by simp [retCs1, retCs2]) (by simp [retCs1, retCs2]) (by simp [retCs1, retCs2])
        (by simp [retCs1, retCs2])
        (by
          intro c hc a hcov
          rcases List.mem_append.mp hc with hc | hc
          · simp only [retCs1, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl
            all_goals try exact hcov.elim
            right
            obtain ⟨j, hj, rfl⟩ := hcov
            rw [hSt]
            simp only [MemoryRegion.Contains]
            rw [slot_toNat (by omega) htop (by omega)]
            omega
          · simp only [retCs2, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl
            all_goals try exact hcov.elim
            left
            obtain ⟨j, hj, rfl⟩ := hcov
            rw [hO, hRoom]
            simp only [MemoryRegion.Contains, ite_true]
            rw [hTi j hj]
            omega)
    refine ⟨fuel, fin, hRet, h₁, h₂, h₃, h₄, h₅, ?_⟩
    simp only [hRoom, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · show (fin.regValue .rax).setWidth 32 = 0
      rw [hrax, show v.regValue .rax = 0 from hraxV]
      rfl
    have hct := hPost.ciphertext
    have htag := hPost.tag
    unfold readOutput AEAD.encryptWithTag
    apply readRegion_of_hasBytes
    rw [hO]
    simp only [hRoom, ↓reduceIte]
    cases hE : chacha20AeadEncrypt associatedData key nonce plaintext with
    | mk ct tg =>
    rw [hE] at hct htag
    simp only at hct htag ⊢
    obtain ⟨hctLen, hctB⟩ := hct
    change ct.size = plaintext.size at hctLen
    have htgLen : (ByteArray.mk tg.toArray).size = 16 := by simp [ByteArray.size]
    refine ⟨?_, fun i => ?_⟩
    · show (ct ++ ByteArray.mk tg.toArray).size = plaintext.size + 16
      rw [ByteArray.size_append, hctLen, htgLen]
    have hiB : i.val < plaintext.size + 16 := by
      have h1 := i.isLt
      have h2 : (ct ++ ByteArray.mk tg.toArray).size = plaintext.size + 16 := by
        rw [ByteArray.size_append, hctLen, htgLen]
      omega
    rw [show fin.external = v.external from hext]
    show v.external[BitVec.ofNat 64 ((initial.regValue .rcx).toNat + i.val)]? = _
    by_cases hi : i.val < plaintext.size
    · rw [ByteArray.getElem_append_left (by omega)]
      have hb := hctB ⟨i.val, by omega⟩
      simp only [messageRegion] at hb
      rw [← hb]
      apply hag.byte
      intro c hc hcov
      rcases List.mem_append.mp hc with hc | hc
      · simp only [retCs1, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcov.elim
        obtain ⟨j, hj, he⟩ := hcov
        have := congrArg BitVec.toNat he
        rw [slot_toNat (by omega) htop (by omega), BitVec.toNat_ofNat] at this
        exact hBufSt ((initial.regValue .rcx).toNat + i.val)
          (by simp only [MemoryRegion.Contains]; omega)
          (by simp only [MemoryRegion.Contains]; omega)
      · simp only [retCs2, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcov.elim
        obtain ⟨j, hj, he⟩ := hcov
        have := congrArg BitVec.toNat he
        rw [hTi j hj, BitVec.toNat_ofNat] at this
        omega
    · rw [ByteArray.getElem_append_right (by omega)]
      obtain ⟨j, hj, hij⟩ : ∃ j, j < 16 ∧ i.val = plaintext.size + j := ⟨i.val - plaintext.size, by omega, by omega⟩
      have hidx : i.val - ct.size = j := by omega
      have haddr : BitVec.ofNat 64 ((initial.regValue .rcx).toNat + i.val) =
          T + BitVec.ofNat 64 j := by
        apply BitVec.eq_of_toNat_eq
        rw [hTi j hj, BitVec.toNat_ofNat]
        omega
      rw [haddr]
      have hsomeV : ∀ o < 16, (v.external[T + BitVec.ofNat 64 o]?).isSome :=
        fun o ho => TV.agrees.grow _ (hTP o ho)
      have htb := htag.2 ⟨j, by rw [htgLen]; exact hj⟩
      simp only at htb
      rw [hrdiS] at htb
      have hget : (ByteArray.mk tg.toArray)[i.val - ct.size]'(by
          rw [hidx, htgLen]; exact hj) = (ByteArray.mk tg.toArray)[j]'(by rw [htgLen]; exact hj) := by
        congr 1
      rw [hget]
      by_cases hj8 : j < 8
      · rw [show (stackPtr initial).toNat - 73 + 1 + j = (stackPtr initial).toNat - 72 + j by omega,
          ofNat_stack hroom htop (k := 72) (by omega) (by omega)] at htb
        exact copied_byte (fun o ho => hsomeV o (by omega)) (hwV1.trans hwU1) hj8 htb
      · rw [show (stackPtr initial).toNat - 73 + 1 + j = (stackPtr initial).toNat - 64 + (j - 8) by
            omega, ofNat_stack hroom htop (k := 64) (by omega) (by omega)] at htb
        rw [show T + BitVec.ofNat 64 j = T + BitVec.ofNat 64 8 + BitVec.ofNat 64 (j - 8) by
          rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
        refine copied_byte (fun o ho => ?_) (hwV2.trans hwU2) (by omega) htb
        rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
        exact hsomeV _ (by omega)
  ·
    have hRoom : hasRoom encryptInPlace initial = false := by
      rw [hRoomIff]; exact decide_eq_false hR
    have hripU' : u.RIP = 0x1019ed := by rw [hripU]; simp [hR]
    obtain ⟨fuel, fin, hRet, h₁, h₂, h₃, h₄, h₅, hrax, hext⟩ :=
      ret_finish hCall hS hAt hPost hOutside hLow aU TU.agrees TU.ready TU.code hripU' hspU hPU
        (hkeep1I.trans hretT) (fun k h1 h2 => (hkeep1 k h2).trans (hslotT k h1 h2))
        (by simp [retCs1]) (by simp [retCs1]) (by simp [retCs1]) (by simp [retCs1])
        (by
          intro c hc a hcov
          simp only [retCs1, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl
          all_goals try exact hcov.elim
          right
          obtain ⟨j, hj, rfl⟩ := hcov
          rw [hSt]
          simp only [MemoryRegion.Contains]
          rw [slot_toNat (by omega) htop (by omega)]
          omega)
    refine ⟨fuel, fin, hRet, h₁, h₂, h₃, h₄, h₅, ?_⟩
    simp only [hRoom, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · show (fin.regValue .rax).setWidth 32 = 1
      rw [hrax, show u.regValue .rax = 1 from hraxU]
      rfl
    have hct := hPost.ciphertext
    unfold readOutput AEAD.encryptWithoutTag
    apply readRegion_of_hasBytes
    rw [hO]
    simp only [hRoom, Bool.false_eq_true, ↓reduceIte]
    cases hE : chacha20AeadEncrypt associatedData key nonce plaintext with
    | mk ct tg =>
    rw [hE] at hct
    simp only at hct ⊢
    obtain ⟨hctLen, hctB⟩ := hct
    refine ⟨hctLen, fun i => ?_⟩
    rw [show fin.external = u.external from hext, ← hctB i]
    simp only [messageRegion]
    apply TU.agrees.byte
    intro c hc hcov
    simp only [retCs1, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    obtain ⟨j, hj, he⟩ := hcov
    have hil : i.val < plaintext.size := by
      have := i.isLt; change i.val < ct.size at this
      have : ct.size = plaintext.size := hctLen
      omega
    have := congrArg BitVec.toNat he
    rw [slot_toNat (by omega) htop (by omega), BitVec.toNat_ofNat] at this
    exact hBufSt ((initial.regValue .rcx).toNat + i.val)
      (by simp only [MemoryRegion.Contains]; omega)
      (by simp only [MemoryRegion.Contains]; omega)

theorem core_return_room [bindings : Machine.Bindings] {initial s t : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    (hCall : ValidCall encryptInPlace initial [key, nonce, associatedData, plaintext])
    (hAt : AtCoreCall initial s)
    (hOutside : ¬ InProgram (returnBoundary initial).rip)
    (hPost : CorePost s t key nonce associatedData plaintext (initial.regValue .rcx))
    (hRoom : hasRoom encryptInPlace initial = true) :
    ∃ fuel final, Returns (returnBoundary initial) fuel t final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      SuccessfulStatus final ∧
      MemoryWriteFrame initial final
        #v[outputRegion encryptInPlace initial,
          Stack.region initial encryptInPlace.minStackBytes] ∧
      readOutput encryptInPlace initial final =
        .ok (AEAD.encryptWithTag associatedData key nonce plaintext) := by
  obtain ⟨fuel, final, h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := core_return hCall hAt hOutside hPost
  simp only [hRoom, ↓reduceIte] at h₆
  exact ⟨fuel, final, h₀, h₁, h₂, h₃, h₄, h₆.1, h₅, h₆.2⟩

theorem core_return_no_room [bindings : Machine.Bindings] {initial s t : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    (hCall : ValidCall encryptInPlace initial [key, nonce, associatedData, plaintext])
    (hAt : AtCoreCall initial s)
    (hOutside : ¬ InProgram (returnBoundary initial).rip)
    (hPost : CorePost s t key nonce associatedData plaintext (initial.regValue .rcx))
    (hNoRoom : hasRoom encryptInPlace initial = false) :
    ∃ fuel final, Returns (returnBoundary initial) fuel t final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      FailureStatus final aeadErrorStatus ∧
      MemoryWriteFrame initial final
        #v[outputRegion encryptInPlace initial,
          Stack.region initial encryptInPlace.minStackBytes] ∧
      readOutput encryptInPlace initial final =
        .ok (AEAD.encryptWithoutTag associatedData key nonce plaintext) := by
  obtain ⟨fuel, final, h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := core_return hCall hAt hOutside hPost
  simp only [hNoRoom, Bool.false_eq_true, ↓reduceIte] at h₆
  exact ⟨fuel, final, h₀, h₁, h₂, h₃, h₄, h₆.1, h₅, h₆.2⟩

theorem encrypt_in_place [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData plaintext : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall encryptInPlace initial [key, nonce, associatedData, plaintext]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      if hasRoom encryptInPlace initial then
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion encryptInPlace initial,
            Stack.region initial encryptInPlace.minStackBytes] ∧
        readOutput encryptInPlace initial final =
          .ok (AEAD.encryptWithTag associatedData key nonce plaintext)
      else
        FailureStatus final aeadErrorStatus ∧
        MemoryWriteFrame initial final
          #v[outputRegion encryptInPlace initial,
            Stack.region initial encryptInPlace.minStackBytes] ∧
        readOutput encryptInPlace initial final =
          .ok (AEAD.encryptWithoutTag associatedData key nonce plaintext) := by
  obtain ⟨hb, hOutside⟩ := entry_boundary hBindings hMachine hCall
  obtain ⟨m, s, hAdv, hPre, hAt⟩ := entry_to_core hBindings hMachine hCall
  have hDifferent : (returnBoundary initial).rip ≠ (returnBoundary s).rip := by
    rw [hAt.returnAddress]
    intro h
    exact hOutside (h ▸ coreReturnAddress_inProgram)
  have hReturnLow : (returnBoundary s).rip.toNat < 2 ^ 32 := by
    rw [hAt.returnAddress]
    decide
  obtain ⟨n, t, hCore, hPost⟩ := Core.core_call (returnBoundary initial) hPre hOutside hDifferent hReturnLow
  cases hRoom : hasRoom encryptInPlace initial
  · obtain ⟨k, final, hRet, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ :=
      core_return_no_room hCall hAt hOutside hPost hRoom
    obtain ⟨least, hUnique⟩ :=
      Returns.unique_of_boundary hb ((hAdv.trans hCore).returns hRet)
    exact ⟨least, final, hUnique, h₁, h₂, h₃, h₄, by simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨h₅, h₆, h₇⟩⟩
  · obtain ⟨k, final, hRet, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ :=
      core_return_room hCall hAt hOutside hPost hRoom
    obtain ⟨least, hUnique⟩ :=
      Returns.unique_of_boundary hb ((hAdv.trans hCore).returns hRet)
    exact ⟨least, final, hUnique, h₁, h₂, h₃, h₄, by simp only [↓reduceIte]; exact ⟨h₅, h₆, h₇⟩⟩

end ChaCha20Poly1305.Proofs.Wrapper
