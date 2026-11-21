import ChaCha20Poly1305.Proofs.Core.Cuts
import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30
import ChaCha20Poly1305.Proofs.ChaCha20.Refinement
import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Program.ReadWrite.Bytes

set_option linter.unusedSectionVars false

namespace ChaCha20Poly1305.Proofs.Core.Lengths

open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CoreContract
open ChaCha20Poly1305.Proofs.Poly1305State
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

variable [bindings : Machine.Bindings] {s : RamState} {key : Vector UInt8 32}
  {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}

theorem inv_ready {t : RamState} {o : BitVec 64} {n : Nat} (h : Inv s t o n) : ReadyToStep t :=
  ReadyToStep.of_supported h.machine h.environment.smrr h.environment.memoryType
    (DecoderFeatures.of_supported h.machine h.environment.leadingZeroCount)

                                                                                                
          
structure Room (s : RamState) : Prop where
  room : 992 ≤ (stackPtr s).toNat
  top : (stackPtr s).toNat + 8 < 2 ^ 32
  avoid : ∀ a : BitVec 64, (stackPtr s).toNat - 992 ≤ a.toNat → a.toNat < (stackPtr s).toNat + 8 →
    ¬ (InProgram a ∨ pageTables.Contains a.toNat)
  tables : 0x2020 ≤ (stackPtr s).toNat - 992 ∨ (stackPtr s).toNat + 8 ≤ 0x1000

theorem stackRegion_mem (s : RamState) (o : BitVec 64) (n : Nat) :
    Stack.region s coreStackBytes ∈ coreWritten s o n := by
  simp [coreWritten]

theorem room_of_pre (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) : Room s := by
  obtain ⟨hb, -, hn, -⟩ := hPre.stack
  have hav := hPre.separation.2.2 _ (stackRegion_mem s outPtr plaintext.size)
  have hsp : s.regValue .rsp = stackPtr s := rfl
  simp only [Stack.region, MemoryRegion.Bounded, userAddressLimit, Stack.NoUnderflow,
    Stack.returnAddressBytes, coreStackBytes, hsp] at hb hn
  simp only [MemoryRegion.Avoids, Stack.region, MemoryRegion.Contains, Stack.returnAddressBytes,
    coreStackBytes, hsp] at hav
  refine ⟨hn, by omega, fun a h1 h2 => hav a ⟨h1, by omega⟩, ?_⟩
  refine Classical.byContradiction fun hc => ?_
  let x : Nat := max ((stackPtr s).toNat - 992) 0x1000
  have hx : x < 2 ^ 64 := by omega
  apply hav (BitVec.ofNat 64 x)
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
    constructor <;> omega
  · right
    simp only [pageTables]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
    constructor <;> omega

                                                                                                  
                                  
def Scratch (s : RamState) (a : BitVec 64) : Prop :=
  (stackPtr s).toNat - 536 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 48

def FrameWrites (s : RamState) (cs : List Component) : Prop :=
  Component.df ∉ cs ∧ ∀ c ∈ cs, ∀ a, c.Covers a → Scratch s a

theorem FrameWrites.append {cs cs' : List Component} (h : FrameWrites s cs)
    (h' : FrameWrites s cs') : FrameWrites s (cs ++ cs') := by
  refine ⟨by simp [h.1, h'.1], fun c hc => ?_⟩
  rcases List.mem_append.mp hc with hc | hc
  · exact h.2 c hc
  · exact h'.2 c hc

theorem nonmem_not_covers' {c : Component} (h : c.isMem = false) (x : BitVec 64) :
    ¬ c.Covers x := by
  cases c <;> simp_all [Component.Covers, Component.isMem]

set_option maxRecDepth 8000 in
theorem Room.scratch_stack (hR : Room s) {a : BitVec 64} (h : Scratch s a) :
    (Stack.region s coreStackBytes).Contains a.toNat := by
  have hsp : s.regValue .rsp = stackPtr s := rfl
  simp only [Stack.region, MemoryRegion.Contains, Stack.returnAddressBytes, coreStackBytes]
  rw [hsp]
  have := hR.room
  unfold Scratch at h
  omega

theorem Room.scratch_avoid (hR : Room s) {a : BitVec 64} (h : Scratch s a) :
    ¬ (InProgram a ∨ pageTables.Contains a.toNat) := by
  have := hR.room
  unfold Scratch at h
  exact hR.avoid a (by omega) (by omega)

theorem keep_byte {cs : List Component} {t t' : RamState} (hag : AgreesExcept cs t t')
    (hw : FrameWrites s cs) {x : BitVec 64} (hx : ¬ Scratch s x) :
    t'.external[x]? = t.external[x]? :=
  hag.byte fun c hc hcov => hx (hw.2 c hc x hcov)

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

theorem memLoad_keep {m m' : Ram} {a : BitVec 64} {n : Nat}
    (hk : ∀ i < n / 8, m'[a + BitVec.ofNat 64 i]? = m[a + BitVec.ofNat 64 i]?) :
    memLoad m' a n = memLoad m a n := by
  apply memLoad_congr
  intro i hi
  simp only [memByte]
  congr 1
  exact hk i hi

theorem word64At_keep {r : MemoryRegion} {m m' : Ram} {v : BitVec 64} (h : r.Word64At m v)
    (hk : ∀ i < 8, m'[BitVec.ofNat 64 r.start + BitVec.ofNat 64 i]? =
      m[BitVec.ofNat 64 r.start + BitVec.ofNat 64 i]?) : r.Word64At m' v := by
  have hsome : ∀ i < 8, (m'[BitVec.ofNat 64 r.start + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    rw [hk i hi]
    exact loadBytes_isSome h.2 i hi
  refine ⟨h.1, ?_⟩
  have hv : memLoad m' (BitVec.ofNat 64 r.start) 64 = v :=
    (memLoad_keep (n := 64) hk).trans (word64At_memLoad h)
  rw [← hv]
  exact (Bytes.of_memLoad (n := 64) hsome).loadBytes64

theorem inv_step (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    {t t' : RamState} {cs : List Component} (hInv : Inv s t outPtr plaintext.size)
    (hReady : ReadyToStep t') (hag : AgreesExcept cs t t') (hw : FrameWrites s cs)
    (hrsp : stackPtr t' = framePointer s) : Inv s t' outPtr plaintext.size := by
  have hR := room_of_pre hPre
  have hsp : s.regValue .rsp = stackPtr s := rfl
  have hout : ∀ x : BitVec 64, (stackPtr s).toNat - 48 ≤ x.toNat → ¬ Scratch s x := by
    intro x hx h; unfold Scratch at h; omega
  refine ⟨⟨hReady.smrr, hReady.memoryType, hInv.environment.stringStride,
    hReady.features.lzcnt⟩, hReady.supported (SupportedSSE.of_agreesExcept hag hInv.machine.sse),
    hInv.code.of_agreesExcept hag ?_, hag.directionFlagClear hw.1 hInv.directionFlagUnset, hrsp,
    memoryWriteFrame_trans hInv.frame (hag.memoryWriteFrame ?_), ?_, ?_, ?_⟩
  · intro x hx c hc hcov
    exact hR.scratch_avoid (hw.2 c hc _ hcov) (.inl (inProgram_of_mem hx))
  · intro c hc a hcov
    exact ⟨_, by simp, hR.scratch_stack (hw.2 c hc a hcov)⟩
  · intro region hr
    refine hag.allocated (hInv.allocated region hr) fun a ⟨c, hc, hcov⟩ => hag.grow _ ?_
    obtain ⟨b, hb⟩ := hInv.allocated _ (stackRegion_mem s outPtr plaintext.size) a
      (hR.scratch_stack (hw.2 c hc a hcov))
    simp [hb]
  · intro entry he
    refine word64At_keep (hInv.saved entry he) fun i hi => keep_byte hag hw (hout _ ?_)
    have hr := hR.room
    have ht := hR.top
    simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
    simp only [slot, frameBase, frameBytes, BitVec.toNat_add, BitVec.toNat_ofNat]
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega
  · refine word64At_keep hInv.returnAddress fun i hi => keep_byte hag hw (hout _ ?_)
    have hr := hR.room
    have ht := hR.top
    simp only [Stack.returnSlot, hsp, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega


theorem add_toNat {a : BitVec 64} {i : Nat} (h : a.toNat + i < 2 ^ 64) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
    Nat.mod_eq_of_lt h]

theorem fp_toNat (hR : Room s) : (framePointer s).toNat = (stackPtr s).toNat - 440 := by
  have := hR.room
  simp only [framePointer, frameBytes, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem fp_add (hR : Room s) (k : Nat) (hk : k ≤ 448) :
    (framePointer s + BitVec.ofNat 64 k).toNat = (stackPtr s).toNat - 440 + k := by
  have := hR.top
  rw [add_toNat (by rw [fp_toNat hR]; omega), fp_toNat hR]

theorem fp_sub (hR : Room s) (k : Nat) (hk : k ≤ 552) :
    (framePointer s - BitVec.ofNat 64 k).toNat = (stackPtr s).toNat - 440 - k := by
  have := hR.room
  have hk' : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, fp_toNat hR, hk']; omega), fp_toNat hR, hk']

theorem slot_addr (hR : Room s) (k : Nat) (hk : k ≤ 448) :
    BitVec.ofNat 64 (frameBase s + k) = framePointer s + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  have := hR.top
  rw [fp_add hR k hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [frameBase]; omega)]
  simp only [frameBase, frameBytes]

theorem sib_addr {u : RamState} (hu : stackPtr u = framePointer s) (d : Disp) (k : Nat)
    (hd : d.value = BitVec.ofNat 64 k) (x : BitVec 64) :
    (AddrMode.sib 4 none 0 d).addr u x = framePointer s + BitVec.ofNat 64 k := by
  simp only [AddrMode.addr, AddrMode.reg64]
  rw [show ((4 : BitVec 4).setWidth 5) = (4 : BitVec 5) from rfl, ← stackPtr_eq_read, hu, hd]

theorem textBytes_size : Extracted.textBytes.size = 11759 := by decide

theorem inProg (off : Nat) (h : off < 11759) : InProgram (BitVec.ofNat 64 (0x100000 + off)) := by
  have hp := text_address_in_program off (by rw [textBytes_size]; exact h)
  have he : Extracted.textAddress + BitVec.ofNat 64 off = BitVec.ofNat 64 (0x100000 + off) := by
    apply BitVec.eq_of_toNat_eq
    have h0 : (1048576 : BitVec 64).toNat = 1048576 := rfl
    simp only [Extracted.textAddress, BitVec.toNat_add, BitVec.toNat_ofNat, h0]
    omega
  rwa [he] at hp

theorem stack_some {t u : RamState} {n : Nat} (hInv : Inv s t outPtr n) (hR : Room s)
    (hg : ∀ x : BitVec 64, (t.external[x]?).isSome → (u.external[x]?).isSome)
    {a : BitVec 64} (h1 : (stackPtr s).toNat - 992 ≤ a.toNat)
    (h2 : a.toNat < (stackPtr s).toNat + 8) : (u.external[a]?).isSome := by
  have hsp : s.regValue .rsp = stackPtr s := rfl
  have := hR.room
  obtain ⟨b, hb⟩ := hInv.allocated _ (stackRegion_mem s outPtr n) a (by
    simp only [Stack.region, MemoryRegion.Contains, Stack.returnAddressBytes, coreStackBytes]
    rw [hsp]
    omega)
  exact hg a (by simp [hb])

theorem stack_readable {t u : RamState} {n : Nat} (hInv : Inv s t outPtr n) (hR : Room s)
    (hg : ∀ x : BitVec 64, (t.external[x]?).isSome → (u.external[x]?).isSome)
    {a : BitVec 64} {len : Nat} (h1 : (stackPtr s).toNat - 992 ≤ a.toNat)
    (h2 : a.toNat + len ≤ (stackPtr s).toNat + 8) : MemReadable u a len := by
  have := hR.top
  refine ⟨by omega, fun i hi => stack_some hInv hR hg ?_ ?_⟩ <;>
    rw [add_toNat (by omega)] <;> omega

theorem stack_writable {t u : RamState} {n : Nat} (hInv : Inv s t outPtr n) (hR : Room s)
    (hg : ∀ x : BitVec 64, (t.external[x]?).isSome → (u.external[x]?).isSome)
    {a : BitVec 64} {len : Nat} (h1 : (stackPtr s).toNat - 992 ≤ a.toNat)
    (h2 : a.toNat + len ≤ (stackPtr s).toNat + 8) : MemWritable u a len := by
  have := hR.top
  have := hR.tables
  have hr := stack_readable hInv hR hg h1 h2
  exact ⟨hr.low, hr.mem, by unfold PageTableEntriesApart; omega⟩

theorem stack_writableRange {t u : RamState} {n : Nat} (hInv : Inv s t outPtr n) (hR : Room s)
    (hg : ∀ x : BitVec 64, (t.external[x]?).isSome → (u.external[x]?).isSome)
    {a : BitVec 64} {len : Nat} (h1 : (stackPtr s).toNat - 992 ≤ a.toNat)
    (h2 : a.toNat + len ≤ (stackPtr s).toNat + 8) :
    ChaCha20Poly1305.Proofs.Common.WritableRange u a len := by
  have := hR.top
  refine ⟨stack_readable hInv hR hg h1 h2, fun i hi hp => ?_, fun i hi hp => ?_⟩
  · have hc := (ChaCha20Poly1305.Proofs.Common.inPageTables_iff _).mp hp
    exact hR.avoid (a + BitVec.ofNat 64 i) (by rw [add_toNat (by omega)]; omega)
      (by rw [add_toNat (by omega)]; omega)
      (.inr (by simp only [pageTables, MemoryRegion.Contains]; omega))
  · exact hR.avoid _ (by rw [add_toNat (by omega)]; omega) (by rw [add_toNat (by omega)]; omega)
      (.inl hp)

theorem stack_apart (hR : Room s) {a : BitVec 64} {len : Nat}
    (h1 : (stackPtr s).toNat - 992 ≤ a.toNat) (h2 : a.toNat + len ≤ (stackPtr s).toNat + 8)
    (p : BitVec 64) (codeLen off : Nat) (hp : p = BitVec.ofNat 64 (0x100000 + off))
    (hoff : off + codeLen < 11759) : RangeApart a len p codeLen := by
  have := hR.top
  intro i hi j hj he
  apply hR.avoid (a + BitVec.ofNat 64 i) (by rw [add_toNat (by omega)]; omega)
    (by rw [add_toNat (by omega)]; omega)
  left
  rw [he, hp]
  have he' : BitVec.ofNat 64 (0x100000 + off) + BitVec.ofNat 64 j =
      BitVec.ofNat 64 (0x100000 + (off + j)) := by
    apply BitVec.eq_of_toNat_eq
    rw [add_toNat (by rw [BitVec.toNat_ofNat]; omega)]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [he']
  exact inProg _ (by omega)

theorem mem_scratch (hR : Room s) {a : BitVec 64} {len : Nat}
    (h1 : (stackPtr s).toNat - 536 ≤ a.toNat) (h2 : a.toNat + len ≤ (stackPtr s).toNat - 48) :
    ∀ x, (Component.mem a len).Covers x → Scratch s x := by
  have := hR.top
  rintro x ⟨i, hi, rfl⟩
  unfold Scratch
  rw [add_toNat (by omega)]
  omega


theorem not_covers_mem {a x : BitVec 64} {n : Nat}
    (h : x.toNat < a.toNat ∨ a.toNat + n ≤ x.toNat) (ha : a.toNat + n < 2 ^ 64) :
    ¬ (Component.mem a n).Covers x := by
  rintro ⟨j, hj, rfl⟩
  rw [add_toNat (by omega)] at h
  omega

                                                              
def Same (u v : RamState) (lo hi : Nat) : Prop :=
  ∀ x : BitVec 64, lo ≤ x.toNat → x.toNat < hi → v.external[x]? = u.external[x]?

theorem Same.trans {u v w : RamState} {lo hi : Nat} (h₁ : Same u v lo hi) (h₂ : Same v w lo hi) :
    Same u w lo hi :=
  fun x a b => (h₂ x a b).trans (h₁ x a b)

theorem Same.mono {u v : RamState} {lo hi lo' hi' : Nat} (h : Same u v lo hi) (h₁ : lo ≤ lo')
    (h₂ : hi' ≤ hi) : Same u v lo' hi' :=
  fun x a b => h x (by omega) (by omega)

theorem same_regs {cs : List Component} {u v : RamState} (hag : AgreesExcept cs u v)
    (h : ∀ c ∈ cs, c.isMem = false) (lo hi : Nat) : Same u v lo hi :=
  fun x _ _ => hag.byte fun c hc => nonmem_not_covers' (h c hc) x

theorem same_mem {cs : List Component} {u v : RamState} {a : BitVec 64} {n : Nat}
    (hag : AgreesExcept cs u v) (h : ∀ c ∈ cs, c.isMem = false ∨ c = .mem a n)
    (ha : a.toNat + n < 2 ^ 64) {lo hi : Nat} (hd : hi ≤ a.toNat ∨ a.toNat + n ≤ lo) :
    Same u v lo hi := by
  intro x h1 h2
  apply hag.byte
  intro c hc
  rcases h c hc with hm | rfl
  · exact nonmem_not_covers' hm x
  · exact not_covers_mem (by omega) ha

theorem same_mem2 {cs : List Component} {u v : RamState} {a b : BitVec 64} {n m : Nat}
    (hag : AgreesExcept cs u v)
    (h : ∀ c ∈ cs, c.isMem = false ∨ c = .mem a n ∨ c = .mem b m)
    (ha : a.toNat + n < 2 ^ 64) (hb : b.toNat + m < 2 ^ 64) {lo hi : Nat}
    (hda : hi ≤ a.toNat ∨ a.toNat + n ≤ lo) (hdb : hi ≤ b.toNat ∨ b.toNat + m ≤ lo) :
    Same u v lo hi := by
  intro x h1 h2
  apply hag.byte
  intro c hc
  rcases h c hc with hm | rfl | rfl
  · exact nonmem_not_covers' hm x
  · exact not_covers_mem (by omega) ha
  · exact not_covers_mem (by omega) hb

theorem fw_regs {cs : List Component} (h : ∀ c ∈ cs, c.isMem = false ∧ c ≠ .df) :
    FrameWrites s cs :=
  ⟨fun hd => (h _ hd).2 rfl, fun c hc x hcov => absurd hcov (nonmem_not_covers' (h c hc).1 x)⟩

theorem fw_mem2 (hR : Room s) {cs : List Component} {a b : BitVec 64} {n m : Nat}
    (h : ∀ c ∈ cs, (c.isMem = false ∧ c ≠ .df) ∨ c = .mem a n ∨ c = .mem b m)
    (ha₁ : (stackPtr s).toNat - 536 ≤ a.toNat) (ha₂ : a.toNat + n ≤ (stackPtr s).toNat - 48)
    (hb₁ : (stackPtr s).toNat - 536 ≤ b.toNat) (hb₂ : b.toNat + m ≤ (stackPtr s).toNat - 48) :
    FrameWrites s cs := by
  refine ⟨fun hd => ?_, fun c hc x hcov => ?_⟩
  · rcases h _ hd with ⟨-, h⟩ | h | h
    · exact h rfl
    · cases h
    · cases h
  · rcases h c hc with ⟨hm, -⟩ | rfl | rfl
    · exact absurd hcov (nonmem_not_covers' hm x)
    · exact mem_scratch hR ha₁ ha₂ x hcov
    · exact mem_scratch hR hb₁ hb₂ x hcov

theorem load_same {u v : RamState} {lo hi : Nat} (h : Same u v lo hi) {a : BitVec 64} {n : Nat}
    (h₁ : lo ≤ a.toNat) (h₂ : a.toNat + n / 8 ≤ hi) (hhi : hi < 2 ^ 64) :
    memLoad v.external a n = memLoad u.external a n :=
  memLoad_keep fun i hi' => h _ (by rw [add_toNat (by omega)]; omega)
    (by rw [add_toNat (by omega)]; omega)

theorem limbs_same {u v : RamState} {base : BitVec 64}
    (h : Same u v base.toNat (base.toNat + 20)) (hb : base.toNat + 20 < 2 ^ 64) :
    limbsAt v base = limbsAt u base := by
  funext i
  have := i.isLt
  unfold limbsAt word32
  change memLoad v.external _ 32 = memLoad u.external _ 32
  exact load_same h (by rw [add_toNat (by omega)]; omega) (by rw [add_toNat (by omega)]; omega) hb

theorem pad_same {u v : RamState} {base : BitVec 64}
    (h : Same u v base.toNat (base.toNat + 16)) (hb : base.toNat + 16 < 2 ^ 64) :
    padWords v base = padWords u base := by
  funext i
  have := i.isLt
  unfold padWords word32
  change memLoad v.external _ 32 = memLoad u.external _ 32
  exact load_same h (by rw [add_toNat (by omega)]; omega) (by rw [add_toNat (by omega)]; omega) hb

theorem hasBytes_same {u v : RamState} {r : MemoryRegion} {bytes : ByteArray}
    (h : Same u v r.start (r.start + r.size)) (hr : r.start + r.size < 2 ^ 64)
    (hb : r.HasBytes u.external bytes) : r.HasBytes v.external bytes := by
  refine ⟨hb.1, fun i => ?_⟩
  have hi := i.isLt
  have hl := hb.1
  unfold MemoryRegion.HasLength at hl
  rw [h _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)]
  exact hb.2 i

theorem word64_same {u v : RamState} {r : MemoryRegion} {value : BitVec 64}
    (h : Same u v r.start (r.start + 8)) (hr : r.start + 8 < 2 ^ 64)
    (hw : r.Word64At u.external value) : r.Word64At v.external value :=
  word64At_keep hw fun i hi => h _
    (by rw [add_toNat (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]; omega)
    (by rw [add_toNat (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]; omega)

theorem inCode_inProgram {a : BitVec 64} (h : Poly1305.Callee101e30.InCode a) : InProgram a := by
  have he : (0x101e30 : BitVec 64).toNat = 0x101e30 := rfl
  have hb : (0x101ab0 : BitVec 64).toNat = 0x101ab0 := rfl
  simp only [Poly1305.Callee101e30.InCode, Poly1305.Callee101e30.entry,
    Poly1305.Callee101e30.bodyEntry, he, hb] at h
  have ha : a = BitVec.ofNat 64 (0x100000 + (a.toNat - 0x100000)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [ha]
  exact inProg _ (by omega)

theorem regValue_r15 (u : RamState) : u.regValue .r15 = (Operand.reg 15 : Operand 64).read u := by
  simp only [Operand.read_reg64]
  rfl

theorem regValue_r8 (u : RamState) : u.regValue .r8 = (Operand.reg 8 : Operand 64).read u := by
  simp only [Operand.read_reg64]
  rfl

theorem storedByte_eq (v : BitVec 64) (i : Nat) :
    storedByte v i = UInt8.ofNat (v.toNat / 256 ^ i) := by
  simp only [storedByte, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem block_eq {m : Ram} {a x y : BitVec 64}
    (hs : ∀ i < 16, (m[a + BitVec.ofNat 64 i]?).isSome)
    (hx : memLoad m a 64 = x) (hy : memLoad m (a + BitVec.ofNat 64 8) 64 = y) :
    (⟨Array.ofFn fun i : Fin 16 => (m[a + BitVec.ofNat 64 i.val]?).getD 0⟩ : ByteArray) =
      numTo8LeBytes x.toNat ++ numTo8LeBytes y.toNat := by
  have bx := Bytes.of_memLoad (n := 64) (m := m) (a := a) (fun i hi => hs i (by omega))
  have by' := Bytes.of_memLoad (n := 64) (m := m) (a := a + BitVec.ofNat 64 8) (fun i hi => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact hs (8 + i) (by omega))
  rw [hx] at bx
  rw [hy] at by'
  apply ByteArray.ext
  apply Array.ext
  · simp [numTo8LeBytes]
  · intro i h1 h2
    simp only [Array.size_ofFn] at h1
    simp only [Array.getElem_ofFn, ByteArray.data_append, numTo8LeBytes]
    by_cases hi : i < 8
    · rw [Array.getElem_append_left (by simpa using hi)]
      simp only [Array.getElem_ofFn]
      rw [bx i (by omega), Option.getD_some, storedByte_eq]
    · rw [Array.getElem_append_right (by simp; omega)]
      simp only [Array.getElem_ofFn, Array.size_ofFn]
      have hb := by' (i - 8) (by omega)
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 8 + (i - 8) = i by omega] at hb
      rw [hb, Option.getD_some, storedByte_eq]

theorem absorb_value {r b H : Nat} :
    ((H + b) * r) % prime = (r * (H % prime + b)) % (2 ^ 130 - 5) := by
  change _ = (r * (H % prime + b)) % prime
  rw [Nat.mul_comm (H + b) r, Nat.mul_mod r (H + b), Nat.mul_mod r (H % prime + b),
    Nat.add_mod H b, Nat.add_mod (H % prime) b, Nat.mod_mod]

theorem code_keep (hR : Room s) {cs : List Component} {u v : RamState}
    (hag : AgreesExcept cs u v) (hw : FrameWrites s cs)
    (hc : CodeIn Extracted.programImage u) : CodeIn Extracted.programImage v :=
  hc.of_agreesExcept hag fun _ hx c hc' hcov =>
    hR.scratch_avoid (hw.2 c hc' _ hcov) (.inl (inProgram_of_mem hx))

theorem fw_one (hR : Room s) {cs : List Component} {a : BitVec 64} {n : Nat}
    (h : ∀ c ∈ cs, (c.isMem = false ∧ c ≠ .df) ∨ c = .mem a n)
    (ha₁ : (stackPtr s).toNat - 536 ≤ a.toNat) (ha₂ : a.toNat + n ≤ (stackPtr s).toNat - 48) :
    FrameWrites s cs :=
  fw_mem2 hR (a := a) (b := a) (n := n) (m := n)
    (fun c hc => (h c hc).elim .inl fun e => .inr (.inl e)) ha₁ ha₂ ha₁ ha₂

end ChaCha20Poly1305.Proofs.Core.Lengths

namespace ChaCha20Poly1305.Proofs.Core

open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CoreContract
open ChaCha20Poly1305.Proofs.Poly1305State ChaCha20Poly1305.Proofs.MemoryRoutines.Machine
open ChaCha20Poly1305.Proofs.Core.Lengths

set_option maxRecDepth 8000 in
theorem absorb_lengths [bindings : Machine.Bindings] {s : RamState} {key : Vector UInt8 32}
    {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}
    (boundary : ReturnBoundary) {t : RamState}
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hBoundaryOutside : ¬ InProgram boundary.rip)
    (_hBoundaryDifferent : boundary.rip ≠ (returnBoundary s).rip)
    (hCut : Cut4 s t key nonce associatedData plaintext outPtr) :
    ∃ fuel u, Advances boundary fuel t u ∧
      Cut5 s u key nonce associatedData plaintext outPtr := by
  have hR := room_of_pre hPre
  have hInv := hCut.toInv
  have hP := hR.room
  have hT := hR.top
  have hne : ∀ (a : BitVec 64) (off : Nat), off < 11759 → a = BitVec.ofNat 64 (0x100000 + off) →
      a ≠ boundary.rip := by
    rintro a off hoff rfl he
    exact hBoundaryOutside (he ▸ inProg off hoff)
  have hF : ∀ k, k ≤ 448 → (framePointer s + BitVec.ofNat 64 k).toNat =
      (stackPtr s).toNat - 440 + k := fun k hk => fp_add hR k hk
  have hsp0 : stackPtr t = framePointer s := hInv.rsp
                                    
  have hA1 := sib_addr (u := t) hsp0 (.d32 0x98) 0x98 (by decide)
  obtain ⟨s1, a1, r1, e1⟩ := (mov_r64_m64_effect_step 0x100984 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide)
    (by decide)).advances (inv_ready hInv)
    (program_text_slice hInv.code 0x984 8 (by rw [textBytes_size]; omega))
    ⟨hCut.rip, by
      rw [hA1]
      exact stack_readable hInv hR (fun _ h => h) (by rw [hF _ (by omega)]; omega)
        (by rw [hF _ (by omega)]; omega)⟩
    (hne _ 0x98c (by omega) rfl)
  have ag1 : AgreesExcept [.reg 0, .rip] t s1 := e1.agrees
  have hsp1 : stackPtr s1 = framePointer s := by
    rw [stackPtr_eq_read, ag1.read (by simp), ← stackPtr_eq_read, hsp0]
  have hrax1 : (Operand.reg 0 : Operand 64).read s1 = s.regValue .r8 := by
    have h := e1.writes
    simp only [movR64M64Effect, Write.AllHold] at h
    rw [hA1] at h
    refine h.trans ?_
    have := word64At_memLoad hCut.adLengthSlot
    rw [show (slot s 0x98).start = frameBase s + 0x98 from rfl, slot_addr hR _ (by omega)] at this
    exact this
  have fw1 : FrameWrites s [.reg 0, .rip] := fw_regs (by simp [Component.isMem])
  have c1 := code_keep hR ag1 fw1 hInv.code
  have hg1 : ∀ x : BitVec 64, (t.external[x]?).isSome → (s1.external[x]?).isSome := ag1.grow
                                    
  have hA2 := sib_addr (u := s1) hsp1 (.d8 0x18) 0x18 (by decide)
  obtain ⟨s2, a2, r2, e2⟩ := (mov_m64_r64_effect_step 0x10098c 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide)
    (by decide)).advances r1
    (program_text_slice c1 0x98c 5 (by rw [textBytes_size]; omega))
    ⟨e1.rip.trans rfl, by
      simp only [storeAddrAt]
      rw [hA2]
      exact stack_writable hInv hR hg1 (by rw [hF _ (by omega)]; omega)
        (by rw [hF _ (by omega)]; omega), by
      simp only [storeAddrAt]
      rw [hA2]
      exact stack_apart hR (by rw [hF _ (by omega)]; omega) (by rw [hF _ (by omega)]; omega)
        _ _ 0x98c (by decide) (by decide)⟩
    (hne _ 0x991 (by omega) rfl)
  have ag2 : AgreesExcept [.mem (framePointer s + BitVec.ofNat 64 0x18) 8, .rip] s1 s2 := by
    have h := e2.agrees
    simp only [movM64R64Effect, storeEffect_components, storeAddrAt, hA2] at h
    exact h
  have hmem2 : memLoad s2.external (framePointer s + BitVec.ofNat 64 0x18) 64 =
      s.regValue .r8 := by
    have h := e2.writes
    simp only [movM64R64Effect, storeEffect, storeAddrAt, hA2, Write.AllHold] at h
    exact h.trans hrax1
  have hsp2 : stackPtr s2 = framePointer s := by
    rw [stackPtr_eq_read, ag2.read (by simp), ← stackPtr_eq_read, hsp1]
  have fw2 : FrameWrites s [.mem (framePointer s + BitVec.ofNat 64 0x18) 8, .rip] :=
    fw_one hR (a := framePointer s + BitVec.ofNat 64 0x18) (n := 8) (by simp [Component.isMem])
      (by rw [hF _ (by omega)]; omega) (by rw [hF _ (by omega)]; omega)
  have c2 := code_keep hR ag2 fw2 c1
  have hg2 : ∀ x : BitVec 64, (t.external[x]?).isSome → (s2.external[x]?).isSome :=
    fun x h => ag2.grow x (hg1 x h)
                                    
  have hA3 := sib_addr (u := s2) hsp2 (.d8 0x10) 0x10 (by decide)
  obtain ⟨s3, a3, r3, e3⟩ := (mov_r64_m64_effect_step 0x100991 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide)
    (by decide)).advances r2
    (program_text_slice c2 0x991 5 (by rw [textBytes_size]; omega))
    ⟨e2.rip.trans rfl, by
      rw [hA3]
      exact stack_readable hInv hR hg2 (by rw [hF _ (by omega)]; omega)
        (by rw [hF _ (by omega)]; omega)⟩
    (hne _ 0x996 (by omega) rfl)
  have ag3 : AgreesExcept [.reg 0, .rip] s2 s3 := e3.agrees
  have hsp3 : stackPtr s3 = framePointer s := by
    rw [stackPtr_eq_read, ag3.read (by simp), ← stackPtr_eq_read, hsp2]
  have hrax3 : (Operand.reg 0 : Operand 64).read s3 = BitVec.ofNat 64 plaintext.size := by
    have h := e3.writes
    simp only [movR64M64Effect, Write.AllHold] at h
    rw [hA3] at h
    refine h.trans ?_
    change memLoad s2.external _ 64 = _
    have hS12 : Same s1 s2 ((stackPtr s).toNat - 440 + 0x10) ((stackPtr s).toNat - 440 + 0x18) :=
      same_mem ag2 (a := framePointer s + BitVec.ofNat 64 0x18) (n := 8)
        (by simp [Component.isMem]) (by rw [hF _ (by omega)]; omega)
        (by rw [hF _ (by omega)]; omega)
    have hSt1 := same_regs ag1 (by simp [Component.isMem])
      ((stackPtr s).toNat - 440 + 0x10) ((stackPtr s).toNat - 440 + 0x18)
    rw [load_same (hSt1.trans hS12) (by rw [hF _ (by omega)]; omega) (by rw [hF _ (by omega)]; omega)
      (by omega)]
    have := word64At_memLoad hCut.lengthSlot
    rw [show (slot s 0x10).start = frameBase s + 0x10 from rfl, slot_addr hR _ (by omega)] at this
    exact this
  have fw3 : FrameWrites s [.reg 0, .rip] := fw_regs (by simp [Component.isMem])
  have c3 := code_keep hR ag3 fw3 c2
  have hg3 : ∀ x : BitVec 64, (t.external[x]?).isSome → (s3.external[x]?).isSome :=
    fun x h => ag3.grow x (hg2 x h)
                                    
  have hA4 := sib_addr (u := s3) hsp3 (.d8 0x20) 0x20 (by decide)
  obtain ⟨s4, a4, r4, e4⟩ := (mov_m64_r64_effect_step 0x100996 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide)
    (by decide)).advances r3
    (program_text_slice c3 0x996 5 (by rw [textBytes_size]; omega))
    ⟨e3.rip.trans rfl, by
      simp only [storeAddrAt]
      rw [hA4]
      exact stack_writable hInv hR hg3 (by rw [hF _ (by omega)]; omega)
        (by rw [hF _ (by omega)]; omega), by
      simp only [storeAddrAt]
      rw [hA4]
      exact stack_apart hR (by rw [hF _ (by omega)]; omega) (by rw [hF _ (by omega)]; omega)
        _ _ 0x996 (by decide) (by decide)⟩
    (hne _ 0x99b (by omega) rfl)
  have ag4 : AgreesExcept [.mem (framePointer s + BitVec.ofNat 64 0x20) 8, .rip] s3 s4 := by
    have h := e4.agrees
    simp only [movM64R64Effect, storeEffect_components, storeAddrAt, hA4] at h
    exact h
  have hmem4 : memLoad s4.external (framePointer s + BitVec.ofNat 64 0x20) 64 =
      BitVec.ofNat 64 plaintext.size := by
    have h := e4.writes
    simp only [movM64R64Effect, storeEffect, storeAddrAt, hA4, Write.AllHold] at h
    exact h.trans hrax3
  have hsp4 : stackPtr s4 = framePointer s := by
    rw [stackPtr_eq_read, ag4.read (by simp), ← stackPtr_eq_read, hsp3]
  have fw4 : FrameWrites s [.mem (framePointer s + BitVec.ofNat 64 0x20) 8, .rip] :=
    fw_one hR (a := framePointer s + BitVec.ofNat 64 0x20) (n := 8) (by simp [Component.isMem])
      (by rw [hF _ (by omega)]; omega) (by rw [hF _ (by omega)]; omega)
  have c4 := code_keep hR ag4 fw4 c3
  have hg4 : ∀ x : BitVec 64, (t.external[x]?).isSome → (s4.external[x]?).isSome :=
    fun x h => ag4.grow x (hg3 x h)
                                    
  have hA5 := sib_addr (u := s4) hsp4 (.d8 0x18) 0x18 (by decide)
  obtain ⟨s5, a5, r5, e5⟩ := (lea_r64_effect_step 0x10099b 0x48
    (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide)
    (by decide)).advances r4
    (program_text_slice c4 0x99b 5 (by rw [textBytes_size]; omega))
    (e4.rip.trans rfl) (hne _ 0x9a0 (by omega) rfl)
  have ag5 : AgreesExcept [.reg 6, .rip] s4 s5 := e5.agrees
  have hrsi5 : rsi.read s5 = framePointer s + BitVec.ofNat 64 0x18 := by
    have h := e5.writes
    simp only [leaR64Effect, Write.AllHold] at h
    rw [hA5] at h
    exact h
  have hsp5 : stackPtr s5 = framePointer s := by
    rw [stackPtr_eq_read, ag5.read (by simp), ← stackPtr_eq_read, hsp4]
  have fw5 : FrameWrites s [.reg 6, .rip] := fw_regs (by simp [Component.isMem])
  have c5 := code_keep hR ag5 fw5 c4
  have hg5 : ∀ x : BitVec 64, (t.external[x]?).isSome → (s5.external[x]?).isSome :=
    fun x h => ag5.grow x (hg4 x h)
                           
  obtain ⟨s6, a6, r6, e6⟩ := (mov_r64_r64_effect_step 0x1009a0 0x4c 0xff
    (by unfold RexWPrefix; decide) (by decide)).advances r5
    (program_text_slice c5 0x9a0 3 (by rw [textBytes_size]; omega))
    (e5.rip.trans rfl) (hne _ 0x9a3 (by omega) rfl)
  have ag6 : AgreesExcept [.reg 7, .rip] s5 s6 := e6.agrees
  have hrdi6 : rdi.read s6 = (Operand.reg 15 : Operand 64).read s5 := e6.writes
  have hsp6 : stackPtr s6 = framePointer s := by
    rw [stackPtr_eq_read, ag6.read (by simp), ← stackPtr_eq_read, hsp5]
  have fw6 : FrameWrites s [.reg 7, .rip] := fw_regs (by simp [Component.isMem])
  have c6 := code_keep hR ag6 fw6 c5
  have hg6 : ∀ x : BitVec 64, (t.external[x]?).isSome → (s6.external[x]?).isSome :=
    fun x h => ag6.grow x (hg5 x h)
                            
  have hpa : pushAddr s6 = framePointer s - BitVec.ofNat 64 8 := by
    rw [pushAddr, hsp6]
    rfl
  obtain ⟨s7, a7, r7, e7⟩ := (call_rel32_effect_step 0x1009a3 0x1488 (by decide)).advances r6
    (program_text_slice c6 0x9a3 5 (by rw [textBytes_size]; omega))
    ⟨e6.rip.trans rfl, by
      rw [hpa]
      exact stack_writable hInv hR hg6 (by rw [fp_sub hR _ (by omega)]; omega)
        (by rw [fp_sub hR _ (by omega)]; omega), by
      rw [hpa]
      exact stack_apart hR (by rw [fp_sub hR _ (by omega)]; omega)
        (by rw [fp_sub hR _ (by omega)]; omega) _ _ 0x9a3 (by decide) (by decide)⟩
    (hne _ 0x1e30 (by omega) rfl)
  have ag7 : AgreesExcept [.reg 4, .mem (framePointer s - BitVec.ofNat 64 8) 8, .rip] s6 s7 := by
    have h := e7.agrees
    simp only [pushEffect_components, hpa] at h
    exact h
  have hsp7 : stackPtr s7 = framePointer s - BitVec.ofNat 64 8 := by
    rw [stackPtr_eq_read]
    exact e7.writes.1.trans hpa
  have hret : (returnBoundary s7).rip = 0x1009a8 := (callEffect_stack e7).1.trans (by decide)
  have fw7 : FrameWrites s [.reg 4, .mem (framePointer s - BitVec.ofNat 64 8) 8, .rip] :=
    fw_one hR (a := framePointer s - BitVec.ofNat 64 8) (n := 8) (by simp [Component.isMem])
      (by rw [fp_sub hR _ (by omega)]; omega) (by rw [fp_sub hR _ (by omega)]; omega)
  have c7 := code_keep hR ag7 fw7 c6
  have hg7 : ∀ x : BitVec 64, (t.external[x]?).isSome → (s7.external[x]?).isSome :=
    fun x h => ag7.grow x (hg6 x h)
                                     
  have hr15t : (Operand.reg 15 : Operand 64).read t = polyBase s :=
    (regValue_r15 t).symm.trans hCut.r15
  have hrdi7 : rdi.read s7 = polyBase s := by
    rw [ag7.read (by simp), hrdi6,
      ((((ag1.trans ag2).trans ag3).trans ag4).trans ag5).read (by simp), hr15t]
  have hrsi7 : rsi.read s7 = framePointer s + BitVec.ofNat 64 0x18 := by
    rw [ag7.read (by simp), ag6.read (by simp), hrsi5]
  have hpb : polyBase s = framePointer s + BitVec.ofNat 64 0x150 := rfl
  have hrA : polyBase s + rOffset = framePointer s + BitVec.ofNat 64 0x160 := by
    rw [hpb, rOffset, BitVec.add_assoc]
    rfl
  have hhA : polyBase s + hOffset = framePointer s + BitVec.ofNat 64 0x174 := by
    rw [hpb, hOffset, BitVec.add_assoc]
    rfl
  have hpbN : (polyBase s).toNat = (stackPtr s).toNat - 440 + 0x150 := by
    rw [hpb, hF _ (by omega)]
  have same7 : ∀ lo hi, hi < 2 ^ 64 →
      (hi ≤ (stackPtr s).toNat - 440 + 0x18 ∨ (stackPtr s).toNat - 440 + 0x28 ≤ lo) →
      (hi ≤ (stackPtr s).toNat - 448 ∨ (stackPtr s).toNat - 440 ≤ lo) → Same t s7 lo hi := by
    intro lo hi hhi h1 h2
    have e1' := same_regs ag1 (by simp [Component.isMem]) lo hi
    have e2' := same_mem ag2 (a := framePointer s + BitVec.ofNat 64 0x18) (n := 8)
      (by simp [Component.isMem]) (by rw [hF _ (by omega)]; omega)
      (lo := lo) (hi := hi) (by rw [hF _ (by omega)]; omega)
    have e3' := same_regs ag3 (by simp [Component.isMem]) lo hi
    have e4' := same_mem ag4 (a := framePointer s + BitVec.ofNat 64 0x20) (n := 8)
      (by simp [Component.isMem]) (by rw [hF _ (by omega)]; omega)
      (lo := lo) (hi := hi) (by rw [hF _ (by omega)]; omega)
    have e5' := same_regs ag5 (by simp [Component.isMem]) lo hi
    have e6' := same_regs ag6 (by simp [Component.isMem]) lo hi
    have e7' := same_mem ag7 (a := framePointer s - BitVec.ofNat 64 8) (n := 8)
      (by simp [Component.isMem]) (by rw [fp_sub hR _ (by omega)]; omega)
      (lo := lo) (hi := hi) (by rw [fp_sub hR _ (by omega)]; omega)
    exact (((((e1'.trans e2').trans e3').trans e4').trans e5').trans e6').trans e7'
  have hb160 := hF 0x160 (by omega)
  have hb174 := hF 0x174 (by omega)
  have hb150 := hF 0x150 (by omega)
  have hr7 : rLimbs s7 (polyBase s) = rLimbs t (polyBase s) := by
    unfold rLimbs
    rw [hrA]
    exact limbs_same (by rw [hb160]; exact same7 _ _ (by omega) (by omega) (by omega))
      (by rw [hb160]; omega)
  have hh7 : hLimbs s7 (polyBase s) = hLimbs t (polyBase s) := by
    unfold hLimbs
    rw [hhA]
    exact limbs_same (by rw [hb174]; exact same7 _ _ (by omega) (by omega) (by omega))
      (by rw [hb174]; omega)
  have hsb : Poly1305.Callee101e30.stackBase s7 = framePointer s - BitVec.ofNat 64 96 := by
    rw [Poly1305.Callee101e30.stackBase, hsp7, Poly1305.Callee101e30.stackBytes]
    apply BitVec.eq_of_toNat_eq
    rw [fp_sub hR _ (by omega), BitVec.toNat_sub_of_le, fp_sub hR _ (by omega)]
    · simp only [BitVec.toNat_ofNat]
      omega
    · rw [BitVec.le_def, fp_sub hR _ (by omega)]
      simp only [BitVec.toNat_ofNat]
      omega
  have hrAd : Poly1305.Callee101e30.rAddress s7 = framePointer s + BitVec.ofNat 64 0x160 := by
    rw [Poly1305.Callee101e30.rAddress, hrdi7, hrA]
  have hhAd : Poly1305.Callee101e30.hAddress s7 = framePointer s + BitVec.ofNat 64 0x174 := by
    rw [Poly1305.Callee101e30.hAddress, hrdi7, hhA]
  have hsb96 := fp_sub hR 96 (by omega)
  have hb18 := hF 0x18 (by omega)
  have hpre7 : Poly1305.Callee101e30.CallPre s7 := by
    refine ⟨e7.rip.trans rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsb, Poly1305.Callee101e30.stackBytes]
      exact stack_writableRange hInv hR hg7 (by rw [hsb96]; omega) (by rw [hsb96]; omega)
    · rw [hsp7]
      exact stack_readable hInv hR hg7 (by rw [fp_sub hR _ (by omega)]; omega)
        (by rw [fp_sub hR _ (by omega)]; omega)
    · rw [hsp7, fp_sub hR _ (by omega)]
      simp only [Poly1305.Callee101e30.stackBytes]
      omega
    · rw [hrAd]
      exact stack_readable hInv hR hg7 (by rw [hb160]; omega) (by rw [hb160]; omega)
    · rw [hhAd]
      exact stack_writableRange hInv hR hg7 (by rw [hb174]; omega) (by rw [hb174]; omega)
    · rw [hrsi7]
      exact stack_readable hInv hR hg7 (by rw [hb18]; omega) (by rw [hb18]; omega)
    · rw [hrAd, hsb]
      exact RangeApart.of_toNat (by rw [hb160]; omega) (by rw [hsb96]; simp only [Poly1305.Callee101e30.stackBytes]; omega)
        (by rw [hb160, hsb96]; simp only [Poly1305.Callee101e30.stackBytes]; omega)
    · rw [hhAd, hsb]
      exact RangeApart.of_toNat (by rw [hb174]; omega) (by rw [hsb96]; simp only [Poly1305.Callee101e30.stackBytes]; omega)
        (by rw [hb174, hsb96]; simp only [Poly1305.Callee101e30.stackBytes]; omega)
    · rw [hrsi7, hsb]
      exact RangeApart.of_toNat (by rw [hb18]; omega) (by rw [hsb96]; simp only [Poly1305.Callee101e30.stackBytes]; omega)
        (by rw [hb18, hsb96]; simp only [Poly1305.Callee101e30.stackBytes]; omega)
    · rw [hrdi7, hr7]
      exact hCut.poly.rClamped
    · rw [hrdi7, hh7]
      exact hCut.poly.hBounded
    · rw [hret]
      decide
    · rw [hret]
      simp only [Poly1305.Callee101e30.InCode, Poly1305.Callee101e30.entry,
        Poly1305.Callee101e30.bodyEntry]
      decide
  obtain ⟨f8, u, a8, res⟩ := Poly1305.Callee101e30.call boundary r7 c7 hpre7
    (fun h => hBoundaryOutside (inCode_inProgram h))
    (by rw [hret]; exact fun h => hne _ 0x9a8 (by omega) rfl h.symm)
  have agU : AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9,
      .reg 10, .reg 11, .flags, .rip, .mem (framePointer s - BitVec.ofNat 64 96) 88,
      .mem (framePointer s + BitVec.ofNat 64 0x174) 20] s7 u := by
    have h := res.agrees
    simp only [Poly1305.Callee101e30.callChanges, hsb, hhAd, Poly1305.Callee101e30.stackBytes]
      at h
    exact h
  have fwU : FrameWrites s [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9,
      .reg 10, .reg 11, .flags, .rip, .mem (framePointer s - BitVec.ofNat 64 96) 88,
      .mem (framePointer s + BitVec.ofNat 64 0x174) 20] :=
    fw_mem2 hR (a := framePointer s - BitVec.ofNat 64 96) (n := 88)
      (b := framePointer s + BitVec.ofNat 64 0x174) (m := 20) (by simp [Component.isMem])
      (by rw [hsb96]; omega) (by rw [hsb96]; omega) (by rw [hb174]; omega)
      (by rw [hb174]; omega)
  have hspU : stackPtr u = framePointer s := by
    rw [res.rsp, hsp7]
    exact BitVec.sub_add_cancel _ _
  have invU : Inv s u outPtr plaintext.size :=
    inv_step hPre hInv res.ready
      (((((((ag1.trans ag2).trans ag3).trans ag4).trans ag5).trans ag6).trans ag7).trans agU)
      ((((((((fw1.append fw2).append fw3).append fw4).append fw5).append fw6).append fw7).append
        fwU)) hspU
  have sameU : ∀ lo hi, hi < 2 ^ 64 →
      (hi ≤ (stackPtr s).toNat - 440 + 0x18 ∨ (stackPtr s).toNat - 440 + 0x28 ≤ lo) →
      (hi ≤ (stackPtr s).toNat - 536 ∨ (stackPtr s).toNat - 440 ≤ lo) →
      (hi ≤ (stackPtr s).toNat - 440 + 0x174 ∨ (stackPtr s).toNat - 440 + 0x188 ≤ lo) →
      Same t u lo hi := by
    intro lo hi hhi h1 h2 h3
    refine (same7 lo hi hhi h1 (by omega)).trans ?_
    exact same_mem2 agU (a := framePointer s - BitVec.ofNat 64 96) (n := 88)
      (b := framePointer s + BitVec.ofNat 64 0x174) (m := 20) (by simp [Component.isMem])
      (by rw [hsb96]; omega) (by rw [hb174]; omega) (by rw [hsb96]; omega) (by rw [hb174]; omega)
                     
  have hpt : plaintext.size < 2 ^ 32 := by
    have := hPre.messageInMemory.1
    simp only [MemoryRegion.Bounded, messageRegion, userAddressLimit] at this
    omega
  have hct : (ciphertext key nonce plaintext).size = plaintext.size := by
    unfold ciphertext
    rw [ChaCha20.chacha20Encrypt_eq_xorKeystream]
    exact Common.xorKeystream_size _ _
  have hS47 : Same s4 s7 ((stackPtr s).toNat - 440 + 0x18) ((stackPtr s).toNat - 440 + 0x28) :=
    ((same_regs ag5 (by simp [Component.isMem]) _ _).trans
      (same_regs ag6 (by simp [Component.isMem]) _ _)).trans
      (same_mem ag7 (a := framePointer s - BitVec.ofNat 64 8) (n := 8)
        (by simp [Component.isMem]) (by rw [fp_sub hR _ (by omega)]; omega)
        (by rw [fp_sub hR _ (by omega)]; omega))
  have hS24 : Same s2 s4 ((stackPtr s).toNat - 440 + 0x18) ((stackPtr s).toNat - 440 + 0x20) :=
    (same_regs ag3 (by simp [Component.isMem]) _ _).trans
      (same_mem ag4 (a := framePointer s + BitVec.ofNat 64 0x20) (n := 8)
        (by simp [Component.isMem]) (by rw [hF _ (by omega)]; omega)
        (by rw [hF _ (by omega)]; omega))
  have m18 : memLoad s7.external (framePointer s + BitVec.ofNat 64 0x18) 64 = s.regValue .r8 := by
    rw [load_same hS47 (by rw [hb18]; omega) (by rw [hb18]; omega) (by omega),
      load_same hS24 (by rw [hb18]; omega) (by rw [hb18]; omega) (by omega), hmem2]
  have h18_8 : framePointer s + BitVec.ofNat 64 0x18 + BitVec.ofNat 64 8 =
      framePointer s + BitVec.ofNat 64 0x20 := by
    rw [BitVec.add_assoc]
    rfl
  have m20 : memLoad s7.external (framePointer s + BitVec.ofNat 64 0x18 + BitVec.ofNat 64 8) 64 =
      BitVec.ofNat 64 plaintext.size := by
    have hb20 := hF 0x20 (by omega)
    rw [h18_8, load_same hS47 (by rw [hb20]; omega) (by rw [hb20]; omega) (by omega), hmem4]
  have hblock : Poly1305.Callee101e30.block s7 =
      Poly1305.Mac.lengthBlock associatedData (ciphertext key nonce plaintext) := by
    unfold Poly1305.Callee101e30.block
    rw [hrsi7, block_eq (fun i hi => stack_some hInv hR hg7 (by rw [add_toNat (by omega), hb18]; omega)
      (by rw [add_toNat (by omega), hb18]; omega)) m18 m20]
    unfold Poly1305.Mac.lengthBlock
    rw [hct,
      ← hPre.associatedDataLength, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                        
  refine ⟨_, u, ((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8,
    { toInv := invU, rip := res.rip.trans hret, r15 := ?_, resultSlot := ?_, ciphertext := ?_,
      poly := ?_ }⟩
  · rw [regValue_r15, (((((((ag1.trans ag2).trans ag3).trans ag4).trans ag5).trans ag6).trans
      ag7).trans agU).read (by simp), hr15t]
  · have hb := slot_addr hR 0xa0 (by omega)
    exact word64_same (sameU _ _ (by simp only [slot, frameBase, frameBytes]; omega)
      (by simp only [slot, frameBase, frameBytes]; omega)
      (by simp only [slot, frameBase, frameBytes]; omega)
      (by simp only [slot, frameBase, frameBytes]; omega))
      (by simp only [slot, frameBase, frameBytes]; omega) hCut.resultSlot
  · have hsep := hPre.separation.1
    simp only [coreWritten, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hsep
    have hdis := hsep.2.1
    have hout := hPre.outputInMemory.1
    have hsp : s.regValue .rsp = stackPtr s := rfl
    simp only [MemoryRegion.Bounded, messageRegion, userAddressLimit] at hout
    by_cases hz : plaintext.size = 0
    · refine ⟨hCut.ciphertext.1, fun i => absurd i.isLt ?_⟩
      have := hCut.ciphertext.1
      simp only [MemoryRegion.HasLength, messageRegion] at this
      omega
    have hd : outPtr.toNat + plaintext.size ≤ (stackPtr s).toNat - 992 ∨
        (stackPtr s).toNat + 8 ≤ outPtr.toNat := by
      refine Classical.byContradiction fun hc => ?_
      apply hdis (max outPtr.toNat ((stackPtr s).toNat - 992))
      · simp only [messageRegion, MemoryRegion.Contains]
        omega
      · simp only [Stack.region, MemoryRegion.Contains, Stack.returnAddressBytes, coreStackBytes]
        rw [hsp]
        omega
    exact hasBytes_same (sameU _ _ (by simp only [messageRegion]; omega)
      (by simp only [messageRegion]; omega) (by simp only [messageRegion]; omega)
      (by simp only [messageRegion]; omega)) (by simp only [messageRegion]; omega)
      hCut.ciphertext
  · have hpad : padWords u (polyBase s) = padWords t (polyBase s) :=
      pad_same (by rw [hpbN]; exact sameU _ _ (by omega) (by omega) (by omega) (by omega))
        (by rw [hpbN]; omega)
    have hrU : rLimbs u (polyBase s) = rLimbs t (polyBase s) := by
      unfold rLimbs
      rw [hrA]
      exact limbs_same (by rw [hb160]; exact sameU _ _ (by omega) (by omega) (by omega) (by omega))
        (by rw [hb160]; omega)
    have hval := res.value
    have hbd := res.bounded
    rw [hrdi7] at hval hbd
    rw [hr7, hh7, hblock, hCut.poly.rValue, absorb_value, hCut.poly.hValue] at hval
    refine ⟨hpad ▸ hCut.poly.pad, hrU ▸ hCut.poly.rClamped, hrU ▸ hCut.poly.rValue, hbd, ?_⟩
    rw [hval, fullAcc, Poly1305.Mac.absorbBlocks_single _ _ _ (by
      rw [Poly1305.Mac.lengthBlock]
      rfl)]
    rfl

end ChaCha20Poly1305.Proofs.Core
