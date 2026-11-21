import ChaCha20Poly1305.Proofs.Core.Cuts
import ChaCha20Poly1305.Proofs.Poly1305.Callee101ce0
import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Execution
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Mov.Generated.M8R8.Triple
import X86Proofs.Program.ReadWrite.WriteFrame

namespace ChaCha20Poly1305.Proofs.Core

open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CoreContract
open ChaCha20Poly1305.Proofs.Poly1305State ChaCha20Poly1305.Proofs.Poly1305.Mac
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

set_option maxRecDepth 100000

namespace Finish

theorem tag_eq (key : Vector UInt8 32) (nonce : Vector UInt8 12)
    (associatedData plaintext : ByteArray) :
    (chacha20AeadEncrypt associatedData key nonce plaintext).2 =
      numTo16LeBytes (fullAcc key nonce associatedData plaintext + padOf (otk key nonce)) := by
  simp only [chacha20AeadEncrypt]
  rw [poly1305Mac_aeadMacData]
  rfl

def Wr (s : RamState) (n : Nat) : Prop :=
  (resultRegion s).Contains n ∨ (frameBase s - 56 ≤ n ∧ n < frameBase s + 0x50)

structure Track [bindings : Machine.Bindings] (s t u : RamState) : Prop where
  ready : ReadyToStep u
  code : CodeIn Extracted.programImage u
  sse : Prelude.SupportedSSE bindings.processor u
  df : DirectionFlagUnset u
  same : ∀ a : BitVec 64, ¬ Wr s a.toNat → u.external[a]? = t.external[a]?
  grows : ∀ a : BitVec 64, (t.external[a]?).isSome → (u.external[a]?).isSome

variable [Machine.Bindings] {s t u : RamState} {key : Vector UInt8 32}
  {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}
  {length : Nat}

structure Facts (s : RamState) (outPtr : BitVec 64) (length : Nat) : Prop where
  low : 992 ≤ (stackPtr s).toNat
  high : (stackPtr s).toNat + 8 < 2 ^ 32
  align : (stackPtr s).toNat % 16 = 8
  resultHigh : (s.regValue .rdi).toNat + 17 < 2 ^ 32
  apart : (s.regValue .rdi).toNat + 17 ≤ (stackPtr s).toNat - 992 ∨
    (stackPtr s).toNat + 8 ≤ (s.regValue .rdi).toNat
  wrOk : ∀ a : BitVec 64, Wr s a.toNat → ¬ InProgram a ∧ ¬ pageTables.Contains a.toNat ∧
    ∃ region ∈ coreWritten s outPtr length, region.Contains a.toNat

omit [Machine.Bindings] in
theorem region_sep {r r' : MemoryRegion} (h : r.Disjoint r') (hr : 0 < r.size)
    (hr' : 0 < r'.size) : r.start + r.size ≤ r'.start ∨ r'.start + r'.size ≤ r.start := by
  refine Classical.byContradiction fun hc => ?_
  exact h (max r.start r'.start) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩

omit [Machine.Bindings] in
theorem stack_bounds (S A : Nat) (h1 : 992 ≤ S) (h2 : S - 440 - 56 ≤ A ∧ A < S - 440 + 80) :
    S - 992 ≤ A ∧ A < S - 992 + (S + 8 - (S - 992)) := by
  omega

theorem facts (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) :
    Facts s outPtr plaintext.size := by
  obtain ⟨hBounded, -, hNo, hAlign⟩ := hPre.stack
  have hsp : (stackPtr s).toNat = (s.regValue .rsp).toNat := rfl
  simp only [Stack.region, MemoryRegion.Bounded, userAddressLimit, Stack.returnAddressBytes,
    coreStackBytes] at hBounded
  simp only [Stack.NoUnderflow, coreStackBytes] at hNo
  simp only [MemoryRegion.Aligned, Stack.returnSlot, Stack.callAlignment,
    Stack.returnAddressBytes] at hAlign
  have hres := hPre.resultInMemory.1
  simp only [resultRegion, registerRegion, MemoryRegion.Bounded, userAddressLimit,
    resultBytes] at hres
  have hpair := hPre.separation.1
  simp only [coreWritten, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hpair
  have hsep := region_sep hpair.1.2 (by simp [resultRegion, registerRegion, resultBytes])
    (by simp only [Stack.region, Stack.returnAddressBytes]; omega)
  simp only [resultRegion, registerRegion, resultBytes, Stack.region, Stack.returnAddressBytes,
    coreStackBytes] at hsep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 5
  all_goals (try rw [hsp])
  all_goals (try (clear hpair hPre; omega))
  intro a ha
  have hin : ∃ region ∈ coreWritten s outPtr plaintext.size, region.Contains a.toNat := by
    rcases ha with ha | ha
    · exact ⟨_, by simp only [coreWritten, List.mem_cons, true_or], ha⟩
    · refine ⟨Stack.region s coreStackBytes,
        by simp only [coreWritten, List.mem_cons, true_or, or_true], ?_⟩
      simp only [Stack.region, MemoryRegion.Contains, coreStackBytes, Stack.returnAddressBytes]
      simp only [frameBase, frameBytes] at ha
      change _ ≤ _ ∧ _ < _ at ha
      rw [hsp] at ha
      exact stack_bounds _ _ hNo ha
  obtain ⟨region, hm, hc⟩ := hin
  have hav : ¬ (InProgram a ∨ pageTables.Contains a.toNat) := hPre.separation.2.2 region hm a hc
  refine ⟨fun h => hav (Or.inl h), fun h => hav (Or.inr h), ?_⟩
  exact ⟨region, hm, hc⟩

theorem Track.of_agrees {cs : List Component} {v : RamState} (T : Track s t u)
    (hF : Facts s outPtr length) (ha : AgreesExcept cs u v) (hr : ReadyToStep v)
    (hw : ∀ c ∈ cs, ∀ a, c.Covers a → Wr s a.toNat) (hdf : Component.df ∉ cs) :
    Track s t v where
  ready := hr
  code := CodeIn.of_agreesExcept ha
    (fun x hx c hc hcov => (hF.wrOk x.1 (hw c hc x.1 hcov)).1 (inProgram_of_mem hx)) T.code
  sse := SupportedSSE.of_agreesExcept ha T.sse
  df := ha.directionFlagClear hdf T.df
  same := fun a hna => (ha.byte (fun c hc hcov => hna (hw c hc a hcov))).trans (T.same a hna)
  grows := fun a h => ha.grow a (T.grows a h)

theorem Track.step {pre : RamState → Prop} {e : RamState → Effect} {p : BitVec 64}
    {bytes : List UInt8} {boundary : ReturnBoundary} (T : Track s t u)
    (hF : Facts s outPtr length) (hStep : StepEffect pre (codeRange p bytes) e)
    (hb : CodeIn (codeRange p bytes) u) (hpre : pre u) (hne : (e u).rip ≠ boundary.rip)
    (hw : ∀ c ∈ (e u).components, ∀ a, c.Covers a → Wr s a.toNat)
    (hdf : Component.df ∉ (e u).components) :
    ∃ v, Advances boundary 1 u v ∧ Track s t v ∧ (e u).Holds u v := by
  obtain ⟨v, hadv, hr, he⟩ := hStep.advances T.ready hb hpre hne
  exact ⟨v, hadv, T.of_agrees hF he.agrees hr hw hdf, he⟩

theorem Track.start (hCut : Cut5 s t key nonce associatedData plaintext outPtr) : Track s t t where
  ready := ReadyToStep.of_supported hCut.machine hCut.environment.smrr
    hCut.environment.memoryType
    (DecoderFeatures.of_supported hCut.machine hCut.environment.leadingZeroCount)
  code := hCut.code
  sse := hCut.machine.sse
  df := hCut.directionFlagUnset
  same := fun _ _ => rfl
  grows := fun _ h => h

omit [Machine.Bindings] in
theorem textBytes_size : Extracted.textBytes.size = 11759 := by decide

omit [Machine.Bindings] in
theorem inProgram_at (p : BitVec 64) (h₁ : 0x100000 ≤ p.toNat) (h₂ : p.toNat < 0x102def) :
    InProgram p := by
  have h := text_address_in_program (p.toNat - 0x100000) (by rw [textBytes_size]; omega)
  have he : Extracted.textAddress + BitVec.ofNat 64 (p.toNat - 0x100000) = p := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, show Extracted.textAddress.toNat = 0x100000 from rfl, BitVec.toNat_ofNat]
    omega
  rwa [he] at h

omit [Machine.Bindings] in
theorem code_apart {a p : BitVec 64} {len codeLen : Nat}
    (ha : ∀ i < len, ¬ InProgram (a + BitVec.ofNat 64 i))
    (h₁ : 0x100000 ≤ p.toNat) (h₂ : p.toNat + codeLen ≤ 0x102def) :
    RangeApart a len p codeLen := by
  intro i hi j hj he
  apply ha i hi
  rw [he]
  apply inProgram_at
  · rw [toNat_add_ofNat _ _ (by omega)]; omega
  · rw [toNat_add_ofNat _ _ (by omega)]; omega

omit [Machine.Bindings] in
theorem loadBytes_loop_isSome {memory : Machine.Ram} {address : BitVec 64}
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

omit [Machine.Bindings] in
theorem word64At_memLoad {region : MemoryRegion} {memory : Machine.Ram} {value : BitVec 64}
    (h : region.Word64At memory value) :
    memLoad memory (BitVec.ofNat 64 region.start) 64 = value := by
  have hs : ∀ i < 8, (memory[BitVec.ofNat 64 region.start + BitVec.ofNat 64 i]?).isSome := by
    simpa only [Nat.zero_add] using loadBytes_loop_isSome h.2
  have hb : Bytes memory (BitVec.ofNat 64 region.start) 8
      (storedByte (memLoad memory (BitVec.ofNat 64 region.start) 64)) :=
    Bytes.of_memLoad (n := 64) hs
  exact Except.ok.inj (hb.loadBytes64.symm.trans h.2)

omit [Machine.Bindings] in
theorem frame_toNat (hF : Facts s outPtr length) (d : Nat) (hd : d < 2 ^ 32) :
    (framePointer s + BitVec.ofNat 64 d).toNat = frameBase s + d := by
  have h1 := hF.low
  have h2 := hF.high
  have hfp : (framePointer s).toNat = frameBase s := by
    simp only [framePointer, frameBase, frameBytes, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [toNat_add_ofNat _ _ (by rw [hfp]; simp only [frameBase, frameBytes]; omega), hfp]

omit [Machine.Bindings] in
theorem frameBase_eq : frameBase s = (stackPtr s).toNat - 440 := rfl

omit [Machine.Bindings] in
theorem frame_sub_toNat (hF : Facts s outPtr length) (d : Nat) (hd : d ≤ 440) :
    (framePointer s - BitVec.ofNat 64 d).toNat = frameBase s - d := by
  have h1 := hF.low
  have h2 := hF.high
  simp only [framePointer, frameBase, frameBytes, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem Track.isSome (T : Track s t u)
    (hCut : Cut5 s t key nonce associatedData plaintext outPtr) {a : BitVec 64}
    {region : MemoryRegion} (hm : region ∈ coreWritten s outPtr plaintext.size)
    (hc : region.Contains a.toNat) : (u.external[a]?).isSome := by
  obtain ⟨b, hb⟩ := hCut.allocated region hm a hc
  exact T.grows a (by simp [hb])

omit [Machine.Bindings] in
theorem stack_mem (hF : Facts s outPtr length) {a : BitVec 64}
    (h₁ : frameBase s - 56 ≤ a.toNat) (h₂ : a.toNat < frameBase s + 448) :
    Stack.region s coreStackBytes ∈ coreWritten s outPtr length ∧
      (Stack.region s coreStackBytes).Contains a.toNat := by
  have := hF.low
  refine ⟨by simp [coreWritten], ?_⟩
  simp only [Stack.region, MemoryRegion.Contains, coreStackBytes]
  simp only [frameBase, frameBytes] at h₁ h₂
  change (stackPtr s).toNat - 992 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 992 +
    ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 992))
  omega

theorem Track.readable (T : Track s t u)
    (hCut : Cut5 s t key nonce associatedData plaintext outPtr) {a : BitVec 64} {len : Nat}
    (hlow : a.toNat + len ≤ 2 ^ 32)
    (h : ∀ i < len, ∃ region ∈ coreWritten s outPtr plaintext.size,
      region.Contains (a + BitVec.ofNat 64 i).toNat) : MemReadable u a len :=
  ⟨hlow, fun i hi => by
    obtain ⟨region, hm, hc⟩ := h i hi
    exact T.isSome hCut hm hc⟩

omit [Machine.Bindings] in
theorem stack_range (hF : Facts s outPtr length) {a : BitVec 64} {len : Nat}
    (h₁ : frameBase s - 56 ≤ a.toNat) (h₂ : a.toNat + len ≤ frameBase s + 448) :
    ∀ i < len, ∃ region ∈ coreWritten s outPtr length,
      region.Contains (a + BitVec.ofNat 64 i).toNat := by
  intro i hi
  have := hF.high
  have hlt : a.toNat + i < 2 ^ 64 := by simp only [frameBase, frameBytes] at h₂; omega
  have ha := stack_mem hF (a := a + BitVec.ofNat 64 i)
    (by rw [toNat_add_ofNat _ _ hlt]; omega) (by rw [toNat_add_ofNat _ _ hlt]; omega)
  exact ⟨_, ha.1, ha.2⟩

omit [Machine.Bindings] in
theorem not_table_byte {x : Nat} (h : ¬ pageTables.Contains x) : PageTableEntriesApart x 1 := by
  simp only [pageTables, MemoryRegion.Contains] at h
  omega

theorem Track.writable (T : Track s t u)
    (hCut : Cut5 s t key nonce associatedData plaintext outPtr)
    (hF : Facts s outPtr plaintext.size) {a : BitVec 64} {len : Nat} (hpos : 0 < len)
    (hlow : a.toNat + len ≤ 2 ^ 32) (h : ∀ i < len, Wr s (a + BitVec.ofNat 64 i).toNat) :
    MemWritable u a len :=
  ⟨hlow, fun i hi => by
    obtain ⟨-, -, region, hm, hc⟩ := hF.wrOk _ (h i hi)
    exact T.isSome hCut hm hc,
   PageTableEntriesApart.of_bytes hpos hlow fun i hi =>
    not_table_byte (hF.wrOk _ (h i hi)).2.1⟩

omit [Machine.Bindings] in
theorem wr_frame (hF : Facts s outPtr length) {a : BitVec 64} {len : Nat}
    (h₁ : frameBase s - 56 ≤ a.toNat) (h₂ : a.toNat + len ≤ frameBase s + 0x50) :
    ∀ i < len, Wr s (a + BitVec.ofNat 64 i).toNat := by
  intro i hi
  have := hF.high
  have hlt : a.toNat + i < 2 ^ 64 := by simp only [frameBase, frameBytes] at h₂; omega
  right
  rw [toNat_add_ofNat _ _ hlt]
  omega

omit [Machine.Bindings] in
theorem wr_result (hF : Facts s outPtr length) {a : BitVec 64} {len : Nat}
    (h₁ : (s.regValue .rdi).toNat ≤ a.toNat) (h₂ : a.toNat + len ≤ (s.regValue .rdi).toNat + 17) :
    ∀ i < len, Wr s (a + BitVec.ofNat 64 i).toNat := by
  intro i hi
  have := hF.resultHigh
  have hlt : a.toNat + i < 2 ^ 64 := by omega
  left
  simp only [resultRegion, registerRegion, resultBytes, MemoryRegion.Contains]
  rw [toNat_add_ofNat _ _ hlt]
  omega

omit [Machine.Bindings] in
theorem covers_wr {a x : BitVec 64} {len : Nat} (h : ∀ i < len, Wr s (a + BitVec.ofNat 64 i).toNat)
    (hc : (Component.mem a len).Covers x) : Wr s x.toNat := by
  obtain ⟨i, hi, rfl⟩ := hc
  exact h i hi

omit [Machine.Bindings] in
theorem regs_wr {cs : List Component} (h : ∀ c ∈ cs, c.isMem = false) :
    ∀ c ∈ cs, ∀ a, c.Covers a → Wr s a.toNat := by
  intro c hc a hcov
  have := h c hc
  cases c <;> simp_all [Component.Covers, Component.isMem]

omit [Machine.Bindings] in
theorem not_wr_program (hF : Facts s outPtr length) {a : BitVec 64} {len : Nat}
    (h : ∀ i < len, Wr s (a + BitVec.ofNat 64 i).toNat) :
    ∀ i < len, ¬ InProgram (a + BitVec.ofNat 64 i) :=
  fun i hi => (hF.wrOk _ (h i hi)).1

omit [Machine.Bindings] in
theorem base_addr {u : RamState} {b : BitVec 4} {B : BitVec 64}
    (h : (Operand.reg (b.setWidth 5) : Operand 64).read u = B) (d : Disp) (x : BitVec 64) :
    (AddrMode.base b d).addr u x = B + d.value := by
  simp only [AddrMode.addr, AddrMode.reg64, h]

omit [Machine.Bindings] in
theorem sib_addr {u : RamState} {B : BitVec 64} (h : stackPtr u = B) (d : Disp)
    (x : BitVec 64) : (AddrMode.sib 4 none 0 d).addr u x = B + d.value := by
  simp only [AddrMode.addr, AddrMode.reg64]
  rw [show ((4 : BitVec 4).setWidth 5) = (4 : BitVec 5) from rfl, ← stackPtr_eq_read, h]

omit [Machine.Bindings] in
theorem not_wr_high (hF : Facts s outPtr length) {x : BitVec 64}
    (h₁ : frameBase s + 0x50 ≤ x.toNat) (h₂ : x.toNat < frameBase s + 448) : ¬ Wr s x.toNat := by
  have := hF.apart
  have := hF.low
  simp only [Wr, resultRegion, registerRegion, resultBytes, MemoryRegion.Contains]
  simp only [frameBase, frameBytes] at h₁ h₂ ⊢
  omega

omit [Machine.Bindings] in
theorem frame_byte_toNat (hF : Facts s outPtr length) (d i : Nat) (hd : d + i < 448) :
    (framePointer s + BitVec.ofNat 64 d + BitVec.ofNat 64 i).toNat = frameBase s + d + i := by
  rw [add_ofNat_add_ofNat, frame_toNat hF _ (by omega), Nat.add_assoc]

theorem Track.high_byte (T : Track s t u) (hF : Facts s outPtr length) (d i : Nat)
    (h₁ : 0x50 ≤ d + i) (h₂ : d + i < 448) :
    u.external[framePointer s + BitVec.ofNat 64 d + BitVec.ofNat 64 i]? =
      t.external[framePointer s + BitVec.ofNat 64 d + BitVec.ofNat 64 i]? :=
  T.same _ (not_wr_high hF (by rw [frame_byte_toNat hF d i h₂]; omega)
    (by rw [frame_byte_toNat hF d i h₂]; omega))

theorem Track.high_load (T : Track s t u) (hF : Facts s outPtr length) (d : Nat)
    (h₁ : 0x50 ≤ d) (h₂ : d + 8 ≤ 448) :
    memLoad u.external (framePointer s + BitVec.ofNat 64 d) 64 =
      memLoad t.external (framePointer s + BitVec.ofNat 64 d) 64 := by
  apply memLoad_congr
  intro i hi
  simp only [memByte]
  change (u.external[_]?).getD 0 = (t.external[_]?).getD 0
  rw [T.high_byte hF d i (by omega) (by omega)]

omit [Machine.Bindings] in
theorem polyBase_eq : polyBase s = framePointer s + BitVec.ofNat 64 0x150 := rfl

omit [Machine.Bindings] in
theorem keep_qword {u v : RamState} (hF : Facts s outPtr length) {d d' : Nat}
    (hkeep : ∀ x, (∀ i < 8, x ≠ framePointer s + BitVec.ofNat 64 d' + BitVec.ofNat 64 i) →
      v.external[x]? = u.external[x]?)
    (hd : d + 8 ≤ d' ∨ d' + 8 ≤ d) (h₁ : d + 8 ≤ 448) (h₂ : d' + 8 ≤ 448) :
    memLoad v.external (framePointer s + BitVec.ofNat 64 d) 64 =
      memLoad u.external (framePointer s + BitVec.ofNat 64 d) 64 := by
  apply memLoad_congr
  intro i hi
  simp only [memByte]
  change (v.external[_]?).getD 0 = (u.external[_]?).getD 0
  rw [hkeep]
  intro j hj he
  have := congrArg BitVec.toNat he
  rw [frame_byte_toNat hF d i (by omega), frame_byte_toNat hF d' j (by omega)] at this
  omega

omit [Machine.Bindings] in
theorem ne_boundary {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip)
    (q : BitVec 64) (h₁ : 0x100000 ≤ q.toNat) (h₂ : q.toNat < 0x102def) : q ≠ boundary.rip :=
  fun h => hOut (h ▸ inProgram_at q h₁ h₂)

omit [Machine.Bindings] in
theorem poly_toNat (hF : Facts s outPtr length) (n : Nat) (hn : n ≤ 56) :
    (polyBase s + BitVec.ofNat 64 n).toNat = frameBase s + 0x150 + n := by
  rw [polyBase_eq, frame_byte_toNat hF _ _ (by omega)]

theorem poly_load (T : Track s t u) (hF : Facts s outPtr length) (n : Nat) (hn : n + 8 ≤ 56) :
    memLoad u.external (polyBase s + BitVec.ofNat 64 n) 64 =
      memLoad t.external (polyBase s + BitVec.ofNat 64 n) 64 := by
  rw [polyBase_eq, add_ofNat_add_ofNat]
  exact T.high_load hF _ (by omega) (by omega)

theorem load_poly {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip)
    (hCut : Cut5 s t key nonce associatedData plaintext outPtr)
    (hF : Facts s outPtr plaintext.size) (T : Track s t u) (p : BitVec 64) (reg : BitVec 3)
    (dst : BitVec 5) (hdst : gprNumber 0 (rexR (0x49 : UInt8).toBitVec) reg = dst)
    (hdst4 : dst ≠ 4) (hdst15 : dst ≠ 15) (disp : Disp) (offN len : Nat)
    (hlen : movLoadLen (AddrMode.base 15 disp) = len) (hv : (AddrMode.base 15 disp).Valid)
    (hoff : disp.value = BitVec.ofNat 64 offN) (hoffN : offN + 8 ≤ 56)
    (hp₁ : 0x100000 ≤ p.toNat) (hp₂ : p.toNat + len < 0x102def)
    (hc : CodeIn (codeRange p (0x49 :: 0x8B :: (AddrMode.base 15 disp).modrm reg ::
      (AddrMode.base 15 disp).tail)) u)
    (hrip : u.RIP = p) (hsp : stackPtr u = framePointer s)
    (hr15 : (Operand.reg 15 : Operand 64).read u = polyBase s) :
    ∃ v, Advances boundary 1 u v ∧ Track s t v ∧ v.RIP = p + BitVec.ofNat 64 len ∧
      stackPtr v = framePointer s ∧ (Operand.reg 15 : Operand 64).read v = polyBase s ∧
      (Operand.reg dst : Operand 64).read v =
        memLoad t.external (polyBase s + BitVec.ofNat 64 offN) 64 ∧
      v.external = u.external ∧
      ∀ r : BitVec 5, r ≠ dst → (Operand.reg r : Operand 64).read v =
        (Operand.reg r : Operand 64).read u := by
  have haddr : ∀ x, (AddrMode.base 15 disp).addr u x = polyBase s + BitVec.ofNat 64 offN :=
    fun x => by rw [base_addr (b := 15) hr15, hoff]
  have := hF.high
  obtain ⟨v, a, T', e⟩ := T.step hF
    (mov_r64_m64_effect_step p 0x49 (by unfold RexWPrefix; decide) reg (.base 15 disp) hv
      rfl rfl) hc
    ⟨hrip, by
      rw [haddr]
      refine T.readable hCut ?_ (stack_range hF ?_ ?_) <;>
        rw [poly_toNat hF _ (by omega)] <;> simp only [frameBase, frameBytes] <;> omega⟩
    (by
      show p + BitVec.ofNat 64 (movLoadLen (AddrMode.base 15 disp)) ≠ _
      rw [hlen]
      exact ne_boundary hOut _ (by rw [toNat_add_ofNat _ _ (by omega)]; omega)
        (by rw [toNat_add_ofNat _ _ (by omega)]; omega))
    (regs_wr (by simp [Component.isMem])) (by simp)
  rw [hdst] at e
  have hag : AgreesExcept [.reg dst, .rip] u v := e.agrees
  refine ⟨v, a, T', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e.rip]
    show p + BitVec.ofNat 64 (movLoadLen (AddrMode.base 15 disp)) = _
    rw [hlen]
  · rw [stackPtr_eq_read, hag.read (by simp; exact fun h => hdst4 h.symm), ← stackPtr_eq_read, hsp]
  · rw [hag.read (by simp; exact fun h => hdst15 h.symm), hr15]
  · have h := e.writes
    change (Operand.reg dst : Operand 64).read v =
      (Operand.mem ((AddrMode.base 15 disp).addr u _) : Operand 64).read u at h
    rw [h, haddr]
    exact poly_load T hF offN hoffN
  · exact hag.external (by simp [Component.Covers])
  · intro r hr
    exact hag.read (by simp [hr])

theorem store_frame {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip)
    (hCut : Cut5 s t key nonce associatedData plaintext outPtr)
    (hF : Facts s outPtr plaintext.size) (T : Track s t u) (p : BitVec 64) (reg : BitVec 3)
    (src : BitVec 5) (hsrc : gprNumber 0 (rexR (0x48 : UInt8).toBitVec) reg = src)
    (disp : Disp) (dN len : Nat) (hlen : 3 + (AddrMode.sib 4 none 0 disp).tail.length = len)
    (hv : (AddrMode.sib 4 none 0 disp).Valid)
    (hd : disp.value = BitVec.ofNat 64 dN) (hdN₁ : 0x18 ≤ dN) (hdN₂ : dN + 8 ≤ 0x50)
    (hp₁ : 0x100000 ≤ p.toNat) (hp₂ : p.toNat + len < 0x102def)
    (hc : CodeIn (codeRange p (0x48 :: 0x89 :: (AddrMode.sib 4 none 0 disp).modrm reg ::
      (AddrMode.sib 4 none 0 disp).tail)) u)
    (hrip : u.RIP = p) (hsp : stackPtr u = framePointer s) :
    ∃ v, Advances boundary 1 u v ∧ Track s t v ∧ v.RIP = p + BitVec.ofNat 64 len ∧
      memLoad v.external (framePointer s + BitVec.ofNat 64 dN) 64 =
        (Operand.reg src : Operand 64).read u ∧
      (∀ x, (∀ i < 8, x ≠ framePointer s + BitVec.ofNat 64 dN + BitVec.ofNat 64 i) →
        v.external[x]? = u.external[x]?) ∧
      ∀ r : BitVec 5, (Operand.reg r : Operand 64).read v = (Operand.reg r : Operand 64).read u := by
  have haddr : ∀ x, (AddrMode.sib 4 none 0 disp).addr u x =
      framePointer s + BitVec.ofNat 64 dN := fun x => by rw [sib_addr hsp, hd]
  have haddr' : storeAddrAt p (AddrMode.sib 4 none 0 disp) (3 + (AddrMode.sib 4 none 0 disp).tail.length) u =
      framePointer s + BitVec.ofNat 64 dN := haddr _
  have := hF.high
  have hfn := frame_toNat hF dN (by omega)
  have hw := wr_frame hF (a := framePointer s + BitVec.ofNat 64 dN) (len := 8)
    (by rw [hfn]; omega) (by rw [hfn]; omega)
  obtain ⟨v, a, T', e⟩ := T.step hF
    (mov_m64_r64_effect_step p 0x48 (by unfold RexWPrefix; decide) reg
      (.sib 4 none 0 disp) hv rfl rfl) hc
    ⟨hrip, by
      show MemWritable u ((AddrMode.sib 4 none 0 disp).addr u _) 8
      rw [haddr]
      exact T.writable hCut hF (by omega) (by rw [hfn]; simp only [frameBase, frameBytes]; omega) hw,
     by
      show RangeApart ((AddrMode.sib 4 none 0 disp).addr u _) 8 p _
      rw [haddr, hlen]
      exact code_apart (not_wr_program hF hw) hp₁ (by omega)⟩
    (by
      show p + BitVec.ofNat 64 (3 + (AddrMode.sib 4 none 0 disp).tail.length) ≠ _
      rw [hlen]
      exact ne_boundary hOut _ (by rw [toNat_add_ofNat _ _ (by omega)]; omega)
        (by rw [toNat_add_ofNat _ _ (by omega)]; omega))
    (by
      intro c hc x hcov
      simp only [movM64R64Effect, storeEffect_components, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      rcases hc with rfl | rfl
      · rw [haddr'] at hcov
        exact covers_wr hw hcov
      · exact absurd hcov (by simp [Component.Covers]))
    (by simp [movM64R64Effect])
  rw [hsrc] at e
  have hag : AgreesExcept [.mem (framePointer s + BitVec.ofNat 64 dN) 8, .rip] u v := by
    have h := e.agrees
    simp only [movM64R64Effect, storeEffect_components] at h
    rw [haddr'] at h
    exact h
  refine ⟨v, a, T', ?_, ?_, ?_, ?_⟩
  · rw [e.rip]
    show p + BitVec.ofNat 64 (3 + (AddrMode.sib 4 none 0 disp).tail.length) = _
    rw [hlen]
  · have h := e.writes
    change (Operand.mem ((AddrMode.sib 4 none 0 disp).addr u _) : Operand 64).read v =
      (Operand.reg src : Operand 64).read u at h
    rw [haddr] at h
    exact h
  · intro x hx
    apply hag.byte
    intro c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := hcov
      exact hx i hi rfl
    · exact hcov
  · intro r
    exact hag.read (by simp)

theorem copy_state {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip)
    (hCut : Cut5 s t key nonce associatedData plaintext outPtr)
    (hF : Facts s outPtr plaintext.size) :
    ∃ fuel u, Advances boundary fuel t u ∧ Track s t u ∧ u.RIP = 0x1009e6 ∧
      stackPtr u = framePointer s ∧
      ∀ k < 7, memLoad u.external (framePointer s + BitVec.ofNat 64 (0x18 + 8 * k)) 64 =
        memLoad t.external (polyBase s + BitVec.ofNat 64 (8 * k)) 64 := by
  have T_0 := Track.start hCut
  have rip_0 : t.RIP = 0x1009a8 := hCut.rip
  have sp_0 : stackPtr t = framePointer s := hCut.rsp
  have r15_0 : (Operand.reg 15 : Operand 64).read t = polyBase s := hCut.r15
  obtain ⟨v1, a_v1, T_v1, rip_v1, sp_v1, r15_v1, val_v1, ext_v1, regs_v1⟩ :=
    load_poly hOut hCut hF T_0 0x1009a8 0 0 rfl (by decide) (by decide) (.d8 0x30) 0x30 4 rfl
      (by decide) rfl (by decide) (by decide) (by decide)
      (program_text_slice T_0.code 0x9a8 4 (by decide +kernel)) rip_0 sp_0 r15_0
  obtain ⟨w1, a_w1, T_w1, rip_w1, val_w1, keep_w1, regs_w1⟩ :=
    store_frame hOut hCut hF T_v1 0x1009ac 0 0 rfl (.d8 0x48) 0x48 5 rfl (by decide) rfl
      (by decide) (by decide) (by decide) (by decide)
      (program_text_slice T_v1.code 0x9ac 5 (by decide +kernel)) rip_v1 sp_v1
  have sp_w1 : stackPtr w1 = framePointer s := by
    rw [stackPtr_eq_read, regs_w1, ← stackPtr_eq_read, sp_v1]
  have r15_w1 : (Operand.reg 15 : Operand 64).read w1 = polyBase s := by
    rw [regs_w1, r15_v1]
  obtain ⟨v2, a_v2, T_v2, rip_v2, sp_v2, r15_v2, val_v2, ext_v2, regs_v2⟩ :=
    load_poly hOut hCut hF T_w1 0x1009b1 0 0 rfl (by decide) (by decide) (.d8 0x28) 0x28 4 rfl
      (by decide) rfl (by decide) (by decide) (by decide)
      (program_text_slice T_w1.code 0x9b1 4 (by decide +kernel)) rip_w1 sp_w1 r15_w1
  obtain ⟨w2, a_w2, T_w2, rip_w2, val_w2, keep_w2, regs_w2⟩ :=
    store_frame hOut hCut hF T_v2 0x1009b5 0 0 rfl (.d8 0x40) 0x40 5 rfl (by decide) rfl
      (by decide) (by decide) (by decide) (by decide)
      (program_text_slice T_v2.code 0x9b5 5 (by decide +kernel)) rip_v2 sp_v2
  have sp_w2 : stackPtr w2 = framePointer s := by
    rw [stackPtr_eq_read, regs_w2, ← stackPtr_eq_read, sp_v2]
  have r15_w2 : (Operand.reg 15 : Operand 64).read w2 = polyBase s := by
    rw [regs_w2, r15_v2]
  obtain ⟨v3, a_v3, T_v3, rip_v3, sp_v3, r15_v3, val_v3, ext_v3, regs_v3⟩ :=
    load_poly hOut hCut hF T_w2 0x1009ba 0 0 rfl (by decide) (by decide) (.d8 0x20) 0x20 4 rfl
      (by decide) rfl (by decide) (by decide) (by decide)
      (program_text_slice T_w2.code 0x9ba 4 (by decide +kernel)) rip_w2 sp_w2 r15_w2
  obtain ⟨w3, a_w3, T_w3, rip_w3, val_w3, keep_w3, regs_w3⟩ :=
    store_frame hOut hCut hF T_v3 0x1009be 0 0 rfl (.d8 0x38) 0x38 5 rfl (by decide) rfl
      (by decide) (by decide) (by decide) (by decide)
      (program_text_slice T_v3.code 0x9be 5 (by decide +kernel)) rip_v3 sp_v3
  have sp_w3 : stackPtr w3 = framePointer s := by
    rw [stackPtr_eq_read, regs_w3, ← stackPtr_eq_read, sp_v3]
  have r15_w3 : (Operand.reg 15 : Operand 64).read w3 = polyBase s := by
    rw [regs_w3, r15_v3]
  obtain ⟨v4, a_v4, T_v4, rip_v4, sp_v4, r15_v4, val_v4, ext_v4, regs_v4⟩ :=
    load_poly hOut hCut hF T_w3 0x1009c3 0 0 rfl (by decide) (by decide) (.d8 0x18) 0x18 4 rfl
      (by decide) rfl (by decide) (by decide) (by decide)
      (program_text_slice T_w3.code 0x9c3 4 (by decide +kernel)) rip_w3 sp_w3 r15_w3
  obtain ⟨w4, a_w4, T_w4, rip_w4, val_w4, keep_w4, regs_w4⟩ :=
    store_frame hOut hCut hF T_v4 0x1009c7 0 0 rfl (.d8 0x30) 0x30 5 rfl (by decide) rfl
      (by decide) (by decide) (by decide) (by decide)
      (program_text_slice T_v4.code 0x9c7 5 (by decide +kernel)) rip_v4 sp_v4
  have sp_w4 : stackPtr w4 = framePointer s := by
    rw [stackPtr_eq_read, regs_w4, ← stackPtr_eq_read, sp_v4]
  have r15_w4 : (Operand.reg 15 : Operand 64).read w4 = polyBase s := by
    rw [regs_w4, r15_v4]
  obtain ⟨v5, a_v5, T_v5, rip_v5, sp_v5, r15_v5, val_v5, ext_v5, regs_v5⟩ :=
    load_poly hOut hCut hF T_w4 0x1009cc 0 0 rfl (by decide) (by decide) (.d8 0x10) 0x10 4 rfl
      (by decide) rfl (by decide) (by decide) (by decide)
      (program_text_slice T_w4.code 0x9cc 4 (by decide +kernel)) rip_w4 sp_w4 r15_w4
  obtain ⟨w5, a_w5, T_w5, rip_w5, val_w5, keep_w5, regs_w5⟩ :=
    store_frame hOut hCut hF T_v5 0x1009d0 0 0 rfl (.d8 0x28) 0x28 5 rfl (by decide) rfl
      (by decide) (by decide) (by decide) (by decide)
      (program_text_slice T_v5.code 0x9d0 5 (by decide +kernel)) rip_v5 sp_v5
  have sp_w5 : stackPtr w5 = framePointer s := by
    rw [stackPtr_eq_read, regs_w5, ← stackPtr_eq_read, sp_v5]
  have r15_w5 : (Operand.reg 15 : Operand 64).read w5 = polyBase s := by
    rw [regs_w5, r15_v5]
  obtain ⟨v6, a_v6, T_v6, rip_v6, sp_v6, r15_v6, val_v6, ext_v6, regs_v6⟩ :=
    load_poly hOut hCut hF T_w5 0x1009d5 0 0 rfl (by decide) (by decide) .none 0 3 rfl
      (by decide) rfl (by decide) (by decide) (by decide)
      (program_text_slice T_w5.code 0x9d5 3 (by decide +kernel)) rip_w5 sp_w5 r15_w5
  obtain ⟨v7, a_v7, T_v7, rip_v7, sp_v7, r15_v7, val_v7, ext_v7, regs_v7⟩ :=
    load_poly hOut hCut hF T_v6 0x1009d8 1 1 rfl (by decide) (by decide) (.d8 0x08) 0x08 4 rfl
      (by decide) rfl (by decide) (by decide) (by decide)
      (program_text_slice T_v6.code 0x9d8 4 (by decide +kernel)) rip_v6 sp_v6 r15_v6
  obtain ⟨w6, a_w6, T_w6, rip_w6, val_w6, keep_w6, regs_w6⟩ :=
    store_frame hOut hCut hF T_v7 0x1009dc 1 1 rfl (.d8 0x20) 0x20 5 rfl (by decide) rfl
      (by decide) (by decide) (by decide) (by decide)
      (program_text_slice T_v7.code 0x9dc 5 (by decide +kernel)) rip_v7 sp_v7
  have sp_w6 : stackPtr w6 = framePointer s := by
    rw [stackPtr_eq_read, regs_w6, ← stackPtr_eq_read, sp_v7]
  have r15_w6 : (Operand.reg 15 : Operand 64).read w6 = polyBase s := by
    rw [regs_w6, r15_v7]
  obtain ⟨w7, a_w7, T_w7, rip_w7, val_w7, keep_w7, regs_w7⟩ :=
    store_frame hOut hCut hF T_w6 0x1009e1 0 0 rfl (.d8 0x18) 0x18 5 rfl (by decide) rfl
      (by decide) (by decide) (by decide) (by decide)
      (program_text_slice T_w6.code 0x9e1 5 (by decide +kernel)) rip_w6 sp_w6
  have sp_w7 : stackPtr w7 = framePointer s := by
    rw [stackPtr_eq_read, regs_w7, ← stackPtr_eq_read, sp_w6]
  have r15_w7 : (Operand.reg 15 : Operand 64).read w7 = polyBase s := by
    rw [regs_w7, r15_w6]
  refine ⟨_, w7, a_v1.trans (a_w1.trans (a_v2.trans (a_w2.trans (a_v3.trans (a_w3.trans
    (a_v4.trans (a_w4.trans (a_v5.trans (a_w5.trans (a_v6.trans (a_v7.trans
    (a_w6.trans a_w7)))))))))))), T_w7, rip_w7, sp_w7, ?_⟩
  intro k hk
  obtain _ | _ | _ | _ | _ | _ | _ | k := k
  rotate_left 7
  · omega
  · show memLoad w7.external (framePointer s + BitVec.ofNat 64 24) 64 =
      memLoad t.external (polyBase s + BitVec.ofNat 64 0) 64
    rw [val_w7,
      regs_w6,
      regs_v7 0 (by decide),
      val_v6]
  · show memLoad w7.external (framePointer s + BitVec.ofNat 64 32) 64 =
      memLoad t.external (polyBase s + BitVec.ofNat 64 8) 64
    rw [keep_qword (d := 32) hF keep_w7 (by omega) (by omega) (by omega),
      val_w6,
      val_v7]
  · show memLoad w7.external (framePointer s + BitVec.ofNat 64 40) 64 =
      memLoad t.external (polyBase s + BitVec.ofNat 64 16) 64
    rw [keep_qword (d := 40) hF keep_w7 (by omega) (by omega) (by omega),
      keep_qword (d := 40) hF keep_w6 (by omega) (by omega) (by omega),
      ext_v7,
      ext_v6,
      val_w5,
      val_v5]
  · show memLoad w7.external (framePointer s + BitVec.ofNat 64 48) 64 =
      memLoad t.external (polyBase s + BitVec.ofNat 64 24) 64
    rw [keep_qword (d := 48) hF keep_w7 (by omega) (by omega) (by omega),
      keep_qword (d := 48) hF keep_w6 (by omega) (by omega) (by omega),
      ext_v7,
      ext_v6,
      keep_qword (d := 48) hF keep_w5 (by omega) (by omega) (by omega),
      ext_v5,
      val_w4,
      val_v4]
  · show memLoad w7.external (framePointer s + BitVec.ofNat 64 56) 64 =
      memLoad t.external (polyBase s + BitVec.ofNat 64 32) 64
    rw [keep_qword (d := 56) hF keep_w7 (by omega) (by omega) (by omega),
      keep_qword (d := 56) hF keep_w6 (by omega) (by omega) (by omega),
      ext_v7,
      ext_v6,
      keep_qword (d := 56) hF keep_w5 (by omega) (by omega) (by omega),
      ext_v5,
      keep_qword (d := 56) hF keep_w4 (by omega) (by omega) (by omega),
      ext_v4,
      val_w3,
      val_v3]
  · show memLoad w7.external (framePointer s + BitVec.ofNat 64 64) 64 =
      memLoad t.external (polyBase s + BitVec.ofNat 64 40) 64
    rw [keep_qword (d := 64) hF keep_w7 (by omega) (by omega) (by omega),
      keep_qword (d := 64) hF keep_w6 (by omega) (by omega) (by omega),
      ext_v7,
      ext_v6,
      keep_qword (d := 64) hF keep_w5 (by omega) (by omega) (by omega),
      ext_v5,
      keep_qword (d := 64) hF keep_w4 (by omega) (by omega) (by omega),
      ext_v4,
      keep_qword (d := 64) hF keep_w3 (by omega) (by omega) (by omega),
      ext_v3,
      val_w2,
      val_v2]
  · show memLoad w7.external (framePointer s + BitVec.ofNat 64 72) 64 =
      memLoad t.external (polyBase s + BitVec.ofNat 64 48) 64
    rw [keep_qword (d := 72) hF keep_w7 (by omega) (by omega) (by omega),
      keep_qword (d := 72) hF keep_w6 (by omega) (by omega) (by omega),
      ext_v7,
      ext_v6,
      keep_qword (d := 72) hF keep_w5 (by omega) (by omega) (by omega),
      ext_v5,
      keep_qword (d := 72) hF keep_w4 (by omega) (by omega) (by omega),
      ext_v4,
      keep_qword (d := 72) hF keep_w3 (by omega) (by omega) (by omega),
      ext_v3,
      keep_qword (d := 72) hF keep_w2 (by omega) (by omega) (by omega),
      ext_v2,
      val_w1,
      val_v1]

omit [Machine.Bindings] in
theorem copy_bytes {u : RamState}
    (h : ∀ k < 7, memLoad u.external (framePointer s + BitVec.ofNat 64 (0x18 + 8 * k)) 64 =
      memLoad t.external (polyBase s + BitVec.ofNat 64 (8 * k)) 64) :
    ∀ n < 56, memByte u.external (framePointer s + BitVec.ofNat 64 (0x18 + n)) =
      memByte t.external (polyBase s + BitVec.ofNat 64 n) := by
  intro n hn
  have hb := memByte_of_memLoad_eq (h (n / 8) (by omega)) (n % 8) (by omega)
  rw [add_ofNat_add_ofNat, add_ofNat_add_ofNat,
    show 0x18 + 8 * (n / 8) + n % 8 = 0x18 + n by omega,
    show 8 * (n / 8) + n % 8 = n by omega] at hb
  exact hb

theorem result_load (T : Track s t u) (hCut : Cut5 s t key nonce associatedData plaintext outPtr)
    (hF : Facts s outPtr plaintext.size) :
    memLoad u.external (framePointer s + BitVec.ofNat 64 0xa0) 64 = s.regValue .rdi := by
  rw [T.high_load hF 0xa0 (by omega) (by omega)]
  have h := word64At_memLoad hCut.resultSlot
  have he : BitVec.ofNat 64 (slot s 0xa0).start = framePointer s + BitVec.ofNat 64 0xa0 := by
    apply BitVec.eq_of_toNat_eq
    rw [frame_toNat hF _ (by omega), BitVec.toNat_ofNat]
    have := hF.high
    simp only [slot, frameBase, frameBytes]
    omega
  rw [he] at h
  exact h

structure AtCall (s t c : RamState) : Prop where
  rip : c.RIP = 0x101ce0
  rsp : stackPtr c = framePointer s - BitVec.ofNat 64 8
  top : stackTop c = 0x1009fc
  rdi : rdi.read c = s.regValue .rdi + 1
  rsi : rsi.read c = framePointer s + BitVec.ofNat 64 0x18
  r14 : (Operand.reg 14 : Operand 64).read c = s.regValue .rdi
  copy : ∀ n < 56, memByte c.external (framePointer s + BitVec.ofNat 64 (0x18 + n)) =
    memByte t.external (polyBase s + BitVec.ofNat 64 n)

theorem to_call {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip)
    (hCut : Cut5 s t key nonce associatedData plaintext outPtr)
    (hF : Facts s outPtr plaintext.size) :
    ∃ fuel c, Advances boundary fuel t c ∧ Track s t c ∧ AtCall s t c := by
  obtain ⟨f0, u, a0, T, hrip, hsp, hcopy⟩ := copy_state hOut hCut hF
  have := hF.high
  have := hF.low
  have haddr1 : ∀ x, (AddrMode.sib 4 none 0 (.d32 0xa0)).addr u x =
      framePointer s + BitVec.ofNat 64 0xa0 := fun x => by rw [sib_addr hsp]; rfl
  have hfa := frame_toNat hF 0xa0 (by omega)
  obtain ⟨u1, a1, T1, e1⟩ := T.step hF
    (mov_r64_m64_effect_step 0x1009e6 0x4c (by unfold RexWPrefix; decide) 6
      (.sib 4 none 0 (.d32 0xa0)) ⟨by decide, fun h => by cases h⟩ rfl rfl)
    (program_text_slice T.code 0x9e6 8 (by decide +kernel))
    ⟨hrip, by
      rw [haddr1]
      refine T.readable hCut ?_ (stack_range hF ?_ ?_) <;> rw [hfa] <;>
        simp only [frameBase, frameBytes] <;> omega⟩
    (ne_boundary hOut (0x1009ee : BitVec 64) (by decide) (by decide))
    (regs_wr (by simp [Component.isMem])) (by simp)
  have ag1 : AgreesExcept [.reg 14, .rip] u u1 := e1.agrees
  have r14_1 : (Operand.reg 14 : Operand 64).read u1 = s.regValue .rdi := by
    have h := e1.writes
    change (Operand.reg 14 : Operand 64).read u1 =
      (Operand.mem ((AddrMode.sib 4 none 0 (.d32 0xa0)).addr u _) : Operand 64).read u at h
    rw [h, haddr1]
    exact result_load T hCut hF
  have sp1 : stackPtr u1 = framePointer s := by
    rw [stackPtr_eq_read, ag1.read (by simp), ← stackPtr_eq_read, hsp]
  have ext1 : u1.external = u.external := ag1.external (by simp [Component.Covers])
  obtain ⟨u2, a2, T2, e2⟩ := T1.step hF
    (lea_r64_effect_step 0x1009ee 0x49 (by unfold RexWPrefix; decide) 7
      (.base 14 (.d8 1)) ⟨by decide, fun h => by cases h⟩ rfl rfl)
    (program_text_slice T1.code 0x9ee 4 (by decide +kernel))
    e1.rip (ne_boundary hOut (0x1009f2 : BitVec 64) (by decide) (by decide))
    (regs_wr (by simp [Component.isMem])) (by simp)
  have ag2 : AgreesExcept [.reg 7, .rip] u1 u2 := e2.agrees
  have rdi2 : rdi.read u2 = s.regValue .rdi + 1 := by
    have h := e2.writes
    change (Operand.reg 7 : Operand 64).read u2 =
      (AddrMode.base 14 (.d8 1)).addr u1 (0x1009ee + BitVec.ofNat 64 4) at h
    rw [h, base_addr (b := 14) r14_1]
    rfl
  have sp2 : stackPtr u2 = framePointer s := by
    rw [stackPtr_eq_read, ag2.read (by simp), ← stackPtr_eq_read, sp1]
  have r14_2 : (Operand.reg 14 : Operand 64).read u2 = s.regValue .rdi := by
    rw [ag2.read (by simp), r14_1]
  have ext2 : u2.external = u1.external := ag2.external (by simp [Component.Covers])
  obtain ⟨u3, a3, T3, e3⟩ := T2.step hF
    (lea_r64_effect_step 0x1009f2 0x48 (by unfold RexWPrefix; decide) 6
      (.sib 4 none 0 (.d8 0x18)) ⟨by decide, fun h => by cases h⟩ rfl rfl)
    (program_text_slice T2.code 0x9f2 5 (by decide +kernel))
    e2.rip (ne_boundary hOut (0x1009f7 : BitVec 64) (by decide) (by decide))
    (regs_wr (by simp [Component.isMem])) (by simp)
  have ag3 : AgreesExcept [.reg 6, .rip] u2 u3 := e3.agrees
  have rsi3 : rsi.read u3 = framePointer s + BitVec.ofNat 64 0x18 := by
    have h := e3.writes
    change (Operand.reg 6 : Operand 64).read u3 =
      (AddrMode.sib 4 none 0 (.d8 0x18)).addr u2 (0x1009f2 + BitVec.ofNat 64 5) at h
    rw [h, sib_addr sp2]
    rfl
  have sp3 : stackPtr u3 = framePointer s := by
    rw [stackPtr_eq_read, ag3.read (by simp), ← stackPtr_eq_read, sp2]
  have r14_3 : (Operand.reg 14 : Operand 64).read u3 = s.regValue .rdi := by
    rw [ag3.read (by simp), r14_2]
  have rdi3 : rdi.read u3 = s.regValue .rdi + 1 := by
    rw [show rdi.read u3 = (Operand.reg 7 : Operand 64).read u3 from rfl, ag3.read (by simp)]
    exact rdi2
  have ext3 : u3.external = u2.external := ag3.external (by simp [Component.Covers])
  have hpush : pushAddr u3 = framePointer s - BitVec.ofNat 64 8 := by
    rw [pushAddr, sp3]; rfl
  have hpt := frame_sub_toNat hF 8 (by omega)
  have hw : ∀ i < 8, Wr s (framePointer s - BitVec.ofNat 64 8 + BitVec.ofNat 64 i).toNat :=
    wr_frame hF (by rw [hpt]; omega) (by rw [hpt]; omega)
  obtain ⟨c, a4, T4, e4⟩ := T3.step hF
    (call_rel32_effect_step 0x1009f7 0x12e4 (by decide))
    (program_text_slice T3.code 0x9f7 5 (by decide +kernel))
    ⟨e3.rip, by
      rw [hpush]
      exact T3.writable hCut hF (by omega) (by rw [hpt]; simp only [frameBase, frameBytes]; omega) hw,
     by
      rw [hpush]
      exact code_apart (not_wr_program hF hw) (by decide) (by decide)⟩
    (ne_boundary hOut (0x101ce0 : BitVec 64) (by decide) (by decide))
    (by
      intro c hc x hcov
      simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact absurd hcov (by simp [Component.Covers])
      · rw [hpush] at hcov
        exact covers_wr hw hcov
      · exact absurd hcov (by simp [Component.Covers]))
    (by simp)
  have ag4 : AgreesExcept [.reg 4, .mem (framePointer s - BitVec.ofNat 64 8) 8, .rip] u3 c := by
    have h := e4.agrees
    simp only [pushEffect_components] at h
    rw [hpush] at h
    exact h
  obtain ⟨htop, hsp4⟩ := callEffect_stack e4
  refine ⟨_, c, a0.trans (a1.trans (a2.trans (a3.trans a4))), T4, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [e4.rip]; rfl
  · have h := e4.writes.1
    change stackPtr c = pushAddr u3 at h
    rw [h, hpush]
  · rw [htop]; rfl
  · rw [show rdi.read c = (Operand.reg 7 : Operand 64).read c from rfl, ag4.read (by simp)]
    exact rdi3
  · rw [show rsi.read c = (Operand.reg 6 : Operand 64).read c from rfl, ag4.read (by simp)]
    exact rsi3
  · rw [ag4.read (by simp), r14_3]
  · intro n hn
    have hb := copy_bytes hcopy n hn
    rw [← hb]
    simp only [memByte]
    change (c.external[_]?).getD 0 = (u.external[_]?).getD 0
    rw [ag4.byte, ext3, ext2, ext1]
    intro comp hcomp hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcomp
    rcases hcomp with rfl | rfl | rfl
    · exact hcov
    · obtain ⟨i, hi, he⟩ := hcov
      have := congrArg BitVec.toNat he
      rw [frame_toNat hF _ (by omega), toNat_add_ofNat _ _ (by rw [hpt]; omega), hpt] at this
      omega
    · exact hcov

theorem saved_load (T : Track s t u) (hCut : Cut5 s t key nonce associatedData plaintext outPtr)
    (hF : Facts s outPtr plaintext.size) {reg : Syntax.Reg} {d : Nat}
    (hm : (reg, d) ∈ savedRegisters) :
    memLoad u.external (framePointer s + BitVec.ofNat 64 d) 64 = s.regValue reg := by
  have hd : 0x188 ≤ d ∧ d ≤ 0x1b0 := by
    simp only [savedRegisters, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    omega
  rw [T.high_load hF d (by omega) (by omega)]
  have h := word64At_memLoad (hCut.saved _ hm)
  have he : BitVec.ofNat 64 (slot s d).start = framePointer s + BitVec.ofNat 64 d := by
    apply BitVec.eq_of_toNat_eq
    rw [frame_toNat hF _ (by omega), BitVec.toNat_ofNat]
    have := hF.high
    simp only [slot, frameBase, frameBytes]
    omega
  rw [he] at h
  exact h

theorem pop_saved {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip)
    (hCut : Cut5 s t key nonce associatedData plaintext outPtr)
    (hF : Facts s outPtr plaintext.size) (T : Track s t u) {p : BitVec 64} {bytes : List UInt8}
    {len : Nat} {dst : BitVec 5}
    (hStep : StepEffect (PopPre p) (codeRange p bytes) (popR64Effect p len dst))
    (hc : CodeIn (codeRange p bytes) u) (hrip : u.RIP = p)
    (hp₁ : 0x100000 ≤ p.toNat) (hp₂ : p.toNat + len < 0x102def) (d : Nat)
    (hd : d + 8 ≤ 448) (hd' : 0x50 ≤ d) (hsp : stackPtr u = framePointer s + BitVec.ofNat 64 d)
    {V : BitVec 64} (hV : memLoad u.external (framePointer s + BitVec.ofNat 64 d) 64 = V) :
    ∃ v, Advances boundary 1 u v ∧ Track s t v ∧ v.RIP = p + BitVec.ofNat 64 len ∧
      stackPtr v = framePointer s + BitVec.ofNat 64 (d + 8) ∧
      (Operand.reg dst : Operand 64).read v = V ∧ v.external = u.external ∧
      ∀ r : BitVec 5, r ≠ dst → r ≠ 4 →
        (Operand.reg r : Operand 64).read v = (Operand.reg r : Operand 64).read u := by
  have := hF.high
  have hfd := frame_toNat hF d (by omega)
  obtain ⟨v, a, T', e⟩ := T.step hF hStep hc
    ⟨hrip, by
      rw [hsp]
      refine T.readable hCut ?_ (stack_range hF ?_ ?_) <;> rw [hfd] <;>
        simp only [frameBase, frameBytes] <;> omega⟩
    (by
      show p + BitVec.ofNat 64 len ≠ _
      exact ne_boundary hOut _ (by rw [toNat_add_ofNat _ _ (by omega)]; omega)
        (by rw [toNat_add_ofNat _ _ (by omega)]; omega))
    (regs_wr (by simp [Component.isMem])) (by simp)
  have ag : AgreesExcept [.reg dst, .reg 4, .rip] u v := e.agrees
  refine ⟨v, a, T', e.rip, ?_, ?_, ag.external (by simp [Component.Covers]), ?_⟩
  · have h := e.writes.2
    change stackPtr v = stackPtr u + 8 at h
    rw [h, hsp, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, add_ofNat_add_ofNat]
  · have h := e.writes.1
    change (Operand.reg dst : Operand 64).read v = memLoad u.external (stackPtr u) 64 at h
    rw [h, hsp, hV]
  · intro r h1 h2
    exact ag.read (by simp [h1]; exact h2)

omit [Machine.Bindings] in
theorem wr_regions (hF : Facts s outPtr length) {n : Nat} (h : Wr s n) :
    (resultRegion s).Contains n ∨ (Stack.region s coreStackBytes).Contains n := by
  rcases h with h | h
  · exact Or.inl h
  · right
    have := hF.low
    simp only [Stack.region, MemoryRegion.Contains, coreStackBytes, Stack.returnAddressBytes]
    simp only [frameBase, frameBytes] at h
    change _ ≤ _ ∧ _ < _ at h
    have hsp : (stackPtr s).toNat = (s.regValue .rsp).toNat := rfl
    rw [hsp] at h this
    exact stack_bounds _ _ this h

omit [Machine.Bindings] in
theorem result_toNat (hF : Facts s outPtr length) (i : Nat) (hi : i ≤ 17) :
    (s.regValue .rdi + BitVec.ofNat 64 i).toNat = (s.regValue .rdi).toNat + i := by
  have := hF.resultHigh
  rw [toNat_add_ofNat _ _ (by omega)]

omit [Machine.Bindings] in
theorem some_of_memByte {m : Machine.Ram} {a : BitVec 64} {b : UInt8} (hs : (m[a]?).isSome)
    (hb : memByte m a = b) : m[a]? = some b := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
  simp only [memByte] at hb
  change (m[a]?).getD 0 = b at hb
  rw [hx] at hb ⊢
  simp only [Option.getD_some] at hb
  rw [hb]

set_option maxHeartbeats 1000000 in
theorem epilogue {boundary : ReturnBoundary} {d : RamState} (hOut : ¬ InProgram boundary.rip)
    (hDiff : boundary.rip ≠ (returnBoundary s).rip)
    (hLow : (returnBoundary s).rip.toNat < 2 ^ 32)
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hCut : Cut5 s t key nonce associatedData plaintext outPtr)
    (hF : Facts s outPtr plaintext.size) (T_d : Track s t d) (rip_d : d.RIP = 0x1009fc)
    (sp_d : stackPtr d = framePointer s)
    (r14_d : (Operand.reg 14 : Operand 64).read d = s.regValue .rdi)
    (htag : ∀ i : Fin 16, d.external[s.regValue .rdi + 1 + BitVec.ofNat 64 i.val]? =
      some (chacha20AeadEncrypt associatedData key nonce plaintext).2[i]) :
    ∃ fuel u, Advances boundary fuel d u ∧
      CorePost s u key nonce associatedData plaintext outPtr := by
  have := hF.high
  have := hF.low
  have := hF.resultHigh
  obtain ⟨x1, a_x1, T_x1, e1⟩ := T_d.step hF (xor_r32_r32_effect_step 0x1009fc 0xc0 (by decide))
    (program_text_slice T_d.code 0x9fc 2 (by decide +kernel)) rip_d
    (ne_boundary hOut (0x1009fe : BitVec 64) (by decide) (by decide))
    (regs_wr (by simp [Component.isMem])) (by simp)
  have ag1 : AgreesExcept [.reg 0, .flags, .rip] d x1 := e1.agrees
  have rax1 : (Operand.reg 0 : Operand 64).read x1 = 0 := by
    have h := e1.writes
    change (Operand.reg 0 : Operand 64).read x1 =
      ((Operand.reg 0 : Operand 32).read d ^^^ (Operand.reg 0 : Operand 32).read d).setWidth 64 at h
    rw [h, BitVec.xor_self]
    rfl
  have r14_1 : (Operand.reg 14 : Operand 64).read x1 = s.regValue .rdi := by
    rw [ag1.read (by simp), r14_d]
  have sp_x1 : stackPtr x1 = framePointer s := by
    rw [stackPtr_eq_read, ag1.read (by simp), ← stackPtr_eq_read, sp_d]
  have ext_x1 : x1.external = d.external := ag1.external (by simp [Component.Covers])
  have haddr2 : ∀ x, (AddrMode.base 14 .none).addr x1 x = s.regValue .rdi := fun x => by
    rw [base_addr (b := 14) r14_1]
    exact BitVec.add_zero _
  have hw2 : ∀ i < 1, Wr s (s.regValue .rdi + BitVec.ofNat 64 i).toNat :=
    wr_result hF (Nat.le_refl _) (by omega)
  obtain ⟨x2, a_x2, T_x2, e2⟩ := T_x1.step hF
    (mov_m8_r8_rex_effect_step 0x1009fe 0x41 (by unfold RexPrefix; decide) 0 (.base 14 .none)
      ⟨by decide, fun _ => by decide⟩ rfl rfl)
    (program_text_slice T_x1.code 0x9fe 3 (by decide +kernel))
    ⟨e1.rip, by
      show MemWritable x1 ((AddrMode.base 14 .none).addr x1 _) 1
      rw [haddr2]
      exact T_x1.writable hCut hF (by omega) (by omega) hw2,
     by
      show RangeApart ((AddrMode.base 14 .none).addr x1 _) 1 _ _
      rw [haddr2]
      exact code_apart (not_wr_program hF hw2) (by decide) (by decide)⟩
    (ne_boundary hOut (0x100a01 : BitVec 64) (by decide) (by decide))
    (by
      intro c hc x hcov
      simp only [movM8R8Effect, storeEffect_components, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      rcases hc with rfl | rfl
      · rw [haddr2] at hcov
        exact covers_wr hw2 hcov
      · exact absurd hcov (by simp [Component.Covers]))
    (by simp [movM8R8Effect])
  have ag2 : AgreesExcept [.mem (s.regValue .rdi) 1, .rip] x1 x2 := by
    have h := e2.agrees
    simp only [movM8R8Effect, storeEffect_components] at h
    rw [haddr2] at h
    exact h
  have byte2 : x2.external[s.regValue .rdi]? = some 0 := by
    have h := e2.writes
    change (Operand.mem ((AddrMode.base 14 .none).addr x1 _) : Operand 8).read x2 =
      (Operand.reg 0 : Operand 8).read x1 at h
    rw [haddr2] at h
    have hs := T_x2.isSome hCut (region := resultRegion s) (by simp [coreWritten])
      (a := s.regValue .rdi)
      (by simp [resultRegion, registerRegion, MemoryRegion.Contains, resultBytes])
    apply some_of_memByte hs
    have h8 : (Operand.reg 0 : Operand 8).read x1 = 0 := by
      have := rax1
      simp only [Operand.read_reg64] at this
      simp only [Operand.read_reg8, this]
      rfl
    rw [h8] at h
    change memLoad x2.external (s.regValue .rdi) 8 = 0 at h
    rw [memLoad_8] at h
    exact UInt8.toBitVec_inj.mp h
  have keep2 : ∀ x, x ≠ s.regValue .rdi → x2.external[x]? = x1.external[x]? := by
    intro x hx
    apply ag2.byte
    intro c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := hcov
      have : i = 0 := by omega
      subst this
      exact hx (BitVec.add_zero _)
    · exact hcov
  have regs2 : ∀ r : BitVec 5, (Operand.reg r : Operand 64).read x2 =
      (Operand.reg r : Operand 64).read x1 := fun r => ag2.read (by simp)
  obtain ⟨x3, a_x3, T_x3, e3⟩ := T_x2.step hF
    (add_r64_imm32_effect_step 0x100a01 0x48 0xc4 0x188 (by unfold RexWPrefix; decide)
      (by decide) (by decide))
    (program_text_slice T_x2.code 0xa01 7 (by decide +kernel)) e2.rip
    (ne_boundary hOut (0x100a08 : BitVec 64) (by decide) (by decide))
    (regs_wr (by simp [Component.isMem])) (by simp)
  have ag3 : AgreesExcept [.reg 4, .flags, .rip] x2 x3 := e3.agrees
  have rip_x3 : x3.RIP = 0x100a08 := e3.rip
  have sp_x3 : stackPtr x3 = framePointer s + BitVec.ofNat 64 0x188 := by
    have h := e3.writes
    change (Operand.reg 4 : Operand 64).read x3 =
      (Operand.reg 4 : Operand 64).read x2 + (0x188 : BitVec 32).signExtend 64 at h
    rw [stackPtr_eq_read, h, regs2, ← stackPtr_eq_read, sp_x1]
    rfl
  have ext_x3 : x3.external = x2.external := ag3.external (by simp [Component.Covers])
  obtain ⟨x4, a_x4, T_x4, rip_x4, sp_x4, val_x4, ext_x4, regs_x4⟩ :=
    pop_saved hOut hCut hF T_x3 (pop_r64_effect_step 0x100a08 0x5b (by decide) (by decide))
      (program_text_slice T_x3.code 0xa08 1 (by decide +kernel)) rip_x3
      (by decide) (by decide) 0x188 (by omega) (by omega) sp_x3
      (saved_load T_x3 hCut hF (reg := .rbx) (d := 0x188) (by simp [savedRegisters]))
  obtain ⟨x5, a_x5, T_x5, rip_x5, sp_x5, val_x5, ext_x5, regs_x5⟩ :=
    pop_saved hOut hCut hF T_x4 (pop_r64_rex_effect_step 0x100a09 0x41 0x5c (by unfold RexPrefix; decide) (by decide) (by decide))
      (program_text_slice T_x4.code 0xa09 2 (by decide +kernel)) rip_x4
      (by decide) (by decide) 0x190 (by omega) (by omega) sp_x4
      (saved_load T_x4 hCut hF (reg := .r12) (d := 0x190) (by simp [savedRegisters]))
  obtain ⟨x6, a_x6, T_x6, rip_x6, sp_x6, val_x6, ext_x6, regs_x6⟩ :=
    pop_saved hOut hCut hF T_x5 (pop_r64_rex_effect_step 0x100a0b 0x41 0x5d (by unfold RexPrefix; decide) (by decide) (by decide))
      (program_text_slice T_x5.code 0xa0b 2 (by decide +kernel)) rip_x5
      (by decide) (by decide) 0x198 (by omega) (by omega) sp_x5
      (saved_load T_x5 hCut hF (reg := .r13) (d := 0x198) (by simp [savedRegisters]))
  obtain ⟨x7, a_x7, T_x7, rip_x7, sp_x7, val_x7, ext_x7, regs_x7⟩ :=
    pop_saved hOut hCut hF T_x6 (pop_r64_rex_effect_step 0x100a0d 0x41 0x5e (by unfold RexPrefix; decide) (by decide) (by decide))
      (program_text_slice T_x6.code 0xa0d 2 (by decide +kernel)) rip_x6
      (by decide) (by decide) 0x1a0 (by omega) (by omega) sp_x6
      (saved_load T_x6 hCut hF (reg := .r14) (d := 0x1a0) (by simp [savedRegisters]))
  obtain ⟨x8, a_x8, T_x8, rip_x8, sp_x8, val_x8, ext_x8, regs_x8⟩ :=
    pop_saved hOut hCut hF T_x7 (pop_r64_rex_effect_step 0x100a0f 0x41 0x5f (by unfold RexPrefix; decide) (by decide) (by decide))
      (program_text_slice T_x7.code 0xa0f 2 (by decide +kernel)) rip_x7
      (by decide) (by decide) 0x1a8 (by omega) (by omega) sp_x7
      (saved_load T_x7 hCut hF (reg := .r15) (d := 0x1a8) (by simp [savedRegisters]))
  obtain ⟨x9, a_x9, T_x9, rip_x9, sp_x9, val_x9, ext_x9, regs_x9⟩ :=
    pop_saved hOut hCut hF T_x8 (pop_r64_effect_step 0x100a11 0x5d (by decide) (by decide))
      (program_text_slice T_x8.code 0xa11 1 (by decide +kernel)) rip_x8
      (by decide) (by decide) 0x1b0 (by omega) (by omega) sp_x8
      (saved_load T_x8 hCut hF (reg := .rbp) (d := 0x1b0) (by simp [savedRegisters]))
  have hF1b8 : framePointer s + BitVec.ofNat 64 (0x1b0 + 8) = stackPtr s := by
    simp only [framePointer, frameBytes]
    exact BitVec.sub_add_cancel _ _
  have htop : stackTop x9 = (returnBoundary s).rip := by
    change memLoad x9.external (stackPtr x9) 64 = _
    rw [sp_x9, T_x9.high_load hF _ (by omega) (by omega)]
    have h := word64At_memLoad hCut.returnAddress
    rw [hF1b8, show stackPtr s = s.regValue .rsp from rfl]
    simpa only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h
  obtain ⟨u, a_u, T_u, eu⟩ := T_x9.step hF (ret_effect_step 0x100a12)
    (program_text_slice T_x9.code 0xa12 1 (by decide +kernel))
    ⟨⟨rip_x9, by
      rw [sp_x9]
      have hfd := frame_toNat hF (0x1b0 + 8) (by omega)
      refine T_x9.readable hCut ?_ (stack_range hF ?_ ?_) <;> rw [hfd] <;>
        simp only [frameBase, frameBytes] <;> omega⟩, by rw [htop]; exact hLow⟩
    (by
      show stackTop x9 ≠ _
      rw [htop]
      exact fun h => hDiff h.symm)
    (regs_wr (by simp [Component.isMem])) (by simp)
  have agu : AgreesExcept [.reg 4, .rip] x9 u := eu.agrees
  have ext_u : u.external = x9.external := agu.external (by simp [Component.Covers])
  have hext : u.external = x2.external := by
    rw [ext_u, ext_x9, ext_x8, ext_x7, ext_x6, ext_x5, ext_x4, ext_x3]
  have hready := T_u.ready
  have v4 : (Operand.reg 3 : Operand 64).read x4 = s.regValue .rbx := val_x4
  have v5 : (Operand.reg 12 : Operand 64).read x5 = s.regValue .r12 := val_x5
  have v6 : (Operand.reg 13 : Operand 64).read x6 = s.regValue .r13 := val_x6
  have v7 : (Operand.reg 14 : Operand 64).read x7 = s.regValue .r14 := val_x7
  have v8 : (Operand.reg 15 : Operand 64).read x8 = s.regValue .r15 := val_x8
  have v9 : (Operand.reg 5 : Operand 64).read x9 = s.regValue .rbp := val_x9
  refine ⟨_, u, a_x1.trans (a_x2.trans (a_x3.trans (a_x4.trans (a_x5.trans (a_x6.trans
    (a_x7.trans (a_x8.trans (a_x9.trans a_u)))))))), ?_⟩
  refine ⟨⟨hready.smrr, hready.memoryType, hCut.environment.stringStride,
    hready.features.lzcnt⟩, ⟨hready.cpu, T_u.sse, hready.memory, hready.ready⟩, T_u.code,
    ?_, ?_, ?_, T_u.df, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eu.rip]
    exact htop
  · have h := eu.writes
    change stackPtr u = stackPtr x9 + 8 at h
    rw [h, sp_x9, hF1b8]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hu : ∀ n : BitVec 5, n ≠ 4 →
        (Operand.reg n : Operand 64).read u = (Operand.reg n : Operand 64).read x9 :=
      fun n hn => agu.read (by simp; exact hn)
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change u.GPR[gprIndex 3] = s.GPR[gprIndex 3]
      rw [← Operand.read_reg64, ← Operand.read_reg64, hu 3 (by decide), regs_x9 3 (by decide)
        (by decide), regs_x8 3 (by decide) (by decide), regs_x7 3 (by decide) (by decide),
        regs_x6 3 (by decide) (by decide), regs_x5 3 (by decide) (by decide), v4]
      rfl
    · change u.GPR[gprIndex 5] = s.GPR[gprIndex 5]
      rw [← Operand.read_reg64, ← Operand.read_reg64, hu 5 (by decide), v9]
      rfl
    · change u.GPR[gprIndex 12] = s.GPR[gprIndex 12]
      rw [← Operand.read_reg64, ← Operand.read_reg64, hu 12 (by decide), regs_x9 12 (by decide)
        (by decide), regs_x8 12 (by decide) (by decide), regs_x7 12 (by decide) (by decide),
        regs_x6 12 (by decide) (by decide), v5]
      rfl
    · change u.GPR[gprIndex 13] = s.GPR[gprIndex 13]
      rw [← Operand.read_reg64, ← Operand.read_reg64, hu 13 (by decide), regs_x9 13 (by decide)
        (by decide), regs_x8 13 (by decide) (by decide), regs_x7 13 (by decide) (by decide),
        v6]
      rfl
    · change u.GPR[gprIndex 14] = s.GPR[gprIndex 14]
      rw [← Operand.read_reg64, ← Operand.read_reg64, hu 14 (by decide), regs_x9 14 (by decide)
        (by decide), regs_x8 14 (by decide) (by decide), v7]
      rfl
    · change u.GPR[gprIndex 15] = s.GPR[gprIndex 15]
      rw [← Operand.read_reg64, ← Operand.read_reg64, hu 15 (by decide), regs_x9 15 (by decide)
        (by decide), v8]
      rfl
  · intro a hout
    by_cases hW : Wr s a.toNat
    · exfalso
      rcases wr_regions hF hW with h | h
      · exact hout _ (by simp) h
      · exact hout _ (by simp) h
    · rw [T_u.same a hW]
      exact hCut.frame a hout
  · refine ⟨rfl, fun i => ?_⟩
    obtain ⟨iv, hiv⟩ := i
    obtain rfl : iv = 0 := by change iv < 1 at hiv; omega
    show u.external[BitVec.ofNat 64 ((s.regValue .rdi).toNat + 0)]? = some 0
    rw [Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq, hext, byte2]
  · refine ⟨by simp [MemoryRegion.HasLength, ByteArray.size], fun i => ?_⟩
    obtain ⟨iv, hiv⟩ := i
    have hi : iv < 16 := Nat.lt_of_lt_of_eq hiv (by simp [ByteArray.size])
    show u.external[BitVec.ofNat 64 ((s.regValue .rdi).toNat + 1 + iv)]? =
      some (chacha20AeadEncrypt associatedData key nonce plaintext).2.toArray[iv]
    have ha : BitVec.ofNat 64 ((s.regValue .rdi).toNat + 1 + iv) =
        s.regValue .rdi + 1 + BitVec.ofNat 64 iv := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, toNat_add_ofNat _ _ (by
        rw [show s.regValue .rdi + 1 = s.regValue .rdi + BitVec.ofNat 64 1 from rfl,
          result_toNat hF 1 (by omega)]; omega),
        show s.regValue .rdi + 1 = s.regValue .rdi + BitVec.ofNat 64 1 from rfl,
        result_toNat hF 1 (by omega)]
      omega
    rw [ha, hext, keep2, ext_x1, htag ⟨iv, hi⟩]
    · simp only [Option.some.injEq]
      rfl
    · intro he
      have := congrArg BitVec.toNat he
      rw [show s.regValue .rdi + 1 = s.regValue .rdi + BitVec.ofNat 64 1 from rfl,
        add_ofNat_add_ofNat, result_toNat hF _ (by omega)] at this
      omega
  · refine ⟨hCut.ciphertext.1, fun i => ?_⟩
    rw [T_u.same _ ?_]
    · exact hCut.ciphertext.2 i
    · intro hW
      have hb := hPre.outputInMemory.1
      have hlen := hCut.ciphertext.1
      simp only [messageRegion, MemoryRegion.Bounded, userAddressLimit] at hb
      simp only [messageRegion, MemoryRegion.HasLength] at hlen
      have hix := i.isLt
      have hce : (chacha20AeadEncrypt associatedData key nonce plaintext).1.size =
          plaintext.size := hlen
      have hn : (BitVec.ofNat 64 ((messageRegion outPtr plaintext.size).start + i.val)).toNat =
          outPtr.toNat + i.val := by
        simp only [messageRegion, BitVec.toNat_ofNat]
        omega
      have hc : (messageRegion outPtr plaintext.size).Contains
          (BitVec.ofNat 64 ((messageRegion outPtr plaintext.size).start + i.val)).toNat := by
        rw [hn]
        simp only [messageRegion, MemoryRegion.Contains]
        omega
      have hpair := hPre.separation.1
      simp only [coreWritten, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hpair
      rcases wr_regions hF hW with h | h
      · exact hpair.1.1 _ h hc
      · exact hpair.2.1 _ hc h

  · intro region hr a ha
    obtain ⟨byte, hb⟩ := hCut.allocated region hr a ha
    exact Option.isSome_iff_exists.mp (T_u.grows a (by simp only [hb, Option.isSome_some]))

omit [Machine.Bindings] in
theorem word_copy {c : RamState} (hcopy : ∀ n < 56,
      memByte c.external (framePointer s + BitVec.ofNat 64 (0x18 + n)) =
        memByte t.external (polyBase s + BitVec.ofNat 64 n))
    (n : Nat) (hn : n + 4 ≤ 56) :
    word32 c (framePointer s + BitVec.ofNat 64 (0x18 + n)) =
      word32 t (polyBase s + BitVec.ofNat 64 n) := by
  show memLoad c.external _ 32 = memLoad t.external _ 32
  apply memLoad_congr
  intro j hj
  rw [add_ofNat_add_ofNat, add_ofNat_add_ofNat, Nat.add_assoc]
  exact hcopy (n + j) (by omega)

omit [Machine.Bindings] in
theorem limbs_copy {c : RamState} (hcopy : ∀ n < 56,
      memByte c.external (framePointer s + BitVec.ofNat 64 (0x18 + n)) =
        memByte t.external (polyBase s + BitVec.ofNat 64 n)) :
    hLimbs c (framePointer s + BitVec.ofNat 64 0x18) = hLimbs t (polyBase s) := by
  funext i
  show word32 c (framePointer s + BitVec.ofNat 64 0x18 + BitVec.ofNat 64 0x24 +
      BitVec.ofNat 64 (4 * i.val)) =
    word32 t (polyBase s + BitVec.ofNat 64 0x24 + BitVec.ofNat 64 (4 * i.val))
  rw [add_ofNat_add_ofNat (framePointer s), add_ofNat_add_ofNat (framePointer s),
    add_ofNat_add_ofNat (polyBase s), Nat.add_assoc]
  exact word_copy hcopy _ (by have := i.isLt; omega)

omit [Machine.Bindings] in
theorem pad_copy {c : RamState} (hcopy : ∀ n < 56,
      memByte c.external (framePointer s + BitVec.ofNat 64 (0x18 + n)) =
        memByte t.external (polyBase s + BitVec.ofNat 64 n)) :
    padWords c (framePointer s + BitVec.ofNat 64 0x18) = padWords t (polyBase s) := by
  funext i
  show word32 c (framePointer s + BitVec.ofNat 64 0x18 + BitVec.ofNat 64 (4 * i.val)) =
    word32 t (polyBase s + BitVec.ofNat 64 (4 * i.val))
  rw [add_ofNat_add_ofNat (framePointer s)]
  exact word_copy hcopy _ (by have := i.isLt; omega)

theorem finalize_pre (hCut : Cut5 s t key nonce associatedData plaintext outPtr)
    (hF : Facts s outPtr plaintext.size) {c : RamState} (T : Track s t c) (hc : AtCall s t c) :
    Poly1305.Callee101ce0.FinalizePre c := by
  have := hF.high
  have := hF.low
  have := hF.apart
  have := hF.resultHigh
  have hrdi : (rdi.read c).toNat = (s.regValue .rdi).toNat + 1 := by
    rw [hc.rdi, show s.regValue .rdi + 1 = s.regValue .rdi + BitVec.ofNat 64 1 from rfl,
      result_toNat hF 1 (by omega)]
  have hwo : ∀ i < 16, Wr s (rdi.read c + BitVec.ofNat 64 i).toNat :=
    wr_result hF (by rw [hrdi]; omega) (by rw [hrdi]; omega)
  have hsp : (stackPtr c).toNat = frameBase s - 8 := by rw [hc.rsp, frame_sub_toNat hF 8 (by omega)]
  have hfs : Poly1305.Callee101ce0.frameStart c = framePointer s - BitVec.ofNat 64 56 := by
    simp only [Poly1305.Callee101ce0.frameStart, Poly1305.Callee101ce0.frameBytes, hc.rsp]
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  have hfst := frame_sub_toNat hF 56 (by omega)
  have hwf : ∀ i < 48, Wr s (Poly1305.Callee101ce0.frameStart c + BitVec.ofNat 64 i).toNat := by
    rw [hfs]
    exact wr_frame hF (by rw [hfst]; omega) (by rw [hfst]; simp only [frameBase, frameBytes]; omega)
  have hrsi := frame_toNat hF 0x18 (by omega)
  have htop : (returnBoundary c).rip = 0x1009fc := hc.top
  have hlimbs := limbs_copy hc.copy
  refine ⟨hc.rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc.rsi]
    refine T.readable hCut ?_ (stack_range hF ?_ ?_) <;> rw [hrsi] <;>
      simp only [stateBytes, frameBase, frameBytes] <;> omega
  · rw [hc.rsi, hlimbs]
    exact hCut.poly.hBounded
  · refine ⟨T.readable hCut (by rw [hrdi]; simp only [Poly1305.Callee101ce0.tagBytes]; omega)
      (fun i hi => (hF.wrOk _ (hwo i hi)).2.2), fun i hi => (hF.wrOk _ (hwo i hi)).2.1,
      fun i hi => (hF.wrOk _ (hwo i hi)).1⟩
  · rw [hsp]; simp only [Poly1305.Callee101ce0.frameBytes, frameBase, frameBytes]; omega
  · refine ⟨T.readable hCut ?_ (fun i hi => (hF.wrOk _ (hwf i hi)).2.2),
      fun i hi => (hF.wrOk _ (hwf i hi)).2.1, fun i hi => (hF.wrOk _ (hwf i hi)).1⟩
    rw [hfs, hfst]; simp only [Poly1305.Callee101ce0.frameBytes, frameBase, frameBytes]; omega
  · refine T.readable hCut (by rw [hsp]; simp only [frameBase, frameBytes]; omega)
      (stack_range hF (by rw [hsp]; omega) (by rw [hsp]; omega))
  · rw [hc.rsi, hfs]
    apply RangeApart.of_toNat
    all_goals (try rw [hrsi])
    all_goals (try rw [hfst])
    all_goals simp only [stateBytes, Poly1305.Callee101ce0.frameBytes, frameBase, frameBytes]
    all_goals omega
  · rw [hfs]
    apply RangeApart.of_toNat
    all_goals (try rw [hrdi])
    all_goals (try rw [hfst])
    all_goals simp only [Poly1305.Callee101ce0.tagBytes, Poly1305.Callee101ce0.frameBytes,
      frameBase, frameBytes]
    all_goals omega
  · rw [htop]; decide
  · rw [htop]; left; decide

omit [Machine.Bindings] in
theorem finish_bound {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip) :
    boundary.rip.toNat < Poly1305.Callee101ce0.entry.toNat ∨
      Poly1305.Callee101ce0.entry.toNat + Poly1305.Callee101ce0.codeLength ≤
        boundary.rip.toNat := by
  show boundary.rip.toNat < 0x101ce0 ∨ 0x101ce0 + 0x148 ≤ boundary.rip.toNat
  refine Classical.byContradiction fun h => hOut (inProgram_at _ (by omega) (by omega))

end Finish

open Finish in
theorem finish [Machine.Bindings] {s : RamState} {key : Vector UInt8 32}
    {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}
    (boundary : ReturnBoundary) {t : RamState}
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hBoundaryOutside : ¬ InProgram boundary.rip)
    (hBoundaryDifferent : boundary.rip ≠ (returnBoundary s).rip)
    (hReturnLow : (returnBoundary s).rip.toNat < 2 ^ 32)
    (hCut : Cut5 s t key nonce associatedData plaintext outPtr) :
    ∃ fuel u, Advances boundary fuel t u ∧
      CorePost s u key nonce associatedData plaintext outPtr := by
  have hF := facts hPre
  obtain ⟨f1, c, a1, Tc, hc⟩ := to_call hBoundaryOutside hCut hF
  have hpre := finalize_pre hCut hF Tc hc
  have htop : (returnBoundary c).rip = 0x1009fc := hc.top
  obtain ⟨f2, d, a2, hres⟩ := Poly1305.Callee101ce0.finalize_advances boundary
    (finish_bound hBoundaryOutside) c Tc.ready Tc.code hpre
    (by rw [htop]; exact ne_boundary hBoundaryOutside _ (by decide) (by decide))
  have := hF.high
  have := hF.resultHigh
  have hrdi : (rdi.read c).toNat = (s.regValue .rdi).toNat + 1 := by
    rw [hc.rdi, show s.regValue .rdi + 1 = s.regValue .rdi + BitVec.ofNat 64 1 from rfl,
      result_toNat hF 1 (by omega)]
  have hfs : Poly1305.Callee101ce0.frameStart c = framePointer s - BitVec.ofNat 64 56 := by
    simp only [Poly1305.Callee101ce0.frameStart, Poly1305.Callee101ce0.frameBytes, hc.rsp]
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  have hfst := frame_sub_toNat hF 56 (by omega)
  have Td : Track s t d := Tc.of_agrees hF hres.agrees hres.ready (by
    intro comp hcomp x hcov
    simp only [Poly1305.Callee101ce0.callChanges, List.mem_cons, List.not_mem_nil,
      or_false] at hcomp
    rcases hcomp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact (hcov : False).elim | skip
    · exact covers_wr (wr_result hF (by rw [hrdi]; omega)
        (by rw [hrdi]; simp only [Poly1305.Callee101ce0.tagBytes]; omega)) hcov
    · rw [hfs] at hcov
      exact covers_wr (wr_frame hF (by rw [hfst]; omega)
        (by rw [hfst]; simp only [Poly1305.Callee101ce0.frameBytes, frameBase, frameBytes]; omega))
        hcov)
    (by simp [Poly1305.Callee101ce0.callChanges])
  have hrip : d.RIP = 0x1009fc := hres.rip.trans htop
  have hsp : stackPtr d = framePointer s := by
    rw [hres.rsp, hc.rsp]
    exact BitVec.sub_add_cancel _ _
  have hr14 : (Operand.reg 14 : Operand 64).read d = s.regValue .rdi := by
    rw [hres.agrees.read (by simp [Poly1305.Callee101ce0.callChanges]), hc.r14]
  have htagv : Poly1305.Callee101ce0.tag c =
      (chacha20AeadEncrypt associatedData key nonce plaintext).2 := by
    rw [tag_eq, Poly1305.Callee101ce0.tag, hc.rsi, limbs_copy hc.copy, pad_copy hc.copy,
      hCut.poly.hValue, hCut.poly.pad]
  obtain ⟨f3, u, a3, hpost⟩ := epilogue hBoundaryOutside hBoundaryDifferent hReturnLow hPre hCut
    hF Td hrip hsp hr14 (fun i => by rw [← hc.rdi, hres.tag i, htagv])
  exact ⟨_, u, a1.trans (a2.trans a3), hpost⟩


end ChaCha20Poly1305.Proofs.Core
