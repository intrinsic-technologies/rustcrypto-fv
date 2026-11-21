import ChaCha20Poly1305.Spec
import ChaCha20Poly1305.Proofs.Common.Poly1305State
import ChaCha20Poly1305.Proofs.Common.WritableRange
import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Execution
import X86Proofs.Program.Execution
import X86Proofs.Program.Agrees
import X86Proofs.Program.Code
import X86Proofs.Step.ReadyToStep
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.And.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple
import X86Proofs.Instructions.Sar.Generated.R.Triple
import X86Proofs.Instructions.Shl.Generated.R.Triple
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Or.Generated.RR.Triple
import X86Proofs.Instructions.Adc.Generated.RR.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.Mov.Generated.MR.Triple
import X86Proofs.Instructions.Call.Triple

namespace ChaCha20Poly1305.Proofs.Poly1305.Callee101ce0

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 ChaCha20Poly1305.Proofs.Poly1305State
  ChaCha20Poly1305.Proofs.Common ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

def entry : BitVec 64 := 0x101ce0

def codeLength : Nat := 0x148

def frameBytes : Nat := 48

def tagBytes : Nat := 16

def tag (s : RamState) : Vector UInt8 16 :=
  numTo16LeBytes (limbValue (hLimbs s (rsi.read s)) % prime + wordValue (padWords s (rsi.read s)))

def frameStart (s : RamState) : BitVec 64 := stackPtr s - BitVec.ofNat 64 frameBytes

structure FinalizePre (s : RamState) : Prop where
  rip : s.RIP = entry
  state : MemReadable s (rsi.read s) stateBytes
  limbs : BoundedLimbs (hLimbs s (rsi.read s))
  output : WritableRange s (rdi.read s) tagBytes
  stackLow : frameBytes ≤ (stackPtr s).toNat
  frame : WritableRange s (frameStart s) frameBytes
  returnSlot : MemReadable s (stackPtr s) 8
  stateFrame : RangeApart (rsi.read s) stateBytes (frameStart s) frameBytes
  outputFrame : RangeApart (rdi.read s) tagBytes (frameStart s) (frameBytes + 8)
  returnLow : (returnBoundary s).rip.toNat < 2 ^ 32
  returnOutside : (returnBoundary s).rip.toNat < entry.toNat ∨
    entry.toNat + codeLength ≤ (returnBoundary s).rip.toNat

def callChanges (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip, .mem (rdi.read s) tagBytes, .mem (frameStart s) frameBytes]

structure FinalizeResult [Bindings] (s t : RamState) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = (returnBoundary s).rip
  rsp : stackPtr t = stackPtr s + 8
  result : rax.read t = rdi.read s
  agrees : AgreesExcept (callChanges s) s t
  tag : ∀ i : Fin 16,
    t.external[rdi.read s + BitVec.ofNat 64 i.val]? = some (tag s)[i]

theorem run1 [Bindings] {boundary : ReturnBoundary} {pre : RamState → Prop} {code : CodeMap}
    {e : RamState → Effect} (h : StepEffect pre code e) {u : RamState} (hr : ReadyToStep u)
    (hc : CodeIn Extracted.programImage u) (hcode : CodeIn code u)
    (hpre : pre u) {q : BitVec 64} (hq : (e u).rip = q) (hne : q ≠ boundary.rip)
    (hav : (e u).Avoids Extracted.programImage) :
    ∃ v, Advances boundary 1 u v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      v.RIP = q ∧ (e u).Holds u v := by
  obtain ⟨v, ha, hr', he⟩ := h.advances hr hcode hpre (hq ▸ hne)
  exact ⟨v, ha, hr', he.codeIn hav hc, he.rip.trans hq, he⟩

theorem code_at (p : BitVec 64) (off m : Nat) (hp : p = Extracted.textAddress + BitVec.ofNat 64 off)
    (h : off + m ≤ Extracted.textBytes.size) : ∀ j < m, InProgram (p + BitVec.ofNat 64 j) := by
  intro j hj
  subst hp
  rw [add_ofNat_add_ofNat]
  exact text_address_in_program (off + j) (by omega)

theorem avoids_prog {e : Effect}
    (h : ∀ c ∈ e.components, ∀ x, c.Covers x → ¬ InProgram x) :
    e.Avoids Extracted.programImage :=
  fun x hx c hc hcov => h c hc x.1 hcov (inProgram_of_mem hx)

theorem noMem_avoids {e : Effect} (h : ∀ c ∈ e.components, c.isMem = false) :
    e.Avoids Extracted.programImage := by
  apply Effect.Avoids.of_noMem
  intro c hc x hcov
  have := h c hc
  cases c <;> simp_all [Component.Covers, Component.isMem]

theorem writableRange_memWritable {s : RamState} {a : BitVec 64} {n : Nat}
    (h : WritableRange s a n) (hn : 0 < n) : MemWritable s a n := by
  refine ⟨h.readable.low, h.readable.mem, ?_⟩
  have hlow := h.readable.low
  unfold PageTableEntriesApart
  refine Classical.byContradiction fun hc => ?_
  have key : ∃ i < n, 0x1000 ≤ a.toNat + i ∧ a.toNat + i < 0x2020 := by
    by_cases h1 : a.toNat < 0x1000
    · exact ⟨0x1000 - a.toNat, by omega, by omega, by omega⟩
    · exact ⟨0, by omega, by omega, by omega⟩
  obtain ⟨i, hi, h1, h2⟩ := key
  apply h.tables i hi
  rw [inPageTables_iff, toNat_add_ofNat _ _ (by omega)]
  omega

theorem memWritable_grow {s u : RamState} {a : BitVec 64} {n : Nat} (h : MemWritable s a n)
    (hg : ∀ x : BitVec 64, (s.external[x]?).isSome → (u.external[x]?).isSome) : MemWritable u a n :=
  ⟨h.low, fun i hi => hg _ (h.mem i hi), h.tables⟩

theorem memReadable_grow {s u : RamState} {a : BitVec 64} {n : Nat} (h : MemReadable s a n)
    (hg : ∀ x : BitVec 64, (s.external[x]?).isSome → (u.external[x]?).isSome) : MemReadable u a n :=
  ⟨h.low, fun i hi => hg _ (h.mem i hi)⟩

theorem memWritable_at {s : RamState} {a b : BitVec 64} {n : Nat} (h : MemWritable s b n)
    (off len : Nat) (hb : off + len ≤ n) (he : a = b + BitVec.ofNat 64 off) :
    MemWritable s a len := by
  subst he
  refine ⟨?_, ?_, ?_⟩
  · rw [toNat_add_ofNat _ _ (by have := h.low; omega)]
    have := h.low
    omega
  · intro i hi
    rw [add_ofNat_add_ofNat]
    exact h.mem (off + i) (by omega)
  · rw [toNat_add_ofNat _ _ (by have := h.low; omega)]
    have := h.tables
    unfold PageTableEntriesApart at this ⊢
    omega

theorem memReadable_at {s : RamState} {a b : BitVec 64} {n : Nat} (h : MemReadable s b n)
    (off len : Nat) (hb : off + len ≤ n) (he : a = b + BitVec.ofNat 64 off) :
    MemReadable s a len := by
  subst he
  exact memReadable_slice h off len hb

theorem apart_at {s : RamState} {a b : BitVec 64} {n : Nat} (h : WritableRange s b n)
    (off len : Nat) (hb : off + len ≤ n) (he : a = b + BitVec.ofNat 64 off)
    {p : BitVec 64} {m : Nat} (hp : ∀ j < m, InProgram (p + BitVec.ofNat 64 j)) :
    RangeApart a len p m := by
  subst he
  intro i hi j hj heq
  apply h.code (off + i) (by omega)
  rw [← add_ofNat_add_ofNat, heq]
  exact hp j hj

theorem r32_eq (u : RamState) (r : BitVec 5) :
    (Operand.reg r : Operand 32).read u = ((Operand.reg r : Operand 64).read u).setWidth 32 := by
  simp

theorem sw5_7 : BitVec.setWidth 5 (7 : BitVec 4) = (7 : BitVec 5) := rfl

theorem sw5_9 : BitVec.setWidth 5 (9 : BitVec 4) = (9 : BitVec 5) := rfl

theorem sw5_10 : BitVec.setWidth 5 (10 : BitVec 4) = (10 : BitVec 5) := rfl

theorem sw5_12 : BitVec.setWidth 5 (12 : BitVec 4) = (12 : BitVec 5) := rfl

theorem sw_sw (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  simp [BitVec.setWidth_setWidth_of_le]

theorem mem_congr {u v : RamState} {n : Nat} (h : u.external = v.external) (a : BitVec 64) :
    (Operand.mem a : Operand n).read u = (Operand.mem a : Operand n).read v := by
  simp only [Operand.read, h]

def Grows (s u : RamState) : Prop :=
  ∀ x : BitVec 64, (s.external[x]?).isSome → (u.external[x]?).isSome

theorem Grows.step {s u v : RamState} {cs : List Component} (h : Grows s u)
    (he : AgreesExcept cs u v) : Grows s v :=
  fun x hx => he.grow x (h x hx)

def Untouched (s u : RamState) : Prop :=
  ∀ x : BitVec 64, (∀ i < frameBytes, x ≠ frameStart s + BitVec.ofNat 64 i) →
    u.external[x]? = s.external[x]?

theorem Untouched.step {s u v : RamState} {cs : List Component} (h : Untouched s u)
    (he : AgreesExcept cs u v) (hcs : ∀ c ∈ cs, c.isMem = false) : Untouched s v := by
  intro x hx
  refine (he.byte fun c hc hcov => ?_).trans (h x hx)
  have := hcs c hc
  cases c <;> simp_all [Component.Covers, Component.isMem]

theorem Untouched.push {s u v : RamState} {a : BitVec 64} (h : Untouched s u)
    (he : AgreesExcept [.reg 4, .mem a 8, .rip] u v) (off : Nat)
    (ha : a = frameStart s + BitVec.ofNat 64 off) (hoff : off + 8 ≤ frameBytes) :
    Untouched s v := by
  intro x hx
  refine (he.byte fun c hc hcov => ?_).trans (h x hx)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hcov
  · obtain ⟨i, hi, rfl⟩ := hcov
    exact hx (off + i) (by omega) (by rw [ha, add_ofNat_add_ofNat])
  · exact hcov

def FrameKept (s w u : RamState) : Prop :=
  ∀ i < frameBytes + 8, u.external[frameStart s + BitVec.ofNat 64 i]? =
    w.external[frameStart s + BitVec.ofNat 64 i]?

theorem FrameKept.refl (s w : RamState) : FrameKept s w w := fun _ _ => rfl

theorem FrameKept.step {s w u v : RamState} {cs : List Component} (h : FrameKept s w u)
    (he : AgreesExcept cs u v) (hcs : ∀ c ∈ cs, c.isMem = false) : FrameKept s w v := by
  intro i hi
  refine (he.byte fun c hc hcov => ?_).trans (h i hi)
  have := hcs c hc
  cases c <;> simp_all [Component.Covers, Component.isMem]

theorem FrameKept.store {s w u v : RamState} {e : Effect} {a : BitVec 64} (h : FrameKept s w u)
    (hc : e.components = [.mem a 4, .rip]) (he : e.Holds u v) (off : Nat)
    (ha : a = rdi.read s + BitVec.ofNat 64 off) (hoff : off + 4 ≤ tagBytes)
    (hap : RangeApart (rdi.read s) tagBytes (frameStart s) (frameBytes + 8)) :
    FrameKept s w v := by
  have hag := he.agrees
  rw [hc] at hag
  intro i hi
  refine (hag.byte fun c hcm hcov => ?_).trans (h i hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
  rcases hcm with rfl | rfl
  · obtain ⟨j, hj, hx⟩ := hcov
    rw [ha, add_ofNat_add_ofNat] at hx
    exact hap (off + j) (by omega) i hi hx.symm
  · exact hcov

theorem memLoad_of_bytes {u v : RamState} {a : BitVec 64} {n : Nat}
    (h : ∀ i < n / 8, v.external[a + BitVec.ofNat 64 i]? = u.external[a + BitVec.ofNat 64 i]?) :
    (Operand.mem a : Operand n).read v = (Operand.mem a : Operand n).read u := by
  simp only [Operand.read]
  apply memLoad_congr
  intro i hi
  simp only [memByte]
  exact congrArg (fun b : Option UInt8 => b.getD 0) (h i hi)

theorem addr6 {u : RamState} {base : BitVec 64} (h : (Operand.reg 6 : Operand 64).read u = base)
    (d : Disp) (nxt : BitVec 64) : (AddrMode.base 6 d).addr u nxt = base + d.value := by
  simp only [AddrMode.addr, AddrMode.reg64]
  rw [show ((6 : BitVec 4).setWidth 5) = (6 : BitVec 5) from rfl, h]

theorem load_word {s u : RamState} (hU : Untouched s u)
    (hsf : RangeApart (rsi.read s) stateBytes (frameStart s) frameBytes)
    (d : Disp) (k : Nat) (hd : d.value = BitVec.ofNat 64 k) (hk : k + 4 ≤ stateBytes) :
    (Operand.mem (rsi.read s + d.value) : Operand 32).read u =
      word32 s (rsi.read s + BitVec.ofNat 64 k) := by
  rw [hd, word32]
  apply memLoad_of_bytes
  intro i hi
  apply hU
  intro j hj he
  rw [add_ofNat_add_ofNat] at he
  exact hsf (k + i) (by omega) j hj he

theorem Untouched.push' {s u v : RamState} {p : BitVec 64} {len : Nat} {r : BitVec 5}
    (h : Untouched s u) (he : (pushR64Effect p len r u).Holds u v) (off : Nat)
    (ha : pushAddr u = frameStart s + BitVec.ofNat 64 off) (hoff : off + 8 ≤ frameBytes) :
    Untouched s v := by
  have hag := he.agrees
  rw [pushR64Effect_components] at hag
  exact h.push hag off ha hoff

theorem push_avoids {s u : RamState} {p : BitVec 64} {len : Nat} {r : BitVec 5}
    (hf : WritableRange s (frameStart s) frameBytes) (off : Nat)
    (ha : pushAddr u = frameStart s + BitVec.ofNat 64 off) (hoff : off + 8 ≤ frameBytes) :
    (pushR64Effect p len r u).Avoids Extracted.programImage := by
  apply avoids_prog
  intro c hc x hx
  rw [pushR64Effect_components] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hx.elim
  · obtain ⟨i, hi, rfl⟩ := hx
    rw [ha, add_ofNat_add_ofNat]
    exact hf.code (off + i) (by omega)
  · exact hx.elim

theorem slot_keep {s u v : RamState} {p : BitVec 64} {len : Nat} {r : BitVec 5}
    (he : (pushR64Effect p len r u).Holds u v) (off off' : Nat)
    (ha : pushAddr u = frameStart s + BitVec.ofNat 64 off) (hle : off + 8 ≤ off')
    (hoff' : off' + 8 ≤ frameBytes) :
    (Operand.mem (frameStart s + BitVec.ofNat 64 off') : Operand 64).read v =
      (Operand.mem (frameStart s + BitVec.ofNat 64 off') : Operand 64).read u := by
  have hag := he.agrees
  rw [pushR64Effect_components] at hag
  apply memLoad_of_bytes
  intro i hi
  apply hag.byte
  intro c hc hcov
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hcov
  · obtain ⟨j, hj, hx⟩ := hcov
    rw [ha, add_ofNat_add_ofNat, add_ofNat_add_ofNat] at hx
    replace hx := (BitVec.add_right_inj _).mp hx
    have := congrArg BitVec.toNat hx
    simp only [BitVec.toNat_ofNat] at this
    unfold frameBytes at hoff'
    have h1 : (off' + i) % 2 ^ 64 = off' + i := Nat.mod_eq_of_lt (by omega)
    have h2 : (off + j) % 2 ^ 64 = off + j := Nat.mod_eq_of_lt (by omega)
    omega
  · exact hcov

theorem push_slot {u v : RamState} {p : BitVec 64} {len : Nat} {r : BitVec 5}
    (he : (pushR64Effect p len r u).Holds u v) :
    (Operand.mem (pushAddr u) : Operand 64).read v = (Operand.reg r : Operand 64).read u :=
  he.writes.2

theorem push_rsp {u v : RamState} {p : BitVec 64} {len : Nat} {r : BitVec 5}
    (he : (pushR64Effect p len r u).Holds u v) : stackPtr v = pushAddr u := by
  rw [stackPtr_eq_read]
  exact he.writes.1

theorem addr0 {u : RamState} {base : BitVec 64} (h : (Operand.reg 0 : Operand 64).read u = base)
    (d : Disp) (nxt : BitVec 64) : (AddrMode.base 0 d).addr u nxt = base + d.value := by
  simp only [AddrMode.addr, AddrMode.reg64]
  rw [show ((0 : BitVec 4).setWidth 5) = (0 : BitVec 5) from rfl, h]

theorem FrameKept.read64 {s w u : RamState} (h : FrameKept s w u) (off : Nat)
    (hoff : off + 8 ≤ frameBytes + 8) :
    (Operand.mem (frameStart s + BitVec.ofNat 64 off) : Operand 64).read u =
      (Operand.mem (frameStart s + BitVec.ofNat 64 off) : Operand 64).read w := by
  apply memLoad_of_bytes
  intro i hi
  rw [add_ofNat_add_ofNat]
  exact h (off + i) (by omega)

theorem mem_avoids {s : RamState} {e : Effect} {a b : BitVec 64} {len n : Nat}
    (hc : e.components = [.mem a len, .rip]) (hw : WritableRange s b n) (off : Nat)
    (ha : a = b + BitVec.ofNat 64 off) (hoff : off + len ≤ n) :
    e.Avoids Extracted.programImage := by
  apply avoids_prog
  intro c hcm x hx
  rw [hc] at hcm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
  rcases hcm with rfl | rfl
  · obtain ⟨i, hi, rfl⟩ := hx
    rw [ha, add_ofNat_add_ofNat]
    exact hw.code (off + i) (by omega)
  · exact hx.elim

theorem out_keep {s u v : RamState} {e : Effect} {a : BitVec 64}
    (hc : e.components = [.mem a 4, .rip]) (he : e.Holds u v) (off off' : Nat)
    (ha : a = rdi.read s + BitVec.ofNat 64 off) (hd : off + 4 ≤ off' ∨ off' + 4 ≤ off)
    (hoff : off + 4 ≤ tagBytes) (hoff' : off' + 4 ≤ tagBytes) :
    (Operand.mem (rdi.read s + BitVec.ofNat 64 off') : Operand 32).read v =
      (Operand.mem (rdi.read s + BitVec.ofNat 64 off') : Operand 32).read u := by
  have hag := he.agrees
  rw [hc] at hag
  apply memLoad_of_bytes
  intro i hi
  apply hag.byte
  intro c hcm hcov
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
  rcases hcm with rfl | rfl
  · obtain ⟨j, hj, hx⟩ := hcov
    rw [ha, add_ofNat_add_ofNat, add_ofNat_add_ofNat] at hx
    replace hx := (BitVec.add_right_inj _).mp hx
    have := congrArg BitVec.toNat hx
    simp only [BitVec.toNat_ofNat] at this
    unfold tagBytes at hoff hoff'
    have h1 : (off' + i) % 2 ^ 64 = off' + i := Nat.mod_eq_of_lt (by omega)
    have h2 : (off + j) % 2 ^ 64 = off + j := Nat.mod_eq_of_lt (by omega)
    omega
  · exact hcov

theorem out_keep_reg {u v : RamState} {cs : List Component} (he : AgreesExcept cs u v)
    (hcs : ∀ c ∈ cs, c.isMem = false) {n : Nat} (a : BitVec 64) :
    (Operand.mem a : Operand n).read v = (Operand.mem a : Operand n).read u := by
  apply mem_congr
  apply he.external
  intro c hc x hx
  have := hcs c hc
  cases c <;> simp_all [Component.Covers, Component.isMem]

def CS (s : RamState) : List Component :=
  callChanges s ++ [.reg 3, .reg 5, .reg 12, .reg 13, .reg 14, .reg 15]

theorem acc_reg {s u v : RamState} {cs : List Component} (hA : AgreesExcept (CS s) s u)
    (he : AgreesExcept cs u v) (h : ∀ c ∈ cs, c ∈ CS s) : AgreesExcept (CS s) s v :=
  (hA.trans he).mono fun c hc => by
    rcases List.mem_append.mp hc with h1 | h1
    · exact h1
    · exact h c h1

theorem AgreesExcept.widen {cs cs' : List Component} {s t : RamState}
    (h : AgreesExcept cs s t) (hreg : ∀ c ∈ cs, c.isMem = false → c ∈ cs')
    (hmem : ∀ c ∈ cs, ∀ x, c.Covers x → ∃ c' ∈ cs', c'.Covers x) : AgreesExcept cs' s t := by
  classical
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, h.rest, h.grow⟩
  · by_cases hin : c ∈ cs
    · exact absurd (hreg c hin hm) hc
    · exact h.agree c hin hm
  · apply h.memory x
    intro c hc hcov
    obtain ⟨c', hc', hcov'⟩ := hmem c hc x hcov
    exact hx c' hc' hcov'

theorem acc_mem {s u v : RamState} {cs : List Component} {a b : BitVec 64} {len n : Nat}
    (hA : AgreesExcept (CS s) s u) (he : AgreesExcept cs u v)
    (hreg : ∀ c ∈ cs, c.isMem = false → c ∈ CS s)
    (hmemc : ∀ c ∈ cs, c.isMem = true → c = .mem a len) (hb : .mem b n ∈ CS s) (off : Nat)
    (ha : a = b + BitVec.ofNat 64 off) (hoff : off + len ≤ n) : AgreesExcept (CS s) s v := by
  refine (hA.trans he).widen ?_ ?_
  · intro c hc hm
    rcases List.mem_append.mp hc with h1 | h1
    · exact h1
    · exact hreg c h1 hm
  · intro x c hc hx
    rcases List.mem_append.mp hc with h1 | h1
    · exact ⟨c, h1, hx⟩
    · cases hcm : c.isMem
      · cases c <;> simp_all [Component.Covers, Component.isMem]
      · rw [hmemc c h1 hcm] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        exact ⟨_, hb, off + i, by omega, by rw [ha, add_ofNat_add_ofNat]⟩

theorem cf_of_flags {e : Effect} {v : RamState} {f : StatusFlags}
    (hf : e.flags = some (.ofStatusFlags f)) (h : e.FlagsHold v) :
    (StatusFlags.ofRFLAGS v.RFLAGS).CF = f.CF := by
  unfold Effect.FlagsHold at h
  rw [hf] at h
  exact h.1

theorem store_fact {e : Effect} {u v : RamState} {a : BitVec 64} {x : BitVec 32}
    (h : e.Holds u v) (hw : e.writes = [⟨(Operand.mem a : Operand 32), x⟩]) :
    (Operand.mem a : Operand 32).read v = x := by
  have := h.writes
  rw [hw] at this
  exact this

theorem dv_none : Disp.value .none = BitVec.ofNat 64 0 := rfl
theorem dv_4 : Disp.value (.d8 0x4) = BitVec.ofNat 64 0x4 := rfl
theorem dv_8 : Disp.value (.d8 0x8) = BitVec.ofNat 64 0x8 := rfl
theorem dv_c : Disp.value (.d8 0xc) = BitVec.ofNat 64 0xc := rfl

theorem ret_slot_untouched {s u : RamState} (hU : Untouched s u) :
    (Operand.mem (frameStart s + BitVec.ofNat 64 48) : Operand 64).read u =
      (Operand.mem (frameStart s + BitVec.ofNat 64 48) : Operand 64).read s := by
  apply memLoad_of_bytes
  intro i hi
  apply hU
  intro j hj he
  rw [add_ofNat_add_ofNat] at he
  replace he := (BitVec.add_right_inj _).mp he
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat] at this
  unfold frameBytes at hj
  have h1 : (48 + i) % 2 ^ 64 = 48 + i := Nat.mod_eq_of_lt (by omega)
  have h2 : j % 2 ^ 64 = j := Nat.mod_eq_of_lt (by omega)
  omega

theorem finish_agrees {s u : RamState} (hA : AgreesExcept (CS s) s u)
    (h3 : (Operand.reg 3 : Operand 64).read u = (Operand.reg 3 : Operand 64).read s)
    (h5 : (Operand.reg 5 : Operand 64).read u = (Operand.reg 5 : Operand 64).read s)
    (h12 : (Operand.reg 12 : Operand 64).read u = (Operand.reg 12 : Operand 64).read s)
    (h13 : (Operand.reg 13 : Operand 64).read u = (Operand.reg 13 : Operand 64).read s)
    (h14 : (Operand.reg 14 : Operand 64).read u = (Operand.reg 14 : Operand 64).read s)
    (h15 : (Operand.reg 15 : Operand 64).read u = (Operand.reg 15 : Operand 64).read s) :
    AgreesExcept (callChanges s) s u := by
  apply hA.narrow
  intro c hc hn
  simp only [CS, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hc | hc
  · exact absurd hc hn
  · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [Component.Agrees] using h3
    · simpa [Component.Agrees] using h5
    · simpa [Component.Agrees] using h12
    · simpa [Component.Agrees] using h13
    · simpa [Component.Agrees] using h14
    · simpa [Component.Agrees] using h15

theorem store_comps {p : BitVec 64} {len : Nat} {addr : RamState → BitVec 64}
    {v : RamState → BitVec 32} {u : RamState} :
    (storeEffect p len addr v u).components = [.mem (addr u) 4, .rip] := by
  simp [storeEffect_components]

theorem acc_store {s u v : RamState} {e : Effect} {a : BitVec 64} (hA : AgreesExcept (CS s) s u)
    (he : e.Holds u v) (hc : e.components = [.mem a 4, .rip]) (off : Nat)
    (ha : a = rdi.read s + BitVec.ofNat 64 off) (hoff : off + 4 ≤ tagBytes) :
    AgreesExcept (CS s) s v := by
  have hag := he.agrees
  rw [hc] at hag
  refine acc_mem hA hag ?_ ?_ (b := rdi.read s) (n := tagBytes) (by simp [CS, callChanges]) off ha hoff
  · intro c hcm hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl
    · simp [Component.isMem] at hm
    · simp [CS, callChanges]
  · intro c hcm hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl
    · rfl
    · simp [Component.isMem] at hm

structure Words where
  h0 : BitVec 32
  h1 : BitVec 32
  h2 : BitVec 32
  h3 : BitVec 32
  h4 : BitVec 32
  p0 : BitVec 32
  p1 : BitVec 32
  p2 : BitVec 32
  p3 : BitVec 32

def words (s : RamState) : Words where
  h0 := word32 s (rsi.read s + BitVec.ofNat 64 0x24)
  h1 := word32 s (rsi.read s + BitVec.ofNat 64 0x28)
  h2 := word32 s (rsi.read s + BitVec.ofNat 64 0x2c)
  h3 := word32 s (rsi.read s + BitVec.ofNat 64 0x30)
  h4 := word32 s (rsi.read s + BitVec.ofNat 64 0x34)
  p0 := word32 s (rsi.read s + BitVec.ofNat 64 0)
  p1 := word32 s (rsi.read s + BitVec.ofNat 64 4)
  p2 := word32 s (rsi.read s + BitVec.ofNat 64 8)
  p3 := word32 s (rsi.read s + BitVec.ofNat 64 0xc)

theorem words_h0 (s : RamState) : (words s).h0 = word32 s (rsi.read s + BitVec.ofNat 64 0x24) := rfl

theorem words_h1 (s : RamState) : (words s).h1 = word32 s (rsi.read s + BitVec.ofNat 64 0x28) := rfl

theorem words_h2 (s : RamState) : (words s).h2 = word32 s (rsi.read s + BitVec.ofNat 64 0x2c) := rfl

theorem words_h3 (s : RamState) : (words s).h3 = word32 s (rsi.read s + BitVec.ofNat 64 0x30) := rfl

theorem words_h4 (s : RamState) : (words s).h4 = word32 s (rsi.read s + BitVec.ofNat 64 0x34) := rfl

theorem words_p0 (s : RamState) : (words s).p0 = word32 s (rsi.read s + BitVec.ofNat 64 0) := rfl

theorem words_p1 (s : RamState) : (words s).p1 = word32 s (rsi.read s + BitVec.ofNat 64 4) := rfl

theorem words_p2 (s : RamState) : (words s).p2 = word32 s (rsi.read s + BitVec.ofNat 64 8) := rfl

theorem words_p3 (s : RamState) : (words s).p3 = word32 s (rsi.read s + BitVec.ofNat 64 0xc) := rfl

def v7 (w : Words) : BitVec 32 := w.h1
def v9 (w : Words) : BitVec 32 := (v7 w) >>> 26
def v10 (w : Words) : BitVec 32 := (v9 w) + w.h2
def v11 (w : Words) : BitVec 32 := (v7 w) &&& (0x3ffffff : BitVec 32).signExtend 32
def v13 (w : Words) : BitVec 32 := (v10 w) >>> 26
def v14 (w : Words) : BitVec 32 := (v10 w) &&& (0x3ffffff : BitVec 32).signExtend 32
def v15 (w : Words) : BitVec 32 := (v13 w) + w.h3
def v17 (w : Words) : BitVec 32 := (v15 w) >>> 26
def v18 (w : Words) : BitVec 32 := (v15 w) &&& (0x3ffffff : BitVec 32).signExtend 32
def v19 (w : Words) : BitVec 32 := (v17 w) + w.h4
def v21 (w : Words) : BitVec 32 := (v19 w) >>> 26
def v23 (w : Words) : BitVec 32 := (v19 w) &&& (0x3ffffff : BitVec 32).signExtend 32
def v24 (w : Words) : BitVec 32 := (v21 w) + ((v21 w) <<< 2)
def v25 (w : Words) : BitVec 32 := (v24 w) + w.h0
def v27 (w : Words) : BitVec 32 := (v25 w) >>> 26
def v28 (w : Words) : BitVec 32 := (v27 w) + (v11 w)
def v29 (w : Words) : BitVec 32 := (v25 w) &&& (0x3ffffff : BitVec 32).signExtend 32
def v30 (w : Words) : BitVec 32 := (v29 w) + 5
def v32 (w : Words) : BitVec 32 := (v30 w) >>> 26
def v33 (w : Words) : BitVec 32 := (v32 w) + (v28 w)
def v35 (w : Words) : BitVec 32 := (v33 w) >>> 26
def v36 (w : Words) : BitVec 32 := (v35 w) + (v14 w)
def v38 (w : Words) : BitVec 32 := (v36 w) >>> 26
def v39 (w : Words) : BitVec 32 := (v38 w) + (v18 w)
def v41 (w : Words) : BitVec 32 := (v39 w) >>> 26
def v42 (w : Words) : BitVec 32 := (v41 w) + (v23 w)
def v43 (w : Words) : BitVec 32 := (v42 w) + (0xfc000000 : BitVec 32).signExtend 32
def v44 (w : Words) : BitVec 32 := (v41 w) + (v23 w)
def v46 (w : Words) : BitVec 32 := (v43 w).sshiftRight 31
def v47 (w : Words) : BitVec 32 := (v43 w) >>> 31
def v48 (w : Words) : BitVec 32 := (v47 w) - 1
def v50 (w : Words) : BitVec 32 := (v48 w) &&& (0x3ffffff : BitVec 32).signExtend 32
def v51 (w : Words) : BitVec 32 := (v30 w) &&& (v50 w)
def v52 (w : Words) : BitVec 32 := (v33 w) &&& (v50 w)
def v53 (w : Words) : BitVec 32 := (v36 w) &&& (v50 w)
def v54 (w : Words) : BitVec 32 := (v50 w) &&& (v39 w)
def v55 (w : Words) : BitVec 32 := (v48 w) &&& (v44 w)
def v56 (w : Words) : BitVec 32 := (v29 w) &&& (v46 w)
def v57 (w : Words) : BitVec 32 := (v56 w) ||| (v51 w)
def v58 (w : Words) : BitVec 32 := (v28 w) &&& (v46 w)
def v59 (w : Words) : BitVec 32 := (v58 w) ||| (v52 w)
def v60 (w : Words) : BitVec 32 := (v14 w) &&& (v46 w)
def v61 (w : Words) : BitVec 32 := (v60 w) ||| (v53 w)
def v62 (w : Words) : BitVec 32 := (v18 w) &&& (v46 w)
def v63 (w : Words) : BitVec 32 := (v62 w) ||| (v54 w)
def v64 (w : Words) : BitVec 32 := (v46 w) &&& (v19 w)
def v65 (w : Words) : BitVec 32 := (v64 w) ||| (v55 w)
def v67 (w : Words) : BitVec 32 := (v59 w) <<< 26
def v68 (w : Words) : BitVec 32 := (v67 w) ||| (v57 w)
def v69 (w : Words) : BitVec 32 := (v59 w) >>> 6
def v71 (w : Words) : BitVec 32 := (v61 w) <<< 20
def v72 (w : Words) : BitVec 32 := (v71 w) ||| (v69 w)
def v73 (w : Words) : BitVec 32 := (v61 w) >>> 12
def v75 (w : Words) : BitVec 32 := (v63 w) <<< 14
def v76 (w : Words) : BitVec 32 := (v75 w) ||| (v73 w)
def v77 (w : Words) : BitVec 32 := (v63 w) >>> 18
def v78 (w : Words) : BitVec 32 := (v65 w) <<< 8
def v79 (w : Words) : BitVec 32 := (v78 w) ||| (v77 w)
def v80 (w : Words) : BitVec 32 := (v68 w) + w.p0
def cf80 (w : Words) : Bool := (addSpec (v68 w) w.p0).2.CF
def v81 (w : Words) : BitVec 32 := w.p1
def v82 (w : Words) : BitVec 32 := w.p2
def q83 (w : Words) : BitVec 64 := ((v81 w).setWidth 64) + ((v72 w).setWidth 64) + BitVec.ofNat 64 (cf80 w).toNat
def v84 (w : Words) : BitVec 32 := ((q83 w).setWidth 32)
def q85 (w : Words) : BitVec 64 := ((v82 w).setWidth 64) + ((v76 w).setWidth 64)
def q86 (w : Words) : BitVec 64 := (q83 w) >>> 32
def q87 (w : Words) : BitVec 64 := (q86 w) + (q85 w)
def v88 (w : Words) : BitVec 32 := (v79 w) + w.p3
def v89 (w : Words) : BitVec 32 := ((q87 w).setWidth 32)
def q90 (w : Words) : BitVec 64 := (q87 w) >>> 32
def v91 (w : Words) : BitVec 32 := ((q90 w).setWidth 32) + (v88 w)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem body [Bindings] (boundary : ReturnBoundary)
    (hne : ∀ a : BitVec 64, 0x101ce0 ≤ a.toNat → a.toNat ≤ 0x101e27 → a ≠ boundary.rip)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : FinalizePre s) : ∃ fuel u, Advances boundary fuel s u ∧ ReadyToStep u ∧
      CodeIn Extracted.programImage u ∧ u.RIP = 0x101e27 ∧ stackPtr u = stackPtr s ∧
      MemReadable u (stackPtr u) 8 ∧
      (Operand.mem (stackPtr u) : Operand 64).read u = (returnBoundary s).rip ∧
      rax.read u = rdi.read s ∧ AgreesExcept (callChanges s) s u ∧ Grows s u ∧
      (Operand.mem (rdi.read s + BitVec.ofNat 64 0) : Operand 32).read u = v80 (words s) ∧
      (Operand.mem (rdi.read s + BitVec.ofNat 64 4) : Operand 32).read u = v84 (words s) ∧
      (Operand.mem (rdi.read s + BitVec.ofNat 64 8) : Operand 32).read u = v89 (words s) ∧
      (Operand.mem (rdi.read s + BitVec.ofNat 64 12) : Operand 32).read u = v91 (words s) := by
  have hFW : MemWritable s (frameStart s) frameBytes := writableRange_memWritable hp.frame (by decide)
  have hOW : MemWritable s (rdi.read s) tagBytes := writableRange_memWritable hp.output (by decide)
  have G0 : Grows s s := fun _ h => h
  have U0 : Untouched s s := fun _ _ => rfl
  have A0 : AgreesExcept (CS s) s s := AgreesExcept.refl _ _
  have SP0 : stackPtr s = frameStart s + BitVec.ofNat 64 48 := by simp only [frameStart, frameBytes]; bv_omega
  have F0_3 : (Operand.reg 3 : Operand 64).read s = (Operand.reg 3 : Operand 64).read s := rfl
  have F0_5 : (Operand.reg 5 : Operand 64).read s = (Operand.reg 5 : Operand 64).read s := rfl
  have F0_6 : (Operand.reg 6 : Operand 64).read s = (Operand.reg 6 : Operand 64).read s := rfl
  have F0_7 : (Operand.reg 7 : Operand 64).read s = (Operand.reg 7 : Operand 64).read s := rfl
  have F0_12 : (Operand.reg 12 : Operand 64).read s = (Operand.reg 12 : Operand 64).read s := rfl
  have F0_13 : (Operand.reg 13 : Operand 64).read s = (Operand.reg 13 : Operand 64).read s := rfl
  have F0_14 : (Operand.reg 14 : Operand 64).read s = (Operand.reg 14 : Operand 64).read s := rfl
  have F0_15 : (Operand.reg 15 : Operand 64).read s = (Operand.reg 15 : Operand 64).read s := rfl
  have PA0 : pushAddr s = frameStart s + BitVec.ofNat 64 40 := by rw [pushAddr, SP0]; bv_omega
  obtain ⟨u1, a0, r1, c1, ip1, e0⟩ := run1 (push_r64_effect_step 0x101ce0 0x55 (by decide))
    hr hc (program_text_slice hc 0x1ce0 1 (by decide +kernel)) ⟨hp.rip, memWritable_at (memWritable_grow hFW G0) 40 8 (by decide) PA0, apart_at hp.frame 40 8 (by decide) PA0 (code_at _ 0x1ce0 1 (by decide) (by decide +kernel))⟩
    (q := 0x101ce1) rfl (hne _ (by decide) (by decide)) (push_avoids hp.frame 40 PA0 (by decide))
  replace e0 : (pushR64Effect 0x101ce0 1 5 s).Holds s u1 := e0
  have G1 := G0.step e0.agrees
  have A1 := acc_mem A0 e0.agrees (by simp [CS, callChanges, Component.isMem]) (by simp [Component.isMem]) (a := pushAddr s) (len := 8) (b := frameStart s) (n := frameBytes) (by simp [CS, callChanges]) 40 PA0 (by decide)
  have U1 := U0.push' e0 40 PA0 (by decide)
  have SP1 : stackPtr u1 = frameStart s + BitVec.ofNat 64 40 := (push_rsp e0).trans PA0
  have S0_1 : (Operand.mem (frameStart s + BitVec.ofNat 64 40) : Operand 64).read u1 = (Operand.reg 5 : Operand 64).read s := by
    rw [← PA0]; exact (push_slot e0).trans F0_5
  have F1_3 := (e0.agrees.read (r := 3) (n := 64) (by simp)).trans F0_3
  have F1_6 := (e0.agrees.read (r := 6) (n := 64) (by simp)).trans F0_6
  have F1_7 := (e0.agrees.read (r := 7) (n := 64) (by simp)).trans F0_7
  have F1_12 := (e0.agrees.read (r := 12) (n := 64) (by simp)).trans F0_12
  have F1_13 := (e0.agrees.read (r := 13) (n := 64) (by simp)).trans F0_13
  have F1_14 := (e0.agrees.read (r := 14) (n := 64) (by simp)).trans F0_14
  have F1_15 := (e0.agrees.read (r := 15) (n := 64) (by simp)).trans F0_15
  have AD1 := a0
  clear a0 e0 G0 A0 PA0 F0_3 F0_5 F0_6 F0_7 F0_12 F0_13 F0_14 F0_15
  have PA1 : pushAddr u1 = frameStart s + BitVec.ofNat 64 32 := by rw [pushAddr, SP1]; bv_omega
  obtain ⟨u2, a1, r2, c2, ip2, e1⟩ := run1 (push_r64_rex_effect_step 0x101ce1 0x41 0x57 (by unfold RexPrefix; decide) (by decide))
    r1 c1 (program_text_slice c1 0x1ce1 2 (by decide +kernel)) ⟨ip1, memWritable_at (memWritable_grow hFW G1) 32 8 (by decide) PA1, apart_at hp.frame 32 8 (by decide) PA1 (code_at _ 0x1ce1 2 (by decide) (by decide +kernel))⟩
    (q := 0x101ce3) rfl (hne _ (by decide) (by decide)) (push_avoids hp.frame 32 PA1 (by decide))
  replace e1 : (pushR64Effect 0x101ce1 2 15 u1).Holds u1 u2 := e1
  have G2 := G1.step e1.agrees
  have A2 := acc_mem A1 e1.agrees (by simp [CS, callChanges, Component.isMem]) (by simp [Component.isMem]) (a := pushAddr u1) (len := 8) (b := frameStart s) (n := frameBytes) (by simp [CS, callChanges]) 32 PA1 (by decide)
  have U2 := U1.push' e1 32 PA1 (by decide)
  have SP2 : stackPtr u2 = frameStart s + BitVec.ofNat 64 32 := (push_rsp e1).trans PA1
  have S1_2 : (Operand.mem (frameStart s + BitVec.ofNat 64 32) : Operand 64).read u2 = (Operand.reg 15 : Operand 64).read s := by
    rw [← PA1]; exact (push_slot e1).trans F1_15
  have S0_2 := (slot_keep e1 32 40 PA1 (by decide) (by decide)).trans S0_1
  have F2_3 := (e1.agrees.read (r := 3) (n := 64) (by simp)).trans F1_3
  have F2_6 := (e1.agrees.read (r := 6) (n := 64) (by simp)).trans F1_6
  have F2_7 := (e1.agrees.read (r := 7) (n := 64) (by simp)).trans F1_7
  have F2_12 := (e1.agrees.read (r := 12) (n := 64) (by simp)).trans F1_12
  have F2_13 := (e1.agrees.read (r := 13) (n := 64) (by simp)).trans F1_13
  have F2_14 := (e1.agrees.read (r := 14) (n := 64) (by simp)).trans F1_14
  have AD2 := AD1.trans a1
  clear a1 e1 AD1 r1 c1 ip1 G1 A1 SP1 U1 PA1 F1_3 F1_6 F1_7 F1_12 F1_13 F1_14 F1_15 S0_1
  clear u1
  have PA2 : pushAddr u2 = frameStart s + BitVec.ofNat 64 24 := by rw [pushAddr, SP2]; bv_omega
  obtain ⟨u3, a2, r3, c3, ip3, e2⟩ := run1 (push_r64_rex_effect_step 0x101ce3 0x41 0x56 (by unfold RexPrefix; decide) (by decide))
    r2 c2 (program_text_slice c2 0x1ce3 2 (by decide +kernel)) ⟨ip2, memWritable_at (memWritable_grow hFW G2) 24 8 (by decide) PA2, apart_at hp.frame 24 8 (by decide) PA2 (code_at _ 0x1ce3 2 (by decide) (by decide +kernel))⟩
    (q := 0x101ce5) rfl (hne _ (by decide) (by decide)) (push_avoids hp.frame 24 PA2 (by decide))
  replace e2 : (pushR64Effect 0x101ce3 2 14 u2).Holds u2 u3 := e2
  have G3 := G2.step e2.agrees
  have A3 := acc_mem A2 e2.agrees (by simp [CS, callChanges, Component.isMem]) (by simp [Component.isMem]) (a := pushAddr u2) (len := 8) (b := frameStart s) (n := frameBytes) (by simp [CS, callChanges]) 24 PA2 (by decide)
  have U3 := U2.push' e2 24 PA2 (by decide)
  have SP3 : stackPtr u3 = frameStart s + BitVec.ofNat 64 24 := (push_rsp e2).trans PA2
  have S2_3 : (Operand.mem (frameStart s + BitVec.ofNat 64 24) : Operand 64).read u3 = (Operand.reg 14 : Operand 64).read s := by
    rw [← PA2]; exact (push_slot e2).trans F2_14
  have S0_3 := (slot_keep e2 24 40 PA2 (by decide) (by decide)).trans S0_2
  have S1_3 := (slot_keep e2 24 32 PA2 (by decide) (by decide)).trans S1_2
  have F3_3 := (e2.agrees.read (r := 3) (n := 64) (by simp)).trans F2_3
  have F3_6 := (e2.agrees.read (r := 6) (n := 64) (by simp)).trans F2_6
  have F3_7 := (e2.agrees.read (r := 7) (n := 64) (by simp)).trans F2_7
  have F3_12 := (e2.agrees.read (r := 12) (n := 64) (by simp)).trans F2_12
  have F3_13 := (e2.agrees.read (r := 13) (n := 64) (by simp)).trans F2_13
  have AD3 := AD2.trans a2
  clear a2 e2 AD2 r2 c2 ip2 G2 A2 SP2 U2 PA2 F2_3 F2_6 F2_7 F2_12 F2_13 F2_14 S0_2 S1_2
  clear u2
  have PA3 : pushAddr u3 = frameStart s + BitVec.ofNat 64 16 := by rw [pushAddr, SP3]; bv_omega
  obtain ⟨u4, a3, r4, c4, ip4, e3⟩ := run1 (push_r64_rex_effect_step 0x101ce5 0x41 0x55 (by unfold RexPrefix; decide) (by decide))
    r3 c3 (program_text_slice c3 0x1ce5 2 (by decide +kernel)) ⟨ip3, memWritable_at (memWritable_grow hFW G3) 16 8 (by decide) PA3, apart_at hp.frame 16 8 (by decide) PA3 (code_at _ 0x1ce5 2 (by decide) (by decide +kernel))⟩
    (q := 0x101ce7) rfl (hne _ (by decide) (by decide)) (push_avoids hp.frame 16 PA3 (by decide))
  replace e3 : (pushR64Effect 0x101ce5 2 13 u3).Holds u3 u4 := e3
  have G4 := G3.step e3.agrees
  have A4 := acc_mem A3 e3.agrees (by simp [CS, callChanges, Component.isMem]) (by simp [Component.isMem]) (a := pushAddr u3) (len := 8) (b := frameStart s) (n := frameBytes) (by simp [CS, callChanges]) 16 PA3 (by decide)
  have U4 := U3.push' e3 16 PA3 (by decide)
  have SP4 : stackPtr u4 = frameStart s + BitVec.ofNat 64 16 := (push_rsp e3).trans PA3
  have S3_4 : (Operand.mem (frameStart s + BitVec.ofNat 64 16) : Operand 64).read u4 = (Operand.reg 13 : Operand 64).read s := by
    rw [← PA3]; exact (push_slot e3).trans F3_13
  have S0_4 := (slot_keep e3 16 40 PA3 (by decide) (by decide)).trans S0_3
  have S1_4 := (slot_keep e3 16 32 PA3 (by decide) (by decide)).trans S1_3
  have S2_4 := (slot_keep e3 16 24 PA3 (by decide) (by decide)).trans S2_3
  have F4_3 := (e3.agrees.read (r := 3) (n := 64) (by simp)).trans F3_3
  have F4_6 := (e3.agrees.read (r := 6) (n := 64) (by simp)).trans F3_6
  have F4_7 := (e3.agrees.read (r := 7) (n := 64) (by simp)).trans F3_7
  have F4_12 := (e3.agrees.read (r := 12) (n := 64) (by simp)).trans F3_12
  have AD4 := AD3.trans a3
  clear a3 e3 AD3 r3 c3 ip3 G3 A3 SP3 U3 PA3 F3_3 F3_6 F3_7 F3_12 F3_13 S0_3 S1_3 S2_3
  clear u3
  have PA4 : pushAddr u4 = frameStart s + BitVec.ofNat 64 8 := by rw [pushAddr, SP4]; bv_omega
  obtain ⟨u5, a4, r5, c5, ip5, e4⟩ := run1 (push_r64_rex_effect_step 0x101ce7 0x41 0x54 (by unfold RexPrefix; decide) (by decide))
    r4 c4 (program_text_slice c4 0x1ce7 2 (by decide +kernel)) ⟨ip4, memWritable_at (memWritable_grow hFW G4) 8 8 (by decide) PA4, apart_at hp.frame 8 8 (by decide) PA4 (code_at _ 0x1ce7 2 (by decide) (by decide +kernel))⟩
    (q := 0x101ce9) rfl (hne _ (by decide) (by decide)) (push_avoids hp.frame 8 PA4 (by decide))
  replace e4 : (pushR64Effect 0x101ce7 2 12 u4).Holds u4 u5 := e4
  have G5 := G4.step e4.agrees
  have A5 := acc_mem A4 e4.agrees (by simp [CS, callChanges, Component.isMem]) (by simp [Component.isMem]) (a := pushAddr u4) (len := 8) (b := frameStart s) (n := frameBytes) (by simp [CS, callChanges]) 8 PA4 (by decide)
  have U5 := U4.push' e4 8 PA4 (by decide)
  have SP5 : stackPtr u5 = frameStart s + BitVec.ofNat 64 8 := (push_rsp e4).trans PA4
  have S4_5 : (Operand.mem (frameStart s + BitVec.ofNat 64 8) : Operand 64).read u5 = (Operand.reg 12 : Operand 64).read s := by
    rw [← PA4]; exact (push_slot e4).trans F4_12
  have S0_5 := (slot_keep e4 8 40 PA4 (by decide) (by decide)).trans S0_4
  have S1_5 := (slot_keep e4 8 32 PA4 (by decide) (by decide)).trans S1_4
  have S2_5 := (slot_keep e4 8 24 PA4 (by decide) (by decide)).trans S2_4
  have S3_5 := (slot_keep e4 8 16 PA4 (by decide) (by decide)).trans S3_4
  have F5_3 := (e4.agrees.read (r := 3) (n := 64) (by simp)).trans F4_3
  have F5_6 := (e4.agrees.read (r := 6) (n := 64) (by simp)).trans F4_6
  have F5_7 := (e4.agrees.read (r := 7) (n := 64) (by simp)).trans F4_7
  have AD5 := AD4.trans a4
  clear a4 e4 AD4 r4 c4 ip4 G4 A4 SP4 U4 PA4 F4_3 F4_6 F4_7 F4_12 S0_4 S1_4 S2_4 S3_4
  clear u4
  have PA5 : pushAddr u5 = frameStart s + BitVec.ofNat 64 0 := by rw [pushAddr, SP5]; bv_omega
  obtain ⟨u6, a5, r6, c6, ip6, e5⟩ := run1 (push_r64_effect_step 0x101ce9 0x53 (by decide))
    r5 c5 (program_text_slice c5 0x1ce9 1 (by decide +kernel)) ⟨ip5, memWritable_at (memWritable_grow hFW G5) 0 8 (by decide) PA5, apart_at hp.frame 0 8 (by decide) PA5 (code_at _ 0x1ce9 1 (by decide) (by decide +kernel))⟩
    (q := 0x101cea) rfl (hne _ (by decide) (by decide)) (push_avoids hp.frame 0 PA5 (by decide))
  replace e5 : (pushR64Effect 0x101ce9 1 3 u5).Holds u5 u6 := e5
  have G6 := G5.step e5.agrees
  have A6 := acc_mem A5 e5.agrees (by simp [CS, callChanges, Component.isMem]) (by simp [Component.isMem]) (a := pushAddr u5) (len := 8) (b := frameStart s) (n := frameBytes) (by simp [CS, callChanges]) 0 PA5 (by decide)
  have U6 := U5.push' e5 0 PA5 (by decide)
  have SP6 : stackPtr u6 = frameStart s + BitVec.ofNat 64 0 := (push_rsp e5).trans PA5
  have S5_6 : (Operand.mem (frameStart s + BitVec.ofNat 64 0) : Operand 64).read u6 = (Operand.reg 3 : Operand 64).read s := by
    rw [← PA5]; exact (push_slot e5).trans F5_3
  have S0_6 := (slot_keep e5 0 40 PA5 (by decide) (by decide)).trans S0_5
  have S1_6 := (slot_keep e5 0 32 PA5 (by decide) (by decide)).trans S1_5
  have S2_6 := (slot_keep e5 0 24 PA5 (by decide) (by decide)).trans S2_5
  have S3_6 := (slot_keep e5 0 16 PA5 (by decide) (by decide)).trans S3_5
  have S4_6 := (slot_keep e5 0 8 PA5 (by decide) (by decide)).trans S4_5
  have FK6 : FrameKept s u6 u6 := FrameKept.refl s u6
  have F6_6 := (e5.agrees.read (r := 6) (n := 64) (by simp)).trans F5_6
  have F6_7 := (e5.agrees.read (r := 7) (n := 64) (by simp)).trans F5_7
  have AD6 := AD5.trans a5
  clear a5 e5 AD5 r5 c5 ip5 G5 A5 SP5 U5 PA5 F5_3 F5_6 F5_7 S0_5 S1_5 S2_5 S3_5 S4_5
  clear u5
  obtain ⟨u7, a6, r7, c7, ip7, e6⟩ := run1 (mov_r64_r64_effect_step 0x101cea 0x48 0xf8 (by unfold RexWPrefix; decide) (by decide))
    r6 c6 (program_text_slice c6 0x1cea 3 (by decide +kernel)) ip6
    (q := 0x101ced) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e6 : (movR64R64Effect 0x101cea 0 7 u6).Holds u6 u7 := e6
  have G7 := G6.step e6.agrees
  have A7 := acc_reg A6 e6.agrees (by simp [CS, callChanges])
  have U7 := U6.step e6.agrees (by simp [Component.isMem])
  have FK7 := FK6.step e6.agrees (by simp [Component.isMem])
  have SP7 : stackPtr u7 = frameStart s + BitVec.ofNat 64 0 := (e6.agrees.read (r := 4) (n := 64) (by simp)).trans SP6
  have F7_0 : (Operand.reg 0 : Operand 64).read u7 = (Operand.reg 7 : Operand 64).read s := e6.writes.trans F6_7
  have F7_6 := (e6.agrees.read (r := 6) (n := 64) (by simp)).trans F6_6
  have AD7 := AD6.trans a6
  clear a6 e6 AD6 r6 c6 ip6 G6 A6 SP6 FK6 F6_6 F6_7
  obtain ⟨u8, a7, r8, c8, ip8, e7⟩ := run1 (mov_r32_m32_effect_step 0x101ced 0x44 (by unfold RexNoWPrefix; decide) 3 (.base 6 (.d8 0x28)) (by decide) (by decide) (by decide))
    r7 c7 (program_text_slice c7 0x1ced 4 (by decide +kernel)) ⟨ip7, memReadable_at (memReadable_grow hp.state G7) 0x28 4 (by decide) (by rw [addr6 F7_6]; rfl)⟩
    (q := 0x101cf1) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e7 : (movR32M32Effect 0x101ced 11 (.base 6 (.d8 0x28)) u7).Holds u7 u8 := e7
  have G8 := G7.step e7.agrees
  have A8 := acc_reg A7 e7.agrees (by simp [CS, callChanges])
  have U8 := U7.step e7.agrees (by simp [Component.isMem])
  have FK8 := FK7.step e7.agrees (by simp [Component.isMem])
  have SP8 : stackPtr u8 = frameStart s + BitVec.ofNat 64 0 := (e7.agrees.read (r := 4) (n := 64) (by simp)).trans SP7
  have F8_11 : (Operand.reg 11 : Operand 64).read u8 = (v7 (words s)).setWidth 64 := by
    refine (e7.writes : (Operand.reg 11 : Operand 64).read u8 = _).trans ?_
    simp only [movR32M32Effect, r32_eq, addr6 F7_6, load_word U7 hp.stateFrame (.d8 0x28) 0x28 (by decide) (by decide), v7, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F8_0 := (e7.agrees.read (r := 0) (n := 64) (by simp)).trans F7_0
  have F8_6 := (e7.agrees.read (r := 6) (n := 64) (by simp)).trans F7_6
  have AD8 := AD7.trans a7
  clear a7 e7 AD7 r7 c7 ip7 G7 A7 SP7 U7 FK7 F7_0 F7_6
  clear u7
  obtain ⟨u9, a8, r9, c9, ip9, e8⟩ := run1 (mov_r32_r32_rex_effect_step 0x101cf1 0x44 0xd9 (by unfold RexNoWPrefix; decide) (by decide))
    r8 c8 (program_text_slice c8 0x1cf1 3 (by decide +kernel)) ip8
    (q := 0x101cf4) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e8 : (movR32R32Effect 0x101cf1 3 1 11 u8).Holds u8 u9 := e8
  have G9 := G8.step e8.agrees
  have A9 := acc_reg A8 e8.agrees (by simp [CS, callChanges])
  have U9 := U8.step e8.agrees (by simp [Component.isMem])
  have FK9 := FK8.step e8.agrees (by simp [Component.isMem])
  have SP9 : stackPtr u9 = frameStart s + BitVec.ofNat 64 0 := (e8.agrees.read (r := 4) (n := 64) (by simp)).trans SP8
  have F9_1 : (Operand.reg 1 : Operand 64).read u9 = (v7 (words s)).setWidth 64 := by
    refine (e8.writes : (Operand.reg 1 : Operand 64).read u9 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F8_11, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F9_0 := (e8.agrees.read (r := 0) (n := 64) (by simp)).trans F8_0
  have F9_6 := (e8.agrees.read (r := 6) (n := 64) (by simp)).trans F8_6
  have F9_11 := (e8.agrees.read (r := 11) (n := 64) (by simp)).trans F8_11
  have AD9 := AD8.trans a8
  clear a8 e8 AD8 r8 c8 ip8 G8 A8 SP8 U8 FK8 F8_0 F8_6 F8_11
  clear u8
  obtain ⟨u10, a9, r10, c10, ip10, e9⟩ := run1 (shr_r32_imm8_effect_step 0x101cf4 0xe9 0x1a (by decide) (by decide))
    r9 c9 (program_text_slice c9 0x1cf4 3 (by decide +kernel)) ip9
    (q := 0x101cf7) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e9 : (shrR32Effect 0x101cf4 3 1 26 u9).Holds u9 u10 := e9
  have G10 := G9.step e9.agrees
  have A10 := acc_reg A9 e9.agrees (by simp [CS, callChanges])
  have U10 := U9.step e9.agrees (by simp [Component.isMem])
  have FK10 := FK9.step e9.agrees (by simp [Component.isMem])
  have SP10 : stackPtr u10 = frameStart s + BitVec.ofNat 64 0 := (e9.agrees.read (r := 4) (n := 64) (by simp)).trans SP9
  have F10_1 : (Operand.reg 1 : Operand 64).read u10 = (v9 (words s)).setWidth 64 := by
    refine (e9.writes : (Operand.reg 1 : Operand 64).read u10 = _).trans ?_
    simp only [shrR32Effect, r32_eq, F9_1, v9, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F10_0 := (e9.agrees.read (r := 0) (n := 64) (by simp)).trans F9_0
  have F10_6 := (e9.agrees.read (r := 6) (n := 64) (by simp)).trans F9_6
  have F10_11 := (e9.agrees.read (r := 11) (n := 64) (by simp)).trans F9_11
  have AD10 := AD9.trans a9
  clear a9 e9 AD9 r9 c9 ip9 G9 A9 SP9 U9 FK9 F9_0 F9_1 F9_6 F9_11
  clear u9
  obtain ⟨u11, a10, r11, c11, ip11, e10⟩ := run1 (add_r32_m32_effect_step 0x101cf7 1 (.base 6 (.d8 0x2c)) (by decide) (by decide) (by decide))
    r10 c10 (program_text_slice c10 0x1cf7 3 (by decide +kernel)) ⟨ip10, memReadable_at (memReadable_grow hp.state G10) 0x2c 4 (by decide) (by rw [addr6 F10_6]; rfl)⟩
    (q := 0x101cfa) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e10 : (addR32M32Effect 0x101cf7 3 1 (.base 6 (.d8 0x2c)) u10).Holds u10 u11 := e10
  have G11 := G10.step e10.agrees
  have A11 := acc_reg A10 e10.agrees (by simp [CS, callChanges])
  have U11 := U10.step e10.agrees (by simp [Component.isMem])
  have FK11 := FK10.step e10.agrees (by simp [Component.isMem])
  have SP11 : stackPtr u11 = frameStart s + BitVec.ofNat 64 0 := (e10.agrees.read (r := 4) (n := 64) (by simp)).trans SP10
  have F11_1 : (Operand.reg 1 : Operand 64).read u11 = (v10 (words s)).setWidth 64 := by
    refine (e10.writes : (Operand.reg 1 : Operand 64).read u11 = _).trans ?_
    simp only [addR32M32Effect, r32_eq, addr6 F10_6, load_word U10 hp.stateFrame (.d8 0x2c) 0x2c (by decide) (by decide), F10_1, v10, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F11_0 := (e10.agrees.read (r := 0) (n := 64) (by simp)).trans F10_0
  have F11_6 := (e10.agrees.read (r := 6) (n := 64) (by simp)).trans F10_6
  have F11_11 := (e10.agrees.read (r := 11) (n := 64) (by simp)).trans F10_11
  have AD11 := AD10.trans a10
  clear a10 e10 AD10 r10 c10 ip10 G10 A10 SP10 U10 FK10 F10_0 F10_1 F10_6 F10_11
  clear u10
  obtain ⟨u12, a11, r12, c12, ip12, e11⟩ := run1 (and_r32_imm32_rex_effect_step 0x101cfa 0x41 0xe3 0x3ffffff (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r11 c11 (program_text_slice c11 0x1cfa 7 (by decide +kernel)) ip11
    (q := 0x101d01) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e11 : (andR32Imm32Effect 0x101cfa 7 11 0x3ffffff u11).Holds u11 u12 := e11
  have G12 := G11.step e11.agrees
  have A12 := acc_reg A11 e11.agrees (by simp [CS, callChanges])
  have U12 := U11.step e11.agrees (by simp [Component.isMem])
  have FK12 := FK11.step e11.agrees (by simp [Component.isMem])
  have SP12 : stackPtr u12 = frameStart s + BitVec.ofNat 64 0 := (e11.agrees.read (r := 4) (n := 64) (by simp)).trans SP11
  have F12_11 : (Operand.reg 11 : Operand 64).read u12 = (v11 (words s)).setWidth 64 := by
    refine (e11.writes : (Operand.reg 11 : Operand 64).read u12 = _).trans ?_
    simp only [andR32Imm32Effect, r32_eq, F11_11, v11, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F12_0 := (e11.agrees.read (r := 0) (n := 64) (by simp)).trans F11_0
  have F12_1 := (e11.agrees.read (r := 1) (n := 64) (by simp)).trans F11_1
  have F12_6 := (e11.agrees.read (r := 6) (n := 64) (by simp)).trans F11_6
  have AD12 := AD11.trans a11
  clear a11 e11 AD11 r11 c11 ip11 G11 A11 SP11 U11 FK11 F11_0 F11_1 F11_6 F11_11
  clear u11
  obtain ⟨u13, a12, r13, c13, ip13, e12⟩ := run1 (mov_r32_r32_effect_step 0x101d01 0xca (by decide))
    r12 c12 (program_text_slice c12 0x1d01 2 (by decide +kernel)) ip12
    (q := 0x101d03) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e12 : (movR32R32Effect 0x101d01 2 2 1 u12).Holds u12 u13 := e12
  have G13 := G12.step e12.agrees
  have A13 := acc_reg A12 e12.agrees (by simp [CS, callChanges])
  have U13 := U12.step e12.agrees (by simp [Component.isMem])
  have FK13 := FK12.step e12.agrees (by simp [Component.isMem])
  have SP13 : stackPtr u13 = frameStart s + BitVec.ofNat 64 0 := (e12.agrees.read (r := 4) (n := 64) (by simp)).trans SP12
  have F13_2 : (Operand.reg 2 : Operand 64).read u13 = (v10 (words s)).setWidth 64 := by
    refine (e12.writes : (Operand.reg 2 : Operand 64).read u13 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F12_1, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F13_0 := (e12.agrees.read (r := 0) (n := 64) (by simp)).trans F12_0
  have F13_1 := (e12.agrees.read (r := 1) (n := 64) (by simp)).trans F12_1
  have F13_6 := (e12.agrees.read (r := 6) (n := 64) (by simp)).trans F12_6
  have F13_11 := (e12.agrees.read (r := 11) (n := 64) (by simp)).trans F12_11
  have AD13 := AD12.trans a12
  clear a12 e12 AD12 r12 c12 ip12 G12 A12 SP12 U12 FK12 F12_0 F12_1 F12_6 F12_11
  clear u12
  obtain ⟨u14, a13, r14, c14, ip14, e13⟩ := run1 (shr_r32_imm8_effect_step 0x101d03 0xea 0x1a (by decide) (by decide))
    r13 c13 (program_text_slice c13 0x1d03 3 (by decide +kernel)) ip13
    (q := 0x101d06) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e13 : (shrR32Effect 0x101d03 3 2 26 u13).Holds u13 u14 := e13
  have G14 := G13.step e13.agrees
  have A14 := acc_reg A13 e13.agrees (by simp [CS, callChanges])
  have U14 := U13.step e13.agrees (by simp [Component.isMem])
  have FK14 := FK13.step e13.agrees (by simp [Component.isMem])
  have SP14 : stackPtr u14 = frameStart s + BitVec.ofNat 64 0 := (e13.agrees.read (r := 4) (n := 64) (by simp)).trans SP13
  have F14_2 : (Operand.reg 2 : Operand 64).read u14 = (v13 (words s)).setWidth 64 := by
    refine (e13.writes : (Operand.reg 2 : Operand 64).read u14 = _).trans ?_
    simp only [shrR32Effect, r32_eq, F13_2, v13, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F14_0 := (e13.agrees.read (r := 0) (n := 64) (by simp)).trans F13_0
  have F14_1 := (e13.agrees.read (r := 1) (n := 64) (by simp)).trans F13_1
  have F14_6 := (e13.agrees.read (r := 6) (n := 64) (by simp)).trans F13_6
  have F14_11 := (e13.agrees.read (r := 11) (n := 64) (by simp)).trans F13_11
  have AD14 := AD13.trans a13
  clear a13 e13 AD13 r13 c13 ip13 G13 A13 SP13 U13 FK13 F13_0 F13_1 F13_2 F13_6 F13_11
  clear u13
  obtain ⟨u15, a14, r15, c15, ip15, e14⟩ := run1 (and_r32_imm32_effect_step 0x101d06 0xe1 0x3ffffff (by decide) (by decide))
    r14 c14 (program_text_slice c14 0x1d06 6 (by decide +kernel)) ip14
    (q := 0x101d0c) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e14 : (andR32Imm32Effect 0x101d06 6 1 0x3ffffff u14).Holds u14 u15 := e14
  have G15 := G14.step e14.agrees
  have A15 := acc_reg A14 e14.agrees (by simp [CS, callChanges])
  have U15 := U14.step e14.agrees (by simp [Component.isMem])
  have FK15 := FK14.step e14.agrees (by simp [Component.isMem])
  have SP15 : stackPtr u15 = frameStart s + BitVec.ofNat 64 0 := (e14.agrees.read (r := 4) (n := 64) (by simp)).trans SP14
  have F15_1 : (Operand.reg 1 : Operand 64).read u15 = (v14 (words s)).setWidth 64 := by
    refine (e14.writes : (Operand.reg 1 : Operand 64).read u15 = _).trans ?_
    simp only [andR32Imm32Effect, r32_eq, F14_1, v14, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F15_0 := (e14.agrees.read (r := 0) (n := 64) (by simp)).trans F14_0
  have F15_2 := (e14.agrees.read (r := 2) (n := 64) (by simp)).trans F14_2
  have F15_6 := (e14.agrees.read (r := 6) (n := 64) (by simp)).trans F14_6
  have F15_11 := (e14.agrees.read (r := 11) (n := 64) (by simp)).trans F14_11
  have AD15 := AD14.trans a14
  clear a14 e14 AD14 r14 c14 ip14 G14 A14 SP14 U14 FK14 F14_0 F14_1 F14_2 F14_6 F14_11
  clear u14
  obtain ⟨u16, a15, r16, c16, ip16, e15⟩ := run1 (add_r32_m32_effect_step 0x101d0c 2 (.base 6 (.d8 0x30)) (by decide) (by decide) (by decide))
    r15 c15 (program_text_slice c15 0x1d0c 3 (by decide +kernel)) ⟨ip15, memReadable_at (memReadable_grow hp.state G15) 0x30 4 (by decide) (by rw [addr6 F15_6]; rfl)⟩
    (q := 0x101d0f) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e15 : (addR32M32Effect 0x101d0c 3 2 (.base 6 (.d8 0x30)) u15).Holds u15 u16 := e15
  have G16 := G15.step e15.agrees
  have A16 := acc_reg A15 e15.agrees (by simp [CS, callChanges])
  have U16 := U15.step e15.agrees (by simp [Component.isMem])
  have FK16 := FK15.step e15.agrees (by simp [Component.isMem])
  have SP16 : stackPtr u16 = frameStart s + BitVec.ofNat 64 0 := (e15.agrees.read (r := 4) (n := 64) (by simp)).trans SP15
  have F16_2 : (Operand.reg 2 : Operand 64).read u16 = (v15 (words s)).setWidth 64 := by
    refine (e15.writes : (Operand.reg 2 : Operand 64).read u16 = _).trans ?_
    simp only [addR32M32Effect, r32_eq, addr6 F15_6, load_word U15 hp.stateFrame (.d8 0x30) 0x30 (by decide) (by decide), F15_2, v15, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F16_0 := (e15.agrees.read (r := 0) (n := 64) (by simp)).trans F15_0
  have F16_1 := (e15.agrees.read (r := 1) (n := 64) (by simp)).trans F15_1
  have F16_6 := (e15.agrees.read (r := 6) (n := 64) (by simp)).trans F15_6
  have F16_11 := (e15.agrees.read (r := 11) (n := 64) (by simp)).trans F15_11
  have AD16 := AD15.trans a15
  clear a15 e15 AD15 r15 c15 ip15 G15 A15 SP15 U15 FK15 F15_0 F15_1 F15_2 F15_6 F15_11
  clear u15
  obtain ⟨u17, a16, r17, c17, ip17, e16⟩ := run1 (mov_r32_r32_rex_effect_step 0x101d0f 0x41 0xd0 (by unfold RexNoWPrefix; decide) (by decide))
    r16 c16 (program_text_slice c16 0x1d0f 3 (by decide +kernel)) ip16
    (q := 0x101d12) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e16 : (movR32R32Effect 0x101d0f 3 8 2 u16).Holds u16 u17 := e16
  have G17 := G16.step e16.agrees
  have A17 := acc_reg A16 e16.agrees (by simp [CS, callChanges])
  have U17 := U16.step e16.agrees (by simp [Component.isMem])
  have FK17 := FK16.step e16.agrees (by simp [Component.isMem])
  have SP17 : stackPtr u17 = frameStart s + BitVec.ofNat 64 0 := (e16.agrees.read (r := 4) (n := 64) (by simp)).trans SP16
  have F17_8 : (Operand.reg 8 : Operand 64).read u17 = (v15 (words s)).setWidth 64 := by
    refine (e16.writes : (Operand.reg 8 : Operand 64).read u17 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F16_2, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F17_0 := (e16.agrees.read (r := 0) (n := 64) (by simp)).trans F16_0
  have F17_1 := (e16.agrees.read (r := 1) (n := 64) (by simp)).trans F16_1
  have F17_2 := (e16.agrees.read (r := 2) (n := 64) (by simp)).trans F16_2
  have F17_6 := (e16.agrees.read (r := 6) (n := 64) (by simp)).trans F16_6
  have F17_11 := (e16.agrees.read (r := 11) (n := 64) (by simp)).trans F16_11
  have AD17 := AD16.trans a16
  clear a16 e16 AD16 r16 c16 ip16 G16 A16 SP16 U16 FK16 F16_0 F16_1 F16_2 F16_6 F16_11
  clear u16
  obtain ⟨u18, a17, r18, c18, ip18, e17⟩ := run1 (shr_r32_imm8_rex_effect_step 0x101d12 0x41 0xe8 0x1a (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r17 c17 (program_text_slice c17 0x1d12 4 (by decide +kernel)) ip17
    (q := 0x101d16) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e17 : (shrR32Effect 0x101d12 4 8 26 u17).Holds u17 u18 := e17
  have G18 := G17.step e17.agrees
  have A18 := acc_reg A17 e17.agrees (by simp [CS, callChanges])
  have U18 := U17.step e17.agrees (by simp [Component.isMem])
  have FK18 := FK17.step e17.agrees (by simp [Component.isMem])
  have SP18 : stackPtr u18 = frameStart s + BitVec.ofNat 64 0 := (e17.agrees.read (r := 4) (n := 64) (by simp)).trans SP17
  have F18_8 : (Operand.reg 8 : Operand 64).read u18 = (v17 (words s)).setWidth 64 := by
    refine (e17.writes : (Operand.reg 8 : Operand 64).read u18 = _).trans ?_
    simp only [shrR32Effect, r32_eq, F17_8, v17, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F18_0 := (e17.agrees.read (r := 0) (n := 64) (by simp)).trans F17_0
  have F18_1 := (e17.agrees.read (r := 1) (n := 64) (by simp)).trans F17_1
  have F18_2 := (e17.agrees.read (r := 2) (n := 64) (by simp)).trans F17_2
  have F18_6 := (e17.agrees.read (r := 6) (n := 64) (by simp)).trans F17_6
  have F18_11 := (e17.agrees.read (r := 11) (n := 64) (by simp)).trans F17_11
  have AD18 := AD17.trans a17
  clear a17 e17 AD17 r17 c17 ip17 G17 A17 SP17 U17 FK17 F17_0 F17_1 F17_2 F17_6 F17_8 F17_11
  clear u17
  obtain ⟨u19, a18, r19, c19, ip19, e18⟩ := run1 (and_r32_imm32_effect_step 0x101d16 0xe2 0x3ffffff (by decide) (by decide))
    r18 c18 (program_text_slice c18 0x1d16 6 (by decide +kernel)) ip18
    (q := 0x101d1c) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e18 : (andR32Imm32Effect 0x101d16 6 2 0x3ffffff u18).Holds u18 u19 := e18
  have G19 := G18.step e18.agrees
  have A19 := acc_reg A18 e18.agrees (by simp [CS, callChanges])
  have U19 := U18.step e18.agrees (by simp [Component.isMem])
  have FK19 := FK18.step e18.agrees (by simp [Component.isMem])
  have SP19 : stackPtr u19 = frameStart s + BitVec.ofNat 64 0 := (e18.agrees.read (r := 4) (n := 64) (by simp)).trans SP18
  have F19_2 : (Operand.reg 2 : Operand 64).read u19 = (v18 (words s)).setWidth 64 := by
    refine (e18.writes : (Operand.reg 2 : Operand 64).read u19 = _).trans ?_
    simp only [andR32Imm32Effect, r32_eq, F18_2, v18, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F19_0 := (e18.agrees.read (r := 0) (n := 64) (by simp)).trans F18_0
  have F19_1 := (e18.agrees.read (r := 1) (n := 64) (by simp)).trans F18_1
  have F19_6 := (e18.agrees.read (r := 6) (n := 64) (by simp)).trans F18_6
  have F19_8 := (e18.agrees.read (r := 8) (n := 64) (by simp)).trans F18_8
  have F19_11 := (e18.agrees.read (r := 11) (n := 64) (by simp)).trans F18_11
  have AD19 := AD18.trans a18
  clear a18 e18 AD18 r18 c18 ip18 G18 A18 SP18 U18 FK18 F18_0 F18_1 F18_2 F18_6 F18_8 F18_11
  clear u18
  obtain ⟨u20, a19, r20, c20, ip20, e19⟩ := run1 (add_r32_m32_rex_effect_step 0x101d1c 0x44 (by unfold RexNoWPrefix; decide) 0 (.base 6 (.d8 0x34)) (by decide) (by decide) (by decide))
    r19 c19 (program_text_slice c19 0x1d1c 4 (by decide +kernel)) ⟨ip19, memReadable_at (memReadable_grow hp.state G19) 0x34 4 (by decide) (by rw [addr6 F19_6]; rfl)⟩
    (q := 0x101d20) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e19 : (addR32M32Effect 0x101d1c 4 8 (.base 6 (.d8 0x34)) u19).Holds u19 u20 := e19
  have G20 := G19.step e19.agrees
  have A20 := acc_reg A19 e19.agrees (by simp [CS, callChanges])
  have U20 := U19.step e19.agrees (by simp [Component.isMem])
  have FK20 := FK19.step e19.agrees (by simp [Component.isMem])
  have SP20 : stackPtr u20 = frameStart s + BitVec.ofNat 64 0 := (e19.agrees.read (r := 4) (n := 64) (by simp)).trans SP19
  have F20_8 : (Operand.reg 8 : Operand 64).read u20 = (v19 (words s)).setWidth 64 := by
    refine (e19.writes : (Operand.reg 8 : Operand 64).read u20 = _).trans ?_
    simp only [addR32M32Effect, r32_eq, addr6 F19_6, load_word U19 hp.stateFrame (.d8 0x34) 0x34 (by decide) (by decide), F19_8, v19, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F20_0 := (e19.agrees.read (r := 0) (n := 64) (by simp)).trans F19_0
  have F20_1 := (e19.agrees.read (r := 1) (n := 64) (by simp)).trans F19_1
  have F20_2 := (e19.agrees.read (r := 2) (n := 64) (by simp)).trans F19_2
  have F20_6 := (e19.agrees.read (r := 6) (n := 64) (by simp)).trans F19_6
  have F20_11 := (e19.agrees.read (r := 11) (n := 64) (by simp)).trans F19_11
  have AD20 := AD19.trans a19
  clear a19 e19 AD19 r19 c19 ip19 G19 A19 SP19 U19 FK19 F19_0 F19_1 F19_2 F19_6 F19_8 F19_11
  clear u19
  obtain ⟨u21, a20, r21, c21, ip21, e20⟩ := run1 (mov_r32_r32_rex_effect_step 0x101d20 0x45 0xc1 (by unfold RexNoWPrefix; decide) (by decide))
    r20 c20 (program_text_slice c20 0x1d20 3 (by decide +kernel)) ip20
    (q := 0x101d23) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e20 : (movR32R32Effect 0x101d20 3 9 8 u20).Holds u20 u21 := e20
  have G21 := G20.step e20.agrees
  have A21 := acc_reg A20 e20.agrees (by simp [CS, callChanges])
  have U21 := U20.step e20.agrees (by simp [Component.isMem])
  have FK21 := FK20.step e20.agrees (by simp [Component.isMem])
  have SP21 : stackPtr u21 = frameStart s + BitVec.ofNat 64 0 := (e20.agrees.read (r := 4) (n := 64) (by simp)).trans SP20
  have F21_9 : (Operand.reg 9 : Operand 64).read u21 = (v19 (words s)).setWidth 64 := by
    refine (e20.writes : (Operand.reg 9 : Operand 64).read u21 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F20_8, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F21_0 := (e20.agrees.read (r := 0) (n := 64) (by simp)).trans F20_0
  have F21_1 := (e20.agrees.read (r := 1) (n := 64) (by simp)).trans F20_1
  have F21_2 := (e20.agrees.read (r := 2) (n := 64) (by simp)).trans F20_2
  have F21_6 := (e20.agrees.read (r := 6) (n := 64) (by simp)).trans F20_6
  have F21_8 := (e20.agrees.read (r := 8) (n := 64) (by simp)).trans F20_8
  have F21_11 := (e20.agrees.read (r := 11) (n := 64) (by simp)).trans F20_11
  have AD21 := AD20.trans a20
  clear a20 e20 AD20 r20 c20 ip20 G20 A20 SP20 U20 FK20 F20_0 F20_1 F20_2 F20_6 F20_8 F20_11
  clear u20
  obtain ⟨u22, a21, r22, c22, ip22, e21⟩ := run1 (shr_r32_imm8_rex_effect_step 0x101d23 0x41 0xe9 0x1a (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r21 c21 (program_text_slice c21 0x1d23 4 (by decide +kernel)) ip21
    (q := 0x101d27) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e21 : (shrR32Effect 0x101d23 4 9 26 u21).Holds u21 u22 := e21
  have G22 := G21.step e21.agrees
  have A22 := acc_reg A21 e21.agrees (by simp [CS, callChanges])
  have U22 := U21.step e21.agrees (by simp [Component.isMem])
  have FK22 := FK21.step e21.agrees (by simp [Component.isMem])
  have SP22 : stackPtr u22 = frameStart s + BitVec.ofNat 64 0 := (e21.agrees.read (r := 4) (n := 64) (by simp)).trans SP21
  have F22_9 : (Operand.reg 9 : Operand 64).read u22 = (v21 (words s)).setWidth 64 := by
    refine (e21.writes : (Operand.reg 9 : Operand 64).read u22 = _).trans ?_
    simp only [shrR32Effect, r32_eq, F21_9, v21, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F22_0 := (e21.agrees.read (r := 0) (n := 64) (by simp)).trans F21_0
  have F22_1 := (e21.agrees.read (r := 1) (n := 64) (by simp)).trans F21_1
  have F22_2 := (e21.agrees.read (r := 2) (n := 64) (by simp)).trans F21_2
  have F22_6 := (e21.agrees.read (r := 6) (n := 64) (by simp)).trans F21_6
  have F22_8 := (e21.agrees.read (r := 8) (n := 64) (by simp)).trans F21_8
  have F22_11 := (e21.agrees.read (r := 11) (n := 64) (by simp)).trans F21_11
  have AD22 := AD21.trans a21
  clear a21 e21 AD21 r21 c21 ip21 G21 A21 SP21 U21 FK21 F21_0 F21_1 F21_2 F21_6 F21_8 F21_9 F21_11
  clear u21
  obtain ⟨u23, a22, r23, c23, ip23, e22⟩ := run1 (mov_r32_r32_rex_effect_step 0x101d27 0x44 0xc7 (by unfold RexNoWPrefix; decide) (by decide))
    r22 c22 (program_text_slice c22 0x1d27 3 (by decide +kernel)) ip22
    (q := 0x101d2a) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e22 : (movR32R32Effect 0x101d27 3 7 8 u22).Holds u22 u23 := e22
  have G23 := G22.step e22.agrees
  have A23 := acc_reg A22 e22.agrees (by simp [CS, callChanges])
  have U23 := U22.step e22.agrees (by simp [Component.isMem])
  have FK23 := FK22.step e22.agrees (by simp [Component.isMem])
  have SP23 : stackPtr u23 = frameStart s + BitVec.ofNat 64 0 := (e22.agrees.read (r := 4) (n := 64) (by simp)).trans SP22
  have F23_7 : (Operand.reg 7 : Operand 64).read u23 = (v19 (words s)).setWidth 64 := by
    refine (e22.writes : (Operand.reg 7 : Operand 64).read u23 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F22_8, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F23_0 := (e22.agrees.read (r := 0) (n := 64) (by simp)).trans F22_0
  have F23_1 := (e22.agrees.read (r := 1) (n := 64) (by simp)).trans F22_1
  have F23_2 := (e22.agrees.read (r := 2) (n := 64) (by simp)).trans F22_2
  have F23_6 := (e22.agrees.read (r := 6) (n := 64) (by simp)).trans F22_6
  have F23_8 := (e22.agrees.read (r := 8) (n := 64) (by simp)).trans F22_8
  have F23_9 := (e22.agrees.read (r := 9) (n := 64) (by simp)).trans F22_9
  have F23_11 := (e22.agrees.read (r := 11) (n := 64) (by simp)).trans F22_11
  have AD23 := AD22.trans a22
  clear a22 e22 AD22 r22 c22 ip22 G22 A22 SP22 U22 FK22 F22_0 F22_1 F22_2 F22_6 F22_8 F22_9 F22_11
  clear u22
  obtain ⟨u24, a23, r24, c24, ip24, e23⟩ := run1 (and_r32_imm32_effect_step 0x101d2a 0xe7 0x3ffffff (by decide) (by decide))
    r23 c23 (program_text_slice c23 0x1d2a 6 (by decide +kernel)) ip23
    (q := 0x101d30) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e23 : (andR32Imm32Effect 0x101d2a 6 7 0x3ffffff u23).Holds u23 u24 := e23
  have G24 := G23.step e23.agrees
  have A24 := acc_reg A23 e23.agrees (by simp [CS, callChanges])
  have U24 := U23.step e23.agrees (by simp [Component.isMem])
  have FK24 := FK23.step e23.agrees (by simp [Component.isMem])
  have SP24 : stackPtr u24 = frameStart s + BitVec.ofNat 64 0 := (e23.agrees.read (r := 4) (n := 64) (by simp)).trans SP23
  have F24_7 : (Operand.reg 7 : Operand 64).read u24 = (v23 (words s)).setWidth 64 := by
    refine (e23.writes : (Operand.reg 7 : Operand 64).read u24 = _).trans ?_
    simp only [andR32Imm32Effect, r32_eq, F23_7, v23, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F24_0 := (e23.agrees.read (r := 0) (n := 64) (by simp)).trans F23_0
  have F24_1 := (e23.agrees.read (r := 1) (n := 64) (by simp)).trans F23_1
  have F24_2 := (e23.agrees.read (r := 2) (n := 64) (by simp)).trans F23_2
  have F24_6 := (e23.agrees.read (r := 6) (n := 64) (by simp)).trans F23_6
  have F24_8 := (e23.agrees.read (r := 8) (n := 64) (by simp)).trans F23_8
  have F24_9 := (e23.agrees.read (r := 9) (n := 64) (by simp)).trans F23_9
  have F24_11 := (e23.agrees.read (r := 11) (n := 64) (by simp)).trans F23_11
  have AD24 := AD23.trans a23
  clear a23 e23 AD23 r23 c23 ip23 G23 A23 SP23 U23 FK23 F23_0 F23_1 F23_2 F23_6 F23_7 F23_8 F23_9 F23_11
  clear u23
  obtain ⟨u25, a24, r25, c25, ip25, e24⟩ := run1 (lea_r32_rex_effect_step 0x101d30 0x47 (by unfold RexNoWPrefix; decide) 2 (.sib 9 (some 9) 2 .none) (by decide) (by decide) (by decide))
    r24 c24 (program_text_slice c24 0x1d30 4 (by decide +kernel)) ip24
    (q := 0x101d34) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e24 : (leaR32Effect 0x101d30 4 10 (.sib 9 (some 9) 2 .none) u24).Holds u24 u25 := e24
  have G25 := G24.step e24.agrees
  have A25 := acc_reg A24 e24.agrees (by simp [CS, callChanges])
  have U25 := U24.step e24.agrees (by simp [Component.isMem])
  have FK25 := FK24.step e24.agrees (by simp [Component.isMem])
  have SP25 : stackPtr u25 = frameStart s + BitVec.ofNat 64 0 := (e24.agrees.read (r := 4) (n := 64) (by simp)).trans SP24
  have F25_10 : (Operand.reg 10 : Operand 64).read u25 = (v24 (words s)).setWidth 64 := by
    refine (e24.writes : (Operand.reg 10 : Operand 64).read u25 = _).trans ?_
    simp only [leaR32Effect, leaSpec, AddrMode.addr, AddrMode.reg64, Disp.value, sw5_7, sw5_9, sw5_10, sw5_12, F24_9, v24]
    congr 1; apply BitVec.eq_of_toNat_eq; simp; try omega
  have F25_0 := (e24.agrees.read (r := 0) (n := 64) (by simp)).trans F24_0
  have F25_1 := (e24.agrees.read (r := 1) (n := 64) (by simp)).trans F24_1
  have F25_2 := (e24.agrees.read (r := 2) (n := 64) (by simp)).trans F24_2
  have F25_6 := (e24.agrees.read (r := 6) (n := 64) (by simp)).trans F24_6
  have F25_7 := (e24.agrees.read (r := 7) (n := 64) (by simp)).trans F24_7
  have F25_8 := (e24.agrees.read (r := 8) (n := 64) (by simp)).trans F24_8
  have F25_11 := (e24.agrees.read (r := 11) (n := 64) (by simp)).trans F24_11
  have AD25 := AD24.trans a24
  clear a24 e24 AD24 r24 c24 ip24 G24 A24 SP24 U24 FK24 F24_0 F24_1 F24_2 F24_6 F24_7 F24_8 F24_9 F24_11
  clear u24
  obtain ⟨u26, a25, r26, c26, ip26, e25⟩ := run1 (add_r32_m32_rex_effect_step 0x101d34 0x44 (by unfold RexNoWPrefix; decide) 2 (.base 6 (.d8 0x24)) (by decide) (by decide) (by decide))
    r25 c25 (program_text_slice c25 0x1d34 4 (by decide +kernel)) ⟨ip25, memReadable_at (memReadable_grow hp.state G25) 0x24 4 (by decide) (by rw [addr6 F25_6]; rfl)⟩
    (q := 0x101d38) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e25 : (addR32M32Effect 0x101d34 4 10 (.base 6 (.d8 0x24)) u25).Holds u25 u26 := e25
  have G26 := G25.step e25.agrees
  have A26 := acc_reg A25 e25.agrees (by simp [CS, callChanges])
  have U26 := U25.step e25.agrees (by simp [Component.isMem])
  have FK26 := FK25.step e25.agrees (by simp [Component.isMem])
  have SP26 : stackPtr u26 = frameStart s + BitVec.ofNat 64 0 := (e25.agrees.read (r := 4) (n := 64) (by simp)).trans SP25
  have F26_10 : (Operand.reg 10 : Operand 64).read u26 = (v25 (words s)).setWidth 64 := by
    refine (e25.writes : (Operand.reg 10 : Operand 64).read u26 = _).trans ?_
    simp only [addR32M32Effect, r32_eq, addr6 F25_6, load_word U25 hp.stateFrame (.d8 0x24) 0x24 (by decide) (by decide), F25_10, v25, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F26_0 := (e25.agrees.read (r := 0) (n := 64) (by simp)).trans F25_0
  have F26_1 := (e25.agrees.read (r := 1) (n := 64) (by simp)).trans F25_1
  have F26_2 := (e25.agrees.read (r := 2) (n := 64) (by simp)).trans F25_2
  have F26_6 := (e25.agrees.read (r := 6) (n := 64) (by simp)).trans F25_6
  have F26_7 := (e25.agrees.read (r := 7) (n := 64) (by simp)).trans F25_7
  have F26_8 := (e25.agrees.read (r := 8) (n := 64) (by simp)).trans F25_8
  have F26_11 := (e25.agrees.read (r := 11) (n := 64) (by simp)).trans F25_11
  have AD26 := AD25.trans a25
  clear a25 e25 AD25 r25 c25 ip25 G25 A25 SP25 U25 FK25 F25_0 F25_1 F25_2 F25_6 F25_7 F25_8 F25_10 F25_11
  clear u25
  obtain ⟨u27, a26, r27, c27, ip27, e26⟩ := run1 (mov_r32_r32_rex_effect_step 0x101d38 0x45 0xd1 (by unfold RexNoWPrefix; decide) (by decide))
    r26 c26 (program_text_slice c26 0x1d38 3 (by decide +kernel)) ip26
    (q := 0x101d3b) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e26 : (movR32R32Effect 0x101d38 3 9 10 u26).Holds u26 u27 := e26
  have G27 := G26.step e26.agrees
  have A27 := acc_reg A26 e26.agrees (by simp [CS, callChanges])
  have U27 := U26.step e26.agrees (by simp [Component.isMem])
  have FK27 := FK26.step e26.agrees (by simp [Component.isMem])
  have SP27 : stackPtr u27 = frameStart s + BitVec.ofNat 64 0 := (e26.agrees.read (r := 4) (n := 64) (by simp)).trans SP26
  have F27_9 : (Operand.reg 9 : Operand 64).read u27 = (v25 (words s)).setWidth 64 := by
    refine (e26.writes : (Operand.reg 9 : Operand 64).read u27 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F26_10, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F27_0 := (e26.agrees.read (r := 0) (n := 64) (by simp)).trans F26_0
  have F27_1 := (e26.agrees.read (r := 1) (n := 64) (by simp)).trans F26_1
  have F27_2 := (e26.agrees.read (r := 2) (n := 64) (by simp)).trans F26_2
  have F27_6 := (e26.agrees.read (r := 6) (n := 64) (by simp)).trans F26_6
  have F27_7 := (e26.agrees.read (r := 7) (n := 64) (by simp)).trans F26_7
  have F27_8 := (e26.agrees.read (r := 8) (n := 64) (by simp)).trans F26_8
  have F27_10 := (e26.agrees.read (r := 10) (n := 64) (by simp)).trans F26_10
  have F27_11 := (e26.agrees.read (r := 11) (n := 64) (by simp)).trans F26_11
  have AD27 := AD26.trans a26
  clear a26 e26 AD26 r26 c26 ip26 G26 A26 SP26 U26 FK26 F26_0 F26_1 F26_2 F26_6 F26_7 F26_8 F26_10 F26_11
  clear u26
  obtain ⟨u28, a27, r28, c28, ip28, e27⟩ := run1 (shr_r32_imm8_rex_effect_step 0x101d3b 0x41 0xe9 0x1a (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r27 c27 (program_text_slice c27 0x1d3b 4 (by decide +kernel)) ip27
    (q := 0x101d3f) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e27 : (shrR32Effect 0x101d3b 4 9 26 u27).Holds u27 u28 := e27
  have G28 := G27.step e27.agrees
  have A28 := acc_reg A27 e27.agrees (by simp [CS, callChanges])
  have U28 := U27.step e27.agrees (by simp [Component.isMem])
  have FK28 := FK27.step e27.agrees (by simp [Component.isMem])
  have SP28 : stackPtr u28 = frameStart s + BitVec.ofNat 64 0 := (e27.agrees.read (r := 4) (n := 64) (by simp)).trans SP27
  have F28_9 : (Operand.reg 9 : Operand 64).read u28 = (v27 (words s)).setWidth 64 := by
    refine (e27.writes : (Operand.reg 9 : Operand 64).read u28 = _).trans ?_
    simp only [shrR32Effect, r32_eq, F27_9, v27, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F28_0 := (e27.agrees.read (r := 0) (n := 64) (by simp)).trans F27_0
  have F28_1 := (e27.agrees.read (r := 1) (n := 64) (by simp)).trans F27_1
  have F28_2 := (e27.agrees.read (r := 2) (n := 64) (by simp)).trans F27_2
  have F28_6 := (e27.agrees.read (r := 6) (n := 64) (by simp)).trans F27_6
  have F28_7 := (e27.agrees.read (r := 7) (n := 64) (by simp)).trans F27_7
  have F28_8 := (e27.agrees.read (r := 8) (n := 64) (by simp)).trans F27_8
  have F28_10 := (e27.agrees.read (r := 10) (n := 64) (by simp)).trans F27_10
  have F28_11 := (e27.agrees.read (r := 11) (n := 64) (by simp)).trans F27_11
  have AD28 := AD27.trans a27
  clear a27 e27 AD27 r27 c27 ip27 G27 A27 SP27 U27 FK27 F27_0 F27_1 F27_2 F27_6 F27_7 F27_8 F27_9 F27_10 F27_11
  clear u27
  obtain ⟨u29, a28, r29, c29, ip29, e28⟩ := run1 (add_r32_r32_rex_effect_step 0x101d3f 0x45 0xd9 (by unfold RexNoWPrefix; decide) (by decide))
    r28 c28 (program_text_slice c28 0x1d3f 3 (by decide +kernel)) ip28
    (q := 0x101d42) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e28 : (addR32R32Effect 0x101d3f 3 9 11 u28).Holds u28 u29 := e28
  have G29 := G28.step e28.agrees
  have A29 := acc_reg A28 e28.agrees (by simp [CS, callChanges])
  have U29 := U28.step e28.agrees (by simp [Component.isMem])
  have FK29 := FK28.step e28.agrees (by simp [Component.isMem])
  have SP29 : stackPtr u29 = frameStart s + BitVec.ofNat 64 0 := (e28.agrees.read (r := 4) (n := 64) (by simp)).trans SP28
  have F29_9 : (Operand.reg 9 : Operand 64).read u29 = (v28 (words s)).setWidth 64 := by
    refine (e28.writes : (Operand.reg 9 : Operand 64).read u29 = _).trans ?_
    simp only [addR32R32Effect, r32_eq, F28_9, F28_11, v28, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F29_0 := (e28.agrees.read (r := 0) (n := 64) (by simp)).trans F28_0
  have F29_1 := (e28.agrees.read (r := 1) (n := 64) (by simp)).trans F28_1
  have F29_2 := (e28.agrees.read (r := 2) (n := 64) (by simp)).trans F28_2
  have F29_6 := (e28.agrees.read (r := 6) (n := 64) (by simp)).trans F28_6
  have F29_7 := (e28.agrees.read (r := 7) (n := 64) (by simp)).trans F28_7
  have F29_8 := (e28.agrees.read (r := 8) (n := 64) (by simp)).trans F28_8
  have F29_10 := (e28.agrees.read (r := 10) (n := 64) (by simp)).trans F28_10
  have AD29 := AD28.trans a28
  clear a28 e28 AD28 r28 c28 ip28 G28 A28 SP28 U28 FK28 F28_0 F28_1 F28_2 F28_6 F28_7 F28_8 F28_9 F28_10 F28_11
  clear u28
  obtain ⟨u30, a29, r30, c30, ip30, e29⟩ := run1 (and_r32_imm32_rex_effect_step 0x101d42 0x41 0xe2 0x3ffffff (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r29 c29 (program_text_slice c29 0x1d42 7 (by decide +kernel)) ip29
    (q := 0x101d49) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e29 : (andR32Imm32Effect 0x101d42 7 10 0x3ffffff u29).Holds u29 u30 := e29
  have G30 := G29.step e29.agrees
  have A30 := acc_reg A29 e29.agrees (by simp [CS, callChanges])
  have U30 := U29.step e29.agrees (by simp [Component.isMem])
  have FK30 := FK29.step e29.agrees (by simp [Component.isMem])
  have SP30 : stackPtr u30 = frameStart s + BitVec.ofNat 64 0 := (e29.agrees.read (r := 4) (n := 64) (by simp)).trans SP29
  have F30_10 : (Operand.reg 10 : Operand 64).read u30 = (v29 (words s)).setWidth 64 := by
    refine (e29.writes : (Operand.reg 10 : Operand 64).read u30 = _).trans ?_
    simp only [andR32Imm32Effect, r32_eq, F29_10, v29, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F30_0 := (e29.agrees.read (r := 0) (n := 64) (by simp)).trans F29_0
  have F30_1 := (e29.agrees.read (r := 1) (n := 64) (by simp)).trans F29_1
  have F30_2 := (e29.agrees.read (r := 2) (n := 64) (by simp)).trans F29_2
  have F30_6 := (e29.agrees.read (r := 6) (n := 64) (by simp)).trans F29_6
  have F30_7 := (e29.agrees.read (r := 7) (n := 64) (by simp)).trans F29_7
  have F30_8 := (e29.agrees.read (r := 8) (n := 64) (by simp)).trans F29_8
  have F30_9 := (e29.agrees.read (r := 9) (n := 64) (by simp)).trans F29_9
  have AD30 := AD29.trans a29
  clear a29 e29 AD29 r29 c29 ip29 G29 A29 SP29 U29 FK29 F29_0 F29_1 F29_2 F29_6 F29_7 F29_8 F29_9 F29_10
  clear u29
  obtain ⟨u31, a30, r31, c31, ip31, e30⟩ := run1 (lea_r32_rex_effect_step 0x101d49 0x41 (by unfold RexNoWPrefix; decide) 5 (.base 10 (.d8 5)) (by decide) (by decide) (by decide))
    r30 c30 (program_text_slice c30 0x1d49 4 (by decide +kernel)) ip30
    (q := 0x101d4d) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e30 : (leaR32Effect 0x101d49 4 5 (.base 10 (.d8 5)) u30).Holds u30 u31 := e30
  have G31 := G30.step e30.agrees
  have A31 := acc_reg A30 e30.agrees (by simp [CS, callChanges])
  have U31 := U30.step e30.agrees (by simp [Component.isMem])
  have FK31 := FK30.step e30.agrees (by simp [Component.isMem])
  have SP31 : stackPtr u31 = frameStart s + BitVec.ofNat 64 0 := (e30.agrees.read (r := 4) (n := 64) (by simp)).trans SP30
  have F31_5 : (Operand.reg 5 : Operand 64).read u31 = (v30 (words s)).setWidth 64 := by
    refine (e30.writes : (Operand.reg 5 : Operand 64).read u31 = _).trans ?_
    simp only [leaR32Effect, leaSpec, AddrMode.addr, AddrMode.reg64, Disp.value, sw5_7, sw5_9, sw5_10, sw5_12, F30_10, v30]
    congr 1; apply BitVec.eq_of_toNat_eq; simp; try omega
  have F31_0 := (e30.agrees.read (r := 0) (n := 64) (by simp)).trans F30_0
  have F31_1 := (e30.agrees.read (r := 1) (n := 64) (by simp)).trans F30_1
  have F31_2 := (e30.agrees.read (r := 2) (n := 64) (by simp)).trans F30_2
  have F31_6 := (e30.agrees.read (r := 6) (n := 64) (by simp)).trans F30_6
  have F31_7 := (e30.agrees.read (r := 7) (n := 64) (by simp)).trans F30_7
  have F31_8 := (e30.agrees.read (r := 8) (n := 64) (by simp)).trans F30_8
  have F31_9 := (e30.agrees.read (r := 9) (n := 64) (by simp)).trans F30_9
  have F31_10 := (e30.agrees.read (r := 10) (n := 64) (by simp)).trans F30_10
  have AD31 := AD30.trans a30
  clear a30 e30 AD30 r30 c30 ip30 G30 A30 SP30 U30 FK30 F30_0 F30_1 F30_2 F30_6 F30_7 F30_8 F30_9 F30_10
  clear u30
  obtain ⟨u32, a31, r32, c32, ip32, e31⟩ := run1 (mov_r32_r32_rex_effect_step 0x101d4d 0x41 0xeb (by unfold RexNoWPrefix; decide) (by decide))
    r31 c31 (program_text_slice c31 0x1d4d 3 (by decide +kernel)) ip31
    (q := 0x101d50) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e31 : (movR32R32Effect 0x101d4d 3 11 5 u31).Holds u31 u32 := e31
  have G32 := G31.step e31.agrees
  have A32 := acc_reg A31 e31.agrees (by simp [CS, callChanges])
  have U32 := U31.step e31.agrees (by simp [Component.isMem])
  have FK32 := FK31.step e31.agrees (by simp [Component.isMem])
  have SP32 : stackPtr u32 = frameStart s + BitVec.ofNat 64 0 := (e31.agrees.read (r := 4) (n := 64) (by simp)).trans SP31
  have F32_11 : (Operand.reg 11 : Operand 64).read u32 = (v30 (words s)).setWidth 64 := by
    refine (e31.writes : (Operand.reg 11 : Operand 64).read u32 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F31_5, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F32_0 := (e31.agrees.read (r := 0) (n := 64) (by simp)).trans F31_0
  have F32_1 := (e31.agrees.read (r := 1) (n := 64) (by simp)).trans F31_1
  have F32_2 := (e31.agrees.read (r := 2) (n := 64) (by simp)).trans F31_2
  have F32_5 := (e31.agrees.read (r := 5) (n := 64) (by simp)).trans F31_5
  have F32_6 := (e31.agrees.read (r := 6) (n := 64) (by simp)).trans F31_6
  have F32_7 := (e31.agrees.read (r := 7) (n := 64) (by simp)).trans F31_7
  have F32_8 := (e31.agrees.read (r := 8) (n := 64) (by simp)).trans F31_8
  have F32_9 := (e31.agrees.read (r := 9) (n := 64) (by simp)).trans F31_9
  have F32_10 := (e31.agrees.read (r := 10) (n := 64) (by simp)).trans F31_10
  have AD32 := AD31.trans a31
  clear a31 e31 AD31 r31 c31 ip31 G31 A31 SP31 U31 FK31 F31_0 F31_1 F31_2 F31_5 F31_6 F31_7 F31_8 F31_9 F31_10
  clear u31
  obtain ⟨u33, a32, r33, c33, ip33, e32⟩ := run1 (shr_r32_imm8_rex_effect_step 0x101d50 0x41 0xeb 0x1a (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r32 c32 (program_text_slice c32 0x1d50 4 (by decide +kernel)) ip32
    (q := 0x101d54) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e32 : (shrR32Effect 0x101d50 4 11 26 u32).Holds u32 u33 := e32
  have G33 := G32.step e32.agrees
  have A33 := acc_reg A32 e32.agrees (by simp [CS, callChanges])
  have U33 := U32.step e32.agrees (by simp [Component.isMem])
  have FK33 := FK32.step e32.agrees (by simp [Component.isMem])
  have SP33 : stackPtr u33 = frameStart s + BitVec.ofNat 64 0 := (e32.agrees.read (r := 4) (n := 64) (by simp)).trans SP32
  have F33_11 : (Operand.reg 11 : Operand 64).read u33 = (v32 (words s)).setWidth 64 := by
    refine (e32.writes : (Operand.reg 11 : Operand 64).read u33 = _).trans ?_
    simp only [shrR32Effect, r32_eq, F32_11, v32, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F33_0 := (e32.agrees.read (r := 0) (n := 64) (by simp)).trans F32_0
  have F33_1 := (e32.agrees.read (r := 1) (n := 64) (by simp)).trans F32_1
  have F33_2 := (e32.agrees.read (r := 2) (n := 64) (by simp)).trans F32_2
  have F33_5 := (e32.agrees.read (r := 5) (n := 64) (by simp)).trans F32_5
  have F33_6 := (e32.agrees.read (r := 6) (n := 64) (by simp)).trans F32_6
  have F33_7 := (e32.agrees.read (r := 7) (n := 64) (by simp)).trans F32_7
  have F33_8 := (e32.agrees.read (r := 8) (n := 64) (by simp)).trans F32_8
  have F33_9 := (e32.agrees.read (r := 9) (n := 64) (by simp)).trans F32_9
  have F33_10 := (e32.agrees.read (r := 10) (n := 64) (by simp)).trans F32_10
  have AD33 := AD32.trans a32
  clear a32 e32 AD32 r32 c32 ip32 G32 A32 SP32 U32 FK32 F32_0 F32_1 F32_2 F32_5 F32_6 F32_7 F32_8 F32_9 F32_10 F32_11
  clear u32
  obtain ⟨u34, a33, r34, c34, ip34, e33⟩ := run1 (add_r32_r32_rex_effect_step 0x101d54 0x45 0xcb (by unfold RexNoWPrefix; decide) (by decide))
    r33 c33 (program_text_slice c33 0x1d54 3 (by decide +kernel)) ip33
    (q := 0x101d57) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e33 : (addR32R32Effect 0x101d54 3 11 9 u33).Holds u33 u34 := e33
  have G34 := G33.step e33.agrees
  have A34 := acc_reg A33 e33.agrees (by simp [CS, callChanges])
  have U34 := U33.step e33.agrees (by simp [Component.isMem])
  have FK34 := FK33.step e33.agrees (by simp [Component.isMem])
  have SP34 : stackPtr u34 = frameStart s + BitVec.ofNat 64 0 := (e33.agrees.read (r := 4) (n := 64) (by simp)).trans SP33
  have F34_11 : (Operand.reg 11 : Operand 64).read u34 = (v33 (words s)).setWidth 64 := by
    refine (e33.writes : (Operand.reg 11 : Operand 64).read u34 = _).trans ?_
    simp only [addR32R32Effect, r32_eq, F33_11, F33_9, v33, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F34_0 := (e33.agrees.read (r := 0) (n := 64) (by simp)).trans F33_0
  have F34_1 := (e33.agrees.read (r := 1) (n := 64) (by simp)).trans F33_1
  have F34_2 := (e33.agrees.read (r := 2) (n := 64) (by simp)).trans F33_2
  have F34_5 := (e33.agrees.read (r := 5) (n := 64) (by simp)).trans F33_5
  have F34_6 := (e33.agrees.read (r := 6) (n := 64) (by simp)).trans F33_6
  have F34_7 := (e33.agrees.read (r := 7) (n := 64) (by simp)).trans F33_7
  have F34_8 := (e33.agrees.read (r := 8) (n := 64) (by simp)).trans F33_8
  have F34_9 := (e33.agrees.read (r := 9) (n := 64) (by simp)).trans F33_9
  have F34_10 := (e33.agrees.read (r := 10) (n := 64) (by simp)).trans F33_10
  have AD34 := AD33.trans a33
  clear a33 e33 AD33 r33 c33 ip33 G33 A33 SP33 U33 FK33 F33_0 F33_1 F33_2 F33_5 F33_6 F33_7 F33_8 F33_9 F33_10 F33_11
  clear u33
  obtain ⟨u35, a34, r35, c35, ip35, e34⟩ := run1 (mov_r32_r32_rex_effect_step 0x101d57 0x44 0xdb (by unfold RexNoWPrefix; decide) (by decide))
    r34 c34 (program_text_slice c34 0x1d57 3 (by decide +kernel)) ip34
    (q := 0x101d5a) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e34 : (movR32R32Effect 0x101d57 3 3 11 u34).Holds u34 u35 := e34
  have G35 := G34.step e34.agrees
  have A35 := acc_reg A34 e34.agrees (by simp [CS, callChanges])
  have U35 := U34.step e34.agrees (by simp [Component.isMem])
  have FK35 := FK34.step e34.agrees (by simp [Component.isMem])
  have SP35 : stackPtr u35 = frameStart s + BitVec.ofNat 64 0 := (e34.agrees.read (r := 4) (n := 64) (by simp)).trans SP34
  have F35_3 : (Operand.reg 3 : Operand 64).read u35 = (v33 (words s)).setWidth 64 := by
    refine (e34.writes : (Operand.reg 3 : Operand 64).read u35 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F34_11, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F35_0 := (e34.agrees.read (r := 0) (n := 64) (by simp)).trans F34_0
  have F35_1 := (e34.agrees.read (r := 1) (n := 64) (by simp)).trans F34_1
  have F35_2 := (e34.agrees.read (r := 2) (n := 64) (by simp)).trans F34_2
  have F35_5 := (e34.agrees.read (r := 5) (n := 64) (by simp)).trans F34_5
  have F35_6 := (e34.agrees.read (r := 6) (n := 64) (by simp)).trans F34_6
  have F35_7 := (e34.agrees.read (r := 7) (n := 64) (by simp)).trans F34_7
  have F35_8 := (e34.agrees.read (r := 8) (n := 64) (by simp)).trans F34_8
  have F35_9 := (e34.agrees.read (r := 9) (n := 64) (by simp)).trans F34_9
  have F35_10 := (e34.agrees.read (r := 10) (n := 64) (by simp)).trans F34_10
  have F35_11 := (e34.agrees.read (r := 11) (n := 64) (by simp)).trans F34_11
  have AD35 := AD34.trans a34
  clear a34 e34 AD34 r34 c34 ip34 G34 A34 SP34 U34 FK34 F34_0 F34_1 F34_2 F34_5 F34_6 F34_7 F34_8 F34_9 F34_10 F34_11
  clear u34
  obtain ⟨u36, a35, r36, c36, ip36, e35⟩ := run1 (shr_r32_imm8_effect_step 0x101d5a 0xeb 0x1a (by decide) (by decide))
    r35 c35 (program_text_slice c35 0x1d5a 3 (by decide +kernel)) ip35
    (q := 0x101d5d) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e35 : (shrR32Effect 0x101d5a 3 3 26 u35).Holds u35 u36 := e35
  have G36 := G35.step e35.agrees
  have A36 := acc_reg A35 e35.agrees (by simp [CS, callChanges])
  have U36 := U35.step e35.agrees (by simp [Component.isMem])
  have FK36 := FK35.step e35.agrees (by simp [Component.isMem])
  have SP36 : stackPtr u36 = frameStart s + BitVec.ofNat 64 0 := (e35.agrees.read (r := 4) (n := 64) (by simp)).trans SP35
  have F36_3 : (Operand.reg 3 : Operand 64).read u36 = (v35 (words s)).setWidth 64 := by
    refine (e35.writes : (Operand.reg 3 : Operand 64).read u36 = _).trans ?_
    simp only [shrR32Effect, r32_eq, F35_3, v35, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F36_0 := (e35.agrees.read (r := 0) (n := 64) (by simp)).trans F35_0
  have F36_1 := (e35.agrees.read (r := 1) (n := 64) (by simp)).trans F35_1
  have F36_2 := (e35.agrees.read (r := 2) (n := 64) (by simp)).trans F35_2
  have F36_5 := (e35.agrees.read (r := 5) (n := 64) (by simp)).trans F35_5
  have F36_6 := (e35.agrees.read (r := 6) (n := 64) (by simp)).trans F35_6
  have F36_7 := (e35.agrees.read (r := 7) (n := 64) (by simp)).trans F35_7
  have F36_8 := (e35.agrees.read (r := 8) (n := 64) (by simp)).trans F35_8
  have F36_9 := (e35.agrees.read (r := 9) (n := 64) (by simp)).trans F35_9
  have F36_10 := (e35.agrees.read (r := 10) (n := 64) (by simp)).trans F35_10
  have F36_11 := (e35.agrees.read (r := 11) (n := 64) (by simp)).trans F35_11
  have AD36 := AD35.trans a35
  clear a35 e35 AD35 r35 c35 ip35 G35 A35 SP35 U35 FK35 F35_0 F35_1 F35_2 F35_3 F35_5 F35_6 F35_7 F35_8 F35_9 F35_10 F35_11
  clear u35
  obtain ⟨u37, a36, r37, c37, ip37, e36⟩ := run1 (add_r32_r32_effect_step 0x101d5d 0xcb (by decide))
    r36 c36 (program_text_slice c36 0x1d5d 2 (by decide +kernel)) ip36
    (q := 0x101d5f) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e36 : (addR32R32Effect 0x101d5d 2 3 1 u36).Holds u36 u37 := e36
  have G37 := G36.step e36.agrees
  have A37 := acc_reg A36 e36.agrees (by simp [CS, callChanges])
  have U37 := U36.step e36.agrees (by simp [Component.isMem])
  have FK37 := FK36.step e36.agrees (by simp [Component.isMem])
  have SP37 : stackPtr u37 = frameStart s + BitVec.ofNat 64 0 := (e36.agrees.read (r := 4) (n := 64) (by simp)).trans SP36
  have F37_3 : (Operand.reg 3 : Operand 64).read u37 = (v36 (words s)).setWidth 64 := by
    refine (e36.writes : (Operand.reg 3 : Operand 64).read u37 = _).trans ?_
    simp only [addR32R32Effect, r32_eq, F36_3, F36_1, v36, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F37_0 := (e36.agrees.read (r := 0) (n := 64) (by simp)).trans F36_0
  have F37_1 := (e36.agrees.read (r := 1) (n := 64) (by simp)).trans F36_1
  have F37_2 := (e36.agrees.read (r := 2) (n := 64) (by simp)).trans F36_2
  have F37_5 := (e36.agrees.read (r := 5) (n := 64) (by simp)).trans F36_5
  have F37_6 := (e36.agrees.read (r := 6) (n := 64) (by simp)).trans F36_6
  have F37_7 := (e36.agrees.read (r := 7) (n := 64) (by simp)).trans F36_7
  have F37_8 := (e36.agrees.read (r := 8) (n := 64) (by simp)).trans F36_8
  have F37_9 := (e36.agrees.read (r := 9) (n := 64) (by simp)).trans F36_9
  have F37_10 := (e36.agrees.read (r := 10) (n := 64) (by simp)).trans F36_10
  have F37_11 := (e36.agrees.read (r := 11) (n := 64) (by simp)).trans F36_11
  have AD37 := AD36.trans a36
  clear a36 e36 AD36 r36 c36 ip36 G36 A36 SP36 U36 FK36 F36_0 F36_1 F36_2 F36_3 F36_5 F36_6 F36_7 F36_8 F36_9 F36_10 F36_11
  clear u36
  obtain ⟨u38, a37, r38, c38, ip38, e37⟩ := run1 (mov_r32_r32_rex_effect_step 0x101d5f 0x41 0xdf (by unfold RexNoWPrefix; decide) (by decide))
    r37 c37 (program_text_slice c37 0x1d5f 3 (by decide +kernel)) ip37
    (q := 0x101d62) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e37 : (movR32R32Effect 0x101d5f 3 15 3 u37).Holds u37 u38 := e37
  have G38 := G37.step e37.agrees
  have A38 := acc_reg A37 e37.agrees (by simp [CS, callChanges])
  have U38 := U37.step e37.agrees (by simp [Component.isMem])
  have FK38 := FK37.step e37.agrees (by simp [Component.isMem])
  have SP38 : stackPtr u38 = frameStart s + BitVec.ofNat 64 0 := (e37.agrees.read (r := 4) (n := 64) (by simp)).trans SP37
  have F38_15 : (Operand.reg 15 : Operand 64).read u38 = (v36 (words s)).setWidth 64 := by
    refine (e37.writes : (Operand.reg 15 : Operand 64).read u38 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F37_3, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F38_0 := (e37.agrees.read (r := 0) (n := 64) (by simp)).trans F37_0
  have F38_1 := (e37.agrees.read (r := 1) (n := 64) (by simp)).trans F37_1
  have F38_2 := (e37.agrees.read (r := 2) (n := 64) (by simp)).trans F37_2
  have F38_3 := (e37.agrees.read (r := 3) (n := 64) (by simp)).trans F37_3
  have F38_5 := (e37.agrees.read (r := 5) (n := 64) (by simp)).trans F37_5
  have F38_6 := (e37.agrees.read (r := 6) (n := 64) (by simp)).trans F37_6
  have F38_7 := (e37.agrees.read (r := 7) (n := 64) (by simp)).trans F37_7
  have F38_8 := (e37.agrees.read (r := 8) (n := 64) (by simp)).trans F37_8
  have F38_9 := (e37.agrees.read (r := 9) (n := 64) (by simp)).trans F37_9
  have F38_10 := (e37.agrees.read (r := 10) (n := 64) (by simp)).trans F37_10
  have F38_11 := (e37.agrees.read (r := 11) (n := 64) (by simp)).trans F37_11
  have AD38 := AD37.trans a37
  clear a37 e37 AD37 r37 c37 ip37 G37 A37 SP37 U37 FK37 F37_0 F37_1 F37_2 F37_3 F37_5 F37_6 F37_7 F37_8 F37_9 F37_10 F37_11
  clear u37
  obtain ⟨u39, a38, r39, c39, ip39, e38⟩ := run1 (shr_r32_imm8_rex_effect_step 0x101d62 0x41 0xef 0x1a (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r38 c38 (program_text_slice c38 0x1d62 4 (by decide +kernel)) ip38
    (q := 0x101d66) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e38 : (shrR32Effect 0x101d62 4 15 26 u38).Holds u38 u39 := e38
  have G39 := G38.step e38.agrees
  have A39 := acc_reg A38 e38.agrees (by simp [CS, callChanges])
  have U39 := U38.step e38.agrees (by simp [Component.isMem])
  have FK39 := FK38.step e38.agrees (by simp [Component.isMem])
  have SP39 : stackPtr u39 = frameStart s + BitVec.ofNat 64 0 := (e38.agrees.read (r := 4) (n := 64) (by simp)).trans SP38
  have F39_15 : (Operand.reg 15 : Operand 64).read u39 = (v38 (words s)).setWidth 64 := by
    refine (e38.writes : (Operand.reg 15 : Operand 64).read u39 = _).trans ?_
    simp only [shrR32Effect, r32_eq, F38_15, v38, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F39_0 := (e38.agrees.read (r := 0) (n := 64) (by simp)).trans F38_0
  have F39_1 := (e38.agrees.read (r := 1) (n := 64) (by simp)).trans F38_1
  have F39_2 := (e38.agrees.read (r := 2) (n := 64) (by simp)).trans F38_2
  have F39_3 := (e38.agrees.read (r := 3) (n := 64) (by simp)).trans F38_3
  have F39_5 := (e38.agrees.read (r := 5) (n := 64) (by simp)).trans F38_5
  have F39_6 := (e38.agrees.read (r := 6) (n := 64) (by simp)).trans F38_6
  have F39_7 := (e38.agrees.read (r := 7) (n := 64) (by simp)).trans F38_7
  have F39_8 := (e38.agrees.read (r := 8) (n := 64) (by simp)).trans F38_8
  have F39_9 := (e38.agrees.read (r := 9) (n := 64) (by simp)).trans F38_9
  have F39_10 := (e38.agrees.read (r := 10) (n := 64) (by simp)).trans F38_10
  have F39_11 := (e38.agrees.read (r := 11) (n := 64) (by simp)).trans F38_11
  have AD39 := AD38.trans a38
  clear a38 e38 AD38 r38 c38 ip38 G38 A38 SP38 U38 FK38 F38_0 F38_1 F38_2 F38_3 F38_5 F38_6 F38_7 F38_8 F38_9 F38_10 F38_11 F38_15
  clear u38
  obtain ⟨u40, a39, r40, c40, ip40, e39⟩ := run1 (add_r32_r32_rex_effect_step 0x101d66 0x41 0xd7 (by unfold RexNoWPrefix; decide) (by decide))
    r39 c39 (program_text_slice c39 0x1d66 3 (by decide +kernel)) ip39
    (q := 0x101d69) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e39 : (addR32R32Effect 0x101d66 3 15 2 u39).Holds u39 u40 := e39
  have G40 := G39.step e39.agrees
  have A40 := acc_reg A39 e39.agrees (by simp [CS, callChanges])
  have U40 := U39.step e39.agrees (by simp [Component.isMem])
  have FK40 := FK39.step e39.agrees (by simp [Component.isMem])
  have SP40 : stackPtr u40 = frameStart s + BitVec.ofNat 64 0 := (e39.agrees.read (r := 4) (n := 64) (by simp)).trans SP39
  have F40_15 : (Operand.reg 15 : Operand 64).read u40 = (v39 (words s)).setWidth 64 := by
    refine (e39.writes : (Operand.reg 15 : Operand 64).read u40 = _).trans ?_
    simp only [addR32R32Effect, r32_eq, F39_15, F39_2, v39, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F40_0 := (e39.agrees.read (r := 0) (n := 64) (by simp)).trans F39_0
  have F40_1 := (e39.agrees.read (r := 1) (n := 64) (by simp)).trans F39_1
  have F40_2 := (e39.agrees.read (r := 2) (n := 64) (by simp)).trans F39_2
  have F40_3 := (e39.agrees.read (r := 3) (n := 64) (by simp)).trans F39_3
  have F40_5 := (e39.agrees.read (r := 5) (n := 64) (by simp)).trans F39_5
  have F40_6 := (e39.agrees.read (r := 6) (n := 64) (by simp)).trans F39_6
  have F40_7 := (e39.agrees.read (r := 7) (n := 64) (by simp)).trans F39_7
  have F40_8 := (e39.agrees.read (r := 8) (n := 64) (by simp)).trans F39_8
  have F40_9 := (e39.agrees.read (r := 9) (n := 64) (by simp)).trans F39_9
  have F40_10 := (e39.agrees.read (r := 10) (n := 64) (by simp)).trans F39_10
  have F40_11 := (e39.agrees.read (r := 11) (n := 64) (by simp)).trans F39_11
  have AD40 := AD39.trans a39
  clear a39 e39 AD39 r39 c39 ip39 G39 A39 SP39 U39 FK39 F39_0 F39_1 F39_2 F39_3 F39_5 F39_6 F39_7 F39_8 F39_9 F39_10 F39_11 F39_15
  clear u39
  obtain ⟨u41, a40, r41, c41, ip41, e40⟩ := run1 (mov_r32_r32_rex_effect_step 0x101d69 0x45 0xfc (by unfold RexNoWPrefix; decide) (by decide))
    r40 c40 (program_text_slice c40 0x1d69 3 (by decide +kernel)) ip40
    (q := 0x101d6c) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e40 : (movR32R32Effect 0x101d69 3 12 15 u40).Holds u40 u41 := e40
  have G41 := G40.step e40.agrees
  have A41 := acc_reg A40 e40.agrees (by simp [CS, callChanges])
  have U41 := U40.step e40.agrees (by simp [Component.isMem])
  have FK41 := FK40.step e40.agrees (by simp [Component.isMem])
  have SP41 : stackPtr u41 = frameStart s + BitVec.ofNat 64 0 := (e40.agrees.read (r := 4) (n := 64) (by simp)).trans SP40
  have F41_12 : (Operand.reg 12 : Operand 64).read u41 = (v39 (words s)).setWidth 64 := by
    refine (e40.writes : (Operand.reg 12 : Operand 64).read u41 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F40_15, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F41_0 := (e40.agrees.read (r := 0) (n := 64) (by simp)).trans F40_0
  have F41_1 := (e40.agrees.read (r := 1) (n := 64) (by simp)).trans F40_1
  have F41_2 := (e40.agrees.read (r := 2) (n := 64) (by simp)).trans F40_2
  have F41_3 := (e40.agrees.read (r := 3) (n := 64) (by simp)).trans F40_3
  have F41_5 := (e40.agrees.read (r := 5) (n := 64) (by simp)).trans F40_5
  have F41_6 := (e40.agrees.read (r := 6) (n := 64) (by simp)).trans F40_6
  have F41_7 := (e40.agrees.read (r := 7) (n := 64) (by simp)).trans F40_7
  have F41_8 := (e40.agrees.read (r := 8) (n := 64) (by simp)).trans F40_8
  have F41_9 := (e40.agrees.read (r := 9) (n := 64) (by simp)).trans F40_9
  have F41_10 := (e40.agrees.read (r := 10) (n := 64) (by simp)).trans F40_10
  have F41_11 := (e40.agrees.read (r := 11) (n := 64) (by simp)).trans F40_11
  have F41_15 := (e40.agrees.read (r := 15) (n := 64) (by simp)).trans F40_15
  have AD41 := AD40.trans a40
  clear a40 e40 AD40 r40 c40 ip40 G40 A40 SP40 U40 FK40 F40_0 F40_1 F40_2 F40_3 F40_5 F40_6 F40_7 F40_8 F40_9 F40_10 F40_11 F40_15
  clear u40
  obtain ⟨u42, a41, r42, c42, ip42, e41⟩ := run1 (shr_r32_imm8_rex_effect_step 0x101d6c 0x41 0xec 0x1a (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r41 c41 (program_text_slice c41 0x1d6c 4 (by decide +kernel)) ip41
    (q := 0x101d70) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e41 : (shrR32Effect 0x101d6c 4 12 26 u41).Holds u41 u42 := e41
  have G42 := G41.step e41.agrees
  have A42 := acc_reg A41 e41.agrees (by simp [CS, callChanges])
  have U42 := U41.step e41.agrees (by simp [Component.isMem])
  have FK42 := FK41.step e41.agrees (by simp [Component.isMem])
  have SP42 : stackPtr u42 = frameStart s + BitVec.ofNat 64 0 := (e41.agrees.read (r := 4) (n := 64) (by simp)).trans SP41
  have F42_12 : (Operand.reg 12 : Operand 64).read u42 = (v41 (words s)).setWidth 64 := by
    refine (e41.writes : (Operand.reg 12 : Operand 64).read u42 = _).trans ?_
    simp only [shrR32Effect, r32_eq, F41_12, v41, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F42_0 := (e41.agrees.read (r := 0) (n := 64) (by simp)).trans F41_0
  have F42_1 := (e41.agrees.read (r := 1) (n := 64) (by simp)).trans F41_1
  have F42_2 := (e41.agrees.read (r := 2) (n := 64) (by simp)).trans F41_2
  have F42_3 := (e41.agrees.read (r := 3) (n := 64) (by simp)).trans F41_3
  have F42_5 := (e41.agrees.read (r := 5) (n := 64) (by simp)).trans F41_5
  have F42_6 := (e41.agrees.read (r := 6) (n := 64) (by simp)).trans F41_6
  have F42_7 := (e41.agrees.read (r := 7) (n := 64) (by simp)).trans F41_7
  have F42_8 := (e41.agrees.read (r := 8) (n := 64) (by simp)).trans F41_8
  have F42_9 := (e41.agrees.read (r := 9) (n := 64) (by simp)).trans F41_9
  have F42_10 := (e41.agrees.read (r := 10) (n := 64) (by simp)).trans F41_10
  have F42_11 := (e41.agrees.read (r := 11) (n := 64) (by simp)).trans F41_11
  have F42_15 := (e41.agrees.read (r := 15) (n := 64) (by simp)).trans F41_15
  have AD42 := AD41.trans a41
  clear a41 e41 AD41 r41 c41 ip41 G41 A41 SP41 U41 FK41 F41_0 F41_1 F41_2 F41_3 F41_5 F41_6 F41_7 F41_8 F41_9 F41_10 F41_11 F41_12 F41_15
  clear u41
  obtain ⟨u43, a42, r43, c43, ip43, e42⟩ := run1 (lea_r32_rex_effect_step 0x101d70 0x45 (by unfold RexNoWPrefix; decide) 6 (.sib 12 (some 7) 0 .none) (by decide) (by decide) (by decide))
    r42 c42 (program_text_slice c42 0x1d70 4 (by decide +kernel)) ip42
    (q := 0x101d74) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e42 : (leaR32Effect 0x101d70 4 14 (.sib 12 (some 7) 0 .none) u42).Holds u42 u43 := e42
  have G43 := G42.step e42.agrees
  have A43 := acc_reg A42 e42.agrees (by simp [CS, callChanges])
  have U43 := U42.step e42.agrees (by simp [Component.isMem])
  have FK43 := FK42.step e42.agrees (by simp [Component.isMem])
  have SP43 : stackPtr u43 = frameStart s + BitVec.ofNat 64 0 := (e42.agrees.read (r := 4) (n := 64) (by simp)).trans SP42
  have F43_14 : (Operand.reg 14 : Operand 64).read u43 = (v42 (words s)).setWidth 64 := by
    refine (e42.writes : (Operand.reg 14 : Operand 64).read u43 = _).trans ?_
    simp only [leaR32Effect, leaSpec, AddrMode.addr, AddrMode.reg64, Disp.value, sw5_7, sw5_9, sw5_10, sw5_12, F42_12, F42_7, v42]
    congr 1; apply BitVec.eq_of_toNat_eq; simp; try omega
  have F43_0 := (e42.agrees.read (r := 0) (n := 64) (by simp)).trans F42_0
  have F43_1 := (e42.agrees.read (r := 1) (n := 64) (by simp)).trans F42_1
  have F43_2 := (e42.agrees.read (r := 2) (n := 64) (by simp)).trans F42_2
  have F43_3 := (e42.agrees.read (r := 3) (n := 64) (by simp)).trans F42_3
  have F43_5 := (e42.agrees.read (r := 5) (n := 64) (by simp)).trans F42_5
  have F43_6 := (e42.agrees.read (r := 6) (n := 64) (by simp)).trans F42_6
  have F43_7 := (e42.agrees.read (r := 7) (n := 64) (by simp)).trans F42_7
  have F43_8 := (e42.agrees.read (r := 8) (n := 64) (by simp)).trans F42_8
  have F43_9 := (e42.agrees.read (r := 9) (n := 64) (by simp)).trans F42_9
  have F43_10 := (e42.agrees.read (r := 10) (n := 64) (by simp)).trans F42_10
  have F43_11 := (e42.agrees.read (r := 11) (n := 64) (by simp)).trans F42_11
  have F43_12 := (e42.agrees.read (r := 12) (n := 64) (by simp)).trans F42_12
  have F43_15 := (e42.agrees.read (r := 15) (n := 64) (by simp)).trans F42_15
  have AD43 := AD42.trans a42
  clear a42 e42 AD42 r42 c42 ip42 G42 A42 SP42 U42 FK42 F42_0 F42_1 F42_2 F42_3 F42_5 F42_6 F42_7 F42_8 F42_9 F42_10 F42_11 F42_12 F42_15
  clear u42
  obtain ⟨u44, a43, r44, c44, ip44, e43⟩ := run1 (add_r32_imm32_rex_effect_step 0x101d74 0x41 0xc6 0xfc000000 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r43 c43 (program_text_slice c43 0x1d74 7 (by decide +kernel)) ip43
    (q := 0x101d7b) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e43 : (addR32Imm32Effect 0x101d74 7 14 0xfc000000 u43).Holds u43 u44 := e43
  have G44 := G43.step e43.agrees
  have A44 := acc_reg A43 e43.agrees (by simp [CS, callChanges])
  have U44 := U43.step e43.agrees (by simp [Component.isMem])
  have FK44 := FK43.step e43.agrees (by simp [Component.isMem])
  have SP44 : stackPtr u44 = frameStart s + BitVec.ofNat 64 0 := (e43.agrees.read (r := 4) (n := 64) (by simp)).trans SP43
  have F44_14 : (Operand.reg 14 : Operand 64).read u44 = (v43 (words s)).setWidth 64 := by
    refine (e43.writes : (Operand.reg 14 : Operand 64).read u44 = _).trans ?_
    simp only [addR32Imm32Effect, r32_eq, F43_14, v43, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F44_0 := (e43.agrees.read (r := 0) (n := 64) (by simp)).trans F43_0
  have F44_1 := (e43.agrees.read (r := 1) (n := 64) (by simp)).trans F43_1
  have F44_2 := (e43.agrees.read (r := 2) (n := 64) (by simp)).trans F43_2
  have F44_3 := (e43.agrees.read (r := 3) (n := 64) (by simp)).trans F43_3
  have F44_5 := (e43.agrees.read (r := 5) (n := 64) (by simp)).trans F43_5
  have F44_6 := (e43.agrees.read (r := 6) (n := 64) (by simp)).trans F43_6
  have F44_7 := (e43.agrees.read (r := 7) (n := 64) (by simp)).trans F43_7
  have F44_8 := (e43.agrees.read (r := 8) (n := 64) (by simp)).trans F43_8
  have F44_9 := (e43.agrees.read (r := 9) (n := 64) (by simp)).trans F43_9
  have F44_10 := (e43.agrees.read (r := 10) (n := 64) (by simp)).trans F43_10
  have F44_11 := (e43.agrees.read (r := 11) (n := 64) (by simp)).trans F43_11
  have F44_12 := (e43.agrees.read (r := 12) (n := 64) (by simp)).trans F43_12
  have F44_15 := (e43.agrees.read (r := 15) (n := 64) (by simp)).trans F43_15
  have AD44 := AD43.trans a43
  clear a43 e43 AD43 r43 c43 ip43 G43 A43 SP43 U43 FK43 F43_0 F43_1 F43_2 F43_3 F43_5 F43_6 F43_7 F43_8 F43_9 F43_10 F43_11 F43_12 F43_14 F43_15
  clear u43
  obtain ⟨u45, a44, r45, c45, ip45, e44⟩ := run1 (add_r32_r32_rex_effect_step 0x101d7b 0x41 0xfc (by unfold RexNoWPrefix; decide) (by decide))
    r44 c44 (program_text_slice c44 0x1d7b 3 (by decide +kernel)) ip44
    (q := 0x101d7e) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e44 : (addR32R32Effect 0x101d7b 3 12 7 u44).Holds u44 u45 := e44
  have G45 := G44.step e44.agrees
  have A45 := acc_reg A44 e44.agrees (by simp [CS, callChanges])
  have U45 := U44.step e44.agrees (by simp [Component.isMem])
  have FK45 := FK44.step e44.agrees (by simp [Component.isMem])
  have SP45 : stackPtr u45 = frameStart s + BitVec.ofNat 64 0 := (e44.agrees.read (r := 4) (n := 64) (by simp)).trans SP44
  have F45_12 : (Operand.reg 12 : Operand 64).read u45 = (v44 (words s)).setWidth 64 := by
    refine (e44.writes : (Operand.reg 12 : Operand 64).read u45 = _).trans ?_
    simp only [addR32R32Effect, r32_eq, F44_12, F44_7, v44, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F45_0 := (e44.agrees.read (r := 0) (n := 64) (by simp)).trans F44_0
  have F45_1 := (e44.agrees.read (r := 1) (n := 64) (by simp)).trans F44_1
  have F45_2 := (e44.agrees.read (r := 2) (n := 64) (by simp)).trans F44_2
  have F45_3 := (e44.agrees.read (r := 3) (n := 64) (by simp)).trans F44_3
  have F45_5 := (e44.agrees.read (r := 5) (n := 64) (by simp)).trans F44_5
  have F45_6 := (e44.agrees.read (r := 6) (n := 64) (by simp)).trans F44_6
  have F45_8 := (e44.agrees.read (r := 8) (n := 64) (by simp)).trans F44_8
  have F45_9 := (e44.agrees.read (r := 9) (n := 64) (by simp)).trans F44_9
  have F45_10 := (e44.agrees.read (r := 10) (n := 64) (by simp)).trans F44_10
  have F45_11 := (e44.agrees.read (r := 11) (n := 64) (by simp)).trans F44_11
  have F45_14 := (e44.agrees.read (r := 14) (n := 64) (by simp)).trans F44_14
  have F45_15 := (e44.agrees.read (r := 15) (n := 64) (by simp)).trans F44_15
  have AD45 := AD44.trans a44
  clear a44 e44 AD44 r44 c44 ip44 G44 A44 SP44 U44 FK44 F44_0 F44_1 F44_2 F44_3 F44_5 F44_6 F44_7 F44_8 F44_9 F44_10 F44_11 F44_12 F44_14 F44_15
  clear u44
  obtain ⟨u46, a45, r46, c46, ip46, e45⟩ := run1 (mov_r32_r32_rex_effect_step 0x101d7e 0x44 0xf7 (by unfold RexNoWPrefix; decide) (by decide))
    r45 c45 (program_text_slice c45 0x1d7e 3 (by decide +kernel)) ip45
    (q := 0x101d81) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e45 : (movR32R32Effect 0x101d7e 3 7 14 u45).Holds u45 u46 := e45
  have G46 := G45.step e45.agrees
  have A46 := acc_reg A45 e45.agrees (by simp [CS, callChanges])
  have U46 := U45.step e45.agrees (by simp [Component.isMem])
  have FK46 := FK45.step e45.agrees (by simp [Component.isMem])
  have SP46 : stackPtr u46 = frameStart s + BitVec.ofNat 64 0 := (e45.agrees.read (r := 4) (n := 64) (by simp)).trans SP45
  have F46_7 : (Operand.reg 7 : Operand 64).read u46 = (v43 (words s)).setWidth 64 := by
    refine (e45.writes : (Operand.reg 7 : Operand 64).read u46 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F45_14, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F46_0 := (e45.agrees.read (r := 0) (n := 64) (by simp)).trans F45_0
  have F46_1 := (e45.agrees.read (r := 1) (n := 64) (by simp)).trans F45_1
  have F46_2 := (e45.agrees.read (r := 2) (n := 64) (by simp)).trans F45_2
  have F46_3 := (e45.agrees.read (r := 3) (n := 64) (by simp)).trans F45_3
  have F46_5 := (e45.agrees.read (r := 5) (n := 64) (by simp)).trans F45_5
  have F46_6 := (e45.agrees.read (r := 6) (n := 64) (by simp)).trans F45_6
  have F46_8 := (e45.agrees.read (r := 8) (n := 64) (by simp)).trans F45_8
  have F46_9 := (e45.agrees.read (r := 9) (n := 64) (by simp)).trans F45_9
  have F46_10 := (e45.agrees.read (r := 10) (n := 64) (by simp)).trans F45_10
  have F46_11 := (e45.agrees.read (r := 11) (n := 64) (by simp)).trans F45_11
  have F46_12 := (e45.agrees.read (r := 12) (n := 64) (by simp)).trans F45_12
  have F46_14 := (e45.agrees.read (r := 14) (n := 64) (by simp)).trans F45_14
  have F46_15 := (e45.agrees.read (r := 15) (n := 64) (by simp)).trans F45_15
  have AD46 := AD45.trans a45
  clear a45 e45 AD45 r45 c45 ip45 G45 A45 SP45 U45 FK45 F45_0 F45_1 F45_2 F45_3 F45_5 F45_6 F45_8 F45_9 F45_10 F45_11 F45_12 F45_14 F45_15
  clear u45
  obtain ⟨u47, a46, r47, c47, ip47, e46⟩ := run1 (sar_r32_imm8_effect_step 0x101d81 0xff 0x1f (by decide) (by decide))
    r46 c46 (program_text_slice c46 0x1d81 3 (by decide +kernel)) ip46
    (q := 0x101d84) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e46 : (sarR32Effect 0x101d81 3 7 31 u46).Holds u46 u47 := e46
  have G47 := G46.step e46.agrees
  have A47 := acc_reg A46 e46.agrees (by simp [CS, callChanges])
  have U47 := U46.step e46.agrees (by simp [Component.isMem])
  have FK47 := FK46.step e46.agrees (by simp [Component.isMem])
  have SP47 : stackPtr u47 = frameStart s + BitVec.ofNat 64 0 := (e46.agrees.read (r := 4) (n := 64) (by simp)).trans SP46
  have F47_7 : (Operand.reg 7 : Operand 64).read u47 = (v46 (words s)).setWidth 64 := by
    refine (e46.writes : (Operand.reg 7 : Operand 64).read u47 = _).trans ?_
    simp only [sarR32Effect, r32_eq, F46_7, v46, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F47_0 := (e46.agrees.read (r := 0) (n := 64) (by simp)).trans F46_0
  have F47_1 := (e46.agrees.read (r := 1) (n := 64) (by simp)).trans F46_1
  have F47_2 := (e46.agrees.read (r := 2) (n := 64) (by simp)).trans F46_2
  have F47_3 := (e46.agrees.read (r := 3) (n := 64) (by simp)).trans F46_3
  have F47_5 := (e46.agrees.read (r := 5) (n := 64) (by simp)).trans F46_5
  have F47_6 := (e46.agrees.read (r := 6) (n := 64) (by simp)).trans F46_6
  have F47_8 := (e46.agrees.read (r := 8) (n := 64) (by simp)).trans F46_8
  have F47_9 := (e46.agrees.read (r := 9) (n := 64) (by simp)).trans F46_9
  have F47_10 := (e46.agrees.read (r := 10) (n := 64) (by simp)).trans F46_10
  have F47_11 := (e46.agrees.read (r := 11) (n := 64) (by simp)).trans F46_11
  have F47_12 := (e46.agrees.read (r := 12) (n := 64) (by simp)).trans F46_12
  have F47_14 := (e46.agrees.read (r := 14) (n := 64) (by simp)).trans F46_14
  have F47_15 := (e46.agrees.read (r := 15) (n := 64) (by simp)).trans F46_15
  have AD47 := AD46.trans a46
  clear a46 e46 AD46 r46 c46 ip46 G46 A46 SP46 U46 FK46 F46_0 F46_1 F46_2 F46_3 F46_5 F46_6 F46_7 F46_8 F46_9 F46_10 F46_11 F46_12 F46_14 F46_15
  clear u46
  obtain ⟨u48, a47, r48, c48, ip48, e47⟩ := run1 (shr_r32_imm8_rex_effect_step 0x101d84 0x41 0xee 0x1f (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r47 c47 (program_text_slice c47 0x1d84 4 (by decide +kernel)) ip47
    (q := 0x101d88) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e47 : (shrR32Effect 0x101d84 4 14 31 u47).Holds u47 u48 := e47
  have G48 := G47.step e47.agrees
  have A48 := acc_reg A47 e47.agrees (by simp [CS, callChanges])
  have U48 := U47.step e47.agrees (by simp [Component.isMem])
  have FK48 := FK47.step e47.agrees (by simp [Component.isMem])
  have SP48 : stackPtr u48 = frameStart s + BitVec.ofNat 64 0 := (e47.agrees.read (r := 4) (n := 64) (by simp)).trans SP47
  have F48_14 : (Operand.reg 14 : Operand 64).read u48 = (v47 (words s)).setWidth 64 := by
    refine (e47.writes : (Operand.reg 14 : Operand 64).read u48 = _).trans ?_
    simp only [shrR32Effect, r32_eq, F47_14, v47, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F48_0 := (e47.agrees.read (r := 0) (n := 64) (by simp)).trans F47_0
  have F48_1 := (e47.agrees.read (r := 1) (n := 64) (by simp)).trans F47_1
  have F48_2 := (e47.agrees.read (r := 2) (n := 64) (by simp)).trans F47_2
  have F48_3 := (e47.agrees.read (r := 3) (n := 64) (by simp)).trans F47_3
  have F48_5 := (e47.agrees.read (r := 5) (n := 64) (by simp)).trans F47_5
  have F48_6 := (e47.agrees.read (r := 6) (n := 64) (by simp)).trans F47_6
  have F48_7 := (e47.agrees.read (r := 7) (n := 64) (by simp)).trans F47_7
  have F48_8 := (e47.agrees.read (r := 8) (n := 64) (by simp)).trans F47_8
  have F48_9 := (e47.agrees.read (r := 9) (n := 64) (by simp)).trans F47_9
  have F48_10 := (e47.agrees.read (r := 10) (n := 64) (by simp)).trans F47_10
  have F48_11 := (e47.agrees.read (r := 11) (n := 64) (by simp)).trans F47_11
  have F48_12 := (e47.agrees.read (r := 12) (n := 64) (by simp)).trans F47_12
  have F48_15 := (e47.agrees.read (r := 15) (n := 64) (by simp)).trans F47_15
  have AD48 := AD47.trans a47
  clear a47 e47 AD47 r47 c47 ip47 G47 A47 SP47 U47 FK47 F47_0 F47_1 F47_2 F47_3 F47_5 F47_6 F47_7 F47_8 F47_9 F47_10 F47_11 F47_12 F47_14 F47_15
  clear u47
  obtain ⟨u49, a48, r49, c49, ip49, e48⟩ := run1 (dec_r32_rex_effect_step 0x101d88 0x41 0xce (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r48 c48 (program_text_slice c48 0x1d88 3 (by decide +kernel)) ip48
    (q := 0x101d8b) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e48 : (decR32Effect 0x101d88 3 14 u48).Holds u48 u49 := e48
  have G49 := G48.step e48.agrees
  have A49 := acc_reg A48 e48.agrees (by simp [CS, callChanges])
  have U49 := U48.step e48.agrees (by simp [Component.isMem])
  have FK49 := FK48.step e48.agrees (by simp [Component.isMem])
  have SP49 : stackPtr u49 = frameStart s + BitVec.ofNat 64 0 := (e48.agrees.read (r := 4) (n := 64) (by simp)).trans SP48
  have F49_14 : (Operand.reg 14 : Operand 64).read u49 = (v48 (words s)).setWidth 64 := by
    refine (e48.writes : (Operand.reg 14 : Operand 64).read u49 = _).trans ?_
    simp only [decR32Effect, r32_eq, F48_14, v48, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F49_0 := (e48.agrees.read (r := 0) (n := 64) (by simp)).trans F48_0
  have F49_1 := (e48.agrees.read (r := 1) (n := 64) (by simp)).trans F48_1
  have F49_2 := (e48.agrees.read (r := 2) (n := 64) (by simp)).trans F48_2
  have F49_3 := (e48.agrees.read (r := 3) (n := 64) (by simp)).trans F48_3
  have F49_5 := (e48.agrees.read (r := 5) (n := 64) (by simp)).trans F48_5
  have F49_6 := (e48.agrees.read (r := 6) (n := 64) (by simp)).trans F48_6
  have F49_7 := (e48.agrees.read (r := 7) (n := 64) (by simp)).trans F48_7
  have F49_8 := (e48.agrees.read (r := 8) (n := 64) (by simp)).trans F48_8
  have F49_9 := (e48.agrees.read (r := 9) (n := 64) (by simp)).trans F48_9
  have F49_10 := (e48.agrees.read (r := 10) (n := 64) (by simp)).trans F48_10
  have F49_11 := (e48.agrees.read (r := 11) (n := 64) (by simp)).trans F48_11
  have F49_12 := (e48.agrees.read (r := 12) (n := 64) (by simp)).trans F48_12
  have F49_15 := (e48.agrees.read (r := 15) (n := 64) (by simp)).trans F48_15
  have AD49 := AD48.trans a48
  clear a48 e48 AD48 r48 c48 ip48 G48 A48 SP48 U48 FK48 F48_0 F48_1 F48_2 F48_3 F48_5 F48_6 F48_7 F48_8 F48_9 F48_10 F48_11 F48_12 F48_14 F48_15
  clear u48
  obtain ⟨u50, a49, r50, c50, ip50, e49⟩ := run1 (mov_r32_r32_rex_effect_step 0x101d8b 0x45 0xf5 (by unfold RexNoWPrefix; decide) (by decide))
    r49 c49 (program_text_slice c49 0x1d8b 3 (by decide +kernel)) ip49
    (q := 0x101d8e) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e49 : (movR32R32Effect 0x101d8b 3 13 14 u49).Holds u49 u50 := e49
  have G50 := G49.step e49.agrees
  have A50 := acc_reg A49 e49.agrees (by simp [CS, callChanges])
  have U50 := U49.step e49.agrees (by simp [Component.isMem])
  have FK50 := FK49.step e49.agrees (by simp [Component.isMem])
  have SP50 : stackPtr u50 = frameStart s + BitVec.ofNat 64 0 := (e49.agrees.read (r := 4) (n := 64) (by simp)).trans SP49
  have F50_13 : (Operand.reg 13 : Operand 64).read u50 = (v48 (words s)).setWidth 64 := by
    refine (e49.writes : (Operand.reg 13 : Operand 64).read u50 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F49_14, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F50_0 := (e49.agrees.read (r := 0) (n := 64) (by simp)).trans F49_0
  have F50_1 := (e49.agrees.read (r := 1) (n := 64) (by simp)).trans F49_1
  have F50_2 := (e49.agrees.read (r := 2) (n := 64) (by simp)).trans F49_2
  have F50_3 := (e49.agrees.read (r := 3) (n := 64) (by simp)).trans F49_3
  have F50_5 := (e49.agrees.read (r := 5) (n := 64) (by simp)).trans F49_5
  have F50_6 := (e49.agrees.read (r := 6) (n := 64) (by simp)).trans F49_6
  have F50_7 := (e49.agrees.read (r := 7) (n := 64) (by simp)).trans F49_7
  have F50_8 := (e49.agrees.read (r := 8) (n := 64) (by simp)).trans F49_8
  have F50_9 := (e49.agrees.read (r := 9) (n := 64) (by simp)).trans F49_9
  have F50_10 := (e49.agrees.read (r := 10) (n := 64) (by simp)).trans F49_10
  have F50_11 := (e49.agrees.read (r := 11) (n := 64) (by simp)).trans F49_11
  have F50_12 := (e49.agrees.read (r := 12) (n := 64) (by simp)).trans F49_12
  have F50_14 := (e49.agrees.read (r := 14) (n := 64) (by simp)).trans F49_14
  have F50_15 := (e49.agrees.read (r := 15) (n := 64) (by simp)).trans F49_15
  have AD50 := AD49.trans a49
  clear a49 e49 AD49 r49 c49 ip49 G49 A49 SP49 U49 FK49 F49_0 F49_1 F49_2 F49_3 F49_5 F49_6 F49_7 F49_8 F49_9 F49_10 F49_11 F49_12 F49_14 F49_15
  clear u49
  obtain ⟨u51, a50, r51, c51, ip51, e50⟩ := run1 (and_r32_imm32_rex_effect_step 0x101d8e 0x41 0xe5 0x3ffffff (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r50 c50 (program_text_slice c50 0x1d8e 7 (by decide +kernel)) ip50
    (q := 0x101d95) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e50 : (andR32Imm32Effect 0x101d8e 7 13 0x3ffffff u50).Holds u50 u51 := e50
  have G51 := G50.step e50.agrees
  have A51 := acc_reg A50 e50.agrees (by simp [CS, callChanges])
  have U51 := U50.step e50.agrees (by simp [Component.isMem])
  have FK51 := FK50.step e50.agrees (by simp [Component.isMem])
  have SP51 : stackPtr u51 = frameStart s + BitVec.ofNat 64 0 := (e50.agrees.read (r := 4) (n := 64) (by simp)).trans SP50
  have F51_13 : (Operand.reg 13 : Operand 64).read u51 = (v50 (words s)).setWidth 64 := by
    refine (e50.writes : (Operand.reg 13 : Operand 64).read u51 = _).trans ?_
    simp only [andR32Imm32Effect, r32_eq, F50_13, v50, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F51_0 := (e50.agrees.read (r := 0) (n := 64) (by simp)).trans F50_0
  have F51_1 := (e50.agrees.read (r := 1) (n := 64) (by simp)).trans F50_1
  have F51_2 := (e50.agrees.read (r := 2) (n := 64) (by simp)).trans F50_2
  have F51_3 := (e50.agrees.read (r := 3) (n := 64) (by simp)).trans F50_3
  have F51_5 := (e50.agrees.read (r := 5) (n := 64) (by simp)).trans F50_5
  have F51_6 := (e50.agrees.read (r := 6) (n := 64) (by simp)).trans F50_6
  have F51_7 := (e50.agrees.read (r := 7) (n := 64) (by simp)).trans F50_7
  have F51_8 := (e50.agrees.read (r := 8) (n := 64) (by simp)).trans F50_8
  have F51_9 := (e50.agrees.read (r := 9) (n := 64) (by simp)).trans F50_9
  have F51_10 := (e50.agrees.read (r := 10) (n := 64) (by simp)).trans F50_10
  have F51_11 := (e50.agrees.read (r := 11) (n := 64) (by simp)).trans F50_11
  have F51_12 := (e50.agrees.read (r := 12) (n := 64) (by simp)).trans F50_12
  have F51_14 := (e50.agrees.read (r := 14) (n := 64) (by simp)).trans F50_14
  have F51_15 := (e50.agrees.read (r := 15) (n := 64) (by simp)).trans F50_15
  have AD51 := AD50.trans a50
  clear a50 e50 AD50 r50 c50 ip50 G50 A50 SP50 U50 FK50 F50_0 F50_1 F50_2 F50_3 F50_5 F50_6 F50_7 F50_8 F50_9 F50_10 F50_11 F50_12 F50_13 F50_14 F50_15
  clear u50
  obtain ⟨u52, a51, r52, c52, ip52, e51⟩ := run1 (and_r32_r32_rex_effect_step 0x101d95 0x44 0xed (by unfold RexNoWPrefix; decide) (by decide))
    r51 c51 (program_text_slice c51 0x1d95 3 (by decide +kernel)) ip51
    (q := 0x101d98) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e51 : (andR32R32Effect 0x101d95 3 5 13 u51).Holds u51 u52 := e51
  have G52 := G51.step e51.agrees
  have A52 := acc_reg A51 e51.agrees (by simp [CS, callChanges])
  have U52 := U51.step e51.agrees (by simp [Component.isMem])
  have FK52 := FK51.step e51.agrees (by simp [Component.isMem])
  have SP52 : stackPtr u52 = frameStart s + BitVec.ofNat 64 0 := (e51.agrees.read (r := 4) (n := 64) (by simp)).trans SP51
  have F52_5 : (Operand.reg 5 : Operand 64).read u52 = (v51 (words s)).setWidth 64 := by
    refine (e51.writes : (Operand.reg 5 : Operand 64).read u52 = _).trans ?_
    simp only [andR32R32Effect, r32_eq, F51_5, F51_13, v51, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F52_0 := (e51.agrees.read (r := 0) (n := 64) (by simp)).trans F51_0
  have F52_1 := (e51.agrees.read (r := 1) (n := 64) (by simp)).trans F51_1
  have F52_2 := (e51.agrees.read (r := 2) (n := 64) (by simp)).trans F51_2
  have F52_3 := (e51.agrees.read (r := 3) (n := 64) (by simp)).trans F51_3
  have F52_6 := (e51.agrees.read (r := 6) (n := 64) (by simp)).trans F51_6
  have F52_7 := (e51.agrees.read (r := 7) (n := 64) (by simp)).trans F51_7
  have F52_8 := (e51.agrees.read (r := 8) (n := 64) (by simp)).trans F51_8
  have F52_9 := (e51.agrees.read (r := 9) (n := 64) (by simp)).trans F51_9
  have F52_10 := (e51.agrees.read (r := 10) (n := 64) (by simp)).trans F51_10
  have F52_11 := (e51.agrees.read (r := 11) (n := 64) (by simp)).trans F51_11
  have F52_12 := (e51.agrees.read (r := 12) (n := 64) (by simp)).trans F51_12
  have F52_13 := (e51.agrees.read (r := 13) (n := 64) (by simp)).trans F51_13
  have F52_14 := (e51.agrees.read (r := 14) (n := 64) (by simp)).trans F51_14
  have F52_15 := (e51.agrees.read (r := 15) (n := 64) (by simp)).trans F51_15
  have AD52 := AD51.trans a51
  clear a51 e51 AD51 r51 c51 ip51 G51 A51 SP51 U51 FK51 F51_0 F51_1 F51_2 F51_3 F51_5 F51_6 F51_7 F51_8 F51_9 F51_10 F51_11 F51_12 F51_13 F51_14 F51_15
  clear u51
  obtain ⟨u53, a52, r53, c53, ip53, e52⟩ := run1 (and_r32_r32_rex_effect_step 0x101d98 0x45 0xeb (by unfold RexNoWPrefix; decide) (by decide))
    r52 c52 (program_text_slice c52 0x1d98 3 (by decide +kernel)) ip52
    (q := 0x101d9b) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e52 : (andR32R32Effect 0x101d98 3 11 13 u52).Holds u52 u53 := e52
  have G53 := G52.step e52.agrees
  have A53 := acc_reg A52 e52.agrees (by simp [CS, callChanges])
  have U53 := U52.step e52.agrees (by simp [Component.isMem])
  have FK53 := FK52.step e52.agrees (by simp [Component.isMem])
  have SP53 : stackPtr u53 = frameStart s + BitVec.ofNat 64 0 := (e52.agrees.read (r := 4) (n := 64) (by simp)).trans SP52
  have F53_11 : (Operand.reg 11 : Operand 64).read u53 = (v52 (words s)).setWidth 64 := by
    refine (e52.writes : (Operand.reg 11 : Operand 64).read u53 = _).trans ?_
    simp only [andR32R32Effect, r32_eq, F52_11, F52_13, v52, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F53_0 := (e52.agrees.read (r := 0) (n := 64) (by simp)).trans F52_0
  have F53_1 := (e52.agrees.read (r := 1) (n := 64) (by simp)).trans F52_1
  have F53_2 := (e52.agrees.read (r := 2) (n := 64) (by simp)).trans F52_2
  have F53_3 := (e52.agrees.read (r := 3) (n := 64) (by simp)).trans F52_3
  have F53_5 := (e52.agrees.read (r := 5) (n := 64) (by simp)).trans F52_5
  have F53_6 := (e52.agrees.read (r := 6) (n := 64) (by simp)).trans F52_6
  have F53_7 := (e52.agrees.read (r := 7) (n := 64) (by simp)).trans F52_7
  have F53_8 := (e52.agrees.read (r := 8) (n := 64) (by simp)).trans F52_8
  have F53_9 := (e52.agrees.read (r := 9) (n := 64) (by simp)).trans F52_9
  have F53_10 := (e52.agrees.read (r := 10) (n := 64) (by simp)).trans F52_10
  have F53_12 := (e52.agrees.read (r := 12) (n := 64) (by simp)).trans F52_12
  have F53_13 := (e52.agrees.read (r := 13) (n := 64) (by simp)).trans F52_13
  have F53_14 := (e52.agrees.read (r := 14) (n := 64) (by simp)).trans F52_14
  have F53_15 := (e52.agrees.read (r := 15) (n := 64) (by simp)).trans F52_15
  have AD53 := AD52.trans a52
  clear a52 e52 AD52 r52 c52 ip52 G52 A52 SP52 U52 FK52 F52_0 F52_1 F52_2 F52_3 F52_5 F52_6 F52_7 F52_8 F52_9 F52_10 F52_11 F52_12 F52_13 F52_14 F52_15
  clear u52
  obtain ⟨u54, a53, r54, c54, ip54, e53⟩ := run1 (and_r32_r32_rex_effect_step 0x101d9b 0x44 0xeb (by unfold RexNoWPrefix; decide) (by decide))
    r53 c53 (program_text_slice c53 0x1d9b 3 (by decide +kernel)) ip53
    (q := 0x101d9e) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e53 : (andR32R32Effect 0x101d9b 3 3 13 u53).Holds u53 u54 := e53
  have G54 := G53.step e53.agrees
  have A54 := acc_reg A53 e53.agrees (by simp [CS, callChanges])
  have U54 := U53.step e53.agrees (by simp [Component.isMem])
  have FK54 := FK53.step e53.agrees (by simp [Component.isMem])
  have SP54 : stackPtr u54 = frameStart s + BitVec.ofNat 64 0 := (e53.agrees.read (r := 4) (n := 64) (by simp)).trans SP53
  have F54_3 : (Operand.reg 3 : Operand 64).read u54 = (v53 (words s)).setWidth 64 := by
    refine (e53.writes : (Operand.reg 3 : Operand 64).read u54 = _).trans ?_
    simp only [andR32R32Effect, r32_eq, F53_3, F53_13, v53, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F54_0 := (e53.agrees.read (r := 0) (n := 64) (by simp)).trans F53_0
  have F54_1 := (e53.agrees.read (r := 1) (n := 64) (by simp)).trans F53_1
  have F54_2 := (e53.agrees.read (r := 2) (n := 64) (by simp)).trans F53_2
  have F54_5 := (e53.agrees.read (r := 5) (n := 64) (by simp)).trans F53_5
  have F54_6 := (e53.agrees.read (r := 6) (n := 64) (by simp)).trans F53_6
  have F54_7 := (e53.agrees.read (r := 7) (n := 64) (by simp)).trans F53_7
  have F54_8 := (e53.agrees.read (r := 8) (n := 64) (by simp)).trans F53_8
  have F54_9 := (e53.agrees.read (r := 9) (n := 64) (by simp)).trans F53_9
  have F54_10 := (e53.agrees.read (r := 10) (n := 64) (by simp)).trans F53_10
  have F54_11 := (e53.agrees.read (r := 11) (n := 64) (by simp)).trans F53_11
  have F54_12 := (e53.agrees.read (r := 12) (n := 64) (by simp)).trans F53_12
  have F54_13 := (e53.agrees.read (r := 13) (n := 64) (by simp)).trans F53_13
  have F54_14 := (e53.agrees.read (r := 14) (n := 64) (by simp)).trans F53_14
  have F54_15 := (e53.agrees.read (r := 15) (n := 64) (by simp)).trans F53_15
  have AD54 := AD53.trans a53
  clear a53 e53 AD53 r53 c53 ip53 G53 A53 SP53 U53 FK53 F53_0 F53_1 F53_2 F53_3 F53_5 F53_6 F53_7 F53_8 F53_9 F53_10 F53_11 F53_12 F53_13 F53_14 F53_15
  clear u53
  obtain ⟨u55, a54, r55, c55, ip55, e54⟩ := run1 (and_r32_r32_rex_effect_step 0x101d9e 0x45 0xfd (by unfold RexNoWPrefix; decide) (by decide))
    r54 c54 (program_text_slice c54 0x1d9e 3 (by decide +kernel)) ip54
    (q := 0x101da1) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e54 : (andR32R32Effect 0x101d9e 3 13 15 u54).Holds u54 u55 := e54
  have G55 := G54.step e54.agrees
  have A55 := acc_reg A54 e54.agrees (by simp [CS, callChanges])
  have U55 := U54.step e54.agrees (by simp [Component.isMem])
  have FK55 := FK54.step e54.agrees (by simp [Component.isMem])
  have SP55 : stackPtr u55 = frameStart s + BitVec.ofNat 64 0 := (e54.agrees.read (r := 4) (n := 64) (by simp)).trans SP54
  have F55_13 : (Operand.reg 13 : Operand 64).read u55 = (v54 (words s)).setWidth 64 := by
    refine (e54.writes : (Operand.reg 13 : Operand 64).read u55 = _).trans ?_
    simp only [andR32R32Effect, r32_eq, F54_13, F54_15, v54, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F55_0 := (e54.agrees.read (r := 0) (n := 64) (by simp)).trans F54_0
  have F55_1 := (e54.agrees.read (r := 1) (n := 64) (by simp)).trans F54_1
  have F55_2 := (e54.agrees.read (r := 2) (n := 64) (by simp)).trans F54_2
  have F55_3 := (e54.agrees.read (r := 3) (n := 64) (by simp)).trans F54_3
  have F55_5 := (e54.agrees.read (r := 5) (n := 64) (by simp)).trans F54_5
  have F55_6 := (e54.agrees.read (r := 6) (n := 64) (by simp)).trans F54_6
  have F55_7 := (e54.agrees.read (r := 7) (n := 64) (by simp)).trans F54_7
  have F55_8 := (e54.agrees.read (r := 8) (n := 64) (by simp)).trans F54_8
  have F55_9 := (e54.agrees.read (r := 9) (n := 64) (by simp)).trans F54_9
  have F55_10 := (e54.agrees.read (r := 10) (n := 64) (by simp)).trans F54_10
  have F55_11 := (e54.agrees.read (r := 11) (n := 64) (by simp)).trans F54_11
  have F55_12 := (e54.agrees.read (r := 12) (n := 64) (by simp)).trans F54_12
  have F55_14 := (e54.agrees.read (r := 14) (n := 64) (by simp)).trans F54_14
  have AD55 := AD54.trans a54
  clear a54 e54 AD54 r54 c54 ip54 G54 A54 SP54 U54 FK54 F54_0 F54_1 F54_2 F54_3 F54_5 F54_6 F54_7 F54_8 F54_9 F54_10 F54_11 F54_12 F54_13 F54_14 F54_15
  clear u54
  obtain ⟨u56, a55, r56, c56, ip56, e55⟩ := run1 (and_r32_r32_rex_effect_step 0x101da1 0x45 0xe6 (by unfold RexNoWPrefix; decide) (by decide))
    r55 c55 (program_text_slice c55 0x1da1 3 (by decide +kernel)) ip55
    (q := 0x101da4) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e55 : (andR32R32Effect 0x101da1 3 14 12 u55).Holds u55 u56 := e55
  have G56 := G55.step e55.agrees
  have A56 := acc_reg A55 e55.agrees (by simp [CS, callChanges])
  have U56 := U55.step e55.agrees (by simp [Component.isMem])
  have FK56 := FK55.step e55.agrees (by simp [Component.isMem])
  have SP56 : stackPtr u56 = frameStart s + BitVec.ofNat 64 0 := (e55.agrees.read (r := 4) (n := 64) (by simp)).trans SP55
  have F56_14 : (Operand.reg 14 : Operand 64).read u56 = (v55 (words s)).setWidth 64 := by
    refine (e55.writes : (Operand.reg 14 : Operand 64).read u56 = _).trans ?_
    simp only [andR32R32Effect, r32_eq, F55_14, F55_12, v55, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F56_0 := (e55.agrees.read (r := 0) (n := 64) (by simp)).trans F55_0
  have F56_1 := (e55.agrees.read (r := 1) (n := 64) (by simp)).trans F55_1
  have F56_2 := (e55.agrees.read (r := 2) (n := 64) (by simp)).trans F55_2
  have F56_3 := (e55.agrees.read (r := 3) (n := 64) (by simp)).trans F55_3
  have F56_5 := (e55.agrees.read (r := 5) (n := 64) (by simp)).trans F55_5
  have F56_6 := (e55.agrees.read (r := 6) (n := 64) (by simp)).trans F55_6
  have F56_7 := (e55.agrees.read (r := 7) (n := 64) (by simp)).trans F55_7
  have F56_8 := (e55.agrees.read (r := 8) (n := 64) (by simp)).trans F55_8
  have F56_9 := (e55.agrees.read (r := 9) (n := 64) (by simp)).trans F55_9
  have F56_10 := (e55.agrees.read (r := 10) (n := 64) (by simp)).trans F55_10
  have F56_11 := (e55.agrees.read (r := 11) (n := 64) (by simp)).trans F55_11
  have F56_13 := (e55.agrees.read (r := 13) (n := 64) (by simp)).trans F55_13
  have AD56 := AD55.trans a55
  clear a55 e55 AD55 r55 c55 ip55 G55 A55 SP55 U55 FK55 F55_0 F55_1 F55_2 F55_3 F55_5 F55_6 F55_7 F55_8 F55_9 F55_10 F55_11 F55_12 F55_13 F55_14
  clear u55
  obtain ⟨u57, a56, r57, c57, ip57, e56⟩ := run1 (and_r32_r32_rex_effect_step 0x101da4 0x41 0xfa (by unfold RexNoWPrefix; decide) (by decide))
    r56 c56 (program_text_slice c56 0x1da4 3 (by decide +kernel)) ip56
    (q := 0x101da7) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e56 : (andR32R32Effect 0x101da4 3 10 7 u56).Holds u56 u57 := e56
  have G57 := G56.step e56.agrees
  have A57 := acc_reg A56 e56.agrees (by simp [CS, callChanges])
  have U57 := U56.step e56.agrees (by simp [Component.isMem])
  have FK57 := FK56.step e56.agrees (by simp [Component.isMem])
  have SP57 : stackPtr u57 = frameStart s + BitVec.ofNat 64 0 := (e56.agrees.read (r := 4) (n := 64) (by simp)).trans SP56
  have F57_10 : (Operand.reg 10 : Operand 64).read u57 = (v56 (words s)).setWidth 64 := by
    refine (e56.writes : (Operand.reg 10 : Operand 64).read u57 = _).trans ?_
    simp only [andR32R32Effect, r32_eq, F56_10, F56_7, v56, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F57_0 := (e56.agrees.read (r := 0) (n := 64) (by simp)).trans F56_0
  have F57_1 := (e56.agrees.read (r := 1) (n := 64) (by simp)).trans F56_1
  have F57_2 := (e56.agrees.read (r := 2) (n := 64) (by simp)).trans F56_2
  have F57_3 := (e56.agrees.read (r := 3) (n := 64) (by simp)).trans F56_3
  have F57_5 := (e56.agrees.read (r := 5) (n := 64) (by simp)).trans F56_5
  have F57_6 := (e56.agrees.read (r := 6) (n := 64) (by simp)).trans F56_6
  have F57_7 := (e56.agrees.read (r := 7) (n := 64) (by simp)).trans F56_7
  have F57_8 := (e56.agrees.read (r := 8) (n := 64) (by simp)).trans F56_8
  have F57_9 := (e56.agrees.read (r := 9) (n := 64) (by simp)).trans F56_9
  have F57_11 := (e56.agrees.read (r := 11) (n := 64) (by simp)).trans F56_11
  have F57_13 := (e56.agrees.read (r := 13) (n := 64) (by simp)).trans F56_13
  have F57_14 := (e56.agrees.read (r := 14) (n := 64) (by simp)).trans F56_14
  have AD57 := AD56.trans a56
  clear a56 e56 AD56 r56 c56 ip56 G56 A56 SP56 U56 FK56 F56_0 F56_1 F56_2 F56_3 F56_5 F56_6 F56_7 F56_8 F56_9 F56_10 F56_11 F56_13 F56_14
  clear u56
  obtain ⟨u58, a57, r58, c58, ip58, e57⟩ := run1 (or_r32_r32_rex_effect_step 0x101da7 0x41 0xea (by unfold RexNoWPrefix; decide) (by decide))
    r57 c57 (program_text_slice c57 0x1da7 3 (by decide +kernel)) ip57
    (q := 0x101daa) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e57 : (orR32R32Effect 0x101da7 3 10 5 u57).Holds u57 u58 := e57
  have G58 := G57.step e57.agrees
  have A58 := acc_reg A57 e57.agrees (by simp [CS, callChanges])
  have U58 := U57.step e57.agrees (by simp [Component.isMem])
  have FK58 := FK57.step e57.agrees (by simp [Component.isMem])
  have SP58 : stackPtr u58 = frameStart s + BitVec.ofNat 64 0 := (e57.agrees.read (r := 4) (n := 64) (by simp)).trans SP57
  have F58_10 : (Operand.reg 10 : Operand 64).read u58 = (v57 (words s)).setWidth 64 := by
    refine (e57.writes : (Operand.reg 10 : Operand 64).read u58 = _).trans ?_
    simp only [orR32R32Effect, r32_eq, F57_10, F57_5, v57, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F58_0 := (e57.agrees.read (r := 0) (n := 64) (by simp)).trans F57_0
  have F58_1 := (e57.agrees.read (r := 1) (n := 64) (by simp)).trans F57_1
  have F58_2 := (e57.agrees.read (r := 2) (n := 64) (by simp)).trans F57_2
  have F58_3 := (e57.agrees.read (r := 3) (n := 64) (by simp)).trans F57_3
  have F58_6 := (e57.agrees.read (r := 6) (n := 64) (by simp)).trans F57_6
  have F58_7 := (e57.agrees.read (r := 7) (n := 64) (by simp)).trans F57_7
  have F58_8 := (e57.agrees.read (r := 8) (n := 64) (by simp)).trans F57_8
  have F58_9 := (e57.agrees.read (r := 9) (n := 64) (by simp)).trans F57_9
  have F58_11 := (e57.agrees.read (r := 11) (n := 64) (by simp)).trans F57_11
  have F58_13 := (e57.agrees.read (r := 13) (n := 64) (by simp)).trans F57_13
  have F58_14 := (e57.agrees.read (r := 14) (n := 64) (by simp)).trans F57_14
  have AD58 := AD57.trans a57
  clear a57 e57 AD57 r57 c57 ip57 G57 A57 SP57 U57 FK57 F57_0 F57_1 F57_2 F57_3 F57_5 F57_6 F57_7 F57_8 F57_9 F57_10 F57_11 F57_13 F57_14
  clear u57
  obtain ⟨u59, a58, r59, c59, ip59, e58⟩ := run1 (and_r32_r32_rex_effect_step 0x101daa 0x41 0xf9 (by unfold RexNoWPrefix; decide) (by decide))
    r58 c58 (program_text_slice c58 0x1daa 3 (by decide +kernel)) ip58
    (q := 0x101dad) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e58 : (andR32R32Effect 0x101daa 3 9 7 u58).Holds u58 u59 := e58
  have G59 := G58.step e58.agrees
  have A59 := acc_reg A58 e58.agrees (by simp [CS, callChanges])
  have U59 := U58.step e58.agrees (by simp [Component.isMem])
  have FK59 := FK58.step e58.agrees (by simp [Component.isMem])
  have SP59 : stackPtr u59 = frameStart s + BitVec.ofNat 64 0 := (e58.agrees.read (r := 4) (n := 64) (by simp)).trans SP58
  have F59_9 : (Operand.reg 9 : Operand 64).read u59 = (v58 (words s)).setWidth 64 := by
    refine (e58.writes : (Operand.reg 9 : Operand 64).read u59 = _).trans ?_
    simp only [andR32R32Effect, r32_eq, F58_9, F58_7, v58, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F59_0 := (e58.agrees.read (r := 0) (n := 64) (by simp)).trans F58_0
  have F59_1 := (e58.agrees.read (r := 1) (n := 64) (by simp)).trans F58_1
  have F59_2 := (e58.agrees.read (r := 2) (n := 64) (by simp)).trans F58_2
  have F59_3 := (e58.agrees.read (r := 3) (n := 64) (by simp)).trans F58_3
  have F59_6 := (e58.agrees.read (r := 6) (n := 64) (by simp)).trans F58_6
  have F59_7 := (e58.agrees.read (r := 7) (n := 64) (by simp)).trans F58_7
  have F59_8 := (e58.agrees.read (r := 8) (n := 64) (by simp)).trans F58_8
  have F59_10 := (e58.agrees.read (r := 10) (n := 64) (by simp)).trans F58_10
  have F59_11 := (e58.agrees.read (r := 11) (n := 64) (by simp)).trans F58_11
  have F59_13 := (e58.agrees.read (r := 13) (n := 64) (by simp)).trans F58_13
  have F59_14 := (e58.agrees.read (r := 14) (n := 64) (by simp)).trans F58_14
  have AD59 := AD58.trans a58
  clear a58 e58 AD58 r58 c58 ip58 G58 A58 SP58 U58 FK58 F58_0 F58_1 F58_2 F58_3 F58_6 F58_7 F58_8 F58_9 F58_10 F58_11 F58_13 F58_14
  clear u58
  obtain ⟨u60, a59, r60, c60, ip60, e59⟩ := run1 (or_r32_r32_rex_effect_step 0x101dad 0x45 0xd9 (by unfold RexNoWPrefix; decide) (by decide))
    r59 c59 (program_text_slice c59 0x1dad 3 (by decide +kernel)) ip59
    (q := 0x101db0) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e59 : (orR32R32Effect 0x101dad 3 9 11 u59).Holds u59 u60 := e59
  have G60 := G59.step e59.agrees
  have A60 := acc_reg A59 e59.agrees (by simp [CS, callChanges])
  have U60 := U59.step e59.agrees (by simp [Component.isMem])
  have FK60 := FK59.step e59.agrees (by simp [Component.isMem])
  have SP60 : stackPtr u60 = frameStart s + BitVec.ofNat 64 0 := (e59.agrees.read (r := 4) (n := 64) (by simp)).trans SP59
  have F60_9 : (Operand.reg 9 : Operand 64).read u60 = (v59 (words s)).setWidth 64 := by
    refine (e59.writes : (Operand.reg 9 : Operand 64).read u60 = _).trans ?_
    simp only [orR32R32Effect, r32_eq, F59_9, F59_11, v59, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F60_0 := (e59.agrees.read (r := 0) (n := 64) (by simp)).trans F59_0
  have F60_1 := (e59.agrees.read (r := 1) (n := 64) (by simp)).trans F59_1
  have F60_2 := (e59.agrees.read (r := 2) (n := 64) (by simp)).trans F59_2
  have F60_3 := (e59.agrees.read (r := 3) (n := 64) (by simp)).trans F59_3
  have F60_6 := (e59.agrees.read (r := 6) (n := 64) (by simp)).trans F59_6
  have F60_7 := (e59.agrees.read (r := 7) (n := 64) (by simp)).trans F59_7
  have F60_8 := (e59.agrees.read (r := 8) (n := 64) (by simp)).trans F59_8
  have F60_10 := (e59.agrees.read (r := 10) (n := 64) (by simp)).trans F59_10
  have F60_13 := (e59.agrees.read (r := 13) (n := 64) (by simp)).trans F59_13
  have F60_14 := (e59.agrees.read (r := 14) (n := 64) (by simp)).trans F59_14
  have AD60 := AD59.trans a59
  clear a59 e59 AD59 r59 c59 ip59 G59 A59 SP59 U59 FK59 F59_0 F59_1 F59_2 F59_3 F59_6 F59_7 F59_8 F59_9 F59_10 F59_11 F59_13 F59_14
  clear u59
  obtain ⟨u61, a60, r61, c61, ip61, e60⟩ := run1 (and_r32_r32_effect_step 0x101db0 0xf9 (by decide))
    r60 c60 (program_text_slice c60 0x1db0 2 (by decide +kernel)) ip60
    (q := 0x101db2) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e60 : (andR32R32Effect 0x101db0 2 1 7 u60).Holds u60 u61 := e60
  have G61 := G60.step e60.agrees
  have A61 := acc_reg A60 e60.agrees (by simp [CS, callChanges])
  have U61 := U60.step e60.agrees (by simp [Component.isMem])
  have FK61 := FK60.step e60.agrees (by simp [Component.isMem])
  have SP61 : stackPtr u61 = frameStart s + BitVec.ofNat 64 0 := (e60.agrees.read (r := 4) (n := 64) (by simp)).trans SP60
  have F61_1 : (Operand.reg 1 : Operand 64).read u61 = (v60 (words s)).setWidth 64 := by
    refine (e60.writes : (Operand.reg 1 : Operand 64).read u61 = _).trans ?_
    simp only [andR32R32Effect, r32_eq, F60_1, F60_7, v60, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F61_0 := (e60.agrees.read (r := 0) (n := 64) (by simp)).trans F60_0
  have F61_2 := (e60.agrees.read (r := 2) (n := 64) (by simp)).trans F60_2
  have F61_3 := (e60.agrees.read (r := 3) (n := 64) (by simp)).trans F60_3
  have F61_6 := (e60.agrees.read (r := 6) (n := 64) (by simp)).trans F60_6
  have F61_7 := (e60.agrees.read (r := 7) (n := 64) (by simp)).trans F60_7
  have F61_8 := (e60.agrees.read (r := 8) (n := 64) (by simp)).trans F60_8
  have F61_9 := (e60.agrees.read (r := 9) (n := 64) (by simp)).trans F60_9
  have F61_10 := (e60.agrees.read (r := 10) (n := 64) (by simp)).trans F60_10
  have F61_13 := (e60.agrees.read (r := 13) (n := 64) (by simp)).trans F60_13
  have F61_14 := (e60.agrees.read (r := 14) (n := 64) (by simp)).trans F60_14
  have AD61 := AD60.trans a60
  clear a60 e60 AD60 r60 c60 ip60 G60 A60 SP60 U60 FK60 F60_0 F60_1 F60_2 F60_3 F60_6 F60_7 F60_8 F60_9 F60_10 F60_13 F60_14
  clear u60
  obtain ⟨u62, a61, r62, c62, ip62, e61⟩ := run1 (or_r32_r32_effect_step 0x101db2 0xd9 (by decide))
    r61 c61 (program_text_slice c61 0x1db2 2 (by decide +kernel)) ip61
    (q := 0x101db4) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e61 : (orR32R32Effect 0x101db2 2 1 3 u61).Holds u61 u62 := e61
  have G62 := G61.step e61.agrees
  have A62 := acc_reg A61 e61.agrees (by simp [CS, callChanges])
  have U62 := U61.step e61.agrees (by simp [Component.isMem])
  have FK62 := FK61.step e61.agrees (by simp [Component.isMem])
  have SP62 : stackPtr u62 = frameStart s + BitVec.ofNat 64 0 := (e61.agrees.read (r := 4) (n := 64) (by simp)).trans SP61
  have F62_1 : (Operand.reg 1 : Operand 64).read u62 = (v61 (words s)).setWidth 64 := by
    refine (e61.writes : (Operand.reg 1 : Operand 64).read u62 = _).trans ?_
    simp only [orR32R32Effect, r32_eq, F61_1, F61_3, v61, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F62_0 := (e61.agrees.read (r := 0) (n := 64) (by simp)).trans F61_0
  have F62_2 := (e61.agrees.read (r := 2) (n := 64) (by simp)).trans F61_2
  have F62_6 := (e61.agrees.read (r := 6) (n := 64) (by simp)).trans F61_6
  have F62_7 := (e61.agrees.read (r := 7) (n := 64) (by simp)).trans F61_7
  have F62_8 := (e61.agrees.read (r := 8) (n := 64) (by simp)).trans F61_8
  have F62_9 := (e61.agrees.read (r := 9) (n := 64) (by simp)).trans F61_9
  have F62_10 := (e61.agrees.read (r := 10) (n := 64) (by simp)).trans F61_10
  have F62_13 := (e61.agrees.read (r := 13) (n := 64) (by simp)).trans F61_13
  have F62_14 := (e61.agrees.read (r := 14) (n := 64) (by simp)).trans F61_14
  have AD62 := AD61.trans a61
  clear a61 e61 AD61 r61 c61 ip61 G61 A61 SP61 U61 FK61 F61_0 F61_1 F61_2 F61_3 F61_6 F61_7 F61_8 F61_9 F61_10 F61_13 F61_14
  clear u61
  obtain ⟨u63, a62, r63, c63, ip63, e62⟩ := run1 (and_r32_r32_effect_step 0x101db4 0xfa (by decide))
    r62 c62 (program_text_slice c62 0x1db4 2 (by decide +kernel)) ip62
    (q := 0x101db6) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e62 : (andR32R32Effect 0x101db4 2 2 7 u62).Holds u62 u63 := e62
  have G63 := G62.step e62.agrees
  have A63 := acc_reg A62 e62.agrees (by simp [CS, callChanges])
  have U63 := U62.step e62.agrees (by simp [Component.isMem])
  have FK63 := FK62.step e62.agrees (by simp [Component.isMem])
  have SP63 : stackPtr u63 = frameStart s + BitVec.ofNat 64 0 := (e62.agrees.read (r := 4) (n := 64) (by simp)).trans SP62
  have F63_2 : (Operand.reg 2 : Operand 64).read u63 = (v62 (words s)).setWidth 64 := by
    refine (e62.writes : (Operand.reg 2 : Operand 64).read u63 = _).trans ?_
    simp only [andR32R32Effect, r32_eq, F62_2, F62_7, v62, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F63_0 := (e62.agrees.read (r := 0) (n := 64) (by simp)).trans F62_0
  have F63_1 := (e62.agrees.read (r := 1) (n := 64) (by simp)).trans F62_1
  have F63_6 := (e62.agrees.read (r := 6) (n := 64) (by simp)).trans F62_6
  have F63_7 := (e62.agrees.read (r := 7) (n := 64) (by simp)).trans F62_7
  have F63_8 := (e62.agrees.read (r := 8) (n := 64) (by simp)).trans F62_8
  have F63_9 := (e62.agrees.read (r := 9) (n := 64) (by simp)).trans F62_9
  have F63_10 := (e62.agrees.read (r := 10) (n := 64) (by simp)).trans F62_10
  have F63_13 := (e62.agrees.read (r := 13) (n := 64) (by simp)).trans F62_13
  have F63_14 := (e62.agrees.read (r := 14) (n := 64) (by simp)).trans F62_14
  have AD63 := AD62.trans a62
  clear a62 e62 AD62 r62 c62 ip62 G62 A62 SP62 U62 FK62 F62_0 F62_1 F62_2 F62_6 F62_7 F62_8 F62_9 F62_10 F62_13 F62_14
  clear u62
  obtain ⟨u64, a63, r64, c64, ip64, e63⟩ := run1 (or_r32_r32_rex_effect_step 0x101db6 0x44 0xea (by unfold RexNoWPrefix; decide) (by decide))
    r63 c63 (program_text_slice c63 0x1db6 3 (by decide +kernel)) ip63
    (q := 0x101db9) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e63 : (orR32R32Effect 0x101db6 3 2 13 u63).Holds u63 u64 := e63
  have G64 := G63.step e63.agrees
  have A64 := acc_reg A63 e63.agrees (by simp [CS, callChanges])
  have U64 := U63.step e63.agrees (by simp [Component.isMem])
  have FK64 := FK63.step e63.agrees (by simp [Component.isMem])
  have SP64 : stackPtr u64 = frameStart s + BitVec.ofNat 64 0 := (e63.agrees.read (r := 4) (n := 64) (by simp)).trans SP63
  have F64_2 : (Operand.reg 2 : Operand 64).read u64 = (v63 (words s)).setWidth 64 := by
    refine (e63.writes : (Operand.reg 2 : Operand 64).read u64 = _).trans ?_
    simp only [orR32R32Effect, r32_eq, F63_2, F63_13, v63, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F64_0 := (e63.agrees.read (r := 0) (n := 64) (by simp)).trans F63_0
  have F64_1 := (e63.agrees.read (r := 1) (n := 64) (by simp)).trans F63_1
  have F64_6 := (e63.agrees.read (r := 6) (n := 64) (by simp)).trans F63_6
  have F64_7 := (e63.agrees.read (r := 7) (n := 64) (by simp)).trans F63_7
  have F64_8 := (e63.agrees.read (r := 8) (n := 64) (by simp)).trans F63_8
  have F64_9 := (e63.agrees.read (r := 9) (n := 64) (by simp)).trans F63_9
  have F64_10 := (e63.agrees.read (r := 10) (n := 64) (by simp)).trans F63_10
  have F64_14 := (e63.agrees.read (r := 14) (n := 64) (by simp)).trans F63_14
  have AD64 := AD63.trans a63
  clear a63 e63 AD63 r63 c63 ip63 G63 A63 SP63 U63 FK63 F63_0 F63_1 F63_2 F63_6 F63_7 F63_8 F63_9 F63_10 F63_13 F63_14
  clear u63
  obtain ⟨u65, a64, r65, c65, ip65, e64⟩ := run1 (and_r32_r32_rex_effect_step 0x101db9 0x44 0xc7 (by unfold RexNoWPrefix; decide) (by decide))
    r64 c64 (program_text_slice c64 0x1db9 3 (by decide +kernel)) ip64
    (q := 0x101dbc) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e64 : (andR32R32Effect 0x101db9 3 7 8 u64).Holds u64 u65 := e64
  have G65 := G64.step e64.agrees
  have A65 := acc_reg A64 e64.agrees (by simp [CS, callChanges])
  have U65 := U64.step e64.agrees (by simp [Component.isMem])
  have FK65 := FK64.step e64.agrees (by simp [Component.isMem])
  have SP65 : stackPtr u65 = frameStart s + BitVec.ofNat 64 0 := (e64.agrees.read (r := 4) (n := 64) (by simp)).trans SP64
  have F65_7 : (Operand.reg 7 : Operand 64).read u65 = (v64 (words s)).setWidth 64 := by
    refine (e64.writes : (Operand.reg 7 : Operand 64).read u65 = _).trans ?_
    simp only [andR32R32Effect, r32_eq, F64_7, F64_8, v64, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F65_0 := (e64.agrees.read (r := 0) (n := 64) (by simp)).trans F64_0
  have F65_1 := (e64.agrees.read (r := 1) (n := 64) (by simp)).trans F64_1
  have F65_2 := (e64.agrees.read (r := 2) (n := 64) (by simp)).trans F64_2
  have F65_6 := (e64.agrees.read (r := 6) (n := 64) (by simp)).trans F64_6
  have F65_9 := (e64.agrees.read (r := 9) (n := 64) (by simp)).trans F64_9
  have F65_10 := (e64.agrees.read (r := 10) (n := 64) (by simp)).trans F64_10
  have F65_14 := (e64.agrees.read (r := 14) (n := 64) (by simp)).trans F64_14
  have AD65 := AD64.trans a64
  clear a64 e64 AD64 r64 c64 ip64 G64 A64 SP64 U64 FK64 F64_0 F64_1 F64_2 F64_6 F64_7 F64_8 F64_9 F64_10 F64_14
  clear u64
  obtain ⟨u66, a65, r66, c66, ip66, e65⟩ := run1 (or_r32_r32_rex_effect_step 0x101dbc 0x44 0xf7 (by unfold RexNoWPrefix; decide) (by decide))
    r65 c65 (program_text_slice c65 0x1dbc 3 (by decide +kernel)) ip65
    (q := 0x101dbf) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e65 : (orR32R32Effect 0x101dbc 3 7 14 u65).Holds u65 u66 := e65
  have G66 := G65.step e65.agrees
  have A66 := acc_reg A65 e65.agrees (by simp [CS, callChanges])
  have U66 := U65.step e65.agrees (by simp [Component.isMem])
  have FK66 := FK65.step e65.agrees (by simp [Component.isMem])
  have SP66 : stackPtr u66 = frameStart s + BitVec.ofNat 64 0 := (e65.agrees.read (r := 4) (n := 64) (by simp)).trans SP65
  have F66_7 : (Operand.reg 7 : Operand 64).read u66 = (v65 (words s)).setWidth 64 := by
    refine (e65.writes : (Operand.reg 7 : Operand 64).read u66 = _).trans ?_
    simp only [orR32R32Effect, r32_eq, F65_7, F65_14, v65, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F66_0 := (e65.agrees.read (r := 0) (n := 64) (by simp)).trans F65_0
  have F66_1 := (e65.agrees.read (r := 1) (n := 64) (by simp)).trans F65_1
  have F66_2 := (e65.agrees.read (r := 2) (n := 64) (by simp)).trans F65_2
  have F66_6 := (e65.agrees.read (r := 6) (n := 64) (by simp)).trans F65_6
  have F66_9 := (e65.agrees.read (r := 9) (n := 64) (by simp)).trans F65_9
  have F66_10 := (e65.agrees.read (r := 10) (n := 64) (by simp)).trans F65_10
  have AD66 := AD65.trans a65
  clear a65 e65 AD65 r65 c65 ip65 G65 A65 SP65 U65 FK65 F65_0 F65_1 F65_2 F65_6 F65_7 F65_9 F65_10 F65_14
  clear u65
  obtain ⟨u67, a66, r67, c67, ip67, e66⟩ := run1 (mov_r32_r32_rex_effect_step 0x101dbf 0x45 0xc8 (by unfold RexNoWPrefix; decide) (by decide))
    r66 c66 (program_text_slice c66 0x1dbf 3 (by decide +kernel)) ip66
    (q := 0x101dc2) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e66 : (movR32R32Effect 0x101dbf 3 8 9 u66).Holds u66 u67 := e66
  have G67 := G66.step e66.agrees
  have A67 := acc_reg A66 e66.agrees (by simp [CS, callChanges])
  have U67 := U66.step e66.agrees (by simp [Component.isMem])
  have FK67 := FK66.step e66.agrees (by simp [Component.isMem])
  have SP67 : stackPtr u67 = frameStart s + BitVec.ofNat 64 0 := (e66.agrees.read (r := 4) (n := 64) (by simp)).trans SP66
  have F67_8 : (Operand.reg 8 : Operand 64).read u67 = (v59 (words s)).setWidth 64 := by
    refine (e66.writes : (Operand.reg 8 : Operand 64).read u67 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F66_9, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F67_0 := (e66.agrees.read (r := 0) (n := 64) (by simp)).trans F66_0
  have F67_1 := (e66.agrees.read (r := 1) (n := 64) (by simp)).trans F66_1
  have F67_2 := (e66.agrees.read (r := 2) (n := 64) (by simp)).trans F66_2
  have F67_6 := (e66.agrees.read (r := 6) (n := 64) (by simp)).trans F66_6
  have F67_7 := (e66.agrees.read (r := 7) (n := 64) (by simp)).trans F66_7
  have F67_9 := (e66.agrees.read (r := 9) (n := 64) (by simp)).trans F66_9
  have F67_10 := (e66.agrees.read (r := 10) (n := 64) (by simp)).trans F66_10
  have AD67 := AD66.trans a66
  clear a66 e66 AD66 r66 c66 ip66 G66 A66 SP66 U66 FK66 F66_0 F66_1 F66_2 F66_6 F66_7 F66_9 F66_10
  clear u66
  obtain ⟨u68, a67, r68, c68, ip68, e67⟩ := run1 (shl_r32_imm8_rex_effect_step 0x101dc2 0x41 0xe0 0x1a (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r67 c67 (program_text_slice c67 0x1dc2 4 (by decide +kernel)) ip67
    (q := 0x101dc6) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e67 : (shlR32Effect 0x101dc2 4 8 26 u67).Holds u67 u68 := e67
  have G68 := G67.step e67.agrees
  have A68 := acc_reg A67 e67.agrees (by simp [CS, callChanges])
  have U68 := U67.step e67.agrees (by simp [Component.isMem])
  have FK68 := FK67.step e67.agrees (by simp [Component.isMem])
  have SP68 : stackPtr u68 = frameStart s + BitVec.ofNat 64 0 := (e67.agrees.read (r := 4) (n := 64) (by simp)).trans SP67
  have F68_8 : (Operand.reg 8 : Operand 64).read u68 = (v67 (words s)).setWidth 64 := by
    refine (e67.writes : (Operand.reg 8 : Operand 64).read u68 = _).trans ?_
    simp only [shlR32Effect, r32_eq, F67_8, v67, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F68_0 := (e67.agrees.read (r := 0) (n := 64) (by simp)).trans F67_0
  have F68_1 := (e67.agrees.read (r := 1) (n := 64) (by simp)).trans F67_1
  have F68_2 := (e67.agrees.read (r := 2) (n := 64) (by simp)).trans F67_2
  have F68_6 := (e67.agrees.read (r := 6) (n := 64) (by simp)).trans F67_6
  have F68_7 := (e67.agrees.read (r := 7) (n := 64) (by simp)).trans F67_7
  have F68_9 := (e67.agrees.read (r := 9) (n := 64) (by simp)).trans F67_9
  have F68_10 := (e67.agrees.read (r := 10) (n := 64) (by simp)).trans F67_10
  have AD68 := AD67.trans a67
  clear a67 e67 AD67 r67 c67 ip67 G67 A67 SP67 U67 FK67 F67_0 F67_1 F67_2 F67_6 F67_7 F67_8 F67_9 F67_10
  clear u67
  obtain ⟨u69, a68, r69, c69, ip69, e68⟩ := run1 (or_r32_r32_rex_effect_step 0x101dc6 0x45 0xd0 (by unfold RexNoWPrefix; decide) (by decide))
    r68 c68 (program_text_slice c68 0x1dc6 3 (by decide +kernel)) ip68
    (q := 0x101dc9) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e68 : (orR32R32Effect 0x101dc6 3 8 10 u68).Holds u68 u69 := e68
  have G69 := G68.step e68.agrees
  have A69 := acc_reg A68 e68.agrees (by simp [CS, callChanges])
  have U69 := U68.step e68.agrees (by simp [Component.isMem])
  have FK69 := FK68.step e68.agrees (by simp [Component.isMem])
  have SP69 : stackPtr u69 = frameStart s + BitVec.ofNat 64 0 := (e68.agrees.read (r := 4) (n := 64) (by simp)).trans SP68
  have F69_8 : (Operand.reg 8 : Operand 64).read u69 = (v68 (words s)).setWidth 64 := by
    refine (e68.writes : (Operand.reg 8 : Operand 64).read u69 = _).trans ?_
    simp only [orR32R32Effect, r32_eq, F68_8, F68_10, v68, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F69_0 := (e68.agrees.read (r := 0) (n := 64) (by simp)).trans F68_0
  have F69_1 := (e68.agrees.read (r := 1) (n := 64) (by simp)).trans F68_1
  have F69_2 := (e68.agrees.read (r := 2) (n := 64) (by simp)).trans F68_2
  have F69_6 := (e68.agrees.read (r := 6) (n := 64) (by simp)).trans F68_6
  have F69_7 := (e68.agrees.read (r := 7) (n := 64) (by simp)).trans F68_7
  have F69_9 := (e68.agrees.read (r := 9) (n := 64) (by simp)).trans F68_9
  have AD69 := AD68.trans a68
  clear a68 e68 AD68 r68 c68 ip68 G68 A68 SP68 U68 FK68 F68_0 F68_1 F68_2 F68_6 F68_7 F68_8 F68_9 F68_10
  clear u68
  obtain ⟨u70, a69, r70, c70, ip70, e69⟩ := run1 (shr_r32_imm8_rex_effect_step 0x101dc9 0x41 0xe9 0x06 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r69 c69 (program_text_slice c69 0x1dc9 4 (by decide +kernel)) ip69
    (q := 0x101dcd) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e69 : (shrR32Effect 0x101dc9 4 9 6 u69).Holds u69 u70 := e69
  have G70 := G69.step e69.agrees
  have A70 := acc_reg A69 e69.agrees (by simp [CS, callChanges])
  have U70 := U69.step e69.agrees (by simp [Component.isMem])
  have FK70 := FK69.step e69.agrees (by simp [Component.isMem])
  have SP70 : stackPtr u70 = frameStart s + BitVec.ofNat 64 0 := (e69.agrees.read (r := 4) (n := 64) (by simp)).trans SP69
  have F70_9 : (Operand.reg 9 : Operand 64).read u70 = (v69 (words s)).setWidth 64 := by
    refine (e69.writes : (Operand.reg 9 : Operand 64).read u70 = _).trans ?_
    simp only [shrR32Effect, r32_eq, F69_9, v69, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F70_0 := (e69.agrees.read (r := 0) (n := 64) (by simp)).trans F69_0
  have F70_1 := (e69.agrees.read (r := 1) (n := 64) (by simp)).trans F69_1
  have F70_2 := (e69.agrees.read (r := 2) (n := 64) (by simp)).trans F69_2
  have F70_6 := (e69.agrees.read (r := 6) (n := 64) (by simp)).trans F69_6
  have F70_7 := (e69.agrees.read (r := 7) (n := 64) (by simp)).trans F69_7
  have F70_8 := (e69.agrees.read (r := 8) (n := 64) (by simp)).trans F69_8
  have AD70 := AD69.trans a69
  clear a69 e69 AD69 r69 c69 ip69 G69 A69 SP69 U69 FK69 F69_0 F69_1 F69_2 F69_6 F69_7 F69_8 F69_9
  clear u69
  obtain ⟨u71, a70, r71, c71, ip71, e70⟩ := run1 (mov_r32_r32_rex_effect_step 0x101dcd 0x41 0xca (by unfold RexNoWPrefix; decide) (by decide))
    r70 c70 (program_text_slice c70 0x1dcd 3 (by decide +kernel)) ip70
    (q := 0x101dd0) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e70 : (movR32R32Effect 0x101dcd 3 10 1 u70).Holds u70 u71 := e70
  have G71 := G70.step e70.agrees
  have A71 := acc_reg A70 e70.agrees (by simp [CS, callChanges])
  have U71 := U70.step e70.agrees (by simp [Component.isMem])
  have FK71 := FK70.step e70.agrees (by simp [Component.isMem])
  have SP71 : stackPtr u71 = frameStart s + BitVec.ofNat 64 0 := (e70.agrees.read (r := 4) (n := 64) (by simp)).trans SP70
  have F71_10 : (Operand.reg 10 : Operand 64).read u71 = (v61 (words s)).setWidth 64 := by
    refine (e70.writes : (Operand.reg 10 : Operand 64).read u71 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F70_1, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F71_0 := (e70.agrees.read (r := 0) (n := 64) (by simp)).trans F70_0
  have F71_1 := (e70.agrees.read (r := 1) (n := 64) (by simp)).trans F70_1
  have F71_2 := (e70.agrees.read (r := 2) (n := 64) (by simp)).trans F70_2
  have F71_6 := (e70.agrees.read (r := 6) (n := 64) (by simp)).trans F70_6
  have F71_7 := (e70.agrees.read (r := 7) (n := 64) (by simp)).trans F70_7
  have F71_8 := (e70.agrees.read (r := 8) (n := 64) (by simp)).trans F70_8
  have F71_9 := (e70.agrees.read (r := 9) (n := 64) (by simp)).trans F70_9
  have AD71 := AD70.trans a70
  clear a70 e70 AD70 r70 c70 ip70 G70 A70 SP70 U70 FK70 F70_0 F70_1 F70_2 F70_6 F70_7 F70_8 F70_9
  clear u70
  obtain ⟨u72, a71, r72, c72, ip72, e71⟩ := run1 (shl_r32_imm8_rex_effect_step 0x101dd0 0x41 0xe2 0x14 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r71 c71 (program_text_slice c71 0x1dd0 4 (by decide +kernel)) ip71
    (q := 0x101dd4) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e71 : (shlR32Effect 0x101dd0 4 10 20 u71).Holds u71 u72 := e71
  have G72 := G71.step e71.agrees
  have A72 := acc_reg A71 e71.agrees (by simp [CS, callChanges])
  have U72 := U71.step e71.agrees (by simp [Component.isMem])
  have FK72 := FK71.step e71.agrees (by simp [Component.isMem])
  have SP72 : stackPtr u72 = frameStart s + BitVec.ofNat 64 0 := (e71.agrees.read (r := 4) (n := 64) (by simp)).trans SP71
  have F72_10 : (Operand.reg 10 : Operand 64).read u72 = (v71 (words s)).setWidth 64 := by
    refine (e71.writes : (Operand.reg 10 : Operand 64).read u72 = _).trans ?_
    simp only [shlR32Effect, r32_eq, F71_10, v71, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F72_0 := (e71.agrees.read (r := 0) (n := 64) (by simp)).trans F71_0
  have F72_1 := (e71.agrees.read (r := 1) (n := 64) (by simp)).trans F71_1
  have F72_2 := (e71.agrees.read (r := 2) (n := 64) (by simp)).trans F71_2
  have F72_6 := (e71.agrees.read (r := 6) (n := 64) (by simp)).trans F71_6
  have F72_7 := (e71.agrees.read (r := 7) (n := 64) (by simp)).trans F71_7
  have F72_8 := (e71.agrees.read (r := 8) (n := 64) (by simp)).trans F71_8
  have F72_9 := (e71.agrees.read (r := 9) (n := 64) (by simp)).trans F71_9
  have AD72 := AD71.trans a71
  clear a71 e71 AD71 r71 c71 ip71 G71 A71 SP71 U71 FK71 F71_0 F71_1 F71_2 F71_6 F71_7 F71_8 F71_9 F71_10
  clear u71
  obtain ⟨u73, a72, r73, c73, ip73, e72⟩ := run1 (or_r32_r32_rex_effect_step 0x101dd4 0x45 0xca (by unfold RexNoWPrefix; decide) (by decide))
    r72 c72 (program_text_slice c72 0x1dd4 3 (by decide +kernel)) ip72
    (q := 0x101dd7) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e72 : (orR32R32Effect 0x101dd4 3 10 9 u72).Holds u72 u73 := e72
  have G73 := G72.step e72.agrees
  have A73 := acc_reg A72 e72.agrees (by simp [CS, callChanges])
  have U73 := U72.step e72.agrees (by simp [Component.isMem])
  have FK73 := FK72.step e72.agrees (by simp [Component.isMem])
  have SP73 : stackPtr u73 = frameStart s + BitVec.ofNat 64 0 := (e72.agrees.read (r := 4) (n := 64) (by simp)).trans SP72
  have F73_10 : (Operand.reg 10 : Operand 64).read u73 = (v72 (words s)).setWidth 64 := by
    refine (e72.writes : (Operand.reg 10 : Operand 64).read u73 = _).trans ?_
    simp only [orR32R32Effect, r32_eq, F72_10, F72_9, v72, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F73_0 := (e72.agrees.read (r := 0) (n := 64) (by simp)).trans F72_0
  have F73_1 := (e72.agrees.read (r := 1) (n := 64) (by simp)).trans F72_1
  have F73_2 := (e72.agrees.read (r := 2) (n := 64) (by simp)).trans F72_2
  have F73_6 := (e72.agrees.read (r := 6) (n := 64) (by simp)).trans F72_6
  have F73_7 := (e72.agrees.read (r := 7) (n := 64) (by simp)).trans F72_7
  have F73_8 := (e72.agrees.read (r := 8) (n := 64) (by simp)).trans F72_8
  have AD73 := AD72.trans a72
  clear a72 e72 AD72 r72 c72 ip72 G72 A72 SP72 U72 FK72 F72_0 F72_1 F72_2 F72_6 F72_7 F72_8 F72_9 F72_10
  clear u72
  obtain ⟨u74, a73, r74, c74, ip74, e73⟩ := run1 (shr_r32_imm8_effect_step 0x101dd7 0xe9 0x0c (by decide) (by decide))
    r73 c73 (program_text_slice c73 0x1dd7 3 (by decide +kernel)) ip73
    (q := 0x101dda) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e73 : (shrR32Effect 0x101dd7 3 1 12 u73).Holds u73 u74 := e73
  have G74 := G73.step e73.agrees
  have A74 := acc_reg A73 e73.agrees (by simp [CS, callChanges])
  have U74 := U73.step e73.agrees (by simp [Component.isMem])
  have FK74 := FK73.step e73.agrees (by simp [Component.isMem])
  have SP74 : stackPtr u74 = frameStart s + BitVec.ofNat 64 0 := (e73.agrees.read (r := 4) (n := 64) (by simp)).trans SP73
  have F74_1 : (Operand.reg 1 : Operand 64).read u74 = (v73 (words s)).setWidth 64 := by
    refine (e73.writes : (Operand.reg 1 : Operand 64).read u74 = _).trans ?_
    simp only [shrR32Effect, r32_eq, F73_1, v73, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F74_0 := (e73.agrees.read (r := 0) (n := 64) (by simp)).trans F73_0
  have F74_2 := (e73.agrees.read (r := 2) (n := 64) (by simp)).trans F73_2
  have F74_6 := (e73.agrees.read (r := 6) (n := 64) (by simp)).trans F73_6
  have F74_7 := (e73.agrees.read (r := 7) (n := 64) (by simp)).trans F73_7
  have F74_8 := (e73.agrees.read (r := 8) (n := 64) (by simp)).trans F73_8
  have F74_10 := (e73.agrees.read (r := 10) (n := 64) (by simp)).trans F73_10
  have AD74 := AD73.trans a73
  clear a73 e73 AD73 r73 c73 ip73 G73 A73 SP73 U73 FK73 F73_0 F73_1 F73_2 F73_6 F73_7 F73_8 F73_10
  clear u73
  obtain ⟨u75, a74, r75, c75, ip75, e74⟩ := run1 (mov_r32_r32_rex_effect_step 0x101dda 0x41 0xd1 (by unfold RexNoWPrefix; decide) (by decide))
    r74 c74 (program_text_slice c74 0x1dda 3 (by decide +kernel)) ip74
    (q := 0x101ddd) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e74 : (movR32R32Effect 0x101dda 3 9 2 u74).Holds u74 u75 := e74
  have G75 := G74.step e74.agrees
  have A75 := acc_reg A74 e74.agrees (by simp [CS, callChanges])
  have U75 := U74.step e74.agrees (by simp [Component.isMem])
  have FK75 := FK74.step e74.agrees (by simp [Component.isMem])
  have SP75 : stackPtr u75 = frameStart s + BitVec.ofNat 64 0 := (e74.agrees.read (r := 4) (n := 64) (by simp)).trans SP74
  have F75_9 : (Operand.reg 9 : Operand 64).read u75 = (v63 (words s)).setWidth 64 := by
    refine (e74.writes : (Operand.reg 9 : Operand 64).read u75 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F74_2, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F75_0 := (e74.agrees.read (r := 0) (n := 64) (by simp)).trans F74_0
  have F75_1 := (e74.agrees.read (r := 1) (n := 64) (by simp)).trans F74_1
  have F75_2 := (e74.agrees.read (r := 2) (n := 64) (by simp)).trans F74_2
  have F75_6 := (e74.agrees.read (r := 6) (n := 64) (by simp)).trans F74_6
  have F75_7 := (e74.agrees.read (r := 7) (n := 64) (by simp)).trans F74_7
  have F75_8 := (e74.agrees.read (r := 8) (n := 64) (by simp)).trans F74_8
  have F75_10 := (e74.agrees.read (r := 10) (n := 64) (by simp)).trans F74_10
  have AD75 := AD74.trans a74
  clear a74 e74 AD74 r74 c74 ip74 G74 A74 SP74 U74 FK74 F74_0 F74_1 F74_2 F74_6 F74_7 F74_8 F74_10
  clear u74
  obtain ⟨u76, a75, r76, c76, ip76, e75⟩ := run1 (shl_r32_imm8_rex_effect_step 0x101ddd 0x41 0xe1 0x0e (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    r75 c75 (program_text_slice c75 0x1ddd 4 (by decide +kernel)) ip75
    (q := 0x101de1) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e75 : (shlR32Effect 0x101ddd 4 9 14 u75).Holds u75 u76 := e75
  have G76 := G75.step e75.agrees
  have A76 := acc_reg A75 e75.agrees (by simp [CS, callChanges])
  have U76 := U75.step e75.agrees (by simp [Component.isMem])
  have FK76 := FK75.step e75.agrees (by simp [Component.isMem])
  have SP76 : stackPtr u76 = frameStart s + BitVec.ofNat 64 0 := (e75.agrees.read (r := 4) (n := 64) (by simp)).trans SP75
  have F76_9 : (Operand.reg 9 : Operand 64).read u76 = (v75 (words s)).setWidth 64 := by
    refine (e75.writes : (Operand.reg 9 : Operand 64).read u76 = _).trans ?_
    simp only [shlR32Effect, r32_eq, F75_9, v75, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F76_0 := (e75.agrees.read (r := 0) (n := 64) (by simp)).trans F75_0
  have F76_1 := (e75.agrees.read (r := 1) (n := 64) (by simp)).trans F75_1
  have F76_2 := (e75.agrees.read (r := 2) (n := 64) (by simp)).trans F75_2
  have F76_6 := (e75.agrees.read (r := 6) (n := 64) (by simp)).trans F75_6
  have F76_7 := (e75.agrees.read (r := 7) (n := 64) (by simp)).trans F75_7
  have F76_8 := (e75.agrees.read (r := 8) (n := 64) (by simp)).trans F75_8
  have F76_10 := (e75.agrees.read (r := 10) (n := 64) (by simp)).trans F75_10
  have AD76 := AD75.trans a75
  clear a75 e75 AD75 r75 c75 ip75 G75 A75 SP75 U75 FK75 F75_0 F75_1 F75_2 F75_6 F75_7 F75_8 F75_9 F75_10
  clear u75
  obtain ⟨u77, a76, r77, c77, ip77, e76⟩ := run1 (or_r32_r32_rex_effect_step 0x101de1 0x41 0xc9 (by unfold RexNoWPrefix; decide) (by decide))
    r76 c76 (program_text_slice c76 0x1de1 3 (by decide +kernel)) ip76
    (q := 0x101de4) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e76 : (orR32R32Effect 0x101de1 3 9 1 u76).Holds u76 u77 := e76
  have G77 := G76.step e76.agrees
  have A77 := acc_reg A76 e76.agrees (by simp [CS, callChanges])
  have U77 := U76.step e76.agrees (by simp [Component.isMem])
  have FK77 := FK76.step e76.agrees (by simp [Component.isMem])
  have SP77 : stackPtr u77 = frameStart s + BitVec.ofNat 64 0 := (e76.agrees.read (r := 4) (n := 64) (by simp)).trans SP76
  have F77_9 : (Operand.reg 9 : Operand 64).read u77 = (v76 (words s)).setWidth 64 := by
    refine (e76.writes : (Operand.reg 9 : Operand 64).read u77 = _).trans ?_
    simp only [orR32R32Effect, r32_eq, F76_9, F76_1, v76, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F77_0 := (e76.agrees.read (r := 0) (n := 64) (by simp)).trans F76_0
  have F77_2 := (e76.agrees.read (r := 2) (n := 64) (by simp)).trans F76_2
  have F77_6 := (e76.agrees.read (r := 6) (n := 64) (by simp)).trans F76_6
  have F77_7 := (e76.agrees.read (r := 7) (n := 64) (by simp)).trans F76_7
  have F77_8 := (e76.agrees.read (r := 8) (n := 64) (by simp)).trans F76_8
  have F77_10 := (e76.agrees.read (r := 10) (n := 64) (by simp)).trans F76_10
  have AD77 := AD76.trans a76
  clear a76 e76 AD76 r76 c76 ip76 G76 A76 SP76 U76 FK76 F76_0 F76_1 F76_2 F76_6 F76_7 F76_8 F76_9 F76_10
  clear u76
  obtain ⟨u78, a77, r78, c78, ip78, e77⟩ := run1 (shr_r32_imm8_effect_step 0x101de4 0xea 0x12 (by decide) (by decide))
    r77 c77 (program_text_slice c77 0x1de4 3 (by decide +kernel)) ip77
    (q := 0x101de7) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e77 : (shrR32Effect 0x101de4 3 2 18 u77).Holds u77 u78 := e77
  have G78 := G77.step e77.agrees
  have A78 := acc_reg A77 e77.agrees (by simp [CS, callChanges])
  have U78 := U77.step e77.agrees (by simp [Component.isMem])
  have FK78 := FK77.step e77.agrees (by simp [Component.isMem])
  have SP78 : stackPtr u78 = frameStart s + BitVec.ofNat 64 0 := (e77.agrees.read (r := 4) (n := 64) (by simp)).trans SP77
  have F78_2 : (Operand.reg 2 : Operand 64).read u78 = (v77 (words s)).setWidth 64 := by
    refine (e77.writes : (Operand.reg 2 : Operand 64).read u78 = _).trans ?_
    simp only [shrR32Effect, r32_eq, F77_2, v77, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F78_0 := (e77.agrees.read (r := 0) (n := 64) (by simp)).trans F77_0
  have F78_6 := (e77.agrees.read (r := 6) (n := 64) (by simp)).trans F77_6
  have F78_7 := (e77.agrees.read (r := 7) (n := 64) (by simp)).trans F77_7
  have F78_8 := (e77.agrees.read (r := 8) (n := 64) (by simp)).trans F77_8
  have F78_9 := (e77.agrees.read (r := 9) (n := 64) (by simp)).trans F77_9
  have F78_10 := (e77.agrees.read (r := 10) (n := 64) (by simp)).trans F77_10
  have AD78 := AD77.trans a77
  clear a77 e77 AD77 r77 c77 ip77 G77 A77 SP77 U77 FK77 F77_0 F77_2 F77_6 F77_7 F77_8 F77_9 F77_10
  clear u77
  obtain ⟨u79, a78, r79, c79, ip79, e78⟩ := run1 (shl_r32_imm8_effect_step 0x101de7 0xe7 0x08 (by decide) (by decide))
    r78 c78 (program_text_slice c78 0x1de7 3 (by decide +kernel)) ip78
    (q := 0x101dea) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e78 : (shlR32Effect 0x101de7 3 7 8 u78).Holds u78 u79 := e78
  have G79 := G78.step e78.agrees
  have A79 := acc_reg A78 e78.agrees (by simp [CS, callChanges])
  have U79 := U78.step e78.agrees (by simp [Component.isMem])
  have FK79 := FK78.step e78.agrees (by simp [Component.isMem])
  have SP79 : stackPtr u79 = frameStart s + BitVec.ofNat 64 0 := (e78.agrees.read (r := 4) (n := 64) (by simp)).trans SP78
  have F79_7 : (Operand.reg 7 : Operand 64).read u79 = (v78 (words s)).setWidth 64 := by
    refine (e78.writes : (Operand.reg 7 : Operand 64).read u79 = _).trans ?_
    simp only [shlR32Effect, r32_eq, F78_7, v78, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F79_0 := (e78.agrees.read (r := 0) (n := 64) (by simp)).trans F78_0
  have F79_2 := (e78.agrees.read (r := 2) (n := 64) (by simp)).trans F78_2
  have F79_6 := (e78.agrees.read (r := 6) (n := 64) (by simp)).trans F78_6
  have F79_8 := (e78.agrees.read (r := 8) (n := 64) (by simp)).trans F78_8
  have F79_9 := (e78.agrees.read (r := 9) (n := 64) (by simp)).trans F78_9
  have F79_10 := (e78.agrees.read (r := 10) (n := 64) (by simp)).trans F78_10
  have AD79 := AD78.trans a78
  clear a78 e78 AD78 r78 c78 ip78 G78 A78 SP78 U78 FK78 F78_0 F78_2 F78_6 F78_7 F78_8 F78_9 F78_10
  clear u78
  obtain ⟨u80, a79, r80, c80, ip80, e79⟩ := run1 (or_r32_r32_effect_step 0x101dea 0xd7 (by decide))
    r79 c79 (program_text_slice c79 0x1dea 2 (by decide +kernel)) ip79
    (q := 0x101dec) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e79 : (orR32R32Effect 0x101dea 2 7 2 u79).Holds u79 u80 := e79
  have G80 := G79.step e79.agrees
  have A80 := acc_reg A79 e79.agrees (by simp [CS, callChanges])
  have U80 := U79.step e79.agrees (by simp [Component.isMem])
  have FK80 := FK79.step e79.agrees (by simp [Component.isMem])
  have SP80 : stackPtr u80 = frameStart s + BitVec.ofNat 64 0 := (e79.agrees.read (r := 4) (n := 64) (by simp)).trans SP79
  have F80_7 : (Operand.reg 7 : Operand 64).read u80 = (v79 (words s)).setWidth 64 := by
    refine (e79.writes : (Operand.reg 7 : Operand 64).read u80 = _).trans ?_
    simp only [orR32R32Effect, r32_eq, F79_7, F79_2, v79, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F80_0 := (e79.agrees.read (r := 0) (n := 64) (by simp)).trans F79_0
  have F80_6 := (e79.agrees.read (r := 6) (n := 64) (by simp)).trans F79_6
  have F80_8 := (e79.agrees.read (r := 8) (n := 64) (by simp)).trans F79_8
  have F80_9 := (e79.agrees.read (r := 9) (n := 64) (by simp)).trans F79_9
  have F80_10 := (e79.agrees.read (r := 10) (n := 64) (by simp)).trans F79_10
  have AD80 := AD79.trans a79
  clear a79 e79 AD79 r79 c79 ip79 G79 A79 SP79 U79 FK79 F79_0 F79_2 F79_6 F79_7 F79_8 F79_9 F79_10
  clear u79
  obtain ⟨u81, a80, r81, c81, ip81, e80⟩ := run1 (add_r32_m32_rex_effect_step 0x101dec 0x44 (by unfold RexNoWPrefix; decide) 0 (.base 6 .none) (by decide) (by decide) (by decide))
    r80 c80 (program_text_slice c80 0x1dec 3 (by decide +kernel)) ⟨ip80, memReadable_at (memReadable_grow hp.state G80) 0x0 4 (by decide) (by rw [addr6 F80_6]; rfl)⟩
    (q := 0x101def) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e80 : (addR32M32Effect 0x101dec 3 8 (.base 6 .none) u80).Holds u80 u81 := e80
  have G81 := G80.step e80.agrees
  have A81 := acc_reg A80 e80.agrees (by simp [CS, callChanges])
  have U81 := U80.step e80.agrees (by simp [Component.isMem])
  have FK81 := FK80.step e80.agrees (by simp [Component.isMem])
  have SP81 : stackPtr u81 = frameStart s + BitVec.ofNat 64 0 := (e80.agrees.read (r := 4) (n := 64) (by simp)).trans SP80
  have F81_8 : (Operand.reg 8 : Operand 64).read u81 = (v80 (words s)).setWidth 64 := by
    refine (e80.writes : (Operand.reg 8 : Operand 64).read u81 = _).trans ?_
    simp only [addR32M32Effect, r32_eq, addr6 F80_6, load_word U80 hp.stateFrame .none 0x0 (by decide) (by decide), F80_8, v80, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F81_0 := (e80.agrees.read (r := 0) (n := 64) (by simp)).trans F80_0
  have F81_6 := (e80.agrees.read (r := 6) (n := 64) (by simp)).trans F80_6
  have F81_7 := (e80.agrees.read (r := 7) (n := 64) (by simp)).trans F80_7
  have F81_9 := (e80.agrees.read (r := 9) (n := 64) (by simp)).trans F80_9
  have F81_10 := (e80.agrees.read (r := 10) (n := 64) (by simp)).trans F80_10
  have CF81 : (StatusFlags.ofRFLAGS u81.RFLAGS).CF = cf80 (words s) := by
    rw [cf_of_flags rfl e80.flags]
    simp only [cf80, r32_eq, addr6 F80_6, load_word U80 hp.stateFrame .none 0x0 (by decide) (by decide), F80_8, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have AD81 := AD80.trans a80
  clear a80 e80 AD80 r80 c80 ip80 G80 A80 SP80 U80 FK80 F80_0 F80_6 F80_7 F80_8 F80_9 F80_10
  clear u80
  obtain ⟨u82, a81, r82, c82, ip82, e81⟩ := run1 (mov_r32_m32_low_effect_step 0x101def 1 (.base 6 (.d8 0x4)) (by decide) (by decide) (by decide))
    r81 c81 (program_text_slice c81 0x1def 3 (by decide +kernel)) ⟨ip81, memReadable_at (memReadable_grow hp.state G81) 0x4 4 (by decide) (by rw [addr6 F81_6]; rfl)⟩
    (q := 0x101df2) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e81 : (movR32M32LowEffect 0x101def 1 (.base 6 (.d8 0x4)) u81).Holds u81 u82 := e81
  have G82 := G81.step e81.agrees
  have A82 := acc_reg A81 e81.agrees (by simp [CS, callChanges])
  have U82 := U81.step e81.agrees (by simp [Component.isMem])
  have FK82 := FK81.step e81.agrees (by simp [Component.isMem])
  have SP82 : stackPtr u82 = frameStart s + BitVec.ofNat 64 0 := (e81.agrees.read (r := 4) (n := 64) (by simp)).trans SP81
  have F82_1 : (Operand.reg 1 : Operand 64).read u82 = (v81 (words s)).setWidth 64 := by
    refine (e81.writes : (Operand.reg 1 : Operand 64).read u82 = _).trans ?_
    simp only [movR32M32LowEffect, r32_eq, addr6 F81_6, load_word U81 hp.stateFrame (.d8 0x4) 0x4 (by decide) (by decide), v81, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F82_0 := (e81.agrees.read (r := 0) (n := 64) (by simp)).trans F81_0
  have F82_6 := (e81.agrees.read (r := 6) (n := 64) (by simp)).trans F81_6
  have F82_7 := (e81.agrees.read (r := 7) (n := 64) (by simp)).trans F81_7
  have F82_8 := (e81.agrees.read (r := 8) (n := 64) (by simp)).trans F81_8
  have F82_9 := (e81.agrees.read (r := 9) (n := 64) (by simp)).trans F81_9
  have F82_10 := (e81.agrees.read (r := 10) (n := 64) (by simp)).trans F81_10
  have CF82 : (StatusFlags.ofRFLAGS u82.RFLAGS).CF = cf80 (words s) := by
    rw [e81.agrees.statusFlags (by simp)]; exact CF81
  have AD82 := AD81.trans a81
  clear a81 e81 AD81 r81 c81 ip81 G81 A81 SP81 U81 FK81 CF81 F81_0 F81_6 F81_7 F81_8 F81_9 F81_10
  clear u81
  obtain ⟨u83, a82, r83, c83, ip83, e82⟩ := run1 (mov_r32_m32_low_effect_step 0x101df2 2 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide))
    r82 c82 (program_text_slice c82 0x1df2 3 (by decide +kernel)) ⟨ip82, memReadable_at (memReadable_grow hp.state G82) 0x8 4 (by decide) (by rw [addr6 F82_6]; rfl)⟩
    (q := 0x101df5) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e82 : (movR32M32LowEffect 0x101df2 2 (.base 6 (.d8 0x8)) u82).Holds u82 u83 := e82
  have G83 := G82.step e82.agrees
  have A83 := acc_reg A82 e82.agrees (by simp [CS, callChanges])
  have U83 := U82.step e82.agrees (by simp [Component.isMem])
  have FK83 := FK82.step e82.agrees (by simp [Component.isMem])
  have SP83 : stackPtr u83 = frameStart s + BitVec.ofNat 64 0 := (e82.agrees.read (r := 4) (n := 64) (by simp)).trans SP82
  have F83_2 : (Operand.reg 2 : Operand 64).read u83 = (v82 (words s)).setWidth 64 := by
    refine (e82.writes : (Operand.reg 2 : Operand 64).read u83 = _).trans ?_
    simp only [movR32M32LowEffect, r32_eq, addr6 F82_6, load_word U82 hp.stateFrame (.d8 0x8) 0x8 (by decide) (by decide), v82, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F83_0 := (e82.agrees.read (r := 0) (n := 64) (by simp)).trans F82_0
  have F83_1 := (e82.agrees.read (r := 1) (n := 64) (by simp)).trans F82_1
  have F83_6 := (e82.agrees.read (r := 6) (n := 64) (by simp)).trans F82_6
  have F83_7 := (e82.agrees.read (r := 7) (n := 64) (by simp)).trans F82_7
  have F83_8 := (e82.agrees.read (r := 8) (n := 64) (by simp)).trans F82_8
  have F83_9 := (e82.agrees.read (r := 9) (n := 64) (by simp)).trans F82_9
  have F83_10 := (e82.agrees.read (r := 10) (n := 64) (by simp)).trans F82_10
  have CF83 : (StatusFlags.ofRFLAGS u83.RFLAGS).CF = cf80 (words s) := by
    rw [e82.agrees.statusFlags (by simp)]; exact CF82
  have AD83 := AD82.trans a82
  clear a82 e82 AD82 r82 c82 ip82 G82 A82 SP82 U82 FK82 CF82 F82_0 F82_1 F82_6 F82_7 F82_8 F82_9 F82_10
  clear u82
  obtain ⟨u84, a83, r84, c84, ip84, e83⟩ := run1 (adc_r64_r64_effect_step 0x101df5 0x4c 0xd1 (cf80 (words s)) (by unfold RexWPrefix; decide) (by decide))
    r83 c83 (program_text_slice c83 0x1df5 3 (by decide +kernel)) ⟨ip83, CF83⟩
    (q := 0x101df8) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e83 : (adcR64R64Effect 0x101df5 1 10 (cf80 (words s)) u83).Holds u83 u84 := e83
  have G84 := G83.step e83.agrees
  have A84 := acc_reg A83 e83.agrees (by simp [CS, callChanges])
  have U84 := U83.step e83.agrees (by simp [Component.isMem])
  have FK84 := FK83.step e83.agrees (by simp [Component.isMem])
  have SP84 : stackPtr u84 = frameStart s + BitVec.ofNat 64 0 := (e83.agrees.read (r := 4) (n := 64) (by simp)).trans SP83
  have F84_1 : (Operand.reg 1 : Operand 64).read u84 = q83 (words s) := by
    refine (e83.writes : (Operand.reg 1 : Operand 64).read u84 = _).trans ?_
    simp only [adcR64R64Effect, F83_1, F83_10, q83]
  have F84_0 := (e83.agrees.read (r := 0) (n := 64) (by simp)).trans F83_0
  have F84_2 := (e83.agrees.read (r := 2) (n := 64) (by simp)).trans F83_2
  have F84_6 := (e83.agrees.read (r := 6) (n := 64) (by simp)).trans F83_6
  have F84_7 := (e83.agrees.read (r := 7) (n := 64) (by simp)).trans F83_7
  have F84_8 := (e83.agrees.read (r := 8) (n := 64) (by simp)).trans F83_8
  have F84_9 := (e83.agrees.read (r := 9) (n := 64) (by simp)).trans F83_9
  have AD84 := AD83.trans a83
  clear a83 e83 AD83 r83 c83 ip83 G83 A83 SP83 U83 FK83 CF83 F83_0 F83_1 F83_2 F83_6 F83_7 F83_8 F83_9 F83_10
  clear u83
  obtain ⟨u85, a84, r85, c85, ip85, e84⟩ := run1 (mov_r32_r32_rex_effect_step 0x101df8 0x41 0xca (by unfold RexNoWPrefix; decide) (by decide))
    r84 c84 (program_text_slice c84 0x1df8 3 (by decide +kernel)) ip84
    (q := 0x101dfb) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e84 : (movR32R32Effect 0x101df8 3 10 1 u84).Holds u84 u85 := e84
  have G85 := G84.step e84.agrees
  have A85 := acc_reg A84 e84.agrees (by simp [CS, callChanges])
  have U85 := U84.step e84.agrees (by simp [Component.isMem])
  have FK85 := FK84.step e84.agrees (by simp [Component.isMem])
  have SP85 : stackPtr u85 = frameStart s + BitVec.ofNat 64 0 := (e84.agrees.read (r := 4) (n := 64) (by simp)).trans SP84
  have F85_10 : (Operand.reg 10 : Operand 64).read u85 = (v84 (words s)).setWidth 64 := by
    refine (e84.writes : (Operand.reg 10 : Operand 64).read u85 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F84_1, v84, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F85_0 := (e84.agrees.read (r := 0) (n := 64) (by simp)).trans F84_0
  have F85_1 := (e84.agrees.read (r := 1) (n := 64) (by simp)).trans F84_1
  have F85_2 := (e84.agrees.read (r := 2) (n := 64) (by simp)).trans F84_2
  have F85_6 := (e84.agrees.read (r := 6) (n := 64) (by simp)).trans F84_6
  have F85_7 := (e84.agrees.read (r := 7) (n := 64) (by simp)).trans F84_7
  have F85_8 := (e84.agrees.read (r := 8) (n := 64) (by simp)).trans F84_8
  have F85_9 := (e84.agrees.read (r := 9) (n := 64) (by simp)).trans F84_9
  have AD85 := AD84.trans a84
  clear a84 e84 AD84 r84 c84 ip84 G84 A84 SP84 U84 FK84 F84_0 F84_1 F84_2 F84_6 F84_7 F84_8 F84_9
  clear u84
  obtain ⟨u86, a85, r86, c86, ip86, e85⟩ := run1 (add_r64_r64_effect_step 0x101dfb 0x4c 0xca (by unfold RexWPrefix; decide) (by decide))
    r85 c85 (program_text_slice c85 0x1dfb 3 (by decide +kernel)) ip85
    (q := 0x101dfe) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e85 : (addR64R64Effect 0x101dfb 2 9 u85).Holds u85 u86 := e85
  have G86 := G85.step e85.agrees
  have A86 := acc_reg A85 e85.agrees (by simp [CS, callChanges])
  have U86 := U85.step e85.agrees (by simp [Component.isMem])
  have FK86 := FK85.step e85.agrees (by simp [Component.isMem])
  have SP86 : stackPtr u86 = frameStart s + BitVec.ofNat 64 0 := (e85.agrees.read (r := 4) (n := 64) (by simp)).trans SP85
  have F86_2 : (Operand.reg 2 : Operand 64).read u86 = q85 (words s) := by
    refine (e85.writes : (Operand.reg 2 : Operand 64).read u86 = _).trans ?_
    simp only [addR64R64Effect, F85_2, F85_9, q85]
  have F86_0 := (e85.agrees.read (r := 0) (n := 64) (by simp)).trans F85_0
  have F86_1 := (e85.agrees.read (r := 1) (n := 64) (by simp)).trans F85_1
  have F86_6 := (e85.agrees.read (r := 6) (n := 64) (by simp)).trans F85_6
  have F86_7 := (e85.agrees.read (r := 7) (n := 64) (by simp)).trans F85_7
  have F86_8 := (e85.agrees.read (r := 8) (n := 64) (by simp)).trans F85_8
  have F86_10 := (e85.agrees.read (r := 10) (n := 64) (by simp)).trans F85_10
  have AD86 := AD85.trans a85
  clear a85 e85 AD85 r85 c85 ip85 G85 A85 SP85 U85 FK85 F85_0 F85_1 F85_2 F85_6 F85_7 F85_8 F85_9 F85_10
  clear u85
  obtain ⟨u87, a86, r87, c87, ip87, e86⟩ := run1 (shr_r64_imm8_effect_step 0x101dfe 0x48 0xe9 0x20 (by unfold RexWPrefix; decide) (by decide) (by decide))
    r86 c86 (program_text_slice c86 0x1dfe 4 (by decide +kernel)) ip86
    (q := 0x101e02) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e86 : (shrR64Effect 0x101dfe 4 1 32 u86).Holds u86 u87 := e86
  have G87 := G86.step e86.agrees
  have A87 := acc_reg A86 e86.agrees (by simp [CS, callChanges])
  have U87 := U86.step e86.agrees (by simp [Component.isMem])
  have FK87 := FK86.step e86.agrees (by simp [Component.isMem])
  have SP87 : stackPtr u87 = frameStart s + BitVec.ofNat 64 0 := (e86.agrees.read (r := 4) (n := 64) (by simp)).trans SP86
  have F87_1 : (Operand.reg 1 : Operand 64).read u87 = q86 (words s) := by
    refine (e86.writes : (Operand.reg 1 : Operand 64).read u87 = _).trans ?_
    simp only [shrR64Effect, F86_1, q86]
  have F87_0 := (e86.agrees.read (r := 0) (n := 64) (by simp)).trans F86_0
  have F87_2 := (e86.agrees.read (r := 2) (n := 64) (by simp)).trans F86_2
  have F87_6 := (e86.agrees.read (r := 6) (n := 64) (by simp)).trans F86_6
  have F87_7 := (e86.agrees.read (r := 7) (n := 64) (by simp)).trans F86_7
  have F87_8 := (e86.agrees.read (r := 8) (n := 64) (by simp)).trans F86_8
  have F87_10 := (e86.agrees.read (r := 10) (n := 64) (by simp)).trans F86_10
  have AD87 := AD86.trans a86
  clear a86 e86 AD86 r86 c86 ip86 G86 A86 SP86 U86 FK86 F86_0 F86_1 F86_2 F86_6 F86_7 F86_8 F86_10
  clear u86
  obtain ⟨u88, a87, r88, c88, ip88, e87⟩ := run1 (add_r64_r64_effect_step 0x101e02 0x48 0xd1 (by unfold RexWPrefix; decide) (by decide))
    r87 c87 (program_text_slice c87 0x1e02 3 (by decide +kernel)) ip87
    (q := 0x101e05) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e87 : (addR64R64Effect 0x101e02 1 2 u87).Holds u87 u88 := e87
  have G88 := G87.step e87.agrees
  have A88 := acc_reg A87 e87.agrees (by simp [CS, callChanges])
  have U88 := U87.step e87.agrees (by simp [Component.isMem])
  have FK88 := FK87.step e87.agrees (by simp [Component.isMem])
  have SP88 : stackPtr u88 = frameStart s + BitVec.ofNat 64 0 := (e87.agrees.read (r := 4) (n := 64) (by simp)).trans SP87
  have F88_1 : (Operand.reg 1 : Operand 64).read u88 = q87 (words s) := by
    refine (e87.writes : (Operand.reg 1 : Operand 64).read u88 = _).trans ?_
    simp only [addR64R64Effect, F87_1, F87_2, q87]
  have F88_0 := (e87.agrees.read (r := 0) (n := 64) (by simp)).trans F87_0
  have F88_6 := (e87.agrees.read (r := 6) (n := 64) (by simp)).trans F87_6
  have F88_7 := (e87.agrees.read (r := 7) (n := 64) (by simp)).trans F87_7
  have F88_8 := (e87.agrees.read (r := 8) (n := 64) (by simp)).trans F87_8
  have F88_10 := (e87.agrees.read (r := 10) (n := 64) (by simp)).trans F87_10
  have AD88 := AD87.trans a87
  clear a87 e87 AD87 r87 c87 ip87 G87 A87 SP87 U87 FK87 F87_0 F87_1 F87_2 F87_6 F87_7 F87_8 F87_10
  clear u87
  obtain ⟨u89, a88, r89, c89, ip89, e88⟩ := run1 (add_r32_m32_effect_step 0x101e05 7 (.base 6 (.d8 0xc)) (by decide) (by decide) (by decide))
    r88 c88 (program_text_slice c88 0x1e05 3 (by decide +kernel)) ⟨ip88, memReadable_at (memReadable_grow hp.state G88) 0xc 4 (by decide) (by rw [addr6 F88_6]; rfl)⟩
    (q := 0x101e08) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e88 : (addR32M32Effect 0x101e05 3 7 (.base 6 (.d8 0xc)) u88).Holds u88 u89 := e88
  have G89 := G88.step e88.agrees
  have A89 := acc_reg A88 e88.agrees (by simp [CS, callChanges])
  have FK89 := FK88.step e88.agrees (by simp [Component.isMem])
  have SP89 : stackPtr u89 = frameStart s + BitVec.ofNat 64 0 := (e88.agrees.read (r := 4) (n := 64) (by simp)).trans SP88
  have F89_7 : (Operand.reg 7 : Operand 64).read u89 = (v88 (words s)).setWidth 64 := by
    refine (e88.writes : (Operand.reg 7 : Operand 64).read u89 = _).trans ?_
    simp only [addR32M32Effect, r32_eq, addr6 F88_6, load_word U88 hp.stateFrame (.d8 0xc) 0xc (by decide) (by decide), F88_7, v88, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F89_0 := (e88.agrees.read (r := 0) (n := 64) (by simp)).trans F88_0
  have F89_1 := (e88.agrees.read (r := 1) (n := 64) (by simp)).trans F88_1
  have F89_8 := (e88.agrees.read (r := 8) (n := 64) (by simp)).trans F88_8
  have F89_10 := (e88.agrees.read (r := 10) (n := 64) (by simp)).trans F88_10
  have AD89 := AD88.trans a88
  clear a88 e88 AD88 r88 c88 ip88 G88 A88 SP88 U88 FK88 F88_0 F88_1 F88_6 F88_7 F88_8 F88_10
  clear u88
  obtain ⟨u90, a89, r90, c90, ip90, e89⟩ := run1 (mov_r32_r32_effect_step 0x101e08 0xca (by decide))
    r89 c89 (program_text_slice c89 0x1e08 2 (by decide +kernel)) ip89
    (q := 0x101e0a) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e89 : (movR32R32Effect 0x101e08 2 2 1 u89).Holds u89 u90 := e89
  have G90 := G89.step e89.agrees
  have A90 := acc_reg A89 e89.agrees (by simp [CS, callChanges])
  have FK90 := FK89.step e89.agrees (by simp [Component.isMem])
  have SP90 : stackPtr u90 = frameStart s + BitVec.ofNat 64 0 := (e89.agrees.read (r := 4) (n := 64) (by simp)).trans SP89
  have F90_2 : (Operand.reg 2 : Operand 64).read u90 = (v89 (words s)).setWidth 64 := by
    refine (e89.writes : (Operand.reg 2 : Operand 64).read u90 = _).trans ?_
    simp only [movR32R32Effect, r32_eq, F89_1, v89, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F90_0 := (e89.agrees.read (r := 0) (n := 64) (by simp)).trans F89_0
  have F90_1 := (e89.agrees.read (r := 1) (n := 64) (by simp)).trans F89_1
  have F90_7 := (e89.agrees.read (r := 7) (n := 64) (by simp)).trans F89_7
  have F90_8 := (e89.agrees.read (r := 8) (n := 64) (by simp)).trans F89_8
  have F90_10 := (e89.agrees.read (r := 10) (n := 64) (by simp)).trans F89_10
  have AD90 := AD89.trans a89
  clear a89 e89 AD89 r89 c89 ip89 G89 A89 SP89 FK89 F89_0 F89_1 F89_7 F89_8 F89_10
  clear u89
  obtain ⟨u91, a90, r91, c91, ip91, e90⟩ := run1 (shr_r64_imm8_effect_step 0x101e0a 0x48 0xe9 0x20 (by unfold RexWPrefix; decide) (by decide) (by decide))
    r90 c90 (program_text_slice c90 0x1e0a 4 (by decide +kernel)) ip90
    (q := 0x101e0e) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e90 : (shrR64Effect 0x101e0a 4 1 32 u90).Holds u90 u91 := e90
  have G91 := G90.step e90.agrees
  have A91 := acc_reg A90 e90.agrees (by simp [CS, callChanges])
  have FK91 := FK90.step e90.agrees (by simp [Component.isMem])
  have SP91 : stackPtr u91 = frameStart s + BitVec.ofNat 64 0 := (e90.agrees.read (r := 4) (n := 64) (by simp)).trans SP90
  have F91_1 : (Operand.reg 1 : Operand 64).read u91 = q90 (words s) := by
    refine (e90.writes : (Operand.reg 1 : Operand 64).read u91 = _).trans ?_
    simp only [shrR64Effect, F90_1, q90]
  have F91_0 := (e90.agrees.read (r := 0) (n := 64) (by simp)).trans F90_0
  have F91_2 := (e90.agrees.read (r := 2) (n := 64) (by simp)).trans F90_2
  have F91_7 := (e90.agrees.read (r := 7) (n := 64) (by simp)).trans F90_7
  have F91_8 := (e90.agrees.read (r := 8) (n := 64) (by simp)).trans F90_8
  have F91_10 := (e90.agrees.read (r := 10) (n := 64) (by simp)).trans F90_10
  have AD91 := AD90.trans a90
  clear a90 e90 AD90 r90 c90 ip90 G90 A90 SP90 FK90 F90_0 F90_1 F90_2 F90_7 F90_8 F90_10
  clear u90
  obtain ⟨u92, a91, r92, c92, ip92, e91⟩ := run1 (add_r32_r32_effect_step 0x101e0e 0xf9 (by decide))
    r91 c91 (program_text_slice c91 0x1e0e 2 (by decide +kernel)) ip91
    (q := 0x101e10) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e91 : (addR32R32Effect 0x101e0e 2 1 7 u91).Holds u91 u92 := e91
  have G92 := G91.step e91.agrees
  have A92 := acc_reg A91 e91.agrees (by simp [CS, callChanges])
  have FK92 := FK91.step e91.agrees (by simp [Component.isMem])
  have SP92 : stackPtr u92 = frameStart s + BitVec.ofNat 64 0 := (e91.agrees.read (r := 4) (n := 64) (by simp)).trans SP91
  have F92_1 : (Operand.reg 1 : Operand 64).read u92 = (v91 (words s)).setWidth 64 := by
    refine (e91.writes : (Operand.reg 1 : Operand 64).read u92 = _).trans ?_
    simp only [addR32R32Effect, r32_eq, F91_1, F91_7, v91, sw_sw, words_h0, words_h1, words_h2, words_h3, words_h4, words_p0, words_p1, words_p2, words_p3]
  have F92_0 := (e91.agrees.read (r := 0) (n := 64) (by simp)).trans F91_0
  have F92_2 := (e91.agrees.read (r := 2) (n := 64) (by simp)).trans F91_2
  have F92_8 := (e91.agrees.read (r := 8) (n := 64) (by simp)).trans F91_8
  have F92_10 := (e91.agrees.read (r := 10) (n := 64) (by simp)).trans F91_10
  have AD92 := AD91.trans a91
  clear a91 e91 AD91 r91 c91 ip91 G91 A91 SP91 FK91 F91_0 F91_1 F91_2 F91_7 F91_8 F91_10
  clear u91
  obtain ⟨u93, a92, r93, c93, ip93, e92⟩ := run1 (mov_m32_r32_effect_step 0x101e10 0x44 (by unfold RexNoWPrefix; decide) 0 (.base 0 .none) (by decide) (by decide) (by decide))
    r92 c92 (program_text_slice c92 0x1e10 3 (by decide +kernel)) ⟨ip92, memWritable_at (memWritable_grow hOW G92) 0 4 (by decide) (by simp only [storeAddrAt, addr0 F92_0, dv_none]), apart_at hp.output 0 4 (by decide) (by simp only [storeAddrAt, addr0 F92_0, dv_none]) (code_at _ 0x1e10 3 (by decide) (by decide +kernel))⟩
    (q := 0x101e13) rfl (hne _ (by decide) (by decide)) (mem_avoids store_comps hp.output 0 (by simp only [storeAddrAt, addr0 F92_0, dv_none]) (by decide))
  replace e92 : (movM32R32Effect 0x101e10 8 (.base 0 .none) u92).Holds u92 u93 := e92
  have G93 := G92.step e92.agrees
  have A93 := acc_store A92 e92 store_comps 0 (by simp only [storeAddrAt, addr0 F92_0, dv_none]) (by decide)
  have FK93 := FK92.store store_comps e92 0 (by simp only [storeAddrAt, addr0 F92_0, dv_none]) (by decide) hp.outputFrame
  have SP93 : stackPtr u93 = frameStart s + BitVec.ofNat 64 0 := (e92.agrees.read (r := 4) (n := 64) (by simp [movM32R32Effect, storeEffect_components])).trans SP92
  have O0_93 : (Operand.mem (rdi.read s + BitVec.ofNat 64 0) : Operand 32).read u93 = v80 (words s) := by
    have h := store_fact e92 rfl
    simp only [storeAddrAt, addr0 F92_0, dv_none, r32_eq, F92_8, sw_sw] at h
    exact h
  have F93_0 := (e92.agrees.read (r := 0) (n := 64) (by simp [movM32R32Effect, storeEffect_components])).trans F92_0
  have F93_1 := (e92.agrees.read (r := 1) (n := 64) (by simp [movM32R32Effect, storeEffect_components])).trans F92_1
  have F93_2 := (e92.agrees.read (r := 2) (n := 64) (by simp [movM32R32Effect, storeEffect_components])).trans F92_2
  have F93_10 := (e92.agrees.read (r := 10) (n := 64) (by simp [movM32R32Effect, storeEffect_components])).trans F92_10
  have AD93 := AD92.trans a92
  clear a92 e92 AD92 r92 c92 ip92 G92 A92 SP92 FK92 F92_0 F92_1 F92_2 F92_8 F92_10
  clear u92
  obtain ⟨u94, a93, r94, c94, ip94, e93⟩ := run1 (mov_m32_r32_effect_step 0x101e13 0x44 (by unfold RexNoWPrefix; decide) 2 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide))
    r93 c93 (program_text_slice c93 0x1e13 4 (by decide +kernel)) ⟨ip93, memWritable_at (memWritable_grow hOW G93) 4 4 (by decide) (by simp only [storeAddrAt, addr0 F93_0, dv_4]), apart_at hp.output 4 4 (by decide) (by simp only [storeAddrAt, addr0 F93_0, dv_4]) (code_at _ 0x1e13 4 (by decide) (by decide +kernel))⟩
    (q := 0x101e17) rfl (hne _ (by decide) (by decide)) (mem_avoids store_comps hp.output 4 (by simp only [storeAddrAt, addr0 F93_0, dv_4]) (by decide))
  replace e93 : (movM32R32Effect 0x101e13 10 (.base 0 (.d8 0x4)) u93).Holds u93 u94 := e93
  have G94 := G93.step e93.agrees
  have A94 := acc_store A93 e93 store_comps 4 (by simp only [storeAddrAt, addr0 F93_0, dv_4]) (by decide)
  have FK94 := FK93.store store_comps e93 4 (by simp only [storeAddrAt, addr0 F93_0, dv_4]) (by decide) hp.outputFrame
  have O0_94 := (out_keep store_comps e93 4 0 (by simp only [storeAddrAt, addr0 F93_0, dv_4]) (by decide) (by decide) (by decide)).trans O0_93
  have SP94 : stackPtr u94 = frameStart s + BitVec.ofNat 64 0 := (e93.agrees.read (r := 4) (n := 64) (by simp [movM32R32Effect, storeEffect_components])).trans SP93
  have O4_94 : (Operand.mem (rdi.read s + BitVec.ofNat 64 4) : Operand 32).read u94 = v84 (words s) := by
    have h := store_fact e93 rfl
    simp only [storeAddrAt, addr0 F93_0, dv_4, r32_eq, F93_10, sw_sw] at h
    exact h
  have F94_0 := (e93.agrees.read (r := 0) (n := 64) (by simp [movM32R32Effect, storeEffect_components])).trans F93_0
  have F94_1 := (e93.agrees.read (r := 1) (n := 64) (by simp [movM32R32Effect, storeEffect_components])).trans F93_1
  have F94_2 := (e93.agrees.read (r := 2) (n := 64) (by simp [movM32R32Effect, storeEffect_components])).trans F93_2
  have AD94 := AD93.trans a93
  clear a93 e93 AD93 r93 c93 ip93 G93 A93 SP93 FK93 F93_0 F93_1 F93_2 F93_10 O0_93
  clear u93
  obtain ⟨u95, a94, r95, c95, ip95, e94⟩ := run1 (mov_m32_r32_low_effect_step 0x101e17 2 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide))
    r94 c94 (program_text_slice c94 0x1e17 3 (by decide +kernel)) ⟨ip94, memWritable_at (memWritable_grow hOW G94) 8 4 (by decide) (by simp only [storeAddrAt, addr0 F94_0, dv_8]), apart_at hp.output 8 4 (by decide) (by simp only [storeAddrAt, addr0 F94_0, dv_8]) (code_at _ 0x1e17 3 (by decide) (by decide +kernel))⟩
    (q := 0x101e1a) rfl (hne _ (by decide) (by decide)) (mem_avoids store_comps hp.output 8 (by simp only [storeAddrAt, addr0 F94_0, dv_8]) (by decide))
  replace e94 : (movM32R32LowEffect 0x101e17 2 (.base 0 (.d8 0x8)) u94).Holds u94 u95 := e94
  have G95 := G94.step e94.agrees
  have A95 := acc_store A94 e94 store_comps 8 (by simp only [storeAddrAt, addr0 F94_0, dv_8]) (by decide)
  have FK95 := FK94.store store_comps e94 8 (by simp only [storeAddrAt, addr0 F94_0, dv_8]) (by decide) hp.outputFrame
  have O0_95 := (out_keep store_comps e94 8 0 (by simp only [storeAddrAt, addr0 F94_0, dv_8]) (by decide) (by decide) (by decide)).trans O0_94
  have O4_95 := (out_keep store_comps e94 8 4 (by simp only [storeAddrAt, addr0 F94_0, dv_8]) (by decide) (by decide) (by decide)).trans O4_94
  have SP95 : stackPtr u95 = frameStart s + BitVec.ofNat 64 0 := (e94.agrees.read (r := 4) (n := 64) (by simp [movM32R32LowEffect, storeEffect_components])).trans SP94
  have O8_95 : (Operand.mem (rdi.read s + BitVec.ofNat 64 8) : Operand 32).read u95 = v89 (words s) := by
    have h := store_fact e94 rfl
    simp only [storeAddrAt, addr0 F94_0, dv_8, r32_eq, F94_2, sw_sw] at h
    exact h
  have F95_0 := (e94.agrees.read (r := 0) (n := 64) (by simp [movM32R32LowEffect, storeEffect_components])).trans F94_0
  have F95_1 := (e94.agrees.read (r := 1) (n := 64) (by simp [movM32R32LowEffect, storeEffect_components])).trans F94_1
  have AD95 := AD94.trans a94
  clear a94 e94 AD94 r94 c94 ip94 G94 A94 SP94 FK94 F94_0 F94_1 F94_2 O0_94 O4_94
  clear u94
  obtain ⟨u96, a95, r96, c96, ip96, e95⟩ := run1 (mov_m32_r32_low_effect_step 0x101e1a 1 (.base 0 (.d8 0xc)) (by decide) (by decide) (by decide))
    r95 c95 (program_text_slice c95 0x1e1a 3 (by decide +kernel)) ⟨ip95, memWritable_at (memWritable_grow hOW G95) 12 4 (by decide) (by simp only [storeAddrAt, addr0 F95_0, dv_c]), apart_at hp.output 12 4 (by decide) (by simp only [storeAddrAt, addr0 F95_0, dv_c]) (code_at _ 0x1e1a 3 (by decide) (by decide +kernel))⟩
    (q := 0x101e1d) rfl (hne _ (by decide) (by decide)) (mem_avoids store_comps hp.output 12 (by simp only [storeAddrAt, addr0 F95_0, dv_c]) (by decide))
  replace e95 : (movM32R32LowEffect 0x101e1a 1 (.base 0 (.d8 0xc)) u95).Holds u95 u96 := e95
  have G96 := G95.step e95.agrees
  have A96 := acc_store A95 e95 store_comps 12 (by simp only [storeAddrAt, addr0 F95_0, dv_c]) (by decide)
  have FK96 := FK95.store store_comps e95 12 (by simp only [storeAddrAt, addr0 F95_0, dv_c]) (by decide) hp.outputFrame
  have O0_96 := (out_keep store_comps e95 12 0 (by simp only [storeAddrAt, addr0 F95_0, dv_c]) (by decide) (by decide) (by decide)).trans O0_95
  have O4_96 := (out_keep store_comps e95 12 4 (by simp only [storeAddrAt, addr0 F95_0, dv_c]) (by decide) (by decide) (by decide)).trans O4_95
  have O8_96 := (out_keep store_comps e95 12 8 (by simp only [storeAddrAt, addr0 F95_0, dv_c]) (by decide) (by decide) (by decide)).trans O8_95
  have SP96 : stackPtr u96 = frameStart s + BitVec.ofNat 64 0 := (e95.agrees.read (r := 4) (n := 64) (by simp [movM32R32LowEffect, storeEffect_components])).trans SP95
  have O12_96 : (Operand.mem (rdi.read s + BitVec.ofNat 64 12) : Operand 32).read u96 = v91 (words s) := by
    have h := store_fact e95 rfl
    simp only [storeAddrAt, addr0 F95_0, dv_c, r32_eq, F95_1, sw_sw] at h
    exact h
  have F96_0 := (e95.agrees.read (r := 0) (n := 64) (by simp [movM32R32LowEffect, storeEffect_components])).trans F95_0
  have AD96 := AD95.trans a95
  clear a95 e95 AD95 r95 c95 ip95 G95 A95 SP95 FK95 F95_0 F95_1 O0_95 O4_95 O8_95
  clear u95
  obtain ⟨u97, a96, r97, c97, ip97, e96⟩ := run1 (pop_r64_effect_step 0x101e1d 0x5b (by decide) (by decide))
    r96 c96 (program_text_slice c96 0x1e1d 1 (by decide +kernel)) ⟨ip96, memReadable_at (memReadable_grow hp.frame.readable G96) 0 8 (by decide) SP96⟩
    (q := 0x101e1e) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e96 : (popR64Effect 0x101e1d 1 3 u96).Holds u96 u97 := e96
  have G97 := G96.step e96.agrees
  have A97 := acc_reg A96 e96.agrees (by simp [CS, callChanges])
  have FK97 := FK96.step e96.agrees (by simp [Component.isMem])
  have O0_97 := (out_keep_reg e96.agrees (by simp [Component.isMem]) _).trans O0_96
  have O4_97 := (out_keep_reg e96.agrees (by simp [Component.isMem]) _).trans O4_96
  have O8_97 := (out_keep_reg e96.agrees (by simp [Component.isMem]) _).trans O8_96
  have O12_97 := (out_keep_reg e96.agrees (by simp [Component.isMem]) _).trans O12_96
  have F97_3 : (Operand.reg 3 : Operand 64).read u97 = (Operand.reg 3 : Operand 64).read s := by
    refine (e96.writes.1 : (Operand.reg 3 : Operand 64).read u97 = _).trans ?_
    rw [SP96, FK96.read64 0 (by decide)]; exact S5_6
  have SP97 : stackPtr u97 = frameStart s + BitVec.ofNat 64 8 := by
    rw [stackPtr_eq_read]; refine (e96.writes.2 : (Operand.reg 4 : Operand 64).read u97 = _).trans ?_; rw [SP96]; bv_omega
  have F97_0 := (e96.agrees.read (r := 0) (n := 64) (by simp)).trans F96_0
  have AD97 := AD96.trans a96
  clear a96 e96 AD96 r96 c96 ip96 G96 A96 SP96 FK96 F96_0 O0_96 O4_96 O8_96 O12_96
  clear u96
  obtain ⟨u98, a97, r98, c98, ip98, e97⟩ := run1 (pop_r64_rex_effect_step 0x101e1e 0x41 0x5c (by unfold RexPrefix; decide) (by decide) (by decide))
    r97 c97 (program_text_slice c97 0x1e1e 2 (by decide +kernel)) ⟨ip97, memReadable_at (memReadable_grow hp.frame.readable G97) 8 8 (by decide) SP97⟩
    (q := 0x101e20) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e97 : (popR64Effect 0x101e1e 2 12 u97).Holds u97 u98 := e97
  have G98 := G97.step e97.agrees
  have A98 := acc_reg A97 e97.agrees (by simp [CS, callChanges])
  have FK98 := FK97.step e97.agrees (by simp [Component.isMem])
  have O0_98 := (out_keep_reg e97.agrees (by simp [Component.isMem]) _).trans O0_97
  have O4_98 := (out_keep_reg e97.agrees (by simp [Component.isMem]) _).trans O4_97
  have O8_98 := (out_keep_reg e97.agrees (by simp [Component.isMem]) _).trans O8_97
  have O12_98 := (out_keep_reg e97.agrees (by simp [Component.isMem]) _).trans O12_97
  have F98_12 : (Operand.reg 12 : Operand 64).read u98 = (Operand.reg 12 : Operand 64).read s := by
    refine (e97.writes.1 : (Operand.reg 12 : Operand 64).read u98 = _).trans ?_
    rw [SP97, FK97.read64 8 (by decide)]; exact S4_6
  have SP98 : stackPtr u98 = frameStart s + BitVec.ofNat 64 16 := by
    rw [stackPtr_eq_read]; refine (e97.writes.2 : (Operand.reg 4 : Operand 64).read u98 = _).trans ?_; rw [SP97]; bv_omega
  have F98_0 := (e97.agrees.read (r := 0) (n := 64) (by simp)).trans F97_0
  have F98_3 := (e97.agrees.read (r := 3) (n := 64) (by simp)).trans F97_3
  have AD98 := AD97.trans a97
  clear a97 e97 AD97 r97 c97 ip97 G97 A97 SP97 FK97 F97_0 F97_3 O0_97 O4_97 O8_97 O12_97
  clear u97
  obtain ⟨u99, a98, r99, c99, ip99, e98⟩ := run1 (pop_r64_rex_effect_step 0x101e20 0x41 0x5d (by unfold RexPrefix; decide) (by decide) (by decide))
    r98 c98 (program_text_slice c98 0x1e20 2 (by decide +kernel)) ⟨ip98, memReadable_at (memReadable_grow hp.frame.readable G98) 16 8 (by decide) SP98⟩
    (q := 0x101e22) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e98 : (popR64Effect 0x101e20 2 13 u98).Holds u98 u99 := e98
  have G99 := G98.step e98.agrees
  have A99 := acc_reg A98 e98.agrees (by simp [CS, callChanges])
  have FK99 := FK98.step e98.agrees (by simp [Component.isMem])
  have O0_99 := (out_keep_reg e98.agrees (by simp [Component.isMem]) _).trans O0_98
  have O4_99 := (out_keep_reg e98.agrees (by simp [Component.isMem]) _).trans O4_98
  have O8_99 := (out_keep_reg e98.agrees (by simp [Component.isMem]) _).trans O8_98
  have O12_99 := (out_keep_reg e98.agrees (by simp [Component.isMem]) _).trans O12_98
  have F99_13 : (Operand.reg 13 : Operand 64).read u99 = (Operand.reg 13 : Operand 64).read s := by
    refine (e98.writes.1 : (Operand.reg 13 : Operand 64).read u99 = _).trans ?_
    rw [SP98, FK98.read64 16 (by decide)]; exact S3_6
  have SP99 : stackPtr u99 = frameStart s + BitVec.ofNat 64 24 := by
    rw [stackPtr_eq_read]; refine (e98.writes.2 : (Operand.reg 4 : Operand 64).read u99 = _).trans ?_; rw [SP98]; bv_omega
  have F99_0 := (e98.agrees.read (r := 0) (n := 64) (by simp)).trans F98_0
  have F99_3 := (e98.agrees.read (r := 3) (n := 64) (by simp)).trans F98_3
  have F99_12 := (e98.agrees.read (r := 12) (n := 64) (by simp)).trans F98_12
  have AD99 := AD98.trans a98
  clear a98 e98 AD98 r98 c98 ip98 G98 A98 SP98 FK98 F98_0 F98_3 F98_12 O0_98 O4_98 O8_98 O12_98
  clear u98
  obtain ⟨u100, a99, r100, c100, ip100, e99⟩ := run1 (pop_r64_rex_effect_step 0x101e22 0x41 0x5e (by unfold RexPrefix; decide) (by decide) (by decide))
    r99 c99 (program_text_slice c99 0x1e22 2 (by decide +kernel)) ⟨ip99, memReadable_at (memReadable_grow hp.frame.readable G99) 24 8 (by decide) SP99⟩
    (q := 0x101e24) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e99 : (popR64Effect 0x101e22 2 14 u99).Holds u99 u100 := e99
  have G100 := G99.step e99.agrees
  have A100 := acc_reg A99 e99.agrees (by simp [CS, callChanges])
  have FK100 := FK99.step e99.agrees (by simp [Component.isMem])
  have O0_100 := (out_keep_reg e99.agrees (by simp [Component.isMem]) _).trans O0_99
  have O4_100 := (out_keep_reg e99.agrees (by simp [Component.isMem]) _).trans O4_99
  have O8_100 := (out_keep_reg e99.agrees (by simp [Component.isMem]) _).trans O8_99
  have O12_100 := (out_keep_reg e99.agrees (by simp [Component.isMem]) _).trans O12_99
  have F100_14 : (Operand.reg 14 : Operand 64).read u100 = (Operand.reg 14 : Operand 64).read s := by
    refine (e99.writes.1 : (Operand.reg 14 : Operand 64).read u100 = _).trans ?_
    rw [SP99, FK99.read64 24 (by decide)]; exact S2_6
  have SP100 : stackPtr u100 = frameStart s + BitVec.ofNat 64 32 := by
    rw [stackPtr_eq_read]; refine (e99.writes.2 : (Operand.reg 4 : Operand 64).read u100 = _).trans ?_; rw [SP99]; bv_omega
  have F100_0 := (e99.agrees.read (r := 0) (n := 64) (by simp)).trans F99_0
  have F100_3 := (e99.agrees.read (r := 3) (n := 64) (by simp)).trans F99_3
  have F100_12 := (e99.agrees.read (r := 12) (n := 64) (by simp)).trans F99_12
  have F100_13 := (e99.agrees.read (r := 13) (n := 64) (by simp)).trans F99_13
  have AD100 := AD99.trans a99
  clear a99 e99 AD99 r99 c99 ip99 G99 A99 SP99 FK99 F99_0 F99_3 F99_12 F99_13 O0_99 O4_99 O8_99 O12_99
  clear u99
  obtain ⟨u101, a100, r101, c101, ip101, e100⟩ := run1 (pop_r64_rex_effect_step 0x101e24 0x41 0x5f (by unfold RexPrefix; decide) (by decide) (by decide))
    r100 c100 (program_text_slice c100 0x1e24 2 (by decide +kernel)) ⟨ip100, memReadable_at (memReadable_grow hp.frame.readable G100) 32 8 (by decide) SP100⟩
    (q := 0x101e26) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e100 : (popR64Effect 0x101e24 2 15 u100).Holds u100 u101 := e100
  have G101 := G100.step e100.agrees
  have A101 := acc_reg A100 e100.agrees (by simp [CS, callChanges])
  have FK101 := FK100.step e100.agrees (by simp [Component.isMem])
  have O0_101 := (out_keep_reg e100.agrees (by simp [Component.isMem]) _).trans O0_100
  have O4_101 := (out_keep_reg e100.agrees (by simp [Component.isMem]) _).trans O4_100
  have O8_101 := (out_keep_reg e100.agrees (by simp [Component.isMem]) _).trans O8_100
  have O12_101 := (out_keep_reg e100.agrees (by simp [Component.isMem]) _).trans O12_100
  have F101_15 : (Operand.reg 15 : Operand 64).read u101 = (Operand.reg 15 : Operand 64).read s := by
    refine (e100.writes.1 : (Operand.reg 15 : Operand 64).read u101 = _).trans ?_
    rw [SP100, FK100.read64 32 (by decide)]; exact S1_6
  have SP101 : stackPtr u101 = frameStart s + BitVec.ofNat 64 40 := by
    rw [stackPtr_eq_read]; refine (e100.writes.2 : (Operand.reg 4 : Operand 64).read u101 = _).trans ?_; rw [SP100]; bv_omega
  have F101_0 := (e100.agrees.read (r := 0) (n := 64) (by simp)).trans F100_0
  have F101_3 := (e100.agrees.read (r := 3) (n := 64) (by simp)).trans F100_3
  have F101_12 := (e100.agrees.read (r := 12) (n := 64) (by simp)).trans F100_12
  have F101_13 := (e100.agrees.read (r := 13) (n := 64) (by simp)).trans F100_13
  have F101_14 := (e100.agrees.read (r := 14) (n := 64) (by simp)).trans F100_14
  have AD101 := AD100.trans a100
  clear a100 e100 AD100 r100 c100 ip100 G100 A100 SP100 FK100 F100_0 F100_3 F100_12 F100_13 F100_14 O0_100 O4_100 O8_100 O12_100
  clear u100
  obtain ⟨u102, a101, r102, c102, ip102, e101⟩ := run1 (pop_r64_effect_step 0x101e26 0x5d (by decide) (by decide))
    r101 c101 (program_text_slice c101 0x1e26 1 (by decide +kernel)) ⟨ip101, memReadable_at (memReadable_grow hp.frame.readable G101) 40 8 (by decide) SP101⟩
    (q := 0x101e27) rfl (hne _ (by decide) (by decide)) (noMem_avoids (by simp [Component.isMem]))
  replace e101 : (popR64Effect 0x101e26 1 5 u101).Holds u101 u102 := e101
  have G102 := G101.step e101.agrees
  have A102 := acc_reg A101 e101.agrees (by simp [CS, callChanges])
  have FK102 := FK101.step e101.agrees (by simp [Component.isMem])
  have O0_102 := (out_keep_reg e101.agrees (by simp [Component.isMem]) _).trans O0_101
  have O4_102 := (out_keep_reg e101.agrees (by simp [Component.isMem]) _).trans O4_101
  have O8_102 := (out_keep_reg e101.agrees (by simp [Component.isMem]) _).trans O8_101
  have O12_102 := (out_keep_reg e101.agrees (by simp [Component.isMem]) _).trans O12_101
  have F102_5 : (Operand.reg 5 : Operand 64).read u102 = (Operand.reg 5 : Operand 64).read s := by
    refine (e101.writes.1 : (Operand.reg 5 : Operand 64).read u102 = _).trans ?_
    rw [SP101, FK101.read64 40 (by decide)]; exact S0_6
  have SP102 : stackPtr u102 = frameStart s + BitVec.ofNat 64 48 := by
    rw [stackPtr_eq_read]; refine (e101.writes.2 : (Operand.reg 4 : Operand 64).read u102 = _).trans ?_; rw [SP101]; bv_omega
  have F102_0 := (e101.agrees.read (r := 0) (n := 64) (by simp)).trans F101_0
  have F102_3 := (e101.agrees.read (r := 3) (n := 64) (by simp)).trans F101_3
  have F102_12 := (e101.agrees.read (r := 12) (n := 64) (by simp)).trans F101_12
  have F102_13 := (e101.agrees.read (r := 13) (n := 64) (by simp)).trans F101_13
  have F102_14 := (e101.agrees.read (r := 14) (n := 64) (by simp)).trans F101_14
  have F102_15 := (e101.agrees.read (r := 15) (n := 64) (by simp)).trans F101_15
  have AD102 := AD101.trans a101
  clear a101 e101 AD101 r101 c101 ip101 G101 A101 SP101 FK101 F101_0 F101_3 F101_12 F101_13 F101_14 F101_15 O0_101 O4_101 O8_101 O12_101
  clear u101
  refine ⟨_, u102, AD102, r102, c102, ip102, ?_, ?_, ?_, F102_0, ?_, G102, O0_102, O4_102, O8_102, O12_102⟩
  · rw [SP102, SP0]
  · rw [SP102, ← SP0]; exact memReadable_grow hp.returnSlot G102
  · rw [SP102, FK102.read64 48 (by decide), ret_slot_untouched U6, ← SP0]; rfl
  · exact finish_agrees A102 F102_3 F102_5 F102_12 F102_13 F102_14 F102_15

theorem tn_and (x : BitVec 32) : (x &&& (0x3ffffff : BitVec 32).signExtend 32).toNat = x.toNat % 2^26 := by
  rw [show (0x3ffffff : BitVec 32).signExtend 32 = (0x3ffffff : BitVec 32) by decide, BitVec.toNat_and]
  rw [show (0x3ffffff : BitVec 32).toNat = 2^26 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
theorem tn_shr (x : BitVec 32) (k : Nat) : (x >>> k).toNat = x.toNat / 2^k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
theorem tn_shl (x : BitVec 32) (k : Nat) : (x <<< k).toNat = x.toNat * 2^k % 2^32 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
theorem tn_add (x y : BitVec 32) : (x + y).toNat = (x.toNat + y.toNat) % 2^32 := BitVec.toNat_add x y
theorem tn_add64 (x y : BitVec 64) : (x + y).toNat = (x.toNat + y.toNat) % 2^64 := BitVec.toNat_add x y
theorem tn_sw (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp; have := x.isLt; omega
theorem tn_sw32 (x : BitVec 64) : (x.setWidth 32).toNat = x.toNat % 2^32 := by simp
theorem tn_shr64 (x : BitVec 64) (k : Nat) : (x >>> k).toNat = x.toNat / 2^k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
theorem tn_c (x y : BitVec 32) :
    (decide ((x + y).toNat ≠ x.toNat + y.toNat)).toNat = (x.toNat + y.toNat) / 2^32 := by
  rw [BitVec.toNat_add]
  have hx := x.isLt; have hy := y.isLt
  by_cases h : x.toNat + y.toNat < 2^32
  · rw [Nat.mod_eq_of_lt h, decide_eq_false (by omega)]
    simp; omega
  · rw [decide_eq_true (by omega)]
    simp; omega
theorem tn_ofNatBool (b : Bool) : (BitVec.ofNat 64 b.toNat).toNat = b.toNat := by
  cases b <;> simp
theorem sshift31 (y : BitVec 32) (h : 2^31 ≤ y.toNat) : y.sshiftRight 31 = -1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hm : y.msb = true := by rw [BitVec.msb_eq_decide]; simpa using h
  rw [BitVec.getLsbD_sshiftRight]
  have : (-1 : BitVec 32) = BitVec.allOnes 32 := by decide
  rw [this, BitVec.getLsbD_allOnes]
  by_cases h0 : i = 0
  · subst h0; rw [BitVec.msb_eq_getLsbD_last] at hm; simpa using hm
  · simp [hi, hm]; omega
theorem sshift31' (y : BitVec 32) (h : y.toNat < 2^31) : y.sshiftRight 31 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hm : y.msb = false := by rw [BitVec.msb_eq_decide]; simpa using h
  rw [BitVec.getLsbD_sshiftRight]
  by_cases h0 : i = 0
  · subst h0; rw [BitVec.msb_eq_getLsbD_last] at hm; simpa using hm
  · simp [hi, hm]; omega
theorem or_shl_toNat (a b : BitVec 32) (k : Nat) (hk : k ≤ 32) (hb : b.toNat < 2^k) :
    ((a <<< k) ||| b).toNat = (a.toNat % 2^(32-k)) * 2^k + b.toNat := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft]
  have h1 : (a.toNat <<< k) % 2^32 = (a.toNat % 2^(32-k)) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    have : 2^32 = 2^(32-k) * 2^k := by rw [← Nat.pow_add]; congr 1; omega
    rw [this, Nat.mul_mod_mul_right]
  rw [h1, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]
theorem or_shr_toNat (a b : BitVec 32) (k j : Nat) (hk : k ≤ 32) (hb : b.toNat / 2^j < 2^k) :
    ((a <<< k) ||| (b >>> j)).toNat = (a.toNat % 2^(32-k)) * 2^k + b.toNat / 2^j := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  have h1 : (a.toNat <<< k) % 2^32 = (a.toNat % 2^(32-k)) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    have : 2^32 = 2^(32-k) * 2^k := by rw [← Nat.pow_add]; congr 1; omega
    rw [this, Nat.mul_mod_mul_right]
  rw [h1, Nat.shiftRight_eq_div_pow, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]

theorem pack_nat (x0 x1 x2 x3 x4 p0 p1 p2 p3 : Nat) :
    let w0 := (x1 % 2^6) * 2^26 + x0
    let w1 := (x2 % 2^12) * 2^20 + x1 / 2^6
    let w2 := (x3 % 2^18) * 2^14 + x2 / 2^12
    let w3 := (x4 % 2^24) * 2^8 + x3 / 2^18
    let r := p1 + w1 + (w0 + p0) / 2^32
    let q := r / 2^32 + (p2 + w2)
    let N := x0 + 2^26 * x1 + 2^52 * x2 + 2^78 * x3 + 2^104 * x4 + (p0 + 2^32 * p1 + 2^64 * p2 + 2^96 * p3)
    (w0 + p0) % 2^32 = N % 2^32 ∧ r % 2^32 = N / 2^32 % 2^32 ∧ q % 2^32 = N / 2^64 % 2^32 ∧
    (q / 2^32 + (w3 + p3) % 2^32) % 2^32 = N / 2^96 % 2^32 := by
  intro w0 w1 w2 w3 r q N
  omega

theorem tn_sub (x y : BitVec 32) : (x - y).toNat = (2^32 - y.toNat + x.toNat) % 2^32 := BitVec.toNat_sub x y

theorem tn_and' (x y : BitVec 32) : (x &&& y).toNat = x.toNat &&& y.toNat := BitVec.toNat_and x y
theorem tn_or' (x y : BitVec 32) : (x ||| y).toNat = x.toNat ||| y.toNat := BitVec.toNat_or x y

theorem nand_ones (x : Nat) (hx : x < 2^32) : x &&& (2^32 - 1) = x := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]
theorem nand_ones' (x : Nat) (hx : x < 2^32) : (2^32 - 1) &&& x = x := by
  rw [Nat.and_comm, nand_ones x hx]
theorem nand_m (x : Nat) : x &&& (2^26 - 1) = x % 2^26 := Nat.and_two_pow_sub_one_eq_mod x 26
theorem nand_m' (x : Nat) : (2^26 - 1) &&& x = x % 2^26 := by rw [Nat.and_comm, nand_m]

def T2 (w : Words) : Nat := w.h1.toNat / 2^26 + w.h2.toNat
def T3 (w : Words) : Nat := T2 w / 2^26 + w.h3.toNat
def T4 (w : Words) : Nat := T3 w / 2^26 + w.h4.toNat
def T0 (w : Words) : Nat := 5 * (T4 w / 2^26) + w.h0.toNat
def A1 (w : Words) : Nat := T0 w / 2^26 + w.h1.toNat % 2^26
def G0 (w : Words) : Nat := T0 w % 2^26 + 5
def G1 (w : Words) : Nat := G0 w / 2^26 + A1 w
def G2 (w : Words) : Nat := G1 w / 2^26 + T2 w % 2^26
def G3 (w : Words) : Nat := G2 w / 2^26 + T3 w % 2^26
def U (w : Words) : Nat := G3 w / 2^26 + T4 w % 2^26
def Hv (w : Words) : Nat := w.h0.toNat + 2^26 * w.h1.toNat + 2^52 * w.h2.toNat +
  2^78 * w.h3.toNat + 2^104 * w.h4.toNat
def Pv (w : Words) : Nat := w.p0.toNat + 2^32 * w.p1.toNat + 2^64 * w.p2.toNat + 2^96 * w.p3.toNat

structure Bounded (w : Words) : Prop where
  b0 : w.h0.toNat < 2^26
  b1 : w.h1.toNat < 2^26 + 2^6
  b2 : w.h2.toNat < 2^26
  b3 : w.h3.toNat < 2^26
  b4 : w.h4.toNat < 2^26

theorem bnds {w : Words} (h : Bounded w) : T2 w < 2^26 + 2 ∧ T3 w < 2^26 + 1 ∧ T4 w < 2^26 + 1 ∧
    T4 w / 2^26 < 2 ∧ T0 w < 2^26 + 10 ∧ A1 w < 2^26 + 2 ∧ G0 w < 2^26 + 5 ∧ G1 w < 2^27 ∧
    G2 w < 2^27 ∧ G3 w < 2^27 ∧ U w < 2^27 := by
  have := h.b0; have := h.b1; have := h.b2; have := h.b3; have := h.b4
  simp only [U, G3, G2, G1, G0, A1, T0, T4, T3, T2]
  omega

theorem fin_defs {w : Words} (h : Bounded w) : A1 w < 2^26 ∧
    (2^26 ≤ U w → G0 w % 2^26 + 2^26 * (G1 w % 2^26) + 2^52 * (G2 w % 2^26) +
      2^78 * (G3 w % 2^26) + 2^104 * U w = Hv w % (2^130 - 5) + 2^130) ∧
    (U w < 2^26 → T0 w % 2^26 + 2^26 * A1 w + 2^52 * (T2 w % 2^26) + 2^78 * (T3 w % 2^26) +
      2^104 * T4 w = Hv w % (2^130 - 5) + 2^130 * (T4 w / 2^26)) := by
  have := h.b0; have := h.b1; have := h.b2; have := h.b3; have := h.b4
  simp only [U, G3, G2, G1, G0, A1, T0, T4, T3, T2, Hv]
  omega

theorem add_nw (x y : BitVec 32) {a b : Nat} (hx : x.toNat = a) (hy : y.toNat = b)
    (h : a + b < 2^32) : (x + y).toNat = a + b := by
  rw [tn_add, hx, hy, Nat.mod_eq_of_lt h]

theorem carry_vals {w : Words} (h : Bounded w) :
    (v14 w).toNat = T2 w % 2^26 ∧ (v18 w).toNat = T3 w % 2^26 ∧ (v19 w).toNat = T4 w ∧
    (v23 w).toNat = T4 w % 2^26 ∧ (v28 w).toNat = A1 w ∧ (v29 w).toNat = T0 w % 2^26 ∧
    (v30 w).toNat = G0 w ∧ (v33 w).toNat = G1 w ∧ (v36 w).toNat = G2 w ∧
    (v39 w).toNat = G3 w ∧ (v42 w).toNat = U w := by
  obtain ⟨c2, c3, c4, c4', c0, ca, cg0, cg1, cg2, cg3, cu⟩ := bnds h
  have hb1 := h.b1
  have e9 : (v9 w).toNat = w.h1.toNat / 2^26 := by rw [v9, v7, tn_shr]
  have e10 : (v10 w).toNat = T2 w := by
    rw [v10]; exact add_nw _ _ e9 rfl (by unfold T2 at c2; omega)
  have e13 : (v13 w).toNat = T2 w / 2^26 := by rw [v13, tn_shr, e10]
  have e15 : (v15 w).toNat = T3 w := by
    rw [v15]; exact add_nw _ _ e13 rfl (by unfold T3 at c3; omega)
  have e17 : (v17 w).toNat = T3 w / 2^26 := by rw [v17, tn_shr, e15]
  have e19 : (v19 w).toNat = T4 w := by
    rw [v19]; exact add_nw _ _ e17 rfl (by unfold T4 at c4; omega)
  have e21 : (v21 w).toNat = T4 w / 2^26 := by rw [v21, tn_shr, e19]
  have e24 : (v24 w).toNat = 5 * (T4 w / 2^26) := by rw [v24, tn_add, tn_shl, e21]; omega
  have e25 : (v25 w).toNat = T0 w := by
    rw [v25]; exact add_nw _ _ e24 rfl (by unfold T0 at c0; omega)
  have e11 : (v11 w).toNat = w.h1.toNat % 2^26 := by rw [v11, v7, tn_and]
  have e27 : (v27 w).toNat = T0 w / 2^26 := by rw [v27, tn_shr, e25]
  have e28 : (v28 w).toNat = A1 w := by
    rw [v28]; exact add_nw _ _ e27 e11 (by unfold A1 at ca; omega)
  have e29 : (v29 w).toNat = T0 w % 2^26 := by rw [v29, tn_and, e25]
  have e30 : (v30 w).toNat = G0 w := by
    rw [v30]; exact add_nw _ _ e29 rfl (by unfold G0 at cg0; omega)
  have e32 : (v32 w).toNat = G0 w / 2^26 := by rw [v32, tn_shr, e30]
  have e33 : (v33 w).toNat = G1 w := by
    rw [v33]; exact add_nw _ _ e32 e28 (by unfold G1 at cg1; omega)
  have e14 : (v14 w).toNat = T2 w % 2^26 := by rw [v14, tn_and, e10]
  have e35 : (v35 w).toNat = G1 w / 2^26 := by rw [v35, tn_shr, e33]
  have e36 : (v36 w).toNat = G2 w := by
    rw [v36]; exact add_nw _ _ e35 e14 (by unfold G2 at cg2; omega)
  have e18 : (v18 w).toNat = T3 w % 2^26 := by rw [v18, tn_and, e15]
  have e38 : (v38 w).toNat = G2 w / 2^26 := by rw [v38, tn_shr, e36]
  have e39 : (v39 w).toNat = G3 w := by
    rw [v39]; exact add_nw _ _ e38 e18 (by unfold G3 at cg3; omega)
  have e23 : (v23 w).toNat = T4 w % 2^26 := by rw [v23, tn_and, e19]
  have e41 : (v41 w).toNat = G3 w / 2^26 := by rw [v41, tn_shr, e39]
  have e42 : (v42 w).toNat = U w := by
    rw [v42]; exact add_nw _ _ e41 e23 (by unfold U at cu; omega)
  exact ⟨e14, e18, e19, e23, e28, e29, e30, e33, e36, e39, e42⟩

theorem mod128 {S Y c : Nat} (h : S = Y + 2^130 * c) : S % 2^128 = Y % 2^128 := by
  subst h
  rw [show 2^130 * c = 2^128 * (4 * c) by rw [← Nat.mul_assoc], Nat.add_mul_mod_self_left]

theorem sel_vals {w : Words} (h : Bounded w) : ∃ x0 x1 x2 x3 x4 : Nat, x0 < 2^26 ∧ x1 < 2^26 ∧
    x2 < 2^26 ∧ x3 < 2^26 ∧ (v57 w).toNat = x0 ∧ (v59 w).toNat = x1 ∧ (v61 w).toNat = x2 ∧
    (v63 w).toNat = x3 ∧ (v65 w).toNat = x4 ∧
    (x0 + 2^26 * x1 + 2^52 * x2 + 2^78 * x3 + 2^104 * x4) % 2^128 =
      Hv w % (2^130 - 5) % 2^128 := by
  obtain ⟨e14, e18, e19, e23, e28, e29, e30, e33, e36, e39, e42⟩ := carry_vals h
  obtain ⟨c2, c3, c4, c4', c0, ca, cg0, cg1, cg2, cg3, cu⟩ := bnds h
  obtain ⟨fa, fpos, fneg⟩ := fin_defs h
  have hfc : ((0xfc000000 : BitVec 32).signExtend 32).toNat = 0xfc000000 := by decide
  have e43 : (v43 w).toNat = (U w + 0xfc000000) % 2^32 := by
    rw [v43, tn_add, e42, hfc]
  have e47 : (v47 w).toNat = (v43 w).toNat / 2^31 := by rw [v47, tn_shr]
  have e48 : (v48 w).toNat = (2^32 - 1 + (v47 w).toNat) % 2^32 := by rw [v48, tn_sub]; rfl
  have e50 : (v50 w).toNat = (v48 w).toNat % 2^26 := by rw [v50, tn_and]
  have e44 : (v44 w).toNat = U w := by rw [v44, ← v42, e42]
  by_cases hu : U w < 2^26
  · have h43 : 2^31 ≤ (v43 w).toNat := by rw [e43]; omega
    have h46n : (v46 w).toNat = 2^32 - 1 := by rw [v46, sshift31 _ h43]; try decide
    have h48 : (v48 w).toNat = 0 := by rw [e48, e47, e43]; omega
    have h50 : (v50 w).toNat = 0 := by rw [e50, h48]
    refine ⟨T0 w % 2^26, A1 w, T2 w % 2^26, T3 w % 2^26, T4 w,
      by omega, fa, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [v57, tn_or', v56, v51, tn_and', tn_and', h46n, h50, Nat.and_zero, Nat.or_zero,
        nand_ones _ (v29 w).isLt, e29]
    · rw [v59, tn_or', v58, v52, tn_and', tn_and', h46n, h50, Nat.and_zero, Nat.or_zero,
        nand_ones _ (v28 w).isLt, e28]
    · rw [v61, tn_or', v60, v53, tn_and', tn_and', h46n, h50, Nat.and_zero, Nat.or_zero,
        nand_ones _ (v14 w).isLt, e14]
    · rw [v63, tn_or', v62, v54, tn_and', tn_and', h46n, h50, Nat.zero_and, Nat.or_zero,
        nand_ones _ (v18 w).isLt, e18]
    · rw [v65, tn_or', v64, v55, tn_and', tn_and', h46n, h48, Nat.zero_and, Nat.or_zero,
        nand_ones' _ (v19 w).isLt, e19]
    · exact mod128 (fneg hu)
  · have h43 : (v43 w).toNat < 2^31 := by rw [e43]; omega
    have h46n : (v46 w).toNat = 0 := by rw [v46, sshift31' _ h43]; try rfl
    have h48 : (v48 w).toNat = 2^32 - 1 := by rw [e48, e47, e43]; omega
    have h50 : (v50 w).toNat = 2^26 - 1 := by rw [e50, h48]
    refine ⟨G0 w % 2^26, G1 w % 2^26, G2 w % 2^26, G3 w % 2^26, U w,
      by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [v57, tn_or', v56, v51, tn_and', tn_and', h46n, h50, Nat.and_zero, Nat.zero_or,
        nand_m, e30]
    · rw [v59, tn_or', v58, v52, tn_and', tn_and', h46n, h50, Nat.and_zero, Nat.zero_or,
        nand_m, e33]
    · rw [v61, tn_or', v60, v53, tn_and', tn_and', h46n, h50, Nat.and_zero, Nat.zero_or,
        nand_m, e36]
    · rw [v63, tn_or', v62, v54, tn_and', tn_and', h46n, h50, Nat.and_zero, Nat.zero_or,
        nand_m', e39]
    · rw [v65, tn_or', v64, v55, tn_and', tn_and', h46n, h48, Nat.zero_and, Nat.zero_or,
        nand_ones' _ (v44 w).isLt, e44]
    · exact mod128 (c := 1) ((fpos (by omega)).trans (by rw [Nat.mul_one]))

theorem final_nat (x0 x1 x2 x3 x4 p0 p1 p2 p3 a68 a72 a76 a79 c q83 q85 q87 o80 o84 o89 o88 o91 Y : Nat)
    (hX : (x0 + 2^26 * x1 + 2^52 * x2 + 2^78 * x3 + 2^104 * x4) % 2^128 = Y % 2^128)
    (h68 : a68 = (x1 % 2^6) * 2^26 + x0) (h72 : a72 = (x2 % 2^12) * 2^20 + x1 / 2^6)
    (h76 : a76 = (x3 % 2^18) * 2^14 + x2 / 2^12) (h79 : a79 = (x4 % 2^24) * 2^8 + x3 / 2^18)
    (hc : c = (a68 + p0) / 2^32) (h80 : o80 = (a68 + p0) % 2^32)
    (h83 : q83 = p1 + a72 + c) (h84 : o84 = q83 % 2^32) (h85 : q85 = p2 + a76)
    (h87 : q87 = q83 / 2^32 + q85) (h89 : o89 = q87 % 2^32) (h88 : o88 = (a79 + p3) % 2^32)
    (h91 : o91 = (q87 / 2^32 % 2^32 + o88) % 2^32) :
    let N := Y + (p0 + 2^32 * p1 + 2^64 * p2 + 2^96 * p3)
    o80 = N % 2^32 ∧ o84 = N / 2^32 % 2^32 ∧ o89 = N / 2^64 % 2^32 ∧ o91 = N / 2^96 % 2^32 := by
  intro N
  have hP := pack_nat x0 x1 x2 x3 x4 p0 p1 p2 p3
  simp only at hP
  subst h68 h72 h76 h79 hc h80 h83 h84 h85 h87 h89 h88 h91
  omega

theorem model_out {w : Words} (h : Bounded w) :
    (v80 w).toNat = (Hv w % (2^130 - 5) + Pv w) % 2^32 ∧
    (v84 w).toNat = (Hv w % (2^130 - 5) + Pv w) / 2^32 % 2^32 ∧
    (v89 w).toNat = (Hv w % (2^130 - 5) + Pv w) / 2^64 % 2^32 ∧
    (v91 w).toNat = (Hv w % (2^130 - 5) + Pv w) / 2^96 % 2^32 := by
  obtain ⟨x0, x1, x2, x3, x4, hx0, hx1, hx2, hx3, f0, f1, f2, f3, f4, hX⟩ := sel_vals h
  have e68 : (v68 w).toNat = (x1 % 2^6) * 2^26 + x0 := by
    rw [v68, v67, or_shl_toNat _ _ 26 (by decide) (by omega), f1, f0]
  have e72 : (v72 w).toNat = (x2 % 2^12) * 2^20 + x1 / 2^6 := by
    rw [v72, v71, v69, or_shr_toNat _ _ 20 6 (by decide) (by rw [f1]; omega), f2, f1]
  have e76 : (v76 w).toNat = (x3 % 2^18) * 2^14 + x2 / 2^12 := by
    rw [v76, v75, v73, or_shr_toNat _ _ 14 12 (by decide) (by rw [f2]; omega), f3, f2]
  have e79 : (v79 w).toNat = (x4 % 2^24) * 2^8 + x3 / 2^18 := by
    rw [v79, v78, v77, or_shr_toNat _ _ 8 18 (by decide) (by rw [f3]; omega), f4, f3]
  have ec : (cf80 w).toNat = ((v68 w).toNat + w.p0.toNat) / 2^32 := by
    rw [cf80]; simp only [addSpec]; rw [tn_c]
  have e80 : (v80 w).toNat = ((v68 w).toNat + w.p0.toNat) % 2^32 := by rw [v80, tn_add]
  have hc1 : (cf80 w).toNat ≤ 1 := by cases cf80 w <;> decide
  have e83 : (q83 w).toNat = w.p1.toNat + (v72 w).toNat + (cf80 w).toNat := by
    rw [q83, tn_add64, tn_add64, tn_sw, tn_sw, tn_ofNatBool, v81]
    have := (v72 w).isLt; have := w.p1.isLt
    omega
  have e84 : (v84 w).toNat = (q83 w).toNat % 2^32 := by rw [v84, tn_sw32]
  have e85 : (q85 w).toNat = w.p2.toNat + (v76 w).toNat := by
    rw [q85, tn_add64, tn_sw, tn_sw, v82]; have := (v76 w).isLt; have := w.p2.isLt; omega
  have e87 : (q87 w).toNat = (q83 w).toNat / 2^32 + (q85 w).toNat := by
    rw [q87, tn_add64, q86, tn_shr64]
    have := (v76 w).isLt; have := w.p2.isLt; have := (v72 w).isLt; have := w.p1.isLt
    omega
  have e89 : (v89 w).toNat = (q87 w).toNat % 2^32 := by rw [v89, tn_sw32]
  have e88 : (v88 w).toNat = ((v79 w).toNat + w.p3.toNat) % 2^32 := by rw [v88, tn_add]
  have e91 : (v91 w).toNat = ((q87 w).toNat / 2^32 % 2^32 + (v88 w).toNat) % 2^32 := by
    rw [v91, tn_add, tn_sw32, q90, tn_shr64]
  exact final_nat x0 x1 x2 x3 x4 w.p0.toNat w.p1.toNat w.p2.toNat w.p3.toNat _ _ _ _ _ _ _ _
    _ _ _ _ _ _ hX e68 e72 e76 e79 ec e80 e83 e84 e85 e87 e89 e88 e91

theorem hl_at (s : RamState) (st : BitVec 64) (i : Fin 5) :
    hLimbs s st i = word32 s (st + BitVec.ofNat 64 (0x24 + 4 * i.val)) := by
  simp only [hLimbs, limbsAt, hOffset]
  rw [BitVec.add_assoc, BitVec.ofNat_add]
  rfl

theorem pw_at (s : RamState) (st : BitVec 64) (i : Fin 4) :
    padWords s st i = word32 s (st + BitVec.ofNat 64 (4 * i.val)) := rfl

theorem words_bounded {s : RamState} (h : BoundedLimbs (hLimbs s (rsi.read s))) :
    Bounded (words s) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  rw [hl_at] at h0 h1 h2 h3 h4
  exact ⟨h0, h1, h2, h3, h4⟩

theorem hv_eq (s : RamState) : limbValue (hLimbs s (rsi.read s)) = Hv (words s) := by
  simp only [limbValue, hl_at, Hv, words_h0, words_h1, words_h2, words_h3, words_h4]
  rfl

theorem pv_eq (s : RamState) : wordValue (padWords s (rsi.read s)) = Pv (words s) := by
  simp only [wordValue, pw_at, Pv, words_p0, words_p1, words_p2, words_p3]
  rfl

theorem byte_of_read32 {t : RamState} {a : BitVec 64} {x : BitVec 32}
    (h : (Operand.mem a : Operand 32).read t = x) (hs : MemReadable t a 4) (j : Nat)
    (hj : j < 4) : t.external[a + BitVec.ofNat 64 j]? = some (storedByte x j) := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hs.mem j hj)
  rw [hb, ← h]
  have := storedByte_memLoad t.external a (n := 32) j (by omega)
  change some b = some (storedByte (memLoad t.external a 32) j)
  rw [this]
  simp [memByte, PhysicalMemory.read, hb]

theorem tag_byte (N : Nat) (x : BitVec 32) (k j : Nat) (hx : x.toNat = N / 2^(32*k) % 2^32)
    (hj : j < 4) : storedByte x j = UInt8.ofNat (N / 256^(4*k+j)) := by
  apply UInt8.toNat_inj.mp
  simp only [storedByte, hx, Nat.shiftRight_eq_div_pow]
  have hp : 256^(4*k+j) = 2^(32*k) * 2^(8*j) := by
    rw [show (256 : Nat) = 2^8 by rfl, ← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega
  rw [hp, ← Nat.div_div_eq_div_mul]
  generalize N / 2^(32*k) = A
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp <;> omega

theorem tag_mem {s t : RamState} (hm : MemReadable t (rdi.read s) tagBytes)
    (hb : Bounded (words s))
    (o0 : (Operand.mem (rdi.read s + BitVec.ofNat 64 0) : Operand 32).read t = v80 (words s))
    (o4 : (Operand.mem (rdi.read s + BitVec.ofNat 64 4) : Operand 32).read t = v84 (words s))
    (o8 : (Operand.mem (rdi.read s + BitVec.ofNat 64 8) : Operand 32).read t = v89 (words s))
    (o12 : (Operand.mem (rdi.read s + BitVec.ofNat 64 12) : Operand 32).read t = v91 (words s)) :
    ∀ i : Fin 16, t.external[rdi.read s + BitVec.ofNat 64 i.val]? = some (tag s)[i] := by
  intro i
  obtain ⟨m0, m4, m8, m12⟩ := model_out hb
  have hN : limbValue (hLimbs s (rsi.read s)) % prime + wordValue (padWords s (rsi.read s)) =
      Hv (words s) % (2^130 - 5) + Pv (words s) := by rw [hv_eq, pv_eq]; rfl
  have hi := i.isLt
  have hsplit : rdi.read s + BitVec.ofNat 64 i.val =
      rdi.read s + BitVec.ofNat 64 (4 * (i.val / 4)) + BitVec.ofNat 64 (i.val % 4) := by
    rw [add_ofNat_add_ofNat]; congr 2; omega
  have hidx : 4 * (i.val / 4) + i.val % 4 = i.val := by omega
  have hval : (tag s)[i] = UInt8.ofNat ((Hv (words s) % (2^130 - 5) + Pv (words s)) /
      256^(4 * (i.val / 4) + i.val % 4)) := by
    rw [hidx, ← hN]
    simp [tag, numTo16LeBytes]
  rw [hsplit, hval]
  have hm' (k : Nat) (hk : k < 4) :
      MemReadable t (rdi.read s + BitVec.ofNat 64 (4 * k)) 4 :=
    memReadable_slice hm (4 * k) 4 (by unfold tagBytes; omega)
  rcases (by omega : i.val / 4 = 0 ∨ i.val / 4 = 1 ∨ i.val / 4 = 2 ∨ i.val / 4 = 3) with
    h | h | h | h <;> rw [h]
  · rw [byte_of_read32 o0 (hm' 0 (by decide)) _ (by omega),
      tag_byte (Hv (words s) % (2^130 - 5) + Pv (words s)) _ 0 _ (by rw [m0]; simp) (by omega)]
  · rw [byte_of_read32 o4 (hm' 1 (by decide)) _ (by omega),
      tag_byte (Hv (words s) % (2^130 - 5) + Pv (words s)) _ 1 _ (by rw [m4]) (by omega)]
  · rw [byte_of_read32 o8 (hm' 2 (by decide)) _ (by omega),
      tag_byte (Hv (words s) % (2^130 - 5) + Pv (words s)) _ 2 _ (by rw [m8]) (by omega)]
  · rw [byte_of_read32 o12 (hm' 3 (by decide)) _ (by omega),
      tag_byte (Hv (words s) % (2^130 - 5) + Pv (words s)) _ 3 _ (by rw [m12]) (by omega)]

theorem body_ne {s : RamState} (hp : FinalizePre s) :
    ∀ a : BitVec 64, 0x101ce0 ≤ a.toNat → a.toNat ≤ 0x101e27 → a ≠ (returnBoundary s).rip := by
  intro a h1 h2 he
  have := hp.returnOutside
  rw [← he] at this
  simp only [entry, codeLength] at this
  have : (0x101ce0 : BitVec 64).toNat = 0x101ce0 := rfl
  omega

theorem finish_ret [Bindings] {s u : RamState}
    (hp : FinalizePre s) (hr : ReadyToStep u)
    (hc : CodeIn Extracted.programImage u) (hip : u.RIP = 0x101e27)
    (hsp : stackPtr u = stackPtr s) (hrd : MemReadable u (stackPtr u) 8)
    (hret : (Operand.mem (stackPtr u) : Operand 64).read u = (returnBoundary s).rip)
    (hrax : rax.read u = rdi.read s) (hag : AgreesExcept (callChanges s) s u)
    (hg : Grows s u)
    (o0 : (Operand.mem (rdi.read s + BitVec.ofNat 64 0) : Operand 32).read u = v80 (words s))
    (o4 : (Operand.mem (rdi.read s + BitVec.ofNat 64 4) : Operand 32).read u = v84 (words s))
    (o8 : (Operand.mem (rdi.read s + BitVec.ofNat 64 8) : Operand 32).read u = v89 (words s))
    (o12 : (Operand.mem (rdi.read s + BitVec.ofNat 64 12) : Operand 32).read u = v91 (words s)) :
    ∃ v, Machine.step u = some (.next v) ∧ FinalizeResult s v := by
  obtain ⟨v, hstep, hrv, hev⟩ := ret_effect_step 0x101e27 u hr
    (program_text_slice hc 0x1e27 1 (by decide +kernel))
    ⟨⟨hip, hrd⟩, by show ((Operand.mem (stackPtr u) : Operand 64).read u).toNat < 2 ^ 32; rw [hret]; exact hp.returnLow⟩
  have hagv := hev.agrees
  rw [retEffect_components] at hagv
  have hext : v.external = u.external := hagv.external (by simp [Component.Covers])
  refine ⟨v, hstep, hrv, hev.rip.trans hret, ?_, ?_, ?_, ?_⟩
  · rw [stackPtr_eq_read]; exact hev.writes.trans (by rw [hsp])
  · exact (hagv.read (by simp)).trans hrax
  · exact (hag.trans hagv).mono (by simp [callChanges])
  · have hm : MemReadable u (rdi.read s) tagBytes :=
      memReadable_grow hp.output.readable hg
    have hmv : MemReadable v (rdi.read s) tagBytes := ⟨hm.low, fun i hi => hext ▸ hm.mem i hi⟩
    exact tag_mem hmv (words_bounded hp.limbs) (by rw [mem_congr hext]; exact o0)
      (by rw [mem_congr hext]; exact o4) (by rw [mem_congr hext]; exact o8)
      (by rw [mem_congr hext]; exact o12)

theorem finalize_returns [Bindings] (s : RamState) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hp : FinalizePre s) :
    ∃ fuel t, Returns (returnBoundary s) fuel s t ∧ FinalizeResult s t := by
  obtain ⟨n, u, ha, hr', hc', hip, hsp, hrd, hret, hrax, hag, hg, o0, o4, o8, o12⟩ :=
    body _ (body_ne hp) s hr hc hp
  obtain ⟨v, hstep, hres⟩ := finish_ret hp hr' hc' hip hsp hrd hret hrax hag hg o0 o4 o8 o12
  refine ⟨n + 1, v, ha.returns (Returns.of_step hstep hres.rip ?_), hres⟩
  have := hres.rsp
  rw [stackPtr] at this
  exact this

theorem finalize_advances [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < entry.toNat ∨ entry.toNat + codeLength ≤ boundary.rip.toNat)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : FinalizePre s) (hne : (returnBoundary s).rip ≠ boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ FinalizeResult s t := by
  have hne' : ∀ a : BitVec 64, 0x101ce0 ≤ a.toNat → a.toNat ≤ 0x101e27 → a ≠ boundary.rip := by
    intro a h1 h2 he
    rw [← he] at hb
    simp only [entry, codeLength] at hb
    have : (0x101ce0 : BitVec 64).toNat = 0x101ce0 := rfl
    omega
  obtain ⟨n, u, ha, hr', hc', hip, hsp, hrd, hret, hrax, hag, hg, o0, o4, o8, o12⟩ :=
    body _ hne' s hr hc hp
  obtain ⟨v, hstep, hres⟩ := finish_ret hp hr' hc' hip hsp hrd hret hrax hag hg o0 o4 o8 o12
  exact ⟨n + 1, v, ha.trans (Advances.of_step hstep (.inl (hres.rip ▸ hne))), hres⟩

end ChaCha20Poly1305.Proofs.Poly1305.Callee101ce0
