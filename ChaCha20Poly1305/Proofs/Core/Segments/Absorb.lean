import ChaCha20Poly1305.Proofs.Core.Cuts
import ChaCha20Poly1305.Proofs.Poly1305.Mac
import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30
import ChaCha20Poly1305.Proofs.MemoryContracts
import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Execution
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Nop.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple

namespace ChaCha20Poly1305.Proofs.Core.Absorb

open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CoreContract
open ChaCha20Poly1305.Proofs.Poly1305State ChaCha20Poly1305.Proofs.Poly1305.Mac
open ChaCha20Poly1305.Proofs.Common

def InStack (s : RamState) (x : BitVec 64) : Prop :=
  (stackPtr s).toNat - 992 ≤ x.toNat ∧ x.toNat < (stackPtr s).toNat + 8

structure Geometry (s t0 : RamState) : Prop where
  low : 992 ≤ (stackPtr s).toNat
  high : (stackPtr s).toNat + 8 < 2 ^ 32
  allocated : ∀ x, InStack s x → (t0.external[x]?).isSome
  code : ∀ x, InStack s x → ¬ InProgram x
  tables : 0x2020 ≤ (stackPtr s).toNat - 992 ∨ (stackPtr s).toNat + 8 ≤ 0x1000

structure Track [Bindings] (P : BitVec 64) (cs : List Component) (base t : RamState) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  agrees : AgreesExcept cs base t
  rsp : stackPtr t = P

theorem Track.refl [Bindings] {P : BitVec 64} {cs : List Component} {t : RamState}
    (hr : ReadyToStep t) (hc : CodeIn Extracted.programImage t) (hp : stackPtr t = P) :
    Track P cs t t :=
  ⟨hr, hc, AgreesExcept.refl cs t, hp⟩

theorem Track.extend [Bindings] {P : BitVec 64} {cs cs' : List Component} {base u v : RamState}
    (T : Track P cs base u) (hr : ReadyToStep v) (hc : CodeIn Extracted.programImage v)
    (ha : AgreesExcept cs' u v) (hp : stackPtr v = P)
    (hreg : ∀ c ∈ cs', c.isMem = false → c ∈ cs)
    (hmem : ∀ x, ∀ c ∈ cs', c.Covers x → ∃ c' ∈ cs, c'.Covers x) :
    Track P cs base v :=
  ⟨hr, hc, (T.agrees.trans (ha.widen hreg hmem)).mono (by
    intro c hc; simp only [List.mem_append, or_self] at hc; exact hc), hp⟩

theorem ite_t {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

theorem ite_f {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem frame_toNat (s : RamState) (h : 992 ≤ (stackPtr s).toNat) :
    (framePointer s).toNat = (stackPtr s).toNat - frameBytes := by
  unfold framePointer
  rw [BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def, BitVec.toNat_ofNat]
    simp only [frameBytes]
    omega)]
  simp [frameBytes]

theorem covers_toNat {a x : BitVec 64} {n : Nat} (h : (Component.mem a n).Covers x)
    (hlow : a.toNat + n < 2 ^ 64) : ∃ i < n, x.toNat = a.toNat + i := by
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, hi, toNat_add_ofNat _ _ (by omega)⟩

theorem Geometry.ne_code {s t0 : RamState} (G : Geometry s t0) {a p : BitVec 64} {n len : Nat}
    (hlo : (stackPtr s).toNat - 992 ≤ a.toNat)
    (hhi : a.toNat + n ≤ (stackPtr s).toNat + 8)
    (hp : ∀ j < len, InProgram (p + BitVec.ofNat 64 j)) : RangeApart a n p len := by
  intro i hi j hj he
  have hhigh := G.high
  apply G.code (a + BitVec.ofNat 64 i)
  · unfold InStack
    rw [toNat_add_ofNat _ _ (by omega)]
    omega
  · rw [he]; exact hp j hj

theorem Geometry.memWritable [Bindings] {s t0 t : RamState} (G : Geometry s t0) {cs : List Component}
    (ha : AgreesExcept cs t0 t) {a : BitVec 64} {n : Nat}
    (hlo : (stackPtr s).toNat - 992 ≤ a.toNat)
    (hhi : a.toNat + n ≤ (stackPtr s).toNat + 8) : MemWritable t a n := by
  have hhigh := G.high
  refine ⟨by omega, ?_, ?_⟩
  · intro i hi
    apply ha.grow
    apply G.allocated
    unfold InStack
    rw [toNat_add_ofNat _ _ (by omega)]
    omega
  · have := G.tables
    unfold PageTableEntriesApart
    omega

theorem Geometry.writableRange [Bindings] {s t0 t : RamState} (G : Geometry s t0)
    {cs : List Component} (ha : AgreesExcept cs t0 t) {a : BitVec 64} {n : Nat}
    (hlo : (stackPtr s).toNat - 992 ≤ a.toNat)
    (hhi : a.toNat + n ≤ (stackPtr s).toNat + 8) : WritableRange t a n := by
  have hhigh := G.high
  refine ⟨⟨by omega, ?_⟩, ?_, ?_⟩
  · intro i hi
    apply ha.grow
    apply G.allocated
    unfold InStack
    rw [toNat_add_ofNat _ _ (by omega)]
    omega
  · intro i hi
    rw [inPageTables_iff, toNat_add_ofNat _ _ (by omega)]
    have := G.tables
    omega
  · intro i hi
    apply G.code
    unfold InStack
    rw [toNat_add_ofNat _ _ (by omega)]
    omega

theorem inProg (a : BitVec 64) (h : 0x100000 ≤ a.toNat ∧ a.toNat < 0x100000 + 11759) :
    InProgram a := by
  have hs : Extracted.textBytes.size = 11759 := by decide
  have hp := MemoryRoutines.Machine.text_address_in_program (a.toNat - 0x100000) (by omega)
  have he : Extracted.textAddress + BitVec.ofNat 64 (a.toNat - 0x100000) = a := by
    apply BitVec.eq_of_toNat_eq
    have h0 : Extracted.textAddress.toNat = 0x100000 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, h0]
    have := a.isLt
    omega
  rwa [he] at hp

theorem ne_boundary {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip) {a : BitVec 64}
    (h : 0x100000 ≤ a.toNat ∧ a.toNat < 0x100000 + 11759) : a ≠ boundary.rip := by
  rintro rfl
  exact hOut (inProg _ h)

theorem ne_boundary_add {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip)
    {L : BitVec 64} {a b : Nat}
    (h : 0x100000 ≤ L.toNat + (a + b) ∧ L.toNat + (a + b) < 0x100000 + 11759) :
    L + BitVec.ofNat 64 a + BitVec.ofNat 64 b ≠ boundary.rip := by
  rw [add_ofNat_add_ofNat]
  exact ne_boundary hOut (by rw [toNat_add_ofNat _ _ (by omega)]; omega)

theorem inProg_range (p : BitVec 64) (len : Nat)
    (h : 0x100000 ≤ p.toNat ∧ p.toNat + len ≤ 0x100000 + 11759) :
    ∀ j < len, InProgram (p + BitVec.ofNat 64 j) := by
  intro j hj
  apply inProg
  rw [toNat_add_ofNat _ _ (by omega)]
  omega

theorem read_mem_eq {u v : RamState} {a : BitVec 64} {n : Nat}
    (h : ∀ i < n / 8, v.external[a + BitVec.ofNat 64 i]? = u.external[a + BitVec.ofNat 64 i]?) :
    (Operand.mem a : Operand n).read v = (Operand.mem a : Operand n).read u := by
  change memLoad v.external a n = memLoad u.external a n
  exact memLoad_congr fun i hi => memByte_congr (h i hi)

theorem Track.step [Bindings] {P : BitVec 64} {cs : List Component} {base u : RamState}
    {pre : RamState → Prop} {e : RamState → Effect} {p : BitVec 64} {bytes : List UInt8}
    {boundary : ReturnBoundary}
    (hStep : StepEffect pre (codeRange p bytes) e) (T : Track P cs base u)
    (hbytes : CodeIn (codeRange p bytes) u) (hpre : pre u) (hne : (e u).rip ≠ boundary.rip)
    (hreg : ∀ c ∈ (e u).components, c.isMem = false → c ∈ cs)
    (hmem : ∀ x, ∀ c ∈ (e u).components, c.Covers x →
      (∃ c' ∈ cs, c'.Covers x) ∧ ¬ InProgram x)
    (hrsp : Component.reg 4 ∉ (e u).components) :
    ∃ v, Advances boundary 1 u v ∧ Track P cs base v ∧ (e u).Holds u v := by
  obtain ⟨v, ha, hr, he⟩ := hStep.advances T.ready hbytes hpre hne
  refine ⟨v, ha, T.extend hr (he.codeIn ?_ T.code) he.agrees ?_ hreg
    (fun x c hc hx => (hmem x c hc hx).1), he⟩
  · intro x hx c hc hcov
    exact (hmem x.1 c hc hcov).2 (MemoryRoutines.Machine.inProgram_of_mem hx)
  · rw [stackPtr_eq_read, he.agrees.read hrsp, ← stackPtr_eq_read, T.rsp]

theorem regOnly {cs : List Component} (h : ∀ c ∈ cs, c.isMem = false) :
    ∀ x, ∀ c ∈ cs, c.Covers x → ∀ (Q : Prop), Q := by
  intro x c hc hcov
  have := h c hc
  cases c <;> simp_all [Component.Covers, Component.isMem]

theorem callEffect_read {target : RamState → BitVec 64} {ret : BitVec 64}
    {s u : RamState} (h : (callEffect target ret s).Holds s u)
    {r : BitVec 5} (hr : r ≠ 4) {n : Nat} :
    (Operand.reg r : Operand n).read u = (Operand.reg r : Operand n).read s :=
  h.agrees.read (by
    simp only [pushEffect_components, List.mem_cons, Component.reg.injEq,
      reduceCtorEq, List.not_mem_nil, or_false]
    exact hr)

theorem callEffect_rsp {target : RamState → BitVec 64} {ret : BitVec 64}
    {s u : RamState} (h : (callEffect target ret s).Holds s u) :
    stackPtr u = pushAddr s := h.writes.1

theorem callEffect_returnBoundary {target : RamState → BitVec 64} {ret : BitVec 64}
    {s u : RamState} (h : (callEffect target ret s).Holds s u) :
    returnBoundary u = { rip := ret, rsp := stackPtr s } := by
  have hs := callEffect_stack h
  change ({ rip := stackTop u, rsp := stackPtr u + 8 } : ReturnBoundary) = _
  rw [hs.1, hs.2]

def callFoot (P : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .flags, .rip,
    .mem (P - BitVec.ofNat 64 96) 96, .mem (P + BitVec.ofNat 64 0x174) 20, .mem (P + BitVec.ofNat 64 0x18) 16]

theorem sub_toNat (P : BitVec 64) (k : Nat) (h : k ≤ P.toNat) :
    (P - BitVec.ofNat 64 k).toNat = P.toNat - k := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; have := P.isLt; omega)]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := P.isLt; omega)]

theorem add_toNat (P : BitVec 64) (k : Nat) (h : P.toNat + k < 2 ^ 64) :
    (P + BitVec.ofNat 64 k).toNat = P.toNat + k :=
  toNat_add_ofNat _ _ h

theorem rangeApart_of_toNat {a b : BitVec 64} {n m : Nat} (ha : a.toNat + n < 2 ^ 64)
    (hb : b.toNat + m < 2 ^ 64) (h : a.toNat + n ≤ b.toNat ∨ b.toNat + m ≤ a.toNat) :
    RangeApart a n b m :=
  RangeApart.of_toNat (by omega) (by omega) h

theorem PolyState.transfer {u v : RamState} {base : BitVec 64} {otk : Vector UInt8 32}
    {acc acc' : Nat} (h : PolyState u base otk acc)
    (hlow : ∀ i < 0x24, v.external[base + BitVec.ofNat 64 i]? = u.external[base + BitVec.ofNat 64 i]?)
    (hb : BoundedLimbs (hLimbs v base)) (hv : limbValue (hLimbs v base) % prime = acc') :
    PolyState v base otk acc' := by
  have hw : ∀ k, k + 4 ≤ 0x24 → word32 v (base + BitVec.ofNat 64 k) =
      word32 u (base + BitVec.ofNat 64 k) := by
    intro k hk
    apply read_mem_eq
    intro i hi
    rw [add_ofNat_add_ofNat]
    exact hlow _ (by omega)
  have hpad : padWords v base = padWords u base := by
    funext i
    exact hw _ (by omega)
  have hr : rLimbs v base = rLimbs u base := by
    funext i
    unfold rLimbs limbsAt
    rw [rOffset, show (0x10 : BitVec 64) = BitVec.ofNat 64 0x10 from rfl, add_ofNat_add_ofNat]
    exact hw _ (by omega)
  exact ⟨hpad ▸ h.pad, hr ▸ h.rClamped, hr ▸ h.rValue, hb, hv⟩

theorem inCode_inProgram {a : BitVec 64} (h : Poly1305.Callee101e30.InCode a) : InProgram a := by
  apply inProg
  unfold Poly1305.Callee101e30.InCode Poly1305.Callee101e30.entry
    Poly1305.Callee101e30.bodyEntry at h
  have h1 : (0x101e30 : BitVec 64).toNat = 0x101e30 := rfl
  have h2 : (0x101ab0 : BitVec 64).toNat = 0x101ab0 := rfl
  rw [h1, h2] at h
  omega

theorem covers_widen {a b x : BitVec 64} {n m : Nat} (hx : (Component.mem a n).Covers x)
    (ha : a.toNat + n < 2 ^ 64) (hb : b.toNat + m < 2 ^ 64)
    (hsub : b.toNat ≤ a.toNat ∧ a.toNat + n ≤ b.toNat + m) : (Component.mem b m).Covers x := by
  obtain ⟨i, hi, hxi⟩ := covers_toNat hx ha
  refine ⟨a.toNat + i - b.toNat, by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [hxi, toNat_add_ofNat _ _ (by omega)]
  omega

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

theorem calleeSaved_of_agrees {cs : List Component} {u v : RamState} (h : AgreesExcept cs u v)
    (h3 : Component.reg 3 ∉ cs) (h5 : Component.reg 5 ∉ cs) (h12 : Component.reg 12 ∉ cs)
    (h13 : Component.reg 13 ∉ cs) (h14 : Component.reg 14 ∉ cs) (h15 : Component.reg 15 ∉ cs) :
    CalleeSavedRegistersUnchanged u v := by
  intro r hr
  have hu := regValue_read u
  have hv := regValue_read v
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hu.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.1]; exact h.read h3
  · rw [hu.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.1]; exact h.read h5
  · rw [hu.2.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.1]; exact h.read h12
  · rw [hu.2.2.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.2.1]; exact h.read h13
  · rw [hu.2.2.2.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.2.2.1]; exact h.read h14
  · rw [hu.2.2.2.2.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.2.2.2.1]; exact h.read h15

theorem calleeSaved_trans {u v w : RamState} (h1 : CalleeSavedRegistersUnchanged u v)
    (h2 : CalleeSavedRegistersUnchanged v w) : CalleeSavedRegistersUnchanged u w :=
  fun r hr => (h2 r hr).trans (h1 r hr)

theorem word32_eq {u v : RamState} {a : BitVec 64}
    (h : ∀ i < 4, v.external[a + BitVec.ofNat 64 i]? = u.external[a + BitVec.ofNat 64 i]?) :
    word32 v a = word32 u a :=
  read_mem_eq h

theorem limbs_eq {u v : RamState} {base : BitVec 64} {off : Nat} (hoff : off + 20 ≤ 0x38)
    (h : ∀ i < 0x38, v.external[base + BitVec.ofNat 64 i]? = u.external[base + BitVec.ofNat 64 i]?) :
    limbsAt v (base + BitVec.ofNat 64 off) = limbsAt u (base + BitVec.ofNat 64 off) := by
  funext i
  apply word32_eq
  intro j hj
  rw [add_ofNat_add_ofNat, add_ofNat_add_ofNat]
  exact h _ (by omega)

theorem rLimbs_eq {u v : RamState} {base : BitVec 64}
    (h : ∀ i < 0x38, v.external[base + BitVec.ofNat 64 i]? = u.external[base + BitVec.ofNat 64 i]?) :
    rLimbs v base = rLimbs u base :=
  limbs_eq (off := 0x10) (by decide) h

theorem hLimbs_eq {u v : RamState} {base : BitVec 64}
    (h : ∀ i < 0x38, v.external[base + BitVec.ofNat 64 i]? = u.external[base + BitVec.ofNat 64 i]?) :
    hLimbs v base = hLimbs u base :=
  limbs_eq (off := 0x24) (by decide) h

theorem PolyState.of_mem {u v : RamState} {base : BitVec 64} {otk : Vector UInt8 32} {acc : Nat}
    (hp : PolyState u base otk acc)
    (h : ∀ i < 0x38, v.external[base + BitVec.ofNat 64 i]? = u.external[base + BitVec.ofNat 64 i]?) :
    PolyState v base otk acc := by
  have hpad : padWords v base = padWords u base := by
    funext i
    apply word32_eq
    intro j hj
    have := i.isLt
    simpa only [padWords, add_ofNat_add_ofNat] using h (4 * i.val + j) (by omega)
  exact ⟨hpad ▸ hp.pad, (rLimbs_eq h) ▸ hp.rClamped, (rLimbs_eq h) ▸ hp.rValue,
    (hLimbs_eq h) ▸ hp.hBounded, (hLimbs_eq h) ▸ hp.hValue⟩

theorem absorb_value {H R acc : Nat} {blk : ByteArray} (hH : H % prime = acc) :
    ((H + leBytesToNum (blk ++ ⟨#[0x01]⟩)) * R) % prime = absorbBlock R acc blk := by
  rw [← hH, absorbBlock_mod, absorbBlock_eq]

set_option maxHeartbeats 1000000 in
theorem poly_call [Bindings] {s t0 u : RamState} (G : Geometry s t0) {boundary : ReturnBoundary}
    (hOut : ¬ InProgram boundary.rip) {csA : List Component} (hA : AgreesExcept csA t0 u)
    (hr : ReadyToStep u) (hc : CodeIn Extracted.programImage u)
    (hrsp : stackPtr u = framePointer s)
    {p : BitVec 64} {disp : BitVec 32} (hrip : u.RIP = p)
    (hbytes : CodeIn (codeRange p (encodeCallRel32 disp)) u)
    (htarget : branchTarget p 5 (disp.signExtend 64) = 0x101e30)
    (hp : 0x100000 ≤ p.toNat ∧ p.toNat + 5 < 0x101ab0)
    (hrdi : rdi.read u = polyBase s)
    {blk : ByteArray} (hsize : blk.size = 16)
    (hblkLow : (rsi.read u).toNat + 16 ≤ 2 ^ 32)
    (hblk : ∀ i < 16, u.external[rsi.read u + BitVec.ofNat 64 i]? = some blk[i]!)
    (hblkApart : RangeApart (rsi.read u) 16 (framePointer s - BitVec.ofNat 64 96) 96)
    {otk : Vector UInt8 32} {acc : Nat} (hpoly : PolyState u (polyBase s) otk acc) :
    ∃ fuel v, Advances boundary fuel u v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      v.RIP = p + BitVec.ofNat 64 5 ∧ stackPtr v = framePointer s ∧
      AgreesExcept (callFoot (framePointer s)) u v ∧ CalleeSavedRegistersUnchanged u v ∧
      PolyState v (polyBase s) otk (absorbBlock (clampedR otk) acc blk) := by
  have hPn := frame_toNat s G.low
  have hlow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hPn
  have hpush : pushAddr u = framePointer s - BitVec.ofNat 64 8 := by
    rw [pushAddr, hrsp]; rfl
  have hpushN : (pushAddr u).toNat = (framePointer s).toNat - 8 := by
    rw [hpush, sub_toNat _ _ (by omega)]
  have hpre : PushPre p 5 u := by
    refine ⟨hrip, ?_, ?_⟩
    · exact G.memWritable hA (by omega)
        (by omega)
    · exact G.ne_code (by omega) (by omega)
        (inProg_range p 5 (by omega))
  have htargetLow : (branchTarget p 5 (disp.signExtend 64)).toNat < 2 ^ 32 := by
    rw [htarget]; decide
  obtain ⟨u1, a1, r1, e1⟩ := (call_rel32_effect_step p disp htargetLow).advances hr hbytes hpre
    (by
      change branchTarget p 5 (disp.signExtend 64) ≠ boundary.rip
      rw [htarget]; exact ne_boundary hOut (by decide))
  have hc1 : CodeIn Extracted.programImage u1 := by
    apply e1.codeIn _ hc
    intro x hx c hcm hcov
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl | rfl
    · exact hcov
    · obtain ⟨i, hi, hxi⟩ := hcov
      apply G.code _ _ (MemoryRoutines.Machine.inProgram_of_mem hx)
      unfold InStack
      rw [hxi, toNat_add_ofNat _ _ (by omega)]
      omega
    · exact hcov
  have hrsp1 : stackPtr u1 = framePointer s - BitVec.ofNat 64 8 := (callEffect_rsp e1).trans hpush
  have hret1 : returnBoundary u1 = { rip := p + BitVec.ofNat 64 5, rsp := framePointer s } := by
    rw [callEffect_returnBoundary e1, hrsp]
  have hrdi1 : rdi.read u1 = polyBase s := (callEffect_read e1 (r := 7) (by decide)).trans hrdi
  have hrsi1 : rsi.read u1 = rsi.read u := callEffect_read e1 (r := 6) (by decide)
  have hA1 : AgreesExcept (csA ++ [.reg 4, .mem (pushAddr u) 8, .rip]) t0 u1 := by
    have := hA.trans e1.agrees
    simpa only [pushEffect_components] using this
  have hpolyN : (polyBase s).toNat = (framePointer s).toNat + 0x150 := by
    unfold polyBase polyOffset
    rw [add_toNat _ _ (by omega)]
  have hbaseN : (Poly1305.Callee101e30.stackBase u1).toNat = (framePointer s).toNat - 96 := by
    unfold Poly1305.Callee101e30.stackBase Poly1305.Callee101e30.stackBytes
    rw [hrsp1, BitVec.sub_sub, ← BitVec.ofNat_add, sub_toNat _ _ (by omega)]
  have hrA : (Poly1305.Callee101e30.rAddress u1).toNat = (framePointer s).toNat + 0x160 := by
    unfold Poly1305.Callee101e30.rAddress rOffset
    rw [hrdi1, show (0x10 : BitVec 64) = BitVec.ofNat 64 0x10 from rfl,
      add_toNat _ _ (by omega), hpolyN]
  have hhA : (Poly1305.Callee101e30.hAddress u1).toNat = (framePointer s).toNat + 0x174 := by
    unfold Poly1305.Callee101e30.hAddress hOffset
    rw [hrdi1, show (0x24 : BitVec 64) = BitVec.ofNat 64 0x24 from rfl,
      add_toNat _ _ (by omega), hpolyN]
  have hkeep1 : ∀ x : BitVec 64, (x.toNat < (framePointer s).toNat - 8 ∨
      (framePointer s).toNat ≤ x.toNat) → u1.external[x]? = u.external[x]? := by
    intro x hx
    apply e1.agrees.byte
    intro c hc hcov
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · obtain ⟨i, hi, hx'⟩ := covers_toNat hcov (by omega)
      omega
    · exact hcov
  have hbase : Poly1305.Callee101e30.stackBase u1 = framePointer s - BitVec.ofNat 64 96 := by
    apply BitVec.eq_of_toNat_eq
    rw [hbaseN, sub_toNat _ 96 (by omega)]
  have hpushC : ∀ x, (Component.mem (pushAddr u) 8).Covers x →
      (Component.mem (framePointer s - BitVec.ofNat 64 96) 96).Covers x := by
    intro x hx
    exact covers_widen hx (by omega) (by rw [sub_toNat _ 96 (by omega)]; omega)
      (by rw [sub_toNat _ 96 (by omega), hpushN]; omega)
  have hblk1 : ∀ i < 16, u1.external[rsi.read u + BitVec.ofNat 64 i]? = some blk[i]! := by
    intro i hi
    rw [← hblk i hi]
    apply e1.agrees.byte
    intro c hc hcov
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · obtain ⟨j, hj, hje⟩ := hpushC _ hcov
      exact hblkApart i hi j hj hje
    · exact hcov
  have hbaseMem : ∀ i < 0x38, u1.external[polyBase s + BitVec.ofNat 64 i]? =
      u.external[polyBase s + BitVec.ofNat 64 i]? := by
    intro i hi
    apply hkeep1
    right
    rw [add_toNat _ _ (by omega), hpolyN]
    omega
  have hret5 : (p + BitVec.ofNat 64 5).toNat = p.toNat + 5 := add_toNat _ _ (by omega)
  have hpre1 : Poly1305.Callee101e30.CallPre u1 := by
    refine ⟨e1.rip.trans htarget, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact G.writableRange hA1 (by omega)
        (by simp only [Poly1305.Callee101e30.stackBytes]; omega)
    · exact (G.writableRange hA1 (by rw [hrsp1, sub_toNat _ _ (by omega)]; omega) (by rw [hrsp1, sub_toNat _ _ (by omega)]; omega)).readable
    · rw [hrsp1, sub_toNat _ _ (by omega)]; simp only [Poly1305.Callee101e30.stackBytes]; omega
    · exact (G.writableRange hA1 (by rw [hrA]; omega)
        (by rw [hrA]; omega)).readable
    · exact G.writableRange hA1 (by rw [hhA]; omega)
        (by rw [hhA]; omega)
    · rw [hrsi1]
      exact ⟨hblkLow, fun i hi => by rw [hblk1 i hi]; rfl⟩
    · exact rangeApart_of_toNat (by rw [hrA]; omega) (by rw [hbaseN]; simp only [Poly1305.Callee101e30.stackBytes]; omega)
        (by rw [hrA, hbaseN]; simp only [Poly1305.Callee101e30.stackBytes]; omega)
    · exact rangeApart_of_toNat (by rw [hhA]; omega) (by rw [hbaseN]; simp only [Poly1305.Callee101e30.stackBytes]; omega)
        (by rw [hhA, hbaseN]; simp only [Poly1305.Callee101e30.stackBytes]; omega)
    · rw [hrsi1, hbase]; exact hblkApart
    · rw [hrdi1, rLimbs_eq hbaseMem]; exact hpoly.rClamped
    · rw [hrdi1, hLimbs_eq hbaseMem]; exact hpoly.hBounded
    · rw [hret1]; dsimp only; omega
    · rw [hret1]
      dsimp only
      unfold Poly1305.Callee101e30.InCode Poly1305.Callee101e30.entry
        Poly1305.Callee101e30.bodyEntry
      have h1 : (0x101e30 : BitVec 64).toNat = 0x101e30 := rfl
      have h2 : (0x101ab0 : BitVec 64).toNat = 0x101ab0 := rfl
      rw [h1, h2, hret5]
      omega
  obtain ⟨fuel, v, a2, hres⟩ := Poly1305.Callee101e30.call boundary r1 hc1 hpre1
    (fun h => hOut (inCode_inProgram h))
    (by
      rw [hret1]
      exact (ne_boundary hOut (by dsimp only; rw [hret5]; omega)).symm)
  have hrspv : stackPtr v = framePointer s := by
    rw [hres.rsp, hrsp1]
    apply BitVec.eq_of_toNat_eq
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, add_toNat _ _ (by
      rw [sub_toNat _ _ (by omega)]; omega), sub_toNat _ _ (by omega)]
    omega
  have hagr : AgreesExcept (callFoot (framePointer s)) u v := by
    have h0 := e1.agrees.trans hres.agrees
    rw [pushEffect_components] at h0
    have h1 : AgreesExcept (.reg 4 :: callFoot (framePointer s)) u v := by
      apply h0.widen
      · intro c hc hm
        simp only [Poly1305.Callee101e30.callChanges, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hc
        simp only [callFoot, List.mem_cons, List.not_mem_nil, or_false]
        rcases hc with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl) <;> simp_all [Component.isMem]
      · intro x c hc hcov
        simp only [Poly1305.Callee101e30.callChanges, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hc
        rcases hc with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl) <;> try exact absurd hcov id
        · exact ⟨.mem (framePointer s - BitVec.ofNat 64 96) 96, by simp [callFoot], hpushC x hcov⟩
        · refine ⟨.mem (framePointer s - BitVec.ofNat 64 96) 96, by simp [callFoot], covers_widen hcov
            (by rw [hbaseN]; simp only [Poly1305.Callee101e30.stackBytes]; omega)
            (by rw [sub_toNat _ 96 (by omega)]; omega) ?_⟩
          rw [hbaseN, sub_toNat _ 96 (by omega)]
          simp only [Poly1305.Callee101e30.stackBytes]
          omega
        · refine ⟨.mem (framePointer s + BitVec.ofNat 64 0x174) 20, by simp [callFoot], covers_widen hcov
            (by rw [hhA]; omega)
            (by rw [add_toNat _ _ (by omega)]; omega) ?_⟩
          rw [hhA, add_toNat _ _ (by omega)]
          omega
    apply h1.narrow
    intro c hc hn
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · change v.GPR[gprIndex 4] = u.GPR[gprIndex 4]
      have := hrspv.trans hrsp.symm
      exact this
    · exact absurd hc hn
  have hcs1 : CalleeSavedRegistersUnchanged u u1 :=
    calleeSaved_of_agrees e1.agrees (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have hvMem : ∀ i < 0x24, v.external[polyBase s + BitVec.ofNat 64 i]? =
      u.external[polyBase s + BitVec.ofNat 64 i]? := by
    intro i hi
    apply hagr.byte
    intro c hc hcov
    simp only [callFoot, List.mem_cons, List.not_mem_nil, or_false] at hc
    have hx : (polyBase s + BitVec.ofNat 64 i).toNat = (framePointer s).toNat + 0x150 + i := by
      rw [add_toNat _ _ (by omega), hpolyN]
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> try exact hcov
    · obtain ⟨j, hj, hje⟩ := covers_toNat hcov (by rw [sub_toNat _ 96 (by omega)]; omega)
      rw [hx, sub_toNat _ 96 (by omega)] at hje
      omega
    · obtain ⟨j, hj, hje⟩ := covers_toNat hcov (by
        rw [add_toNat _ _ (by omega)]
        omega)
      rw [hx, add_toNat _ _ (by omega)] at hje
      omega
    · obtain ⟨j, hj, hje⟩ := covers_toNat hcov (by
        rw [add_toNat _ _ (by omega)]
        omega)
      rw [hx, add_toNat _ _ (by omega)] at hje
      omega
  have hblock : Poly1305.Callee101e30.block u1 = blk := by
    apply ByteArray.ext
    apply Array.ext
    · simp [Poly1305.Callee101e30.block, hsize, ByteArray.size_data]
    · intro i h1 h2
      simp only [Poly1305.Callee101e30.block, Array.getElem_ofFn]
      have hi : i < 16 := by simpa [hsize] using h2
      rw [hrsi1, hblk1 i hi]
      simp only [Option.getD_some]
      rw [getElem!_pos blk i (by omega)]
      rfl
  refine ⟨1 + fuel, v, a1.trans a2, hres.ready, hres.code, ?_, hrspv, hagr,
    calleeSaved_trans hcs1 hres.calleeSaved, ?_⟩
  · rw [hres.rip, hret1]
  · refine PolyState.transfer hpoly hvMem ?_ ?_
    · have := hres.bounded
      rwa [hrdi1] at this
    · have := hres.value
      rw [hrdi1, hblock, hLimbs_eq hbaseMem, rLimbs_eq hbaseMem, hpoly.rValue] at this
      rw [this]
      exact absorb_value hpoly.hValue

theorem rodata_readable {s : RamState} (hc : CodeIn Extracted.programImage s) (offset : Nat)
    (hoff : offset + 8 ≤ Extracted.rodataBytes.size) :
    MemReadable s (Extracted.rodataAddress + BitVec.ofNat 64 offset) 8 := by
  have hs := hc.slice_of_section (sec := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩)
    (by simp [Extracted.programSections]) offset 8 hoff
  refine ⟨?_, ?_⟩
  · have hr : Extracted.rodataAddress.toNat = 0x200000 := rfl
    have hsz : Extracted.rodataBytes.size < 0x10000 := by decide +kernel
    rw [toNat_add_ofNat _ _ (by omega), hr]
    omega
  · intro i hi
    have hl : i < (Extracted.rodataBytes.toListFrom offset 8).length := by
      rw [chunked_toListFrom_length]; omega
    have he := hs.bytesAt i hl
    rw [add_ofNat_add_ofNat] at he ⊢
    rw [he]
    rfl

set_option maxHeartbeats 1000000 in
theorem ptr_call_push [Bindings] {s t0 u : RamState} (G : Geometry s t0)
    {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip) {csA : List Component}
    (hA : AgreesExcept csA t0 u) (hr : ReadyToStep u) (hc : CodeIn Extracted.programImage u)
    (hrsp : stackPtr u = framePointer s)
    {p : BitVec 64} {d : BitVec 32} (hrip : u.RIP = p)
    (hbytes : CodeIn (codeRange p (encodeCallM64 (.rip d))) u)
    {offset : Nat} (hoff : offset + 8 ≤ Extracted.rodataBytes.size)
    (hslot : p + BitVec.ofNat 64 6 + d.signExtend 64 =
      Extracted.rodataAddress + BitVec.ofNat 64 offset)
    {entry : BitVec 64}
    (hentry : (Operand.mem (Extracted.rodataAddress + BitVec.ofNat 64 offset) : Operand 64).read u
      = entry)
    (hentryP : 0x100000 ≤ entry.toNat ∧ entry.toNat < 0x100000 + 11759)
    (hp : 0x100000 ≤ p.toNat ∧ p.toNat + 6 < 0x100000 + 11759) :
    ∃ u1, Advances boundary 1 u u1 ∧ ReadyToStep u1 ∧ CodeIn Extracted.programImage u1 ∧
      u1.RIP = entry ∧ stackPtr u1 = framePointer s - BitVec.ofNat 64 8 ∧
      returnBoundary u1 = { rip := p + BitVec.ofNat 64 6, rsp := framePointer s } ∧
      AgreesExcept [.reg 4, .mem (framePointer s - BitVec.ofNat 64 8) 8, .rip] u u1 := by
  have hPn := frame_toNat s G.low
  have hlow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hPn
  have hpush : pushAddr u = framePointer s - BitVec.ofNat 64 8 := by
    rw [pushAddr, hrsp]; rfl
  have hpushN : (pushAddr u).toNat = (framePointer s).toNat - 8 := by
    rw [hpush, sub_toNat _ _ (by omega)]
  have htgt : callMemPtr p (.rip d) u = entry := by
    show (Operand.mem (p + BitVec.ofNat 64 6 + d.signExtend 64) : Operand 64).read u = entry
    rw [hslot]; exact hentry
  have hpre : CallMemPre p (.rip d) u := by
    refine ⟨⟨⟨hrip, ?_, ?_⟩, ?_⟩, ?_⟩
    · exact G.memWritable hA (by omega)
        (by omega)
    · exact G.ne_code (by omega) (by omega)
        (inProg_range p _ (by simp [callMemLen, AddrMode.tail]; omega))
    · rw [htgt]; omega
    · show MemReadable u (p + BitVec.ofNat 64 6 + d.signExtend 64) 8
      rw [hslot]; exact rodata_readable hc offset hoff
  obtain ⟨u1, a1, r1, e1⟩ := (call_m64_effect_step p (.rip d) trivial rfl rfl).advances hr hbytes
    hpre (by
      change callMemPtr p (.rip d) u ≠ boundary.rip
      rw [htgt]; exact ne_boundary hOut hentryP)
  have hc1 : CodeIn Extracted.programImage u1 := by
    apply e1.codeIn _ hc
    intro x hx c hcm hcov
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl | rfl
    · exact hcov
    · obtain ⟨i, hi, hxi⟩ := hcov
      apply G.code _ _ (MemoryRoutines.Machine.inProgram_of_mem hx)
      unfold InStack
      rw [hxi, toNat_add_ofNat _ _ (by omega)]
      omega
    · exact hcov
  refine ⟨u1, a1, r1, hc1, e1.rip.trans htgt, (callEffect_rsp e1).trans hpush, ?_, ?_⟩
  · rw [callEffect_returnBoundary e1, hrsp]
    rfl
  · have := e1.agrees
    rwa [pushEffect_components, hpush] at this

structure Site where
  L : BitVec 64
  rex : UInt8
  disp : BitVec 32
  counter : BitVec 5

def adSite : Site := ⟨0x100880, 0x49, 0x15a4, 13⟩

def ctSite : Site := ⟨0x100930, 0x48, 0x14f4, 5⟩

def loopBytes (st : Site) : List UInt8 :=
  [0x4c, 0x8d, 0x76, 0x10, 0x4c, 0x89, 0xff] ++ encodeCallRel32 st.disp ++
    [0x4c, 0x89, 0xf6, st.rex, 0x83, 0xc5, 0xf0, 0x75, 0xeb]

def loopFoot (P : BitVec 64) (c : BitVec 5) : List Component :=
  .reg 14 :: .reg c :: callFoot P

theorem code_at {t : RamState} (hc : CodeIn Extracted.programImage t) (off : Nat)
    (bytes : List UInt8) (hle : off + bytes.length ≤ Extracted.textBytes.size)
    (h : Extracted.textBytes.toListFrom off bytes.length = bytes) :
    CodeIn (codeRange (BitVec.ofNat 64 (0x100000 + off)) bytes) t := by
  have := MemoryRoutines.Machine.program_text_slice hc off bytes.length hle
  rw [h] at this
  have he : Extracted.textAddress + BitVec.ofNat 64 off = BitVec.ofNat 64 (0x100000 + off) := by
    rw [BitVec.ofNat_add]; rfl
  rwa [he] at this

theorem site_code {st : Site} (hst : st = adSite ∨ st = ctSite) {t : RamState}
    (hc : CodeIn Extracted.programImage t) : CodeIn (codeRange st.L (loopBytes st)) t := by
  rcases hst with rfl | rfl
  · exact code_at hc 0x880 (loopBytes adSite) (by decide +kernel) (by decide +kernel)
  · exact code_at hc 0x930 (loopBytes ctSite) (by decide +kernel) (by decide +kernel)

structure LoopAt [Bindings] (st : Site) (s t0 e t : RamState) (cs : List Component)
    (ptr : BitVec 64) (bytes : ByteArray) (otk : Vector UInt8 32) (acc0 k : Nat) : Prop where
  track : Track (framePointer s) cs t0 t
  loop : AgreesExcept (loopFoot (framePointer s) st.counter) e t
  rip : t.RIP = st.L
  rsi : rsi.read t = ptr + BitVec.ofNat 64 (16 * k)
  counter : (Operand.reg st.counter : Operand 64).read t =
    BitVec.ofNat 64 (16 * (bytes.size / 16 - k))
  r15 : (Operand.reg 15 : Operand 64).read t = polyBase s
  poly : PolyState t (polyBase s) otk (absorbBlocks (clampedR otk) acc0 (bytes.extract 0 (16 * k)))

structure LoopDone [Bindings] (st : Site) (s t0 e t : RamState) (cs : List Component)
    (bytes : ByteArray) (otk : Vector UInt8 32) (acc0 : Nat) : Prop where
  track : Track (framePointer s) cs t0 t
  loop : AgreesExcept (loopFoot (framePointer s) st.counter) e t
  rip : t.RIP = st.L + BitVec.ofNat 64 21
  r15 : (Operand.reg 15 : Operand 64).read t = polyBase s
  poly : PolyState t (polyBase s) otk
    (absorbBlocks (clampedR otk) acc0 (bytes.extract 0 (16 * (bytes.size / 16))))

theorem extract_block_byte (bytes : ByteArray) (k i : Nat) (hk : 16 * k + 16 ≤ bytes.size)
    (hi : i < 16) : (bytes.extract (16 * k) (16 * k + 16))[i]! = bytes[16 * k + i]! := by
  have h1 : i < (bytes.extract (16 * k) (16 * k + 16)).size := by
    rw [ByteArray.size_extract]; omega
  rw [getElem!_pos _ i h1, getElem!_pos _ _ (by omega), ByteArray.getElem_extract]

theorem extract_block_size (bytes : ByteArray) (k : Nat) (hk : 16 * k + 16 ≤ bytes.size) :
    (bytes.extract (16 * k) (16 * k + 16)).size = 16 := by
  rw [ByteArray.size_extract]; omega

theorem loopFoot_mem {P : BitVec 64} {c : BitVec 5} {cs : List Component}
    (hcs : ∀ x ∈ loopFoot P c, x ∈ cs) : ∀ x ∈ callFoot P, x ∈ cs :=
  fun x hx => hcs x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))

theorem dec16 (m : Nat) (hm : 1 ≤ m) (hb : 16 * m ≤ 2 ^ 32) :
    BitVec.ofNat 64 (16 * m) + BitVec.signExtend 64 (0xf0 : BitVec 8) =
      BitVec.ofNat 64 (16 * (m - 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((0xf0 : BitVec 8).signExtend 64).toNat = 2 ^ 64 - 16 from rfl]
  omega

theorem ofNat16_beq_zero (m : Nat) (hb : 16 * m ≤ 2 ^ 32) :
    (BitVec.ofNat 64 (16 * m) == 0) = decide (m = 0) := by
  by_cases h : m = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 (16 * m) ≠ 0 := by
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat] at this
      simp at this
      omega
    simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]; exact this

theorem loopExt {F cs' : List Component} {e t t' : RamState} (h : AgreesExcept F e t)
    (h' : AgreesExcept cs' t t') (hs : ∀ c ∈ cs', c ∈ F) : AgreesExcept F e t' :=
  (h.trans h').mono (by
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hc
    · exact hs c hc)

theorem regOnly_external {cs : List Component} {u v : RamState} (h : AgreesExcept cs u v)
    (hcs : ∀ c ∈ cs, c.isMem = false) (x : BitVec 64) : v.external[x]? = u.external[x]? := by
  rw [h.external (fun c hc y hy => regOnly hcs y c hc hy False)]

set_option maxHeartbeats 4000000 in
theorem loop_iter [Bindings] {st : Site} (hst : st = adSite ∨ st = ctSite)
    {s t0 e : RamState} (G : Geometry s t0) {boundary : ReturnBoundary}
    (hOut : ¬ InProgram boundary.rip)
    {cs : List Component} (hcs : ∀ c ∈ loopFoot (framePointer s) st.counter, c ∈ cs)
    {ptr : BitVec 64} {bytes : ByteArray} {otk : Vector UInt8 32} {acc0 : Nat}
    (hlow : ptr.toNat + bytes.size ≤ 2 ^ 32)
    (hmem : ∀ i < bytes.size, t0.external[ptr + BitVec.ofNat 64 i]? = some bytes[i]!)
    (hfar : ∀ c ∈ cs, ∀ i < bytes.size, ¬ c.Covers (ptr + BitVec.ofNat 64 i))
    {k : Nat} (hk : k < bytes.size / 16) {t : RamState}
    (H : LoopAt st s t0 e t cs ptr bytes otk acc0 k) :
    ∃ fuel t', Advances boundary fuel t t' ∧
      ((k + 1 < bytes.size / 16 ∧ LoopAt st s t0 e t' cs ptr bytes otk acc0 (k + 1)) ∨
       (k + 1 = bytes.size / 16 ∧ LoopDone st s t0 e t' cs bytes otk acc0)) := by
  have hcode := site_code hst H.track.code
  have hL : 0x100000 ≤ st.L.toNat ∧ st.L.toNat + 22 ≤ 0x100000 + 11759 := by
    rcases hst with rfl | rfl <;> decide
  have hLn : ∀ j, j ≤ 21 → (st.L + BitVec.ofNat 64 j).toNat = st.L.toNat + j :=
    fun j hj => add_toNat _ _ (by omega)
  have hfoot := loopFoot_mem hcs
  obtain ⟨t1, a1, T1, e1⟩ := H.track.step
    (lea_r64_effect_step st.L 0x4c (by unfold RexWPrefix; decide) 6 (.base 6 (.d8 0x10)) (by decide) (by decide)
      (by decide))
    (hcode.mono (codeRange_mem_of_take (all := loopBytes st) (by rcases hst with rfl | rfl <;> decide)))
    H.rip (ne_boundary hOut (a := st.L + BitVec.ofNat 64 4) (by rw [hLn 4 (by omega)]; omega))
    (by
      intro c hc _
      simp only [leaR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hcs _ (by simp [loopFoot]; left; decide)
      · exact hfoot _ (by simp [callFoot]))
    (fun x c hc hcov => regOnly (by
      simp only [leaR64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl) <;> rfl) x c hc hcov _)
    (by simp only [leaR64Effect_components]; decide)
  change (leaR64Effect st.L 14 (.base 6 (.d8 0x10)) t).Holds t t1 at e1
  have hr14_1 : (Operand.reg 14 : Operand 64).read t1 = rsi.read t + 0x10 := e1.writes
  have hrip1 : t1.RIP = st.L + BitVec.ofNat 64 4 := e1.rip
  obtain ⟨t2, a2, T2, e2⟩ := T1.step
    (mov_r64_r64_effect_step (st.L + BitVec.ofNat 64 4) 0x4c 0xff (by unfold RexWPrefix; decide) (by decide))
    ((site_code hst T1.code).mono (codeRange_mem_of_drop (p := st.L) (all := loopBytes st) 4 (by rcases hst with rfl | rfl <;> decide)))
    hrip1 (ne_boundary_add hOut (a := 4) (b := 3) (by omega))
    (by
      intro c hc _
      simp only [movR64R64Effect, Effect.components, List.map, Write.component_reg,
        List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      rcases hc with rfl | rfl
      · exact hfoot _ (by simp [callFoot]; decide)
      · exact hfoot _ (by simp [callFoot]))
    (fun x c hc hcov => regOnly (by
      simp only [movR64R64Effect, Effect.components, List.map, Write.component_reg,
        List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false]
      rintro c (rfl | rfl) <;> rfl) x c hc hcov _)
    (by simp only [movR64R64Effect, Effect.components, List.map, Write.component_reg]; decide)
  change (movR64R64Effect (st.L + BitVec.ofNat 64 4) 7 15 t1).Holds t1 t2 at e2
  have hrip2 : t2.RIP = st.L + BitVec.ofNat 64 7 := by
    rw [e2.rip]; simp only [movR64R64Effect]
    rw [show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, add_ofNat_add_ofNat]
  have hrdi2 : rdi.read t2 = polyBase s := by
    have h := e2.writes
    simp only [movR64R64Effect, Write.AllHold] at h
    rw [show rdi = (Operand.reg 7 : Operand 64) from rfl, h, e1.agrees.read (by simp <;> decide),
      H.r15]
  have hrsi2 : rsi.read t2 = ptr + BitVec.ofNat 64 (16 * k) := by
    rw [show rsi = (Operand.reg 6 : Operand 64) from rfl, e2.agrees.read (by simp <;> decide),
      e1.agrees.read (by simp <;> decide)]
    exact H.rsi
  have hr14_2 : (Operand.reg 14 : Operand 64).read t2 = rsi.read t + 0x10 := by
    rw [e2.agrees.read (by simp <;> decide), hr14_1]
  have hr15_2 : (Operand.reg 15 : Operand 64).read t2 = polyBase s := by
    rw [e2.agrees.read (by simp <;> decide), e1.agrees.read (by simp <;> decide), H.r15]
  have hcnt2 : (Operand.reg st.counter : Operand 64).read t2 =
      BitVec.ofNat 64 (16 * (bytes.size / 16 - k)) := by
    rw [e2.agrees.read (by rcases hst with rfl | rfl <;> simp <;> decide),
      e1.agrees.read (by rcases hst with rfl | rfl <;> simp <;> decide)]
    exact H.counter
  have hmem12 : ∀ x : BitVec 64, t2.external[x]? = t.external[x]? := by
    intro x
    rw [e2.agrees.external (by
      simp only [movR64R64Effect, Effect.components, List.map, Write.component_reg,
        List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false]
      rintro c (rfl | rfl) x h <;> exact h),
      e1.agrees.external (by
      simp only [leaR64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl) x h <;> exact h)]
  have h16 : 16 * k + 16 ≤ bytes.size := by omega
  have hblkByte : ∀ i < 16, t2.external[rsi.read t2 + BitVec.ofNat 64 i]? =
      some (bytes.extract (16 * k) (16 * k + 16))[i]! := by
    intro i hi
    rw [hrsi2, add_ofNat_add_ofNat, T2.agrees.byte (fun c hc => hfar c hc _ (by omega)),
      hmem _ (by omega), extract_block_byte bytes k i h16 hi]
  have hP := frame_toNat s G.low
  have hglow := G.low
  have hghigh := G.high
  simp only [frameBytes] at hP
  obtain ⟨f3, t3, a3, r3, c3, hrip3, hrsp3, hag3, hcs3, hpoly3⟩ := poly_call (disp := st.disp) G hOut T2.agrees
    T2.ready T2.code T2.rsp hrip2
    ((site_code hst T2.code).mono (codeRange_mem_of_drop (p := st.L) (all := loopBytes st) 7 (by rcases hst with rfl | rfl <;> decide)))
    (by rcases hst with rfl | rfl <;> decide)
    (by rw [hLn 7 (by omega)]; rcases hst with rfl | rfl <;> simp [adSite, ctSite] <;> decide)
    hrdi2 (extract_block_size bytes k h16)
    (by rw [hrsi2, add_toNat _ _ (by omega)]; omega)
    hblkByte
    (by
      intro i hi j hj he
      rw [hrsi2, add_ofNat_add_ofNat] at he
      exact hfar (.mem (framePointer s - BitVec.ofNat 64 96) 96) (hfoot _ (by simp [callFoot]))
        (16 * k + i) (by omega) ⟨j, hj, he⟩)
    (PolyState.of_mem H.poly fun i _ => hmem12 _)
  have hrip3' : t3.RIP = st.L + BitVec.ofNat 64 12 := by
    rw [hrip3, add_ofNat_add_ofNat]
  have hsaved := fun r (hr : r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15]) => hcs3 r hr
  have hr14_3 : (Operand.reg 14 : Operand 64).read t3 = rsi.read t + 0x10 := by
    have := hsaved .r14 (by simp)
    rw [(regValue_read t3).2.2.2.2.2.2.2.2.2.2.1, (regValue_read t2).2.2.2.2.2.2.2.2.2.2.1] at this
    rw [this, hr14_2]
  have hr15_3 : (Operand.reg 15 : Operand 64).read t3 = polyBase s := by
    have := hsaved .r15 (by simp)
    rw [(regValue_read t3).2.2.2.2.2.2.2.2.2.2.2.1, (regValue_read t2).2.2.2.2.2.2.2.2.2.2.2.1] at this
    rw [this, hr15_2]
  have hcnt3 : (Operand.reg st.counter : Operand 64).read t3 =
      BitVec.ofNat 64 (16 * (bytes.size / 16 - k)) := by
    rcases hst with rfl | rfl
    · have := hsaved .r13 (by simp)
      rw [(regValue_read t3).2.2.2.2.2.2.2.2.2.1, (regValue_read t2).2.2.2.2.2.2.2.2.2.1] at this
      exact this.trans hcnt2
    · have := hsaved .rbp (by simp)
      rw [(regValue_read t3).2.2.2.2.2.2.2.1, (regValue_read t2).2.2.2.2.2.2.2.1] at this
      exact this.trans hcnt2
  have T3 : Track (framePointer s) cs t0 t3 :=
    T2.extend r3 c3 hag3 hrsp3 (fun c hc _ => hfoot c hc)
      (fun x c hc hx => ⟨c, hfoot c hc, hx⟩)
  obtain ⟨t4, a4, T4, e4⟩ := T3.step
    (mov_r64_r64_effect_step (st.L + BitVec.ofNat 64 12) 0x4c 0xf6 (by unfold RexWPrefix; decide) (by decide))
    ((site_code hst T3.code).mono (codeRange_mem_of_drop (p := st.L) (all := loopBytes st) 12 (by rcases hst with rfl | rfl <;> decide)))
    hrip3' (ne_boundary_add hOut (a := 12) (b := 3) (by omega))
    (by
      intro c hc _
      simp only [movR64R64Effect, Effect.components, List.map, Write.component_reg,
        List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      rcases hc with rfl | rfl
      · exact hfoot _ (by simp [callFoot]; decide)
      · exact hfoot _ (by simp [callFoot]))
    (fun x c hc hcov => regOnly (by
      simp only [movR64R64Effect, Effect.components, List.map, Write.component_reg,
        List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false]
      rintro c (rfl | rfl) <;> rfl) x c hc hcov _)
    (by simp only [movR64R64Effect, Effect.components, List.map, Write.component_reg]; decide)
  change (movR64R64Effect (st.L + BitVec.ofNat 64 12) 6 14 t3).Holds t3 t4 at e4
  have hrip4 : t4.RIP = st.L + BitVec.ofNat 64 15 := by
    rw [e4.rip]; simp only [movR64R64Effect]
    rw [show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, add_ofNat_add_ofNat]
  have hrsi4 : rsi.read t4 = ptr + BitVec.ofNat 64 (16 * (k + 1)) := by
    have h := e4.writes
    simp only [movR64R64Effect, Write.AllHold] at h
    rw [show rsi = (Operand.reg 6 : Operand 64) from rfl, h, hr14_3, H.rsi,
      show (0x10 : BitVec 64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add_ofNat]
    congr 2
  have hcnt4 : (Operand.reg st.counter : Operand 64).read t4 =
      BitVec.ofNat 64 (16 * (bytes.size / 16 - k)) := by
    rw [e4.agrees.read (by rcases hst with rfl | rfl <;> simp <;> decide), hcnt3]
  have hr15_4 : (Operand.reg 15 : Operand 64).read t4 = polyBase s := by
    rw [e4.agrees.read (by simp <;> decide), hr15_3]
  have hdst : gprNumber 0 (rexB st.rex.toBitVec) (modrmRm 0xc5) = st.counter := by
    rcases hst with rfl | rfl <;> decide
  obtain ⟨t5, a5, T5, e5⟩ := T4.step
    (add_r64_imm8_effect_step (st.L + BitVec.ofNat 64 15) st.rex 0xc5 0xf0
      (by rcases hst with rfl | rfl <;> unfold RexWPrefix <;> decide) (by decide) (by decide))
    ((site_code hst T4.code).mono (codeRange_mem_of_drop (p := st.L) (all := loopBytes st) 15 (by rcases hst with rfl | rfl <;> decide)))
    hrip4 (ne_boundary_add hOut (a := 15) (b := 4) (by omega))
    (by
      intro c hc _
      rw [addR64Imm8Effect_components, hdst] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact hcs _ (by simp [loopFoot])
      · exact hfoot _ (by simp [callFoot])
      · exact hfoot _ (by simp [callFoot]))
    (fun x c hc hcov => regOnly (by
      rw [addR64Imm8Effect_components]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl | rfl) <;> rfl) x c hc hcov _)
    (by rw [addR64Imm8Effect_components, hdst]; rcases hst with rfl | rfl <;> decide)
  rw [hdst] at e5
  have hrip5 : t5.RIP = st.L + BitVec.ofNat 64 19 := by
    rw [e5.rip]; simp only [addR64Imm8Effect]
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, add_ofNat_add_ofNat]
  have hn : 16 * (bytes.size / 16) ≤ 2 ^ 32 := by omega
  have hval5 : (Operand.reg st.counter : Operand 64).read t5 =
      BitVec.ofNat 64 (16 * (bytes.size / 16 - (k + 1))) := by
    have h := e5.writes
    simp only [addR64Imm8Effect, Write.AllHold] at h
    rw [h, hcnt4, dec16 _ (by omega) (by omega)]
    congr 2
  have hzf : (StatusFlags.ofRFLAGS t5.RFLAGS).ZF = decide (k + 1 = bytes.size / 16) := by
    have h := e5.flags
    simp only [addR64Imm8Effect, Effect.FlagsHold, StatusFlagsOutcome.ofStatusFlags,
      StatusFlagsOutcome.Allows, FlagAllows] at h
    rw [h.2.2.2.1]
    simp only [addSpec, hcnt4]
    rw [dec16 _ (by omega) (by omega), ofNat16_beq_zero _ (by omega)]
    simp only [decide_eq_decide]
    omega
  have htgt : branchTarget (st.L + BitVec.ofNat 64 19) 2 ((0xeb : BitVec 8).signExtend 64) =
      st.L := by
    rcases hst with rfl | rfl <;> decide
  obtain ⟨t6, a6, T6, e6⟩ := T5.step (jcc_rel8_effect_step (st.L + BitVec.ofNat 64 19) 5 0xeb)
    ((site_code hst T5.code).mono (codeRange_mem_of_drop (p := st.L) (all := loopBytes st) 19
      (by rcases hst with rfl | rfl <;> decide)))
    ⟨hrip5, fun _ => by rw [htgt]; omega⟩
    (by
      simp only [jccEffect, branchEffect]
      split
      · rw [htgt]; exact ne_boundary hOut (by omega)
      · exact ne_boundary_add hOut (a := 19) (b := 2) (by omega))
    (by
      intro c hc _
      simp only [jccEffect, branchEffect_components, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      subst hc
      exact hfoot _ (by simp [callFoot]))
    (fun x c hc hcov => regOnly (by
      simp only [jccEffect, branchEffect_components, List.mem_cons, List.not_mem_nil,
        or_false]
      rintro c rfl; rfl) x c hc hcov _)
    (by simp [jccEffect])
  have hrip6 : t6.RIP = if k + 1 = bytes.size / 16 then st.L + BitVec.ofNat 64 21 else st.L := by
    rw [e6.rip]
    simp only [jccEffect, branchEffect, condHolds_5, hzf, htgt]
    by_cases hl : k + 1 = bytes.size / 16
    · simp [hl, add_ofNat_add_ofNat]
    · simp [hl]
  have hreg5 : ∀ c ∈ (addR64Imm8Effect (st.L + BitVec.ofNat 64 15) st.counter 0xf0 t4).components,
      c.isMem = false := by
    rw [addR64Imm8Effect_components]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl) <;> rfl
  have hreg6 : ∀ c ∈ (jccEffect (st.L + BitVec.ofNat 64 19) 2 5 ((0xeb : BitVec 8).signExtend 64)
      t5).components, c.isMem = false := by
    simp only [jccEffect, branchEffect_components, List.mem_cons, List.not_mem_nil, or_false]
    rintro c rfl; rfl
  have hreg4 : ∀ c ∈ (movR64R64Effect (st.L + BitVec.ofNat 64 12) 6 14 t3).components,
      c.isMem = false := by
    simp only [movR64R64Effect, Effect.components, List.map, Write.component_reg,
      List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false]
    rintro c (rfl | rfl) <;> rfl
  have hmem36 : ∀ x : BitVec 64, t6.external[x]? = t3.external[x]? := by
    intro x
    rw [regOnly_external e6.agrees hreg6, regOnly_external e5.agrees hreg5,
      regOnly_external e4.agrees hreg4]
  have hpoly6 : PolyState t6 (polyBase s) otk
      (absorbBlocks (clampedR otk) acc0 (bytes.extract 0 (16 * (k + 1)))) := by
    rw [absorbBlocks_succ _ _ _ _ (by omega)]
    exact PolyState.of_mem hpoly3 fun i _ => hmem36 _
  have hloop6 : AgreesExcept (loopFoot (framePointer s) st.counter) e t6 := by
    refine loopExt (loopExt (loopExt (loopExt (loopExt (loopExt H.loop e1.agrees ?_)
      e2.agrees ?_) hag3 ?_) e4.agrees ?_) e5.agrees ?_) e6.agrees ?_
    · simp only [leaR64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl) <;> simp [loopFoot, callFoot]
    · simp only [movR64R64Effect, Effect.components, List.map, Write.component_reg,
        List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false]
      rintro c (rfl | rfl) <;> simp [loopFoot, callFoot] <;> decide
    · intro c hc; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)
    · simp only [movR64R64Effect, Effect.components, List.map, Write.component_reg,
        List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false]
      rintro c (rfl | rfl) <;> simp [loopFoot, callFoot] <;> decide
    · rw [addR64Imm8Effect_components]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl | rfl) <;> simp [loopFoot, callFoot]
    · simp only [jccEffect, branchEffect_components, List.mem_cons, List.not_mem_nil, or_false]
      rintro c rfl; simp [loopFoot, callFoot]
  have hr15_6 : (Operand.reg 15 : Operand 64).read t6 = polyBase s := by
    rw [e6.agrees.read (by simp [jccEffect]), e5.agrees.read (by
      rw [addR64Imm8Effect_components]; rcases hst with rfl | rfl <;> decide), hr15_4]
  refine ⟨1 + 1 + f3 + 1 + 1 + 1, t6,
    ((((a1.trans a2).trans a3).trans a4).trans a5).trans a6, ?_⟩
  by_cases hl : k + 1 = bytes.size / 16
  · right
    refine ⟨hl, T6, hloop6, by simp [hrip6, hl], hr15_6, ?_⟩
    rw [← hl]; exact hpoly6
  · left
    refine ⟨by omega, T6, hloop6, by simp [hrip6, hl], ?_, ?_, hr15_6, hpoly6⟩
    · rw [show rsi = (Operand.reg 6 : Operand 64) from rfl, e6.agrees.read (by simp [jccEffect]),
        e5.agrees.read (by rw [addR64Imm8Effect_components]; rcases hst with rfl | rfl <;> decide)]
      exact hrsi4
    · rw [e6.agrees.read (by simp [jccEffect]), hval5]

theorem loop_run [Bindings] {st : Site} (hst : st = adSite ∨ st = ctSite)
    {s t0 e : RamState} (G : Geometry s t0) {boundary : ReturnBoundary}
    (hOut : ¬ InProgram boundary.rip)
    {cs : List Component} (hcs : ∀ c ∈ loopFoot (framePointer s) st.counter, c ∈ cs)
    {ptr : BitVec 64} {bytes : ByteArray} {otk : Vector UInt8 32} {acc0 : Nat}
    (hlow : ptr.toNat + bytes.size ≤ 2 ^ 32)
    (hmem : ∀ i < bytes.size, t0.external[ptr + BitVec.ofNat 64 i]? = some bytes[i]!)
    (hfar : ∀ c ∈ cs, ∀ i < bytes.size, ¬ c.Covers (ptr + BitVec.ofNat 64 i)) :
    ∀ m k t, k + m = bytes.size / 16 → k < bytes.size / 16 →
      LoopAt st s t0 e t cs ptr bytes otk acc0 k →
      ∃ fuel t', Advances boundary fuel t t' ∧ LoopDone st s t0 e t' cs bytes otk acc0 := by
  intro m
  induction m with
  | zero => intro k t hm hk _; omega
  | succ m ih =>
    intro k t hm hk H
    obtain ⟨f, t', a, h⟩ := loop_iter hst G hOut hcs hlow hmem hfar hk H
    rcases h with ⟨hk', H'⟩ | ⟨_, D⟩
    · obtain ⟨f', t'', a', D⟩ := ih (k + 1) t' (by omega) hk' H'
      exact ⟨f + f', t'', a.trans a', D⟩
    · exact ⟨f, t', a, D⟩

theorem routine_post [Bindings] {s t0 u u1 v : RamState} (G : Geometry s t0)
    (hrsp : stackPtr u = framePointer s)
    (hpush : AgreesExcept [.reg 4, .mem (framePointer s - BitVec.ofNat 64 8) 8, .rip] u u1)
    (hres : MemoryRoutines.CallResult u1 v) (hrsp1 : stackPtr u1 = framePointer s - BitVec.ofNat 64 8)
    (hdst : (framePointer s).toNat + 0x18 ≤ (rdi.read u1).toNat ∧
      (rdi.read u1).toNat + (MemoryRoutines.rdx.read u1).toNat ≤ (framePointer s).toNat + 0x28) :
    stackPtr v = framePointer s ∧ AgreesExcept (callFoot (framePointer s)) u v ∧
      CalleeSavedRegistersUnchanged u v ∧
      ∀ x : BitVec 64, (framePointer s).toNat ≤ x.toNat → (x.toNat < (rdi.read u1).toNat ∨
        (rdi.read u1).toNat + (MemoryRoutines.rdx.read u1).toNat ≤ x.toNat) →
        v.external[x]? = u.external[x]? := by
  have hP := frame_toNat s G.low
  have hlow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hP
  have hrspv : stackPtr v = framePointer s := by
    rw [hres.rsp, hrsp1]
    apply BitVec.eq_of_toNat_eq
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, add_toNat _ _ (by
      rw [sub_toNat _ _ (by omega)]; omega), sub_toNat _ _ (by omega)]
    omega
  have h0 := hpush.trans hres.agrees
  have h1 : AgreesExcept (.reg 4 :: callFoot (framePointer s)) u v := by
    apply h0.widen
    · intro c hc hm
      simp only [MemoryRoutines.callChanges, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      simp only [callFoot, List.mem_cons, List.not_mem_nil, or_false]
      rcases hc with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl) <;> simp_all [Component.isMem]
    · intro x c hc hcov
      simp only [MemoryRoutines.callChanges, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl) <;> try exact absurd hcov id
      · exact ⟨.mem (framePointer s - BitVec.ofNat 64 96) 96, by simp [callFoot],
          covers_widen hcov (by rw [sub_toNat _ _ (by omega)]; omega)
            (by rw [sub_toNat _ 96 (by omega)]; omega)
            (by rw [sub_toNat _ 96 (by omega), sub_toNat _ _ (by omega)]; omega)⟩
      · exact ⟨.mem (framePointer s + BitVec.ofNat 64 0x18) 16, by simp [callFoot],
          covers_widen hcov (by omega) (by rw [add_toNat _ _ (by omega)]; omega)
            (by rw [add_toNat _ _ (by omega)]; omega)⟩
  refine ⟨hrspv, ?_, ?_, ?_⟩
  · apply h1.narrow
    intro c hc hn
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · change v.GPR[gprIndex 4] = u.GPR[gprIndex 4]
      exact hrspv.trans hrsp.symm
    · exact absurd hc hn
  · exact calleeSaved_trans
      (calleeSaved_of_agrees hpush (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
      hres.calleeSaved
  · intro x hx hout
    apply h0.byte
    intro c hc hcov
    simp only [MemoryRoutines.callChanges, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl) <;> try exact hcov
    · obtain ⟨i, hi, he⟩ := covers_toNat hcov (by rw [sub_toNat _ _ (by omega)]; omega)
      rw [sub_toNat _ _ (by omega)] at he
      omega
    · obtain ⟨i, hi, he⟩ := covers_toNat hcov (by omega)
      omega

set_option maxHeartbeats 1000000 in
theorem routine_pre [Bindings] {s t0 u u1 : RamState} (G : Geometry s t0) {csA : List Component}
    (hA : AgreesExcept csA t0 u)
    (hpush : AgreesExcept [.reg 4, .mem (framePointer s - BitVec.ofNat 64 8) 8, .rip] u u1)
    (hrsp1 : stackPtr u1 = framePointer s - BitVec.ofNat 64 8)
    {p : BitVec 64}
    (hret : returnBoundary u1 = { rip := p + BitVec.ofNat 64 6, rsp := framePointer s })
    (hp : 0x100000 ≤ p.toNat ∧ p.toNat + 6 < 0x102d70)
    (hdf : DirectionFlagClear u.RFLAGS)
    {entry : BitVec 64} {len : Nat} (hentry : u1.RIP = entry) (hlen : 0x102d70 ≤ entry.toNat)
    (hdst : (framePointer s).toNat + 0x18 ≤ (rdi.read u).toNat ∧
      (rdi.read u).toNat + (MemoryRoutines.rdx.read u).toNat ≤ (framePointer s).toNat + 0x28) :
    MemoryRoutines.CallPre entry len u1 ∧ rdi.read u1 = rdi.read u ∧
      MemoryRoutines.rdx.read u1 = MemoryRoutines.rdx.read u ∧ rsi.read u1 = rsi.read u := by
  have hP := frame_toNat s G.low
  have hlow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hP
  have hdi : rdi.read u1 = rdi.read u := hpush.read (by simp)
  have hdx : MemoryRoutines.rdx.read u1 = MemoryRoutines.rdx.read u := hpush.read (by simp)
  have hsi : rsi.read u1 = rsi.read u := hpush.read (by simp)
  have hA1 := hA.trans hpush
  refine ⟨⟨hentry, (hpush.directionFlagClear (by simp) ⟨hdf⟩).df, ?_, ?_, ?_, ?_, ?_⟩, hdi, hdx, hsi⟩
  · rw [hdi, hdx]
    exact G.writableRange hA1 (by omega) (by omega)
  · rw [hrsp1]
    exact (G.writableRange hA1 (by rw [sub_toNat _ _ (by omega)]; omega)
      (by rw [sub_toNat _ _ (by omega)]; omega)).readable
  · rw [hdi, hdx, hrsp1]
    exact rangeApart_of_toNat (by omega) (by rw [sub_toNat _ _ (by omega)]; omega)
      (by rw [sub_toNat _ _ (by omega)]; omega)
  · rw [hret]; dsimp only; rw [add_toNat _ _ (by omega)]; omega
  · rw [hret]; dsimp only; rw [add_toNat _ _ (by omega)]; omega

theorem outside_routine {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip)
    {a b : Nat} (ha : 0x100000 ≤ a) (hb : b ≤ 0x100000 + 11759) :
    boundary.rip.toNat < a ∨ b ≤ boundary.rip.toNat := by
  rcases Nat.lt_or_ge boundary.rip.toNat a with h | h
  · exact .inl h
  rcases Nat.lt_or_ge boundary.rip.toNat b with h' | h'
  · exact absurd (inProg _ ⟨by omega, by omega⟩) hOut
  · exact .inr h'

set_option maxHeartbeats 1000000 in
theorem memset_call [inst : Bindings] (hstride : UnitStringStride inst) {s t0 u : RamState}
    (G : Geometry s t0) {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip)
    {csA : List Component} (hA : AgreesExcept csA t0 u) (hr : ReadyToStep u)
    (hc : CodeIn Extracted.programImage u) (hrsp : stackPtr u = framePointer s)
    (hdf : DirectionFlagClear u.RFLAGS)
    {p : BitVec 64} {d : BitVec 32} (hrip : u.RIP = p)
    (hbytes : CodeIn (codeRange p (encodeCallM64 (.rip d))) u)
    (hslot : p + BitVec.ofNat 64 6 + d.signExtend 64 =
      Extracted.rodataAddress + BitVec.ofNat 64 0x13e0)
    (hp : 0x100000 ≤ p.toNat ∧ p.toNat + 6 < 0x102d70)
    (hdst : (framePointer s).toNat + 0x18 ≤ (rdi.read u).toNat ∧
      (rdi.read u).toNat + (MemoryRoutines.rdx.read u).toNat ≤ (framePointer s).toNat + 0x28) :
    ∃ fuel v, Advances boundary fuel u v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      v.RIP = p + BitVec.ofNat 64 6 ∧ stackPtr v = framePointer s ∧
      AgreesExcept (callFoot (framePointer s)) u v ∧ CalleeSavedRegistersUnchanged u v ∧
      DirectionFlagClear v.RFLAGS ∧
      (∀ x : BitVec 64, (framePointer s).toNat ≤ x.toNat → (x.toNat < (rdi.read u).toNat ∨
        (rdi.read u).toNat + (MemoryRoutines.rdx.read u).toNat ≤ x.toNat) →
        v.external[x]? = u.external[x]?) ∧
      ∀ i < (MemoryRoutines.rdx.read u).toNat, v.external[rdi.read u + BitVec.ofNat 64 i]? =
        some (UInt8.ofBitVec ((rsi.read u).setWidth 8)) := by
  obtain ⟨u1, a1, r1, c1, hrip1, hrsp1, hret1, hpush⟩ := ptr_call_push (entry := 0x102d70)
    G hOut hA hr hc hrsp hrip hbytes (offset := 0x13e0) (by decide +kernel) hslot
    (MemoryContracts.memset_slot u hc) (by decide) (by omega)
  obtain ⟨hpre, hdi, hdx, hsi⟩ := routine_pre (len := 69) G hA hpush hrsp1 hret1 hp hdf hrip1
    (by decide) hdst
  obtain ⟨fuel, v, a2, hres⟩ := MemoryRoutines.memset_advances hstride boundary
    (outside_routine hOut (by decide) (by decide)) u1 r1 c1 hpre
    (by rw [hret1]; exact ne_boundary hOut (by dsimp only; rw [add_toNat _ _ (by omega)]; omega))
  obtain ⟨hrspv, hagr, hcs, hkeep⟩ := routine_post G hrsp hpush hres.toCallResult hrsp1
    (by rw [hdi, hdx]; exact hdst)
  refine ⟨1 + fuel, v, a1.trans a2, hres.ready, hres.codeIn hpre.dst c1, ?_, hrspv, hagr, hcs,
    hres.toCallResult.directionFlagClear hpre.df, by rw [hdi, hdx] at hkeep; exact hkeep, ?_⟩
  · rw [hres.rip, hret1]
  · intro i hi
    have := hres.fill i (by rw [hdx]; exact hi)
    rwa [hdi, hsi] at this

set_option maxHeartbeats 1000000 in
theorem memcpy_call [inst : Bindings] (hstride : UnitStringStride inst) {s t0 u : RamState}
    (G : Geometry s t0) {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip)
    {csA : List Component} (hA : AgreesExcept csA t0 u) (hr : ReadyToStep u)
    (hc : CodeIn Extracted.programImage u) (hrsp : stackPtr u = framePointer s)
    (hdf : DirectionFlagClear u.RFLAGS)
    {p : BitVec 64} {d : BitVec 32} (hrip : u.RIP = p)
    (hbytes : CodeIn (codeRange p (encodeCallM64 (.rip d))) u)
    (hslot : p + BitVec.ofNat 64 6 + d.signExtend 64 =
      Extracted.rodataAddress + BitVec.ofNat 64 0x13a8)
    (hp : 0x100000 ≤ p.toNat ∧ p.toNat + 6 < 0x102d70)
    (hdst : (framePointer s).toNat + 0x18 ≤ (rdi.read u).toNat ∧
      (rdi.read u).toNat + (MemoryRoutines.rdx.read u).toNat ≤ (framePointer s).toNat + 0x28)
    (hsrc : (rsi.read u).toNat + (MemoryRoutines.rdx.read u).toNat ≤ 2 ^ 32)
    (hsrcMem : ∀ i < (MemoryRoutines.rdx.read u).toNat,
      (u.external[rsi.read u + BitVec.ofNat 64 i]?).isSome)
    (hsrcApart : RangeApart (rsi.read u) (MemoryRoutines.rdx.read u).toNat
      (framePointer s - BitVec.ofNat 64 96) 0x90) :
    ∃ fuel v, Advances boundary fuel u v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      v.RIP = p + BitVec.ofNat 64 6 ∧ stackPtr v = framePointer s ∧
      AgreesExcept (callFoot (framePointer s)) u v ∧ CalleeSavedRegistersUnchanged u v ∧
      DirectionFlagClear v.RFLAGS ∧
      (∀ x : BitVec 64, (framePointer s).toNat ≤ x.toNat → (x.toNat < (rdi.read u).toNat ∨
        (rdi.read u).toNat + (MemoryRoutines.rdx.read u).toNat ≤ x.toNat) →
        v.external[x]? = u.external[x]?) ∧
      ∀ i < (MemoryRoutines.rdx.read u).toNat, v.external[rdi.read u + BitVec.ofNat 64 i]? =
        u.external[rsi.read u + BitVec.ofNat 64 i]? := by
  have hP := frame_toNat s G.low
  have hlow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hP
  obtain ⟨u1, a1, r1, c1, hrip1, hrsp1, hret1, hpush⟩ := ptr_call_push (entry := 0x102dc0)
    G hOut hA hr hc hrsp hrip hbytes (offset := 0x13a8) (by decide +kernel) hslot
    (MemoryContracts.memcpy_slot u hc) (by decide) (by omega)
  obtain ⟨hpre, hdi, hdx, hsi⟩ := routine_pre (len := 47) G hA hpush hrsp1 hret1 hp hdf hrip1
    (by decide) hdst
  have hsrc1 : ∀ i < (MemoryRoutines.rdx.read u).toNat,
      u1.external[rsi.read u + BitVec.ofNat 64 i]? = u.external[rsi.read u + BitVec.ofNat 64 i]? := by
    intro i hi
    apply hpush.byte
    intro c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · obtain ⟨j, hj, hje⟩ := hcov
      apply hsrcApart i hi (88 + j) (by omega)
      rw [hje]
      apply BitVec.eq_of_toNat_eq
      rw [add_toNat _ _ (by rw [sub_toNat _ _ (by omega)]; omega), sub_toNat _ _ (by omega),
        add_toNat _ _ (by rw [sub_toNat _ _ (by omega)]; omega), sub_toNat _ _ (by omega)]
      omega
    · exact hcov
  have hcpre : MemoryRoutines.MemcpyPre u1 := by
    refine ⟨hpre, ?_, ?_⟩
    · rw [hsi, hdx]
      exact ⟨hsrc, fun i hi => by rw [hsrc1 i hi]; exact hsrcMem i hi⟩
    · rw [hsi, hdx, hdi]
      refine Classical.byContradiction fun hov => ?_
      rcases Nat.le_total (rsi.read u).toNat (rdi.read u).toNat with hle | hle
      · apply hsrcApart ((rdi.read u).toNat - (rsi.read u).toNat) (by omega)
          ((rdi.read u).toNat - (framePointer s).toNat + 96) (by omega)
        apply BitVec.eq_of_toNat_eq
        rw [add_toNat _ _ (by omega), add_toNat _ _ (by rw [sub_toNat _ _ (by omega)]; omega),
          sub_toNat _ _ (by omega)]
        omega
      · apply hsrcApart 0 (by omega)
          ((rsi.read u).toNat - (framePointer s).toNat + 96) (by omega)
        apply BitVec.eq_of_toNat_eq
        rw [add_toNat _ _ (by omega), add_toNat _ _ (by rw [sub_toNat _ _ (by omega)]; omega),
          sub_toNat _ _ (by omega)]
        omega
  obtain ⟨fuel, v, a2, hres⟩ := MemoryRoutines.memcpy_advances hstride boundary
    (outside_routine hOut (by decide) (by decide)) u1 r1 c1 hcpre
    (by rw [hret1]; exact ne_boundary hOut (by dsimp only; rw [add_toNat _ _ (by omega)]; omega))
  obtain ⟨hrspv, hagr, hcs, hkeep⟩ := routine_post G hrsp hpush hres.toCallResult hrsp1
    (by rw [hdi, hdx]; exact hdst)
  refine ⟨1 + fuel, v, a1.trans a2, hres.ready, hres.codeIn hpre.dst c1, ?_, hrspv, hagr, hcs,
    hres.toCallResult.directionFlagClear hpre.df, by rw [hdi, hdx] at hkeep; exact hkeep, ?_⟩
  · rw [hres.rip, hret1]
  · intro i hi
    have := hres.copy i (by rw [hdx]; exact hi)
    rw [hdi, hsi, hsrc1 i hi] at this
    exact this

theorem Track.regStep [Bindings] {P : BitVec 64} {cs : List Component} {base u : RamState}
    {pre : RamState → Prop} {e : RamState → Effect} {p : BitVec 64} {bytes : List UInt8}
    {boundary : ReturnBoundary}
    (hStep : StepEffect pre (codeRange p bytes) e) (T : Track P cs base u)
    (hbytes : CodeIn (codeRange p bytes) u) (hpre : pre u) (hne : (e u).rip ≠ boundary.rip)
    (hcomp : ∀ c ∈ (e u).components, c.isMem = false ∧ c ∈ cs ∧ c ≠ .reg 4) :
    ∃ v, Advances boundary 1 u v ∧ Track P cs base v ∧ (e u).Holds u v ∧
      ∀ x : BitVec 64, v.external[x]? = u.external[x]? := by
  obtain ⟨v, a, T', he⟩ := T.step hStep hbytes hpre hne (fun c hc _ => (hcomp c hc).2.1)
    (fun x c hc hcov => regOnly (fun c hc => (hcomp c hc).1) x c hc hcov _)
    (fun h => (hcomp _ h).2.2 rfl)
  exact ⟨v, a, T', he, regOnly_external he.agrees (fun c hc => (hcomp c hc).1)⟩

theorem word64At_of {m : Ram} {a v : BitVec 64} (hv : memLoad m a 64 = v)
    (hs : ∀ i < 8, (m[a + BitVec.ofNat 64 i]?).isSome) :
    (⟨a.toNat, 8⟩ : MemoryRegion).Word64At m v := by
  refine ⟨rfl, ?_⟩
  rw [show BitVec.ofNat 64 a.toNat = a by simp]
  apply Bytes.loadBytes64
  intro i hi
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hs i hi)
  rw [hb, ← hv, storedByte_memLoad m a i (by omega)]
  simp [memByte, PhysicalMemory.read, hb]

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

private theorem loadBytes_isSome {memory : Machine.Ram} {address : BitVec 64} {count : Nat}
    {value : BitVec 64} (h : Machine.loadBytes memory address count = .ok value) :
    ∀ i < count, (memory[address + BitVec.ofNat 64 i]?).isSome := by
  simpa only [Nat.zero_add] using loadBytes_loop_isSome h

private theorem word64At_memLoad {region : MemoryRegion} {memory : Machine.Ram} {value : BitVec 64}
    (h : region.Word64At memory value) :
    memLoad memory (BitVec.ofNat 64 region.start) 64 = value := by
  have hb : Bytes memory (BitVec.ofNat 64 region.start) 8
      (storedByte (memLoad memory (BitVec.ofNat 64 region.start) 64)) :=
    Bytes.of_memLoad (n := 64) (loadBytes_isSome h.2)
  exact Except.ok.inj (hb.loadBytes64.symm.trans h.2)

theorem word64At_keep {m m' : Ram} {r : MemoryRegion} {v : BitVec 64} (h : r.Word64At m v)
    (hk : ∀ i < 8, m'[BitVec.ofNat 64 r.start + BitVec.ofNat 64 i]? =
      m[BitVec.ofNat 64 r.start + BitVec.ofNat 64 i]?) : r.Word64At m' v := by
  have hv := word64At_memLoad h
  have hs := loadBytes_isSome h.2
  refine ⟨h.1, ?_⟩
  apply Bytes.loadBytes64
  intro i hi
  rw [hk i hi]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hs i hi)
  rw [hb, ← hv, storedByte_memLoad _ _ i (by omega)]
  simp [memByte, PhysicalMemory.read, hb]

theorem sib_addr {u : RamState} (d : Disp) (next : BitVec 64) :
    (AddrMode.sib 4 none 0 d).addr u next = stackPtr u + d.value := by
  simp only [AddrMode.addr, AddrMode.reg64]
  rw [show ((4 : BitVec 4).setWidth 5) = (4 : BitVec 5) from rfl, ← stackPtr_eq_read]

set_option maxHeartbeats 1000000 in
theorem Track.slotStore [Bindings] {s t0 u : RamState} (G : Geometry s t0) {cs : List Component}
    (T : Track (framePointer s) cs t0 u) {boundary : ReturnBoundary}
    (hOut : ¬ InProgram boundary.rip)
    {p : BitVec 64} {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) {reg : BitVec 3} {d : Disp}
    (hx : rexX rex.toBitVec = (AddrMode.sib 4 none 0 d).rexX)
    (hb : rexB rex.toBitVec = (AddrMode.sib 4 none 0 d).rexB)
    (hbytes : CodeIn (codeRange p
      (rex :: 0x89 :: (AddrMode.sib 4 none 0 d).modrm reg :: (AddrMode.sib 4 none 0 d).tail)) u)
    (hrip : u.RIP = p) {k : Nat} (hd : d.value = BitVec.ofNat 64 k) (hk : k + 8 ≤ 0x1b8)
    (hp : 0x100000 ≤ p.toNat ∧
      p.toNat + (3 + (AddrMode.sib 4 none 0 d).tail.length) < 0x100000 + 11759)
    {a n : Nat} (hc : Component.mem (framePointer s + BitVec.ofNat 64 a) n ∈ cs)
    (ha : a ≤ k ∧ k + 8 ≤ a + n) (hn : a + n ≤ 0x1b8) (hripc : Component.rip ∈ cs) :
    ∃ v, Advances boundary 1 u v ∧ Track (framePointer s) cs t0 v ∧
      (Operand.mem (framePointer s + BitVec.ofNat 64 k) : Operand 64).read v =
        (Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read u ∧
      v.RIP = p + BitVec.ofNat 64 (3 + (AddrMode.sib 4 none 0 d).tail.length) ∧
      AgreesExcept [.mem (framePointer s + BitVec.ofNat 64 k) 8, .rip] u v := by
  have hP := frame_toNat s G.low
  have hlow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hP
  have haddr : storeAddrAt p (.sib 4 none 0 d) (3 + (AddrMode.sib 4 none 0 d).tail.length) u =
      framePointer s + BitVec.ofNat 64 k := by
    unfold storeAddrAt
    rw [sib_addr, T.rsp, hd]
  have hkN : (framePointer s + BitVec.ofNat 64 k).toNat = (framePointer s).toNat + k :=
    add_toNat _ _ (by omega)
  have hpre : StorePre p (3 + (AddrMode.sib 4 none 0 d).tail.length)
      (storeAddrAt p (.sib 4 none 0 d) (3 + (AddrMode.sib 4 none 0 d).tail.length)) 8 u := by
    refine ⟨hrip, ?_, ?_⟩
    · rw [haddr]; exact G.memWritable T.agrees (by omega) (by omega)
    · rw [haddr]; exact G.ne_code (by omega) (by omega) (inProg_range p _ (by omega))
  have hne : p + BitVec.ofNat 64 (3 + (AddrMode.sib 4 none 0 d).tail.length) ≠ boundary.rip :=
    ne_boundary hOut (by rw [add_toNat _ _ (by omega)]; omega)
  obtain ⟨v, av, T', he⟩ := T.step
    (mov_m64_r64_effect_step p rex hrex reg (.sib 4 none 0 d) ⟨by decide, fun _ => by decide⟩ hx hb)
    hbytes hpre
    hne
    (by
      intro c hc hm
      rw [movM64R64Effect_components] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · simp [Component.isMem] at hm
      · exact hripc)
    (by
      intro x c hc hcov
      rw [movM64R64Effect_components, haddr] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · refine ⟨⟨_, hc, covers_widen hcov (by omega) (by rw [add_toNat _ _ (by omega)]; omega)
          (by rw [add_toNat _ _ (by omega)]; omega)⟩, ?_⟩
        obtain ⟨i, hi, hxi⟩ := covers_toNat hcov (by omega)
        apply G.code
        unfold InStack
        omega
      · exact absurd hcov id)
    (by rw [movM64R64Effect_components]; simp)
  refine ⟨v, av, T', ?_, he.rip, ?_⟩
  · have h := he.writes
    simp only [movM64R64Effect, storeEffect, Write.AllHold] at h
    rw [← haddr]; exact h
  · have h := he.agrees
    rwa [movM64R64Effect_components, haddr] at h

theorem stack_mem_written {s : RamState} {outPtr : BitVec 64} {length : Nat} :
    Stack.region s coreStackBytes ∈ coreWritten s outPtr length := by
  simp [coreWritten]

theorem geometry_of [bindings : Bindings] {s t0 : RamState} {key : Vector UInt8 32}
    {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hInv : Inv s t0 outPtr plaintext.size) : Geometry s t0 := by
  obtain ⟨hb, -, hn, -⟩ := hPre.stack
  have ha := hInv.allocated _ stack_mem_written
  have hav := hPre.separation.2.2 _ stack_mem_written
  simp only [Stack.region, MemoryRegion.Bounded, userAddressLimit, MemoryRegion.Allocated,
    MemoryRegion.Contains, Stack.NoUnderflow, Stack.returnAddressBytes, coreStackBytes] at hb ha hn
  simp only [MemoryRegion.Avoids, Stack.region, MemoryRegion.Contains, pageTables,
    Stack.returnAddressBytes, coreStackBytes] at hav
  have hsp : s.regValue .rsp = stackPtr s := rfl
  rw [hsp] at hb ha hn hav
  refine ⟨hn, by omega, ?_, ?_, ?_⟩
  · intro a ⟨h1, h2⟩
    obtain ⟨b, hb⟩ := ha a ⟨h1, by omega⟩
    simp [hb]
  · intro a ⟨h1, h2⟩ hp
    exact hav a ⟨h1, by omega⟩ (.inl hp)
  · refine Classical.byContradiction fun hc => ?_
    let x : Nat := max ((stackPtr s).toNat - 992) 0x1000
    have hx : x < 2 ^ 64 := by omega
    apply hav (BitVec.ofNat 64 x)
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
      constructor <;> omega
    · right
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
      constructor <;> omega

theorem ready_of [bindings : Bindings] {s t : RamState} {outPtr : BitVec 64} {length : Nat}
    (hInv : Inv s t outPtr length) : ReadyToStep t :=
  ReadyToStep.of_supported hInv.machine hInv.environment.smrr hInv.environment.memoryType
    (DecoderFeatures.of_supported hInv.machine hInv.environment.leadingZeroCount)

def Scratch (s : RamState) (x : BitVec 64) : Prop :=
  ((framePointer s).toNat - 96 ≤ x.toNat ∧ x.toNat < (framePointer s).toNat + 0x30) ∨
  ((framePointer s).toNat + 0x98 ≤ x.toNat ∧ x.toNat < (framePointer s).toNat + 0xb0) ∨
  ((framePointer s).toNat + 0x174 ≤ x.toNat ∧ x.toNat < (framePointer s).toNat + 0x188)

theorem Scratch.inStack {s t0 : RamState} (G : Geometry s t0) {x : BitVec 64} (h : Scratch s x) :
    InStack s x := by
  have hP := frame_toNat s G.low
  have hlow := G.low
  simp only [frameBytes] at hP
  unfold Scratch at h
  unfold InStack
  omega

theorem Track.keep [Bindings] {s t0 t : RamState} {cs : List Component}
    (T : Track (framePointer s) cs t0 t)
    (hscr : ∀ c ∈ cs, ∀ x, c.Covers x → Scratch s x) {x : BitVec 64} (hx : ¬ Scratch s x) :
    t.external[x]? = t0.external[x]? :=
  T.agrees.byte fun c hc hcov => hx (hscr c hc x hcov)

theorem inv_of_track [bindings : Bindings] {s t0 t : RamState} {key : Vector UInt8 32}
    {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}
    (_hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hInv : Inv s t0 outPtr plaintext.size) (G : Geometry s t0) {cs : List Component}
    (T : Track (framePointer s) cs t0 t)
    (hscr : ∀ c ∈ cs, ∀ x, c.Covers x → Scratch s x) (hdf : Component.df ∉ cs) :
    Inv s t outPtr plaintext.size := by
  have hP := frame_toNat s G.low
  have hlow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hP
  have hfb : frameBase s = (framePointer s).toNat := by
    unfold frameBase; rw [hP]; rfl
  have hkeepOff : ∀ off, 0x188 ≤ off → off + 8 ≤ 0x1c0 → ∀ i < 8,
      t.external[BitVec.ofNat 64 (frameBase s + off) + BitVec.ofNat 64 i]? =
        t0.external[BitVec.ofNat 64 (frameBase s + off) + BitVec.ofNat 64 i]? := by
    intro off h1 h2 i hi
    apply T.keep hscr
    unfold Scratch
    rw [← BitVec.ofNat_add,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨⟨T.ready.smrr, T.ready.memoryType, hInv.environment.stringStride,
    T.ready.features.lzcnt⟩, T.ready.supported (SupportedSSE.of_agreesExcept T.agrees
      hInv.machine.sse), T.code, T.agrees.directionFlagClear hdf hInv.directionFlagUnset,
    T.rsp, ?_, ?_, ?_, ?_⟩
  · apply memoryWriteFrame_trans hInv.frame
    apply T.agrees.memoryWriteFrame
    intro c hc x hx
    have := (hscr c hc x hx).inStack G
    refine ⟨Stack.region s coreStackBytes, by simp, ?_⟩
    unfold InStack at this
    simp only [Stack.region, MemoryRegion.Contains, Stack.returnAddressBytes, coreStackBytes]
    have hsp : s.regValue .rsp = stackPtr s := rfl
    rw [hsp]
    omega
  · intro r hr
    apply T.agrees.allocated (hInv.allocated r hr)
    rintro a ⟨c, hc, hcov⟩
    exact T.agrees.grow _ (G.allocated a ((hscr c hc a hcov).inStack G))
  · intro entry he
    refine word64At_keep (hInv.saved entry he) ?_
    simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
    unfold slot
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hkeepOff _ (by omega) (by omega)
  · refine word64At_keep hInv.returnAddress ?_
    have : (Stack.returnSlot s).start = frameBase s + 0x1b8 := by
      simp only [Stack.returnSlot, frameBase, frameBytes]
      have hsp : s.regValue .rsp = stackPtr s := rfl
      rw [hsp]; omega
    rw [this]
    exact hkeepOff _ (by omega) (by omega)

def adChanges (P : BitVec 64) : List Component :=
  loopFoot P 13 ++ [.reg 5, .reg 12, .mem (P + BitVec.ofNat 64 8) 0x10,
    .mem (P + BitVec.ofNat 64 0x98) 0x18]

theorem callFoot_scratch {s t0 : RamState} (G : Geometry s t0) :
    ∀ c ∈ callFoot (framePointer s), ∀ x, c.Covers x → Scratch s x := by
  have hP := frame_toNat s G.low
  have hlow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hP
  intro c hc x hx
  simp only [callFoot, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> try exact absurd hx id
  · obtain ⟨i, hi, he⟩ := covers_toNat hx (by rw [sub_toNat _ _ (by omega)]; omega)
    rw [sub_toNat _ _ (by omega)] at he
    unfold Scratch; omega
  · obtain ⟨i, hi, he⟩ := covers_toNat hx (by rw [add_toNat _ _ (by omega)]; omega)
    rw [add_toNat _ _ (by omega)] at he
    unfold Scratch; omega
  · obtain ⟨i, hi, he⟩ := covers_toNat hx (by rw [add_toNat _ _ (by omega)]; omega)
    rw [add_toNat _ _ (by omega)] at he
    unfold Scratch; omega

theorem loopFoot_scratch {s t0 : RamState} (G : Geometry s t0) (r : BitVec 5) :
    ∀ c ∈ loopFoot (framePointer s) r, ∀ x, c.Covers x → Scratch s x := by
  intro c hc x hx
  simp only [loopFoot, List.mem_cons] at hc
  rcases hc with rfl | rfl | hc
  · exact absurd hx id
  · exact absurd hx id
  · exact callFoot_scratch G c hc x hx

theorem adChanges_scratch {s t0 : RamState} (G : Geometry s t0) :
    ∀ c ∈ adChanges (framePointer s), ∀ x, c.Covers x → Scratch s x := by
  have hP := frame_toNat s G.low
  have hlow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hP
  intro c hc x hx
  simp only [adChanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hc | rfl | rfl | rfl | rfl
  · exact loopFoot_scratch G 13 c hc x hx
  · exact absurd hx id
  · exact absurd hx id
  · obtain ⟨i, hi, he⟩ := covers_toNat hx (by rw [add_toNat _ _ (by omega)]; omega)
    rw [add_toNat _ _ (by omega)] at he
    unfold Scratch; omega
  · obtain ⟨i, hi, he⟩ := covers_toNat hx (by rw [add_toNat _ _ (by omega)]; omega)
    rw [add_toNat _ _ (by omega)] at he
    unfold Scratch; omega

theorem code_at' {t : RamState} (hc : CodeIn Extracted.programImage t) (a : BitVec 64)
    (off : Nat) (ha : a = BitVec.ofNat 64 (0x100000 + off)) (bytes : List UInt8)
    (hle : off + bytes.length ≤ Extracted.textBytes.size)
    (h : Extracted.textBytes.toListFrom off bytes.length = bytes) :
    CodeIn (codeRange a bytes) t := by
  subst ha; exact code_at hc off bytes hle h

theorem land_mask (x : Nat) (hx : x < 2 ^ 63) : x &&& 0x7ffffffffffffff0 = x / 16 * 16 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 : x / 16 * 16 = (x >>> 4) <<< 4 := by
    simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have h2 : (0x7ffffffffffffff0 : Nat) = (2 ^ 59 - 1) <<< 4 := by decide
  rw [Nat.testBit_and, h1, h2, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : 4 ≤ i
  · by_cases hi' : i < 63
    · simp [hi, show i - 4 < 59 by omega, show 4 + (i - 4) = i by omega]
    · have : x.testBit i = false := Nat.testBit_lt_two_pow (by
        calc x < 2 ^ 63 := hx
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [hi, show ¬ (i - 4 < 59) by omega, show 4 + (i - 4) = i by omega, this]
  · simp [hi]

theorem land_15 (x : Nat) : x &&& 15 = x % 16 := Nat.and_two_pow_sub_one_eq_mod x 4

theorem slot_keep {u v : RamState} {P : BitVec 64} {k j : Nat}
    (ag : AgreesExcept [.mem (P + BitVec.ofNat 64 k) 8, .rip] u v)
    (hP : P.toNat + 0x200 < 2 ^ 64) (hk : k ≤ 0x1b8) (hj : j ≤ 0x1b8) (hkj : k + 8 ≤ j ∨ j + 8 ≤ k) :
    (Operand.mem (P + BitVec.ofNat 64 j) : Operand 64).read v =
      (Operand.mem (P + BitVec.ofNat 64 j) : Operand 64).read u := by
  apply read_mem_eq
  intro i hi
  apply ag.byte
  intro c hc hcov
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨l, hl, he⟩ := covers_toNat hcov (by rw [add_toNat _ _ (by omega)]; omega)
    rw [add_ofNat_add_ofNat, add_toNat _ _ (by omega), add_toNat _ _ (by omega)] at he
    change i < 8 at hi
    omega
  · exact hcov

theorem slot_regs {u v : RamState} {P : BitVec 64} {k : Nat}
    (ag : AgreesExcept [.mem (P + BitVec.ofNat 64 k) 8, .rip] u v) (r : BitVec 5) :
    (Operand.reg r : Operand 64).read v = (Operand.reg r : Operand 64).read u :=
  ag.read (by simp)

theorem store_keep_above {u v : RamState} {P x : BitVec 64} {k : Nat}
    (ag : AgreesExcept [.mem (P + BitVec.ofNat 64 k) 8, .rip] u v)
    (hP : P.toNat + 0x200 < 2 ^ 64) (hk : k + 8 ≤ 0xb0) (hx : P.toNat + 0xb0 ≤ x.toNat) :
    v.external[x]? = u.external[x]? := by
  apply ag.byte
  intro c hc hcov
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨l, hl, he⟩ := covers_toNat hcov (by rw [add_toNat _ _ (by omega)]; omega)
    rw [add_toNat _ _ (by omega)] at he
    omega
  · exact hcov

set_option maxHeartbeats 4000000 in
theorem ad_prologue [Bindings] {s t0 : RamState} (G : Geometry s t0) {boundary : ReturnBoundary}
    (hOut : ¬ InProgram boundary.rip)
    (T0 : Track (framePointer s) (adChanges (framePointer s)) t0 t0)
    (hrip : t0.RIP = 0x10083c) (hlen : ((Operand.reg 13 : Operand 64).read t0).toNat < 2 ^ 32) :
    ∃ fuel e, Advances boundary fuel t0 e ∧
      Track (framePointer s) (adChanges (framePointer s)) t0 e ∧ e.RIP = 0x100875 ∧
      (Operand.reg 12 : Operand 64).read e =
        BitVec.ofNat 64 (((Operand.reg 13 : Operand 64).read t0).toNat / 16 * 16) ∧
      (Operand.reg 5 : Operand 64).read e =
        BitVec.ofNat 64 (((Operand.reg 13 : Operand 64).read t0).toNat % 16) ∧
      (Operand.reg 13 : Operand 64).read e = (Operand.reg 13 : Operand 64).read t0 ∧
      (Operand.reg 15 : Operand 64).read e = (Operand.reg 15 : Operand 64).read t0 ∧
      (Operand.reg 3 : Operand 64).read e = (Operand.reg 3 : Operand 64).read t0 ∧
      (StatusFlags.ofRFLAGS e.RFLAGS).CF =
        decide (((Operand.reg 13 : Operand 64).read t0).toNat < 16) ∧
      (Operand.mem (framePointer s + BitVec.ofNat 64 8) : Operand 64).read e =
        (Operand.reg 5 : Operand 64).read t0 ∧
      (Operand.mem (framePointer s + BitVec.ofNat 64 0x10) : Operand 64).read e =
        (Operand.reg 1 : Operand 64).read t0 ∧
      (Operand.mem (framePointer s + BitVec.ofNat 64 0x98) : Operand 64).read e =
        (Operand.reg 13 : Operand 64).read t0 ∧
      (Operand.mem (framePointer s + BitVec.ofNat 64 0xa0) : Operand 64).read e =
        (Operand.reg 14 : Operand 64).read t0 ∧
      (Operand.mem (framePointer s + BitVec.ofNat 64 0xa8) : Operand 64).read e =
        (Operand.reg 12 : Operand 64).read t0 ∧
      ∀ x : BitVec 64, (framePointer s).toNat + 0xb0 ≤ x.toNat →
        e.external[x]? = t0.external[x]? := by
  have hP := frame_toNat s G.low
  have hlow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hP
  have hPb : (framePointer s).toNat + 0x200 < 2 ^ 64 := by omega
  obtain ⟨t1, a1, T1, hv1, hrip1, ag1⟩ := T0.slotStore G hOut (p := 0x10083c) (rex := 0x48)
    (reg := 5) (d := .d8 8) (k := 8) (a := 8) (n := 0x10) (by unfold RexWPrefix; decide)
    (by decide) (by decide)
    (code_at' T0.code _ 0x83c (by decide) _ (by decide) (by decide +kernel)) hrip rfl
    (by omega) (by decide) (by simp [adChanges]) (by omega) (by omega)
    (by simp [adChanges, loopFoot, callFoot])
  obtain ⟨t2, a2, T2, hv2, hrip2, ag2⟩ := T1.slotStore G hOut (p := 0x100841) (rex := 0x48)
    (reg := 1) (d := .d8 0x10) (k := 0x10) (a := 8) (n := 0x10) (by unfold RexWPrefix; decide)
    (by decide) (by decide)
    (code_at' T1.code _ 0x841 (by decide) _ (by decide) (by decide +kernel)) hrip1 rfl
    (by omega) (by decide) (by simp [adChanges]) (by omega) (by omega)
    (by simp [adChanges, loopFoot, callFoot])
  obtain ⟨t3, a3, T3, hv3, hrip3, ag3⟩ := T2.slotStore G hOut (p := 0x100846) (rex := 0x4c)
    (reg := 4) (d := .d32 0xa8) (k := 0xa8) (a := 0x98) (n := 0x18)
    (by unfold RexWPrefix; decide) (by decide) (by decide)
    (code_at' T2.code _ 0x846 (by decide) _ (by decide) (by decide +kernel)) hrip2 rfl
    (by omega) (by decide) (by simp [adChanges]) (by omega) (by omega)
    (by simp [adChanges, loopFoot, callFoot])
  obtain ⟨t4, a4, T4, hv4, hrip4, ag4⟩ := T3.slotStore G hOut (p := 0x10084e) (rex := 0x4c)
    (reg := 6) (d := .d32 0xa0) (k := 0xa0) (a := 0x98) (n := 0x18)
    (by unfold RexWPrefix; decide) (by decide) (by decide)
    (code_at' T3.code _ 0x84e (by decide) _ (by decide) (by decide +kernel)) hrip3 rfl
    (by omega) (by decide) (by simp [adChanges]) (by omega) (by omega)
    (by simp [adChanges, loopFoot, callFoot])
  obtain ⟨t5, a5, T5, e5, m5⟩ := T4.regStep
    (mov_r64_imm64_effect_step 0x100856 0x49 0xbc (by unfold RexWPrefix; decide) (by decide)
      0x7ffffffffffffff0)
    (code_at' T4.code _ 0x856 (by decide) _ (by decide) (by decide +kernel))
    hrip4 (ne_boundary hOut (a := 0x100860) (by decide))
    (by simp [movR64Imm64Effect, Effect.components, adChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  obtain ⟨t6, a6, T6, e6, m6⟩ := T5.regStep
    (and_r64_r64_effect_step 0x100860 0x4d 0xec (by unfold RexWPrefix; decide) (by decide))
    (code_at' T5.code _ 0x860 (by decide) _ (by decide) (by decide +kernel))
    e5.rip (ne_boundary hOut (a := 0x100863) (by decide))
    (by simp [adChanges, loopFoot, callFoot, Component.isMem]; decide)
  obtain ⟨t7, a7, T7, e7, m7⟩ := T6.regStep
    (mov_r32_r32_rex_effect_step 0x100863 0x44 0xed (by unfold RexNoWPrefix; decide) (by decide))
    (code_at' T6.code _ 0x863 (by decide) _ (by decide) (by decide +kernel))
    e6.rip (ne_boundary hOut (a := 0x100866) (by decide))
    (by simp [movR32R32Effect, Effect.components, adChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  obtain ⟨t8, a8, T8, e8, m8⟩ := T7.regStep
    (and_r32_imm8_effect_step 0x100866 0xe5 0x0f (by decide) (by decide))
    (code_at' T7.code _ 0x866 (by decide) _ (by decide) (by decide +kernel))
    e7.rip (ne_boundary hOut (a := 0x100869) (by decide))
    (by simp [adChanges, loopFoot, callFoot, Component.isMem]; decide)
  obtain ⟨t9, a9, T9, hv9, hrip9, ag9⟩ := T8.slotStore G hOut (p := 0x100869) (rex := 0x4c)
    (reg := 5) (d := .d32 0x98) (k := 0x98) (a := 0x98) (n := 0x18)
    (by unfold RexWPrefix; decide) (by decide) (by decide)
    (code_at' T8.code _ 0x869 (by decide) _ (by decide) (by decide +kernel)) e8.rip rfl
    (by omega) (by decide) (by simp [adChanges]) (by omega) (by omega)
    (by simp [adChanges, loopFoot, callFoot])
  obtain ⟨t10, a10, T10, e10, m10⟩ := T9.regStep
    (cmp_r64_imm8_effect_step 0x100871 0x49 0xfd 0x10 (by unfold RexWPrefix; decide) (by decide)
      (by decide))
    (code_at' T9.code _ 0x871 (by decide) _ (by decide) (by decide +kernel))
    hrip9 (ne_boundary hOut (a := 0x100875) (by decide))
    (by simp [adChanges, loopFoot, callFoot, Component.isMem])
  have hP8 : (framePointer s).toNat + 0x200 < 2 ^ 64 := hPb
  have r13_5 : (Operand.reg 13 : Operand 64).read t5 = (Operand.reg 13 : Operand 64).read t0 := by
    rw [e5.agrees.read (by simp; decide), slot_regs ag4, slot_regs ag3, slot_regs ag2,
      slot_regs ag1]
  have r12_6 : (Operand.reg 12 : Operand 64).read t6 =
      0x7ffffffffffffff0 &&& (Operand.reg 13 : Operand 64).read t0 := by
    have h6 : (Operand.reg 12 : Operand 64).read t6 =
        (Operand.reg 12 : Operand 64).read t5 &&& (Operand.reg 13 : Operand 64).read t5 := e6.writes
    have h5 : (Operand.reg 12 : Operand 64).read t5 = 0x7ffffffffffffff0 := e5.writes
    rw [h6, h5, r13_5]
  have r13_6 : (Operand.reg 13 : Operand 64).read t6 = (Operand.reg 13 : Operand 64).read t0 := by
    rw [e6.agrees.read (by simp; decide), r13_5]
  have r5_8 : (Operand.reg 5 : Operand 64).read t8 =
      ((((Operand.reg 13 : Operand 64).read t0).setWidth 32) &&&
        (0x0f : BitVec 8).signExtend 32).setWidth 64 := by
    have h8 : (Operand.reg 5 : Operand 64).read t8 =
        ((Operand.reg 5 : Operand 32).read t7 &&& (0x0f : BitVec 8).signExtend 32).setWidth 64 :=
      e8.writes
    have h7 : (Operand.reg 5 : Operand 64).read t7 =
        ((Operand.reg 13 : Operand 32).read t6).setWidth 64 := e7.writes
    have h7' : (Operand.reg 5 : Operand 32).read t7 =
        ((Operand.reg 13 : Operand 64).read t6).setWidth 32 := by
      change ((Operand.reg 5 : Operand 64).read t7).setWidth 32 = _
      rw [h7]
      simp
    rw [h8, h7', r13_6]
  have r13_9 : (Operand.reg 13 : Operand 64).read t9 = (Operand.reg 13 : Operand 64).read t0 := by
    rw [slot_regs ag9, e8.agrees.read (by simp; decide), e7.agrees.read (by simp; decide), r13_6]
  have hreg10 : ∀ r : BitVec 5, (Operand.reg r : Operand 64).read t10 =
      (Operand.reg r : Operand 64).read t9 := fun r => e10.agrees.read (by simp)
  have keep89 : ∀ r : BitVec 5, r ≠ 5 → r ≠ 12 →
      (Operand.reg r : Operand 64).read t9 = (Operand.reg r : Operand 64).read t0 := by
    intro r h5 h12
    rw [slot_regs ag9, e8.agrees.read (by simp; exact h5), e7.agrees.read (by simp; exact h5),
      e6.agrees.read (by simp; exact h12), e5.agrees.read (by simp; exact h12), slot_regs ag4,
      slot_regs ag3, slot_regs ag2, slot_regs ag1]
  have mem10 : ∀ x : BitVec 64, t10.external[x]? = t9.external[x]? := m10
  have hm : ∀ j, (Operand.mem (framePointer s + BitVec.ofNat 64 j) : Operand 64).read t10 =
      (Operand.mem (framePointer s + BitVec.ofNat 64 j) : Operand 64).read t9 :=
    fun j => read_mem_eq fun i _ => mem10 _
  have hm58 : ∀ j, (Operand.mem (framePointer s + BitVec.ofNat 64 j) : Operand 64).read t8 =
      (Operand.mem (framePointer s + BitVec.ofNat 64 j) : Operand 64).read t4 := by
    intro j
    apply read_mem_eq
    intro i _
    rw [m8, m7, m6, m5]
  refine ⟨1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1, t10,
    (((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans
      a9).trans a10), T10, e10.rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hreg10, slot_regs ag9, e8.agrees.read (by simp; decide), e7.agrees.read (by simp; decide),
      r12_6]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_comm,
      show (0x7ffffffffffffff0 : BitVec 64).toNat = 0x7ffffffffffffff0 from rfl,
      land_mask _ (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [hreg10, slot_regs ag9, r5_8]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth,
      show ((0x0f : BitVec 8).signExtend 32).toNat = 15 from rfl, land_15, BitVec.toNat_ofNat]
    omega
  · rw [hreg10, r13_9]
  · rw [hreg10, keep89 15 (by decide) (by decide)]
  · rw [hreg10, keep89 3 (by decide) (by decide)]
  · have h := e10.flags
    simp only [cmpR64Imm8Effect, Effect.FlagsHold, StatusFlagsOutcome.ofStatusFlags,
      StatusFlagsOutcome.Allows, FlagAllows] at h
    rw [h.1, show ∀ x y : BitVec 64, (cmpSpec x y).CF = decide (x.toNat < y.toNat) from fun _ _ => rfl]
    show decide (((Operand.reg 13 : Operand 64).read t9).toNat <
      ((0x10 : BitVec 8).signExtend 64).toNat) = _
    rw [r13_9]; rfl
  · rw [hm, slot_keep ag9 hP8 (by omega) (by omega) (by omega), hm58,
      slot_keep ag4 hP8 (by omega) (by omega) (by omega),
      slot_keep ag3 hP8 (by omega) (by omega) (by omega),
      slot_keep ag2 hP8 (by omega) (by omega) (by omega), hv1]
    rfl
  · rw [hm, slot_keep ag9 hP8 (by omega) (by omega) (by omega), hm58,
      slot_keep ag4 hP8 (by omega) (by omega) (by omega),
      slot_keep ag3 hP8 (by omega) (by omega) (by omega), hv2, slot_regs ag1]
    rfl
  · rw [hm, hv9, e8.agrees.read (by simp; decide), e7.agrees.read (by simp; decide)]
    exact r13_6
  · rw [hm, slot_keep ag9 hP8 (by omega) (by omega) (by omega), hm58, hv4, slot_regs ag3,
      slot_regs ag2, slot_regs ag1]
    rfl
  · rw [hm, slot_keep ag9 hP8 (by omega) (by omega) (by omega), hm58,
      slot_keep ag4 hP8 (by omega) (by omega) (by omega), hv3, slot_regs ag2, slot_regs ag1]
    rfl
  · intro x hx
    rw [mem10, store_keep_above ag9 hP8 (by omega) hx, m8, m7, m6, m5,
      store_keep_above ag4 hP8 (by omega) hx, store_keep_above ag3 hP8 (by omega) hx,
      store_keep_above ag2 hP8 (by omega) hx, store_keep_above ag1 hP8 (by omega) hx]

theorem ofNat_toNat_add (ptr : BitVec 64) (i : Nat) :
    BitVec.ofNat 64 (ptr.toNat + i) = ptr + BitVec.ofNat 64 i := by
  rw [BitVec.ofNat_add]; simp

theorem read_region [bindings : Bindings] {s t0 : RamState} {key : Vector UInt8 32}
    {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hInv : Inv s t0 outPtr plaintext.size) {region : MemoryRegion}
    (hr : region ∈ coreRead s inPtr outPtr plaintext.size) {bytes : ByteArray}
    (hv : ValidInput s region bytes) :
    region.start + bytes.size < 2 ^ 32 ∧
    (∀ i < bytes.size, t0.external[BitVec.ofNat 64 (region.start + i)]? = some bytes[i]!) ∧
    ∀ i < bytes.size, ¬ InStack s (BitVec.ofNat 64 (region.start + i)) := by
  obtain ⟨hb, hlen, hbytes⟩ := hv
  simp only [MemoryRegion.Bounded, userAddressLimit, MemoryRegion.HasLength] at hb hlen
  have hsep := hPre.separation.2.1 _ stack_mem_written region hr
  refine ⟨by omega, ?_, ?_⟩
  · intro i hi
    have hn : (BitVec.ofNat 64 (region.start + i)).toNat = region.start + i := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [read_unchanged hPre hInv.frame hr _ (by rw [hn]; constructor <;> omega),
      hbytes ⟨i, hi⟩, getElem!_pos bytes i hi]
  · intro i hi hin
    have hn : (BitVec.ofNat 64 (region.start + i)).toNat = region.start + i := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    apply hsep (region.start + i)
    · unfold InStack at hin
      rw [hn] at hin
      simp only [Stack.region, MemoryRegion.Contains, Stack.returnAddressBytes, coreStackBytes]
      have hsp : s.regValue .rsp = stackPtr s := rfl
      rw [hsp]
      omega
    · constructor <;> omega

theorem absorbBlocks_extract_zero (r a : Nat) (bytes : ByteArray) :
    absorbBlocks r a (bytes.extract 0 0) = a := by
  simp [absorbBlocks]

set_option maxHeartbeats 4000000 in
theorem ad_head [Bindings] {s t0 e : RamState} (G : Geometry s t0) {boundary : ReturnBoundary}
    (hOut : ¬ InProgram boundary.rip)
    (T : Track (framePointer s) (adChanges (framePointer s)) t0 e)
    (hrip : e.RIP = 0x100875) {ptr : BitVec 64} {ad : ByteArray} {otk : Vector UInt8 32}
    (hlow : ptr.toNat + ad.size ≤ 2 ^ 32)
    (hmem : ∀ i < ad.size, t0.external[ptr + BitVec.ofNat 64 i]? = some ad[i]!)
    (hfar : ∀ c ∈ adChanges (framePointer s), ∀ i < ad.size, ¬ c.Covers (ptr + BitVec.ofNat 64 i))
    (hcf : (StatusFlags.ofRFLAGS e.RFLAGS).CF = decide (ad.size < 16))
    (hr12 : (Operand.reg 12 : Operand 64).read e = BitVec.ofNat 64 (ad.size / 16 * 16))
    (hslot : (Operand.mem (framePointer s + BitVec.ofNat 64 8) : Operand 64).read e = ptr)
    (hr15 : (Operand.reg 15 : Operand 64).read e = polyBase s)
    (hpoly : PolyState e (polyBase s) otk 0) :
    ∃ fuel t, Advances boundary fuel e t ∧
      Track (framePointer s) (adChanges (framePointer s)) t0 t ∧
      AgreesExcept (loopFoot (framePointer s) 13) e t ∧ t.RIP = 0x100895 ∧
      (Operand.reg 15 : Operand 64).read t = polyBase s ∧
      PolyState t (polyBase s) otk
        (absorbBlocks (clampedR otk) 0 (ad.extract 0 (16 * (ad.size / 16)))) := by
  have hP := frame_toNat s G.low
  have hglow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hP
  have hlf : ∀ c ∈ loopFoot (framePointer s) 13, c ∈ adChanges (framePointer s) :=
    fun c hc => List.mem_append_left _ hc
  obtain ⟨t1, a1, T1, e1, m1⟩ := T.regStep (jcc_rel8_effect_step 0x100875 2 0x1e)
    (code_at' T.code _ 0x875 (by decide) _ (by decide) (by decide +kernel))
    ⟨hrip, fun _ => by decide⟩
    (by
      simp only [jccEffect, branchEffect]
      split
      · exact ne_boundary hOut (a := 0x100895) (by decide)
      · exact ne_boundary hOut (a := 0x100877) (by decide))
    (by simp [jccEffect, adChanges, loopFoot, callFoot, Component.isMem])
  have hrip1 : t1.RIP = if ad.size < 16 then 0x100895 else 0x100877 := by
    rw [e1.rip]
    simp only [jccEffect, branchEffect, condHolds_2, hcf]
    by_cases h : ad.size < 16 <;> simp [h] <;> rfl
  have hl1 : AgreesExcept (loopFoot (framePointer s) 13) e t1 :=
    e1.agrees.mono (by simp [jccEffect, loopFoot, callFoot])
  by_cases hs : ad.size < 16
  · have hn : ad.size / 16 = 0 := by omega
    refine ⟨1, t1, a1, T1, hl1, by rw [hrip1, ite_t hs], ?_, ?_⟩
    · rw [e1.agrees.read (by simp [jccEffect]), hr15]
    · rw [hn, Nat.mul_zero, absorbBlocks_extract_zero]
      exact PolyState.of_mem hpoly fun i _ => m1 _
  · have hrip1' : t1.RIP = 0x100877 := by rw [hrip1, ite_f hs]
    obtain ⟨t2, a2, T2, e2, m2⟩ := T1.regStep
      (mov_r64_r64_effect_step 0x100877 0x4d 0xe5 (by unfold RexWPrefix; decide) (by decide))
      (code_at' T1.code _ 0x877 (by decide) _ (by decide) (by decide +kernel))
      hrip1' (ne_boundary hOut (a := 0x10087a) (by decide))
      (by simp [movR64R64Effect, Effect.components, adChanges, loopFoot, callFoot,
        Component.isMem]; decide)
    have haddr : ∀ x, (AddrMode.sib 4 none 0 (.d8 8)).addr t2 x = framePointer s + BitVec.ofNat 64 8 := by
      intro x; rw [sib_addr, T2.rsp]; rfl
    obtain ⟨t3, a3, T3, e3, m3⟩ := T2.regStep
      (mov_r64_m64_effect_step 0x10087a 0x48 (by unfold RexWPrefix; decide) 6
        (.sib 4 none 0 (.d8 8)) ⟨by decide, fun _ => by decide⟩ (by decide) (by decide))
      (code_at' T2.code _ 0x87a (by decide) _ (by decide) (by decide +kernel))
      ⟨e2.rip, by
        rw [haddr]
        exact (G.writableRange T2.agrees (by rw [add_toNat _ _ (by omega)]; omega)
          (by rw [add_toNat _ _ (by omega)]; omega)).readable⟩
      (ne_boundary hOut (a := 0x10087f) (by decide))
      (by simp [movR64M64Effect, Effect.components, adChanges, loopFoot, callFoot,
        Component.isMem]; decide)
    obtain ⟨t4, a4, T4, e4, m4⟩ := T3.regStep (nop_effect_step 0x10087f)
      (code_at' T3.code _ 0x87f (by decide) _ (by decide) (by decide +kernel))
      e3.rip (ne_boundary hOut (a := 0x100880) (by decide))
      (by simp [nopEffect, Effect.components, adChanges, loopFoot, callFoot, Component.isMem])
    have hrsi3 : rsi.read t3 = ptr := by
      have h : rsi.read t3 = (Operand.mem ((AddrMode.sib 4 none 0 (.d8 8)).addr t2
          (0x10087a + BitVec.ofNat 64 (movLoadLen (.sib 4 none 0 (.d8 8))))) : Operand 64).read t2 :=
        e3.writes
      rw [h, haddr, read_mem_eq (fun i _ => (m2 _).trans (m1 _)), hslot]
    have hL : LoopAt adSite s t0 e t4 (adChanges (framePointer s)) ptr ad otk 0 0 := by
      refine ⟨T4, ?_, e4.rip, ?_, ?_, ?_, ?_⟩
      · refine loopExt (loopExt (loopExt hl1 e2.agrees ?_) e3.agrees ?_) e4.agrees ?_
        · simp [movR64R64Effect, Effect.components, loopFoot, callFoot]
          decide
        · simp [movR64M64Effect, Effect.components, loopFoot, callFoot]
          decide
        · simp [nopEffect, Effect.components, loopFoot, callFoot]
      · rw [show rsi = (Operand.reg 6 : Operand 64) from rfl, e4.agrees.read (by
          simp [nopEffect, Effect.components])]
        simpa using hrsi3
      · show (Operand.reg 13 : Operand 64).read t4 = _
        rw [e4.agrees.read (by simp [nopEffect, Effect.components]),
          e3.agrees.read (by simp [movR64M64Effect, Effect.components]; decide)]
        have h : (Operand.reg 13 : Operand 64).read t2 = (Operand.reg 12 : Operand 64).read t1 :=
          e2.writes
        rw [h, e1.agrees.read (by simp [jccEffect]), hr12]
        congr 1
        omega
      · rw [e4.agrees.read (by simp [nopEffect, Effect.components]),
          e3.agrees.read (by simp [movR64M64Effect, Effect.components]; decide),
          e2.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
          e1.agrees.read (by simp [jccEffect]), hr15]
      · rw [Nat.mul_zero, absorbBlocks_extract_zero]
        exact PolyState.of_mem hpoly fun i _ => by rw [m4, m3, m2, m1]
    obtain ⟨f, t5, a5, D⟩ := loop_run (Or.inl rfl) G hOut hlf hlow hmem hfar (ad.size / 16) 0 t4
      (by omega) (by omega) hL
    exact ⟨1 + 1 + 1 + 1 + f, t5, (((a1.trans a2).trans a3).trans a4).trans a5, D.track, D.loop,
      D.rip, D.r15, D.poly⟩

def tailBlock (bytes : ByteArray) : ByteArray :=
  bytes.extract (bytes.size / 16 * 16) bytes.size ++
    ⟨Array.replicate (16 - bytes.size % 16) 0⟩

theorem tailBlock_size (bytes : ByteArray) (_h : bytes.size % 16 ≠ 0) :
    (tailBlock bytes).size = 16 := by
  simp only [tailBlock, ByteArray.size_append, ByteArray.size_extract]
  change _ + (Array.replicate _ _).size = 16
  rw [Array.size_replicate]
  omega

theorem tailBlock_byte (bytes : ByteArray) (h : bytes.size % 16 ≠ 0) (i : Nat) (hi : i < 16) :
    (tailBlock bytes)[i]! =
      if i < bytes.size % 16 then bytes[bytes.size / 16 * 16 + i]! else 0 := by
  have hs := tailBlock_size bytes h
  rw [getElem!_pos _ i (by omega)]
  unfold tailBlock
  rw [ByteArray.getElem_eq_getElem_data]
  simp only [ByteArray.data_append, ByteArray.data_extract]
  rw [Array.getElem_append]
  have he : (bytes.data.extract (bytes.size / 16 * 16) bytes.size).size = bytes.size % 16 := by
    simp only [Array.size_extract, ByteArray.size_data]; omega
  split
  · rename_i h1
    rw [he] at h1
    rw [ite_t h1, Array.getElem_extract, getElem!_pos bytes _ (by omega),
      ByteArray.getElem_eq_getElem_data]
  · rename_i h1
    rw [he] at h1
    rw [ite_f h1]
    simp

theorem extract_all (bytes : ByteArray) : bytes.extract 0 bytes.size = bytes := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by simp)

theorem absorb_padded (r a : Nat) (bytes : ByteArray) :
    absorbBlocks r a (bytes ++ pad16 bytes) =
      if bytes.size % 16 = 0 then absorbBlocks r a (bytes.extract 0 (16 * (bytes.size / 16)))
      else absorbBlock r (absorbBlocks r a (bytes.extract 0 (16 * (bytes.size / 16))))
        (tailBlock bytes) := by
  rw [absorbBlocks_pad16, Nat.mul_comm 16]
  split
  · rename_i h
    rw [show bytes.size / 16 * 16 = bytes.size by omega, extract_all]
  · rfl

theorem ofNat_beq_zero (r : Nat) (h : r < 2 ^ 64) :
    (BitVec.ofNat 64 r == 0) = decide (r = 0) := by
  by_cases hr : r = 0
  · subst hr; rfl
  · have : BitVec.ofNat 64 r ≠ 0 := by
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
      exact hr this
    simp only [hr, decide_false, beq_eq_false_iff_ne, ne_eq]; exact this

theorem cs_read {u v : RamState} (h : CalleeSavedRegistersUnchanged u v) {r : BitVec 5}
    (hr : r = 3 ∨ r = 5 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15) :
    (Operand.reg r : Operand 64).read v = (Operand.reg r : Operand 64).read u := by
  have hu := regValue_read u
  have hv := regValue_read v
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← hu.2.2.2.2.2.2.1, ← hv.2.2.2.2.2.2.1]; exact h _ (by simp)
  · rw [← hu.2.2.2.2.2.2.2.1, ← hv.2.2.2.2.2.2.2.1]; exact h _ (by simp)
  · rw [← hu.2.2.2.2.2.2.2.2.1, ← hv.2.2.2.2.2.2.2.2.1]; exact h _ (by simp)
  · rw [← hu.2.2.2.2.2.2.2.2.2.1, ← hv.2.2.2.2.2.2.2.2.2.1]; exact h _ (by simp)
  · rw [← hu.2.2.2.2.2.2.2.2.2.2.1, ← hv.2.2.2.2.2.2.2.2.2.2.1]; exact h _ (by simp)
  · rw [← hu.2.2.2.2.2.2.2.2.2.2.2.1, ← hv.2.2.2.2.2.2.2.2.2.2.2.1]; exact h _ (by simp)

theorem callFoot_noCover {P x : BitVec 64}
    (hP : 96 ≤ P.toNat) (hP' : P.toNat + 0x200 < 2 ^ 64)
    (hx : P.toNat ≤ x.toNat ∧ (x.toNat < P.toNat + 0x18 ∨
      (P.toNat + 0x28 ≤ x.toNat ∧ x.toNat < P.toNat + 0x174) ∨ P.toNat + 0x188 ≤ x.toNat)) :
    ∀ c ∈ callFoot P, ¬ c.Covers x := by
  intro c hc hcov
  simp only [callFoot, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> try exact hcov
  · obtain ⟨i, hi, he⟩ := covers_toNat hcov (by rw [sub_toNat _ _ (by omega)]; omega)
    rw [sub_toNat _ _ (by omega)] at he
    omega
  · obtain ⟨i, hi, he⟩ := covers_toNat hcov (by rw [add_toNat _ _ (by omega)]; omega)
    rw [add_toNat _ _ (by omega)] at he
    omega
  · obtain ⟨i, hi, he⟩ := covers_toNat hcov (by rw [add_toNat _ _ (by omega)]; omega)
    rw [add_toNat _ _ (by omega)] at he
    omega

theorem callFoot_keep {u v : RamState} {P x : BitVec 64} (hag : AgreesExcept (callFoot P) u v)
    (hP : 96 ≤ P.toNat) (hP' : P.toNat + 0x200 < 2 ^ 64)
    (hx : P.toNat ≤ x.toNat ∧ (x.toNat < P.toNat + 0x18 ∨
      (P.toNat + 0x28 ≤ x.toNat ∧ x.toNat < P.toNat + 0x174) ∨ P.toNat + 0x188 ≤ x.toNat)) :
    v.external[x]? = u.external[x]? :=
  hag.byte (callFoot_noCover hP hP' hx)

theorem loopFoot_keep {u v : RamState} {P x : BitVec 64} {r : BitVec 5}
    (hag : AgreesExcept (loopFoot P r) u v)
    (hP : 96 ≤ P.toNat) (hP' : P.toNat + 0x200 < 2 ^ 64)
    (hx : P.toNat ≤ x.toNat ∧ (x.toNat < P.toNat + 0x18 ∨
      (P.toNat + 0x28 ≤ x.toNat ∧ x.toNat < P.toNat + 0x174) ∨ P.toNat + 0x188 ≤ x.toNat)) :
    v.external[x]? = u.external[x]? := by
  apply hag.byte
  intro c hc hcov
  simp only [loopFoot, List.mem_cons] at hc
  rcases hc with rfl | rfl | hc
  · exact hcov
  · exact hcov
  · exact callFoot_noCover hP hP' hx c hc hcov

set_option maxHeartbeats 8000000 in
theorem ad_tail [inst : Bindings] (hstride : UnitStringStride inst) {s t0 j : RamState}
    (G : Geometry s t0) {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip)
    (T : Track (framePointer s) (adChanges (framePointer s)) t0 j)
    (hdf : DirectionFlagClear j.RFLAGS) (hrip : j.RIP = 0x100895)
    {ptr : BitVec 64} {ad : ByteArray} {otk : Vector UInt8 32}
    (hlow : ptr.toNat + ad.size ≤ 2 ^ 32)
    (hmem : ∀ i < ad.size, t0.external[ptr + BitVec.ofNat 64 i]? = some ad[i]!)
    (hstk : ∀ i < ad.size, ¬ InStack s (ptr + BitVec.ofNat 64 i))
    (hrbp : (Operand.reg 5 : Operand 64).read j = BitVec.ofNat 64 (ad.size % 16))
    (hr12 : (Operand.reg 12 : Operand 64).read j = BitVec.ofNat 64 (ad.size / 16 * 16))
    (hslot : (Operand.mem (framePointer s + BitVec.ofNat 64 8) : Operand 64).read j = ptr)
    (hr15 : (Operand.reg 15 : Operand 64).read j = polyBase s)
    (hpoly : PolyState j (polyBase s) otk
      (absorbBlocks (clampedR otk) 0 (ad.extract 0 (16 * (ad.size / 16))))) :
    ∃ fuel t, Advances boundary fuel j t ∧
      Track (framePointer s) (adChanges (framePointer s)) t0 t ∧ t.RIP = 0x1008d9 ∧
      DirectionFlagClear t.RFLAGS ∧
      (Operand.reg 15 : Operand 64).read t = polyBase s ∧
      (Operand.reg 3 : Operand 64).read t = (Operand.reg 3 : Operand 64).read j ∧
      (∀ x : BitVec 64, ((framePointer s).toNat + 0x10 ≤ x.toNat ∧
          x.toNat < (framePointer s).toNat + 0x18) ∨
        ((framePointer s).toNat + 0x98 ≤ x.toNat ∧ x.toNat < (framePointer s).toNat + 0xb0) →
        t.external[x]? = j.external[x]?) ∧
      PolyState t (polyBase s) otk (absorbBlocks (clampedR otk) 0 (ad ++ pad16 ad)) := by
  have hP := frame_toNat s G.low
  have hglow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hP
  have hrem : ad.size % 16 < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨u1, a1, T1, e1, m1⟩ := T.regStep
    (test_r64_r64_effect_step 0x100895 0x48 0xed (by unfold RexWPrefix; decide) (by decide))
    (code_at' T.code _ 0x895 (by decide) _ (by decide) (by decide +kernel))
    hrip (ne_boundary hOut (a := 0x100898) (by decide))
    (by simp [adChanges, loopFoot, callFoot, Component.isMem])
  have hzf : (StatusFlags.ofRFLAGS u1.RFLAGS).ZF = decide (ad.size % 16 = 0) := by
    have h := e1.flags
    simp only [testR64R64Effect, testFlags, Effect.FlagsHold, StatusFlagsOutcome.Allows,
      FlagAllows] at h
    rw [h.2.2.2.1]
    show ((Operand.reg 5 : Operand 64).read j &&& (Operand.reg 5 : Operand 64).read j == 0) = _
    rw [hrbp, BitVec.and_self, ofNat_beq_zero _ (by omega)]
  obtain ⟨u2, a2, T2, e2, m2⟩ := T1.regStep (jcc_rel8_effect_step 0x100898 4 0x3f)
    (code_at' T1.code _ 0x898 (by decide) _ (by decide) (by decide +kernel))
    ⟨e1.rip, fun _ => by decide⟩
    (by
      simp only [jccEffect, branchEffect]
      split
      · exact ne_boundary hOut (a := 0x1008d9) (by decide)
      · exact ne_boundary hOut (a := 0x10089a) (by decide))
    (by simp [jccEffect, adChanges, loopFoot, callFoot, Component.isMem])
  have hrip2 : u2.RIP = if ad.size % 16 = 0 then 0x1008d9 else 0x10089a := by
    rw [e2.rip]
    simp only [jccEffect, branchEffect, condHolds_4, hzf]
    by_cases h : ad.size % 16 = 0 <;> simp [h] <;> rfl
  have hreg2 : ∀ r : BitVec 5, (Operand.reg r : Operand 64).read u2 =
      (Operand.reg r : Operand 64).read j := fun r => by
    rw [e2.agrees.read (by simp [jccEffect]), e1.agrees.read (by simp)]
  have hdf2 : DirectionFlagClear u2.RFLAGS :=
    ((e1.agrees.trans e2.agrees).directionFlagClear (by simp [jccEffect]) ⟨hdf⟩).df
  by_cases hz : ad.size % 16 = 0
  · refine ⟨1 + 1, u2, a1.trans a2, T2, by rw [hrip2, ite_t hz], hdf2, by rw [hreg2, hr15],
      hreg2 3, fun x _ => by rw [m2, m1], ?_⟩
    rw [absorb_padded, ite_t hz]
    exact PolyState.of_mem hpoly fun i _ => by rw [m2, m1]
  have hrip2' : u2.RIP = 0x10089a := by rw [hrip2, ite_f hz]
  have haddr2 : ∀ x, (AddrMode.sib 4 none 0 (.d8 8)).addr u2 x = framePointer s + BitVec.ofNat 64 8 := by
    intro x; rw [sib_addr, T2.rsp]; rfl
  obtain ⟨u3, a3, T3, e3, m3⟩ := T2.regStep
    (mov_r64_m64_effect_step 0x10089a 0x4c (by unfold RexWPrefix; decide) 6
      (.sib 4 none 0 (.d8 8)) ⟨by decide, fun _ => by decide⟩ (by decide) (by decide))
    (code_at' T2.code _ 0x89a (by decide) _ (by decide) (by decide +kernel))
    ⟨hrip2', by
      rw [haddr2]
      exact (G.writableRange T2.agrees (by rw [add_toNat _ _ (by omega)]; omega)
        (by rw [add_toNat _ _ (by omega)]; omega)).readable⟩
    (ne_boundary hOut (a := 0x10089f) (by decide))
    (by simp [movR64M64Effect, Effect.components, adChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  have hr14_3 : (Operand.reg 14 : Operand 64).read u3 = ptr := by
    have h : (Operand.reg 14 : Operand 64).read u3 = (Operand.mem ((AddrMode.sib 4 none 0 (.d8 8)).addr u2
        (0x10089a + BitVec.ofNat 64 (movLoadLen (.sib 4 none 0 (.d8 8))))) : Operand 64).read u2 :=
      e3.writes
    rw [h, haddr2, read_mem_eq (fun i _ => (m2 _).trans (m1 _)), hslot]
  obtain ⟨u4, a4, T4, e4, m4⟩ := T3.regStep
    (add_r64_r64_effect_step 0x10089f 0x4d 0xe6 (by unfold RexWPrefix; decide) (by decide))
    (code_at' T3.code _ 0x89f (by decide) _ (by decide) (by decide +kernel))
    e3.rip (ne_boundary hOut (a := 0x1008a2) (by decide))
    (by simp [adChanges, loopFoot, callFoot, Component.isMem]; decide)
  have hr14_4 : (Operand.reg 14 : Operand 64).read u4 =
      ptr + BitVec.ofNat 64 (ad.size / 16 * 16) := by
    have h : (Operand.reg 14 : Operand 64).read u4 =
        (Operand.reg 14 : Operand 64).read u3 + (Operand.reg 12 : Operand 64).read u3 := e4.writes
    rw [h, hr14_3, e3.agrees.read (by simp [movR64M64Effect, Effect.components]; decide), hreg2,
      hr12]
  obtain ⟨u5, a5, T5, e5, m5⟩ := T4.regStep
    (mov_r32_imm32_effect_step 0x1008a2 0xba (by decide) 0x10)
    (code_at' T4.code _ 0x8a2 (by decide) _ (by decide) (by decide +kernel))
    e4.rip (ne_boundary hOut (a := 0x1008a7) (by decide))
    (by simp [movR32Imm32Effect, Effect.components, adChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  obtain ⟨u6, a6, T6, e6, m6⟩ := T5.regStep
    (sub_r64_r64_effect_step 0x1008a7 0x48 0xea (by unfold RexWPrefix; decide) (by decide))
    (code_at' T5.code _ 0x8a7 (by decide) _ (by decide) (by decide +kernel))
    e5.rip (ne_boundary hOut (a := 0x1008aa) (by decide))
    (by simp [adChanges, loopFoot, callFoot, Component.isMem]; decide)
  have hrbp6 : (Operand.reg 5 : Operand 64).read u5 = BitVec.ofNat 64 (ad.size % 16) := by
    rw [e5.agrees.read (by simp [movR32Imm32Effect, Effect.components]; decide),
      e4.agrees.read (by simp; decide),
      e3.agrees.read (by simp [movR64M64Effect, Effect.components]; decide), hreg2, hrbp]
  have hrdx6 : (Operand.reg 2 : Operand 64).read u6 = BitVec.ofNat 64 (16 - ad.size % 16) := by
    have h : (Operand.reg 2 : Operand 64).read u6 =
        (Operand.reg 2 : Operand 64).read u5 - (Operand.reg 5 : Operand 64).read u5 := e6.writes
    have h5 : (Operand.reg 2 : Operand 64).read u5 = (0x10 : BitVec 32).setWidth 64 := e5.writes
    rw [h, h5, hrbp6]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show ((0x10 : BitVec 32).setWidth 64).toNat = 16 from rfl]
    omega
  obtain ⟨u7, a7, T7, e7, m7⟩ := T6.regStep
    (lea_r64_effect_step 0x1008aa 0x48 (by unfold RexWPrefix; decide) 7
      (.sib 4 (some 5) 0 .none) ⟨by decide, fun _ => by decide⟩ (by decide) (by decide))
    (code_at' T6.code _ 0x8aa (by decide) _ (by decide) (by decide +kernel))
    e6.rip (ne_boundary hOut (a := 0x1008ae) (by decide))
    (by simp [adChanges, loopFoot, callFoot, Component.isMem]; decide)
  have hrdi7 : (Operand.reg 7 : Operand 64).read u7 =
      framePointer s + BitVec.ofNat 64 (ad.size % 16) := by
    have h : (Operand.reg 7 : Operand 64).read u7 = (AddrMode.sib 4 (some 5) 0 .none).addr u6
        (0x1008aa + BitVec.ofNat 64 (leaLen (.sib 4 (some 5) 0 .none))) := e7.writes
    rw [h]
    simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
    rw [show ((4 : BitVec 4).setWidth 5) = (4 : BitVec 5) from rfl,
      show ((5 : BitVec 4).setWidth 5) = (5 : BitVec 5) from rfl, ← stackPtr_eq_read, T6.rsp,
      e6.agrees.read (by simp; decide), hrbp6]
    simp
  obtain ⟨u8, a8, T8, e8, m8⟩ := T7.regStep
    (add_r64_imm8_effect_step 0x1008ae 0x48 0xc7 0x18 (by unfold RexWPrefix; decide) (by decide)
      (by decide))
    (code_at' T7.code _ 0x8ae (by decide) _ (by decide) (by decide +kernel))
    e7.rip (ne_boundary hOut (a := 0x1008b2) (by decide))
    (by simp [adChanges, loopFoot, callFoot, Component.isMem]; decide)
  have hrdi8 : (Operand.reg 7 : Operand 64).read u8 =
      framePointer s + BitVec.ofNat 64 (0x18 + ad.size % 16) := by
    have h : (Operand.reg 7 : Operand 64).read u8 =
        (Operand.reg 7 : Operand 64).read u7 + (0x18 : BitVec 8).signExtend 64 := e8.writes
    rw [h, hrdi7, show (0x18 : BitVec 8).signExtend 64 = BitVec.ofNat 64 0x18 from rfl,
      add_ofNat_add_ofNat, Nat.add_comm]
  obtain ⟨u9, a9, T9, e9, m9⟩ := T8.regStep
    (xor_r32_r32_effect_step 0x1008b2 0xf6 (by decide))
    (code_at' T8.code _ 0x8b2 (by decide) _ (by decide) (by decide +kernel))
    e8.rip (ne_boundary hOut (a := 0x1008b4) (by decide))
    (by simp [adChanges, loopFoot, callFoot, Component.isMem]; decide)
  have hrsi9 : rsi.read u9 = 0 := by
    have h : (Operand.reg 6 : Operand 64).read u9 =
        ((Operand.reg 6 : Operand 32).read u8 ^^^ (Operand.reg 6 : Operand 32).read u8).setWidth 64 :=
      e9.writes
    rw [show rsi = (Operand.reg 6 : Operand 64) from rfl, h, BitVec.xor_self]
    rfl
  have hrdi9 : rdi.read u9 = framePointer s + BitVec.ofNat 64 (0x18 + ad.size % 16) := by
    rw [show rdi = (Operand.reg 7 : Operand 64) from rfl, e9.agrees.read (by simp; decide), hrdi8]
  have hrdx9 : MemoryRoutines.rdx.read u9 = BitVec.ofNat 64 (16 - ad.size % 16) := by
    rw [show MemoryRoutines.rdx = (Operand.reg 2 : Operand 64) from rfl,
      e9.agrees.read (by simp; decide), e8.agrees.read (by simp; decide),
      e7.agrees.read (by simp; decide), hrdx6]
  have hrdiN : (rdi.read u9).toNat = (framePointer s).toNat + 0x18 + ad.size % 16 := by
    rw [hrdi9, add_toNat _ _ (by omega)]; omega
  have hrdxN : (MemoryRoutines.rdx.read u9).toNat = 16 - ad.size % 16 := by
    rw [hrdx9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hag39 := (((((e3.agrees.trans e4.agrees).trans e5.agrees).trans e6.agrees).trans
    e7.agrees).trans e8.agrees).trans e9.agrees
  have hdf9 : DirectionFlagClear u9.RFLAGS :=
    (hag39.directionFlagClear (by simp [movR64M64Effect, movR32Imm32Effect, addR64R64Effect, subR64R64Effect, leaR64Effect, addR64Imm8Effect, xorR32R32Effect, Effect.components])
      ⟨hdf2⟩).df
  obtain ⟨f10, u10, a10, r10, c10, hrip10, hrsp10, hag10, hcs10, hdf10, hkeep10, hfill10⟩ :=
    memset_call hstride G hOut T9.agrees T9.ready T9.code T9.rsp hdf9 (p := 0x1008b4)
      (d := 0x100b26) e9.rip
      (code_at' T9.code _ 0x8b4 (by decide) _ (by decide) (by decide +kernel))
      (by decide) (by decide) (by omega)
  have T10 : Track (framePointer s) (adChanges (framePointer s)) t0 u10 :=
    T9.extend r10 c10 hag10 hrsp10 (fun c hc _ => List.mem_append_left _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hc))) (fun x c hc hx => ⟨c, List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)), hx⟩)
  have hcs9 : ∀ r : BitVec 5, (r = 3 ∨ r = 5 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15) →
      (Operand.reg r : Operand 64).read u10 = (Operand.reg r : Operand 64).read u9 :=
    fun r hr => cs_read hcs10 hr
  have hr14_9 : (Operand.reg 14 : Operand 64).read u9 =
      ptr + BitVec.ofNat 64 (ad.size / 16 * 16) := by
    rw [e9.agrees.read (by simp; decide), e8.agrees.read (by simp; decide),
      e7.agrees.read (by simp; decide), e6.agrees.read (by simp; decide),
      e5.agrees.read (by simp [movR32Imm32Effect, Effect.components]; decide), hr14_4]
  have hrbp9 : (Operand.reg 5 : Operand 64).read u9 = BitVec.ofNat 64 (ad.size % 16) := by
    rw [e9.agrees.read (by simp; decide), e8.agrees.read (by simp; decide),
      e7.agrees.read (by simp; decide), e6.agrees.read (by simp; decide), hrbp6]
  obtain ⟨u11, a11, T11, e11, m11⟩ := T10.regStep
    (lea_r64_effect_step 0x1008ba 0x4c (by unfold RexWPrefix; decide) 5
      (.sib 4 none 0 (.d8 0x18)) ⟨by decide, fun _ => by decide⟩ (by decide) (by decide))
    (code_at' T10.code _ 0x8ba (by decide) _ (by decide) (by decide +kernel))
    hrip10 (ne_boundary hOut (a := 0x1008bf) (by decide))
    (by simp [adChanges, loopFoot, callFoot, Component.isMem]; decide)
  have hr13_11 : (Operand.reg 13 : Operand 64).read u11 = framePointer s + BitVec.ofNat 64 0x18 := by
    have h : (Operand.reg 13 : Operand 64).read u11 = (AddrMode.sib 4 none 0 (.d8 0x18)).addr u10
        (0x1008ba + BitVec.ofNat 64 (leaLen (.sib 4 none 0 (.d8 0x18)))) := e11.writes
    rw [h, sib_addr, hrsp10]; rfl
  obtain ⟨u12, a12, T12, e12, m12⟩ := T11.regStep
    (mov_r64_r64_effect_step 0x1008bf 0x4c 0xef (by unfold RexWPrefix; decide) (by decide))
    (code_at' T11.code _ 0x8bf (by decide) _ (by decide) (by decide +kernel))
    e11.rip (ne_boundary hOut (a := 0x1008c2) (by decide))
    (by simp [movR64R64Effect, Effect.components, adChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  obtain ⟨u13, a13, T13, e13, m13⟩ := T12.regStep
    (mov_r64_r64_effect_step 0x1008c2 0x4c 0xf6 (by unfold RexWPrefix; decide) (by decide))
    (code_at' T12.code _ 0x8c2 (by decide) _ (by decide) (by decide +kernel))
    e12.rip (ne_boundary hOut (a := 0x1008c5) (by decide))
    (by simp [movR64R64Effect, Effect.components, adChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  obtain ⟨u14, a14, T14, e14, m14⟩ := T13.regStep
    (mov_r64_r64_effect_step 0x1008c5 0x48 0xea (by unfold RexWPrefix; decide) (by decide))
    (code_at' T13.code _ 0x8c5 (by decide) _ (by decide) (by decide +kernel))
    e13.rip (ne_boundary hOut (a := 0x1008c8) (by decide))
    (by simp [movR64R64Effect, Effect.components, adChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  have hrdi14 : rdi.read u14 = framePointer s + BitVec.ofNat 64 0x18 := by
    have h : (Operand.reg 7 : Operand 64).read u12 = (Operand.reg 13 : Operand 64).read u11 :=
      e12.writes
    rw [show rdi = (Operand.reg 7 : Operand 64) from rfl,
      e14.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e13.agrees.read (by simp [movR64R64Effect, Effect.components]; decide), h, hr13_11]
  have hsrc : ptr + BitVec.ofNat 64 (ad.size / 16 * 16) = rsi.read u14 := by
    have h : (Operand.reg 6 : Operand 64).read u13 = (Operand.reg 14 : Operand 64).read u12 :=
      e13.writes
    rw [show rsi = (Operand.reg 6 : Operand 64) from rfl,
      e14.agrees.read (by simp [movR64R64Effect, Effect.components]; decide), h,
      e12.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e11.agrees.read (by simp; decide), hcs9 14 (by decide), hr14_9]
  have hrdx14 : MemoryRoutines.rdx.read u14 = BitVec.ofNat 64 (ad.size % 16) := by
    have h : (Operand.reg 2 : Operand 64).read u14 = (Operand.reg 5 : Operand 64).read u13 :=
      e14.writes
    rw [show MemoryRoutines.rdx = (Operand.reg 2 : Operand 64) from rfl, h,
      e13.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e12.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e11.agrees.read (by simp; decide), hcs9 5 (by decide), hrbp9]
  have hrdxN14 : (MemoryRoutines.rdx.read u14).toNat = ad.size % 16 := by
    rw [hrdx14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsrcN : (ptr + BitVec.ofNat 64 (ad.size / 16 * 16)).toNat = ptr.toNat + ad.size / 16 * 16 :=
    add_toNat _ _ (by omega)
  have hadByte : ∀ i < ad.size, u14.external[ptr + BitVec.ofNat 64 i]? = some ad[i]! := by
    intro i hi
    rw [T14.agrees.byte (fun c hc hcov => hstk i hi ((adChanges_scratch G c hc _ hcov).inStack G)),
      hmem i hi]
  have hdf14 : DirectionFlagClear u14.RFLAGS :=
    ((((e11.agrees.trans e12.agrees).trans e13.agrees).trans e14.agrees).directionFlagClear
      (by simp [movR64R64Effect, leaR64Effect, Effect.components]) ⟨hdf10⟩).df
  have hrem0 : 0 < ad.size % 16 := Nat.pos_of_ne_zero hz
  obtain ⟨f15, u15, a15, r15, c15, hrip15, hrsp15, hag15, hcs15, hdf15, hkeep15, hcopy15⟩ :=
    memcpy_call hstride G hOut T14.agrees T14.ready T14.code T14.rsp hdf14 (p := 0x1008c8)
      (d := 0x100ada) e14.rip
      (code_at' T14.code _ 0x8c8 (by decide) _ (by decide) (by decide +kernel))
      (by decide) (by decide)
      (by rw [hrdi14, hrdxN14, add_toNat _ _ (by omega)]; omega)
      (by rw [← hsrc, hrdxN14, hsrcN]; omega)
      (by
        intro i hi
        rw [hrdxN14] at hi
        rw [← hsrc, add_ofNat_add_ofNat, hadByte _ (by omega)]; rfl)
      (by
        intro i hi k hk he
        rw [hrdxN14] at hi
        rw [← hsrc, add_ofNat_add_ofNat] at he
        apply hstk _ (by omega : ad.size / 16 * 16 + i < ad.size)
        rw [he]
        unfold InStack
        rw [add_toNat _ _ (by rw [sub_toNat _ _ (by omega)]; omega), sub_toNat _ _ (by omega)]
        omega)
  have T15 : Track (framePointer s) (adChanges (framePointer s)) t0 u15 :=
    T14.extend r15 c15 hag15 hrsp15 (fun c hc _ => List.mem_append_left _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hc))) (fun x c hc hx => ⟨c, List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)), hx⟩)
  obtain ⟨u16, a16, T16, e16, m16⟩ := T15.regStep
    (mov_r64_r64_effect_step 0x1008ce 0x4c 0xff (by unfold RexWPrefix; decide) (by decide))
    (code_at' T15.code _ 0x8ce (by decide) _ (by decide) (by decide +kernel))
    hrip15 (ne_boundary hOut (a := 0x1008d1) (by decide))
    (by simp [movR64R64Effect, Effect.components, adChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  obtain ⟨u17, a17, T17, e17, m17⟩ := T16.regStep
    (mov_r64_r64_effect_step 0x1008d1 0x4c 0xee (by unfold RexWPrefix; decide) (by decide))
    (code_at' T16.code _ 0x8d1 (by decide) _ (by decide) (by decide +kernel))
    e16.rip (ne_boundary hOut (a := 0x1008d4) (by decide))
    (by simp [movR64R64Effect, Effect.components, adChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  have hr15_14 : (Operand.reg 15 : Operand 64).read u14 = polyBase s := by
    rw [e14.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e13.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e12.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e11.agrees.read (by simp; decide), hcs9 15 (by decide),
      hag39.read (by simp [movR64M64Effect, movR32Imm32Effect, addR64R64Effect, subR64R64Effect,
        leaR64Effect, addR64Imm8Effect, xorR32R32Effect, Effect.components] <;> decide), hreg2,
      hr15]
  have hr15_15 : (Operand.reg 15 : Operand 64).read u15 = polyBase s := by
    rw [cs_read hcs15 (by decide), hr15_14]
  have hrdi17 : rdi.read u17 = polyBase s := by
    have h : (Operand.reg 7 : Operand 64).read u16 = (Operand.reg 15 : Operand 64).read u15 :=
      e16.writes
    rw [show rdi = (Operand.reg 7 : Operand 64) from rfl,
      e17.agrees.read (by simp [movR64R64Effect, Effect.components]; decide), h, hr15_15]
  have hr13_15 : (Operand.reg 13 : Operand 64).read u15 = framePointer s + BitVec.ofNat 64 0x18 := by
    rw [cs_read hcs15 (by decide),
      e14.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e13.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e12.agrees.read (by simp [movR64R64Effect, Effect.components]; decide), hr13_11]
  have hrsi17 : rsi.read u17 = framePointer s + BitVec.ofNat 64 0x18 := by
    have h : (Operand.reg 6 : Operand 64).read u17 = (Operand.reg 13 : Operand 64).read u16 :=
      e17.writes
    rw [show rsi = (Operand.reg 6 : Operand 64) from rfl, h,
      e16.agrees.read (by simp [movR64R64Effect, Effect.components]; decide), hr13_15]
  have hmem17 : ∀ x : BitVec 64, u17.external[x]? = u15.external[x]? := fun x => by
    rw [m17, m16]
  have hmem14_10 : ∀ x : BitVec 64, u14.external[x]? = u10.external[x]? := fun x => by
    rw [m14, m13, m12, m11]
  have hmem9_2 : ∀ x : BitVec 64, u9.external[x]? = u2.external[x]? := fun x => by
    rw [m9, m8, m7, m6, m5, m4, m3]
  have hP0 : 96 ≤ (framePointer s).toNat := by omega
  have hP1 : (framePointer s).toNat + 0x200 < 2 ^ 64 := by omega
  have hblk : ∀ i < 16, u17.external[rsi.read u17 + BitVec.ofNat 64 i]? =
      some (tailBlock ad)[i]! := by
    intro i hi
    rw [hrsi17, add_ofNat_add_ofNat, hmem17, tailBlock_byte ad hz i hi]
    split
    · rename_i hir
      have hc := hcopy15 i (by rw [hrdxN14]; exact hir)
      rw [hrdi14, add_ofNat_add_ofNat, ← hsrc, add_ofNat_add_ofNat] at hc
      rw [hc, hadByte _ (by omega)]
    · rename_i hir
      have hx : (framePointer s + BitVec.ofNat 64 (0x18 + i)).toNat =
          (framePointer s).toNat + 0x18 + i := by rw [add_toNat _ _ (by omega)]; omega
      rw [hkeep15 _ (by rw [hx]; omega) (by rw [hx, hrdi14, hrdxN14, add_toNat _ _ (by omega)]; omega),
        hmem14_10]
      have hf := hfill10 (i - ad.size % 16) (by rw [hrdxN]; omega)
      rw [hrdi9, add_ofNat_add_ofNat, hrsi9,
        show 0x18 + ad.size % 16 + (i - ad.size % 16) = 0x18 + i by omega] at hf
      rw [hf]
      rfl
  have hfar17 : ∀ x : BitVec 64, (framePointer s).toNat ≤ x.toNat →
      (x.toNat < (framePointer s).toNat + 0x18 ∨ (framePointer s).toNat + 0x28 ≤ x.toNat) →
      u17.external[x]? = j.external[x]? := by
    intro x h1 h2
    rw [hmem17, hkeep15 _ h1 (by rw [hrdi14, hrdxN14, add_toNat _ _ (by omega)]; omega),
      hmem14_10, hkeep10 _ h1 (by rw [hrdiN, hrdxN]; omega), hmem9_2, m2, m1]
  have hpolyN : (polyBase s).toNat = (framePointer s).toNat + 0x150 := by
    unfold polyBase polyOffset; rw [add_toNat _ _ (by omega)]
  have hpoly17 : PolyState u17 (polyBase s) otk
      (absorbBlocks (clampedR otk) 0 (ad.extract 0 (16 * (ad.size / 16)))) :=
    PolyState.of_mem hpoly fun i hi => hfar17 _
      (by rw [add_toNat _ _ (by omega), hpolyN]; omega)
      (by rw [add_toNat _ _ (by omega), hpolyN]; omega)
  have hdf17 : DirectionFlagClear u17.RFLAGS :=
    ((e16.agrees.trans e17.agrees).directionFlagClear
      (by simp [movR64R64Effect, Effect.components]) ⟨hdf15⟩).df
  obtain ⟨f18, v, a18, r18, c18, hrip18, hrsp18, hag18, hcs18, hpoly18⟩ :=
    poly_call (p := 0x1008d4) (disp := 0x1557) G hOut T17.agrees T17.ready T17.code T17.rsp e17.rip
      (code_at' T17.code _ 0x8d4 (by decide) _ (by decide) (by decide +kernel))
      (by decide) (by decide) hrdi17 (tailBlock_size ad hz)
      (by rw [hrsi17, add_toNat _ _ (by omega)]; omega) hblk
      (rangeApart_of_toNat (by rw [hrsi17, add_toNat _ _ (by omega)]; omega)
        (by rw [sub_toNat _ _ (by omega)]; omega)
        (by rw [hrsi17, add_toNat _ _ (by omega), sub_toNat _ _ (by omega)]; omega))
      hpoly17
  have T18 : Track (framePointer s) (adChanges (framePointer s)) t0 v :=
    T17.extend r18 c18 hag18 hrsp18 (fun c hc _ => List.mem_append_left _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hc))) (fun x c hc hx => ⟨c, List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)), hx⟩)
  have hreg1714 : ∀ r : BitVec 5, (r = 3 ∨ r = 15) →
      (Operand.reg r : Operand 64).read u17 = (Operand.reg r : Operand 64).read u14 := by
    intro r hr
    rw [e17.agrees.read (by rcases hr with rfl | rfl <;> simp [movR64R64Effect, Effect.components] <;> decide),
      e16.agrees.read (by rcases hr with rfl | rfl <;> simp [movR64R64Effect, Effect.components] <;> decide),
      cs_read hcs15 (by rcases hr with rfl | rfl <;> simp)]
  refine ⟨1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + f10 + 1 + 1 + 1 + 1 + f15 + 1 + 1 + f18, v,
    ((((((((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans
      a9).trans a10).trans a11).trans a12).trans a13).trans a14).trans a15).trans a16).trans
      a17).trans a18, T18, by rw [hrip18]; rfl,
    (hag18.directionFlagClear (by simp [callFoot]) ⟨hdf17⟩).df, ?_, ?_, ?_, ?_⟩
  · rw [cs_read hcs18 (by decide), hreg1714 15 (by simp), hr15_14]
  · rw [cs_read hcs18 (by decide), hreg1714 3 (by simp),
      e14.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e13.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e12.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e11.agrees.read (by simp; decide), hcs9 3 (by decide),
      hag39.read (by simp [movR64M64Effect, movR32Imm32Effect, addR64R64Effect, subR64R64Effect,
        leaR64Effect, addR64Imm8Effect, xorR32R32Effect, Effect.components] <;> decide), hreg2]
  · intro x hx
    rw [callFoot_keep hag18 hP0 hP1 (by omega), hfar17 _ (by omega) (by omega)]
  · rw [absorb_padded, ite_f hz]
    exact hpoly18

theorem hasBytes_keep {m m' : Ram} {r : MemoryRegion} {b : ByteArray} (h : r.HasBytes m b)
    (hk : ∀ i < r.size, m'[BitVec.ofNat 64 (r.start + i)]? = m[BitVec.ofNat 64 (r.start + i)]?) :
    r.HasBytes m' b := by
  refine ⟨h.1, fun i => ?_⟩
  have hl := h.1
  unfold MemoryRegion.HasLength at hl
  rw [hk i.val (by omega)]
  exact h.2 i

theorem message_far [bindings : Bindings] {s : RamState} {key : Vector UInt8 32}
    {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) :
    inPtr.toNat + plaintext.size < 2 ^ 32 ∧
    ∀ i < plaintext.size, ¬ InStack s (BitVec.ofNat 64 (inPtr.toNat + i)) := by
  obtain ⟨hb, hlen, -⟩ := hPre.messageInMemory
  simp only [MemoryRegion.Bounded, userAddressLimit, messageRegion] at hb
  refine ⟨by omega, ?_⟩
  intro i hi hin
  have hn : (BitVec.ofNat 64 (inPtr.toNat + i)).toNat = inPtr.toNat + i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstk : (Stack.region s coreStackBytes).Contains (inPtr.toNat + i) := by
    unfold InStack at hin
    rw [hn] at hin
    simp only [Stack.region, MemoryRegion.Contains, Stack.returnAddressBytes, coreStackBytes]
    have hsp : s.regValue .rsp = stackPtr s := rfl
    rw [hsp]
    omega
  have hmsg : (messageRegion inPtr plaintext.size).Contains (inPtr.toNat + i) := by
    simp only [messageRegion, MemoryRegion.Contains]; omega
  by_cases he : inPtr = outPtr
  · subst he
    have hp := hPre.separation.1
    simp only [coreWritten, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hp
    exact hp.2.1 _ hmsg hstk
  · have hr : messageRegion inPtr plaintext.size ∈ coreRead s inPtr outPtr plaintext.size := by
      simp [coreRead, he]
    exact hPre.separation.2.1 _ stack_mem_written _ hr _ hstk hmsg

set_option maxHeartbeats 8000000 in
theorem absorb_associated_data [bindings : Machine.Bindings] {s : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    {inPtr outPtr : BitVec 64} (boundary : ReturnBoundary) {t : RamState}
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hBoundaryOutside : ¬ InProgram boundary.rip)
    (_hBoundaryDifferent : boundary.rip ≠ (returnBoundary s).rip)
    (hCut : Cut1 s t key nonce associatedData plaintext inPtr outPtr) :
    ∃ fuel u, Advances boundary fuel t u ∧
      Cut2 s u key nonce associatedData plaintext inPtr outPtr := by
  have hInv := hCut.toInv
  have G := geometry_of hPre hInv
  have hP := frame_toNat s G.low
  have hglow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hP
  have hP0 : 96 ≤ (framePointer s).toNat := by omega
  have hP1 : (framePointer s).toNat + 0x200 < 2 ^ 64 := by omega
  have T0 : Track (framePointer s) (adChanges (framePointer s)) t t :=
    Track.refl (ready_of hInv) hInv.code hInv.rsp
  have hrv := regValue_read t
  have hsv := regValue_read s
  have hadr : associatedDataRegion s ∈ coreRead s inPtr outPtr plaintext.size := by
    simp [coreRead]
  obtain ⟨hadB, hadM, hadS⟩ := read_region hPre hInv hadr hPre.associatedDataInMemory
  have hstart : (associatedDataRegion s).start = (s.regValue .rcx).toNat := rfl
  rw [hstart] at hadB hadM hadS
  have hmem : ∀ i < associatedData.size,
      t.external[s.regValue .rcx + BitVec.ofNat 64 i]? = some associatedData[i]! := by
    intro i hi; rw [← ofNat_toNat_add]; exact hadM i hi
  have hstk : ∀ i < associatedData.size, ¬ InStack s (s.regValue .rcx + BitVec.ofNat 64 i) := by
    intro i hi; rw [← ofNat_toNat_add]; exact hadS i hi
  have hfar : ∀ c ∈ adChanges (framePointer s), ∀ i < associatedData.size,
      ¬ c.Covers (s.regValue .rcx + BitVec.ofNat 64 i) :=
    fun c hc i hi hcov => hstk i hi ((adChanges_scratch G c hc _ hcov).inStack G)
  have hr13 : (Operand.reg 13 : Operand 64).read t = s.regValue .r8 := by
    rw [← hrv.2.2.2.2.2.2.2.2.2.1]; exact hCut.r13
  have hlenN : (s.regValue .r8).toNat = associatedData.size := hPre.associatedDataLength
  obtain ⟨f1, e, a1, T1, hrip1, hr12e, hrbpe, hr13e, hr15e, hrbxe, hcfe, hs8, hs10, hs98, hsa0,
      hsa8, habove⟩ :=
    ad_prologue G hBoundaryOutside T0 hCut.rip (by rw [hr13, hlenN]; omega)
  rw [hr13, hlenN] at hr12e hrbpe hcfe
  have hpolyE : PolyState e (polyBase s) (otk key nonce) 0 :=
    PolyState.of_mem hCut.poly fun i _ => habove _ (by
      unfold polyBase polyOffset
      rw [add_ofNat_add_ofNat, add_toNat _ _ (by omega)]; omega)
  have hr15t : (Operand.reg 15 : Operand 64).read t = polyBase s := by
    rw [← hrv.2.2.2.2.2.2.2.2.2.2.2.1]; exact hCut.r15
  obtain ⟨f2, j, a2, T2, hloop, hrip2, hr15j, hpolyJ⟩ :=
    ad_head G hBoundaryOutside T1 hrip1 (by omega) hmem hfar hcfe hr12e
      (by rw [hs8, ← hrv.2.2.2.2.2.2.2.1]; exact hCut.rbp) (by rw [hr15e, hr15t]) hpolyE
  have hdfj : DirectionFlagClear j.RFLAGS :=
    (T2.agrees.directionFlagClear (by simp [adChanges, loopFoot, callFoot])
      hInv.directionFlagUnset).df
  have hloopKeep : ∀ x : BitVec 64, (framePointer s).toNat ≤ x.toNat →
      (x.toNat < (framePointer s).toNat + 0x18 ∨
        ((framePointer s).toNat + 0x28 ≤ x.toNat ∧ x.toNat < (framePointer s).toNat + 0x174)) →
      j.external[x]? = e.external[x]? := fun x h1 h2 =>
    loopFoot_keep hloop hP0 hP1 ⟨h1, by omega⟩
  have hslotJ : ∀ k, 8 ≤ k → (k + 8 ≤ 0x18 ∨ (0x28 ≤ k ∧ k + 8 ≤ 0x174)) →
      (Operand.mem (framePointer s + BitVec.ofNat 64 k) : Operand 64).read j =
        (Operand.mem (framePointer s + BitVec.ofNat 64 k) : Operand 64).read e := by
    intro k hk1 hk2
    apply read_mem_eq
    intro i hi
    change i < 8 at hi
    rw [add_ofNat_add_ofNat]
    exact hloopKeep _ (by rw [add_toNat _ _ (by omega)]; omega)
      (by rw [add_toNat _ _ (by omega)]; omega)
  obtain ⟨f3, u, a3, T3, hrip3, hdf3, hr15u, hrbxu, hslotsU, hpolyU⟩ :=
    ad_tail hInv.environment.stringStride G hBoundaryOutside T2 hdfj hrip2 (by omega) hmem hstk
      (by rw [hloop.read (by simp [loopFoot, callFoot]), hrbpe])
      (by rw [hloop.read (by simp [loopFoot, callFoot]), hr12e])
      (by rw [hslotJ 8 (by omega) (by omega), hs8, ← hrv.2.2.2.2.2.2.2.1]; exact hCut.rbp)
      hr15j hpolyJ
  have hslotU : ∀ k, (0x10 ≤ k ∧ k + 8 ≤ 0x18) ∨ (0x98 ≤ k ∧ k + 8 ≤ 0xb0) →
      (Operand.mem (framePointer s + BitVec.ofNat 64 k) : Operand 64).read u =
        (Operand.mem (framePointer s + BitVec.ofNat 64 k) : Operand 64).read e := by
    intro k hk
    rw [← hslotJ k (by omega) (by omega)]
    apply read_mem_eq
    intro i hi
    change i < 8 at hi
    rw [add_ofNat_add_ofNat]
    exact hslotsU _ (by rw [add_toNat _ _ (by omega)]; omega)
  have hscr := adChanges_scratch G
  have hdfc : Component.df ∉ adChanges (framePointer s) := by simp [adChanges, loopFoot, callFoot]
  have hfb : frameBase s = (framePointer s).toNat := by unfold frameBase; rw [hP]; rfl
  have hslotW : ∀ k v, 8 ≤ k → k + 8 ≤ 0x1b8 →
      (Operand.mem (framePointer s + BitVec.ofNat 64 k) : Operand 64).read u = v →
      (slot s k).Word64At u.external v := by
    intro k v hk1 hk2 hv
    have hw := word64At_of (m := u.external) hv (fun i hi => by
      apply T3.agrees.grow
      apply G.allocated
      unfold InStack
      rw [add_ofNat_add_ofNat, add_toNat _ _ (by omega)]
      omega)
    have he : (⟨(framePointer s + BitVec.ofNat 64 k).toNat, 8⟩ : MemoryRegion) = slot s k := by
      unfold slot; rw [add_toNat _ _ (by omega), hfb]
    rwa [he] at hw
  have hkeepU : ∀ x : BitVec 64, ¬ Scratch s x → u.external[x]? = t.external[x]? :=
    fun x hx => T3.keep hscr hx
  have hframeKeep : ∀ off n, 0xb0 ≤ off → off + n ≤ 0x174 → ∀ i < n,
      u.external[BitVec.ofNat 64 (frameBase s + off + i)]? =
        t.external[BitVec.ofNat 64 (frameBase s + off + i)]? := by
    intro off n h1 h2 i hi
    apply hkeepU
    unfold Scratch
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨hmB, hmS⟩ := message_far hPre
  refine ⟨f1 + f2 + f3, u, (a1.trans a2).trans a3, ?_⟩
  exact {
    toInv := inv_of_track hPre hInv G T3 hscr hdfc
    rip := hrip3
    r15 := hr15u
    rbx := by
      rw [(regValue_read u).2.2.2.2.2.2.1, hrbxu, hloop.read (by simp [loopFoot, callFoot]), hrbxe,
        ← hrv.2.2.2.2.2.2.1]
      exact hCut.rbx
    lengthSlot := hslotW 0x10 _ (by omega) (by omega) (by
      rw [hslotU 0x10 (by omega), hs10, ← hrv.2.2.2.1]; exact hCut.rcx)
    adLengthSlot := hslotW 0x98 _ (by omega) (by omega) (by
      rw [hslotU 0x98 (by omega), hs98, hr13])
    resultSlot := hslotW 0xa0 _ (by omega) (by omega) (by
      rw [hslotU 0xa0 (by omega), hsa0, ← hrv.2.2.2.2.2.2.2.2.2.2.1]; exact hCut.r14)
    descriptorSlot := hslotW 0xa8 _ (by omega) (by omega) (by
      rw [hslotU 0xa8 (by omega), hsa8, ← hrv.2.2.2.2.2.2.2.2.1]; exact hCut.r12)
    message := hasBytes_keep hCut.message fun i hi => hkeepU _ fun hsc =>
      hmS i hi (hsc.inStack G)
    cipher := hasBytes_keep hCut.cipher fun i hi => hframeKeep cipherOffset 0x40
      (by decide) (by decide) i hi
    position := hasBytes_keep hCut.position fun i hi => by
      have := hframeKeep (cipherOffset + 0x40) 1 (by decide) (by decide) i hi
      simpa [Nat.add_assoc] using this
    poly := hpolyU }

theorem land_mask38 (x : Nat) (hx : x < 2 ^ 38) : x &&& 0x3ffffffff0 = x / 16 * 16 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 : x / 16 * 16 = (x >>> 4) <<< 4 := by
    simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have h2 : (0x3ffffffff0 : Nat) = (2 ^ 34 - 1) <<< 4 := by decide
  rw [Nat.testBit_and, h1, h2, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : 4 ≤ i
  · by_cases hi' : i < 38
    · simp [hi, show i - 4 < 34 by omega, show 4 + (i - 4) = i by omega]
    · have : x.testBit i = false := Nat.testBit_lt_two_pow (by
        calc x < 2 ^ 38 := hx
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [hi, show ¬ (i - 4 < 34) by omega, show 4 + (i - 4) = i by omega, this]
  · simp [hi]

def ctChanges (P : BitVec 64) : List Component :=
  loopFoot P 5 ++ [.reg 3, .reg 12, .reg 13]

theorem ctChanges_scratch {s t0 : RamState} (G : Geometry s t0) :
    ∀ c ∈ ctChanges (framePointer s), ∀ x, c.Covers x → Scratch s x := by
  intro c hc x hx
  simp only [ctChanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hc | rfl | rfl | rfl
  · exact loopFoot_scratch G 5 c hc x hx
  all_goals exact absurd hx id

set_option maxHeartbeats 8000000 in
theorem ct_head [Bindings] {s t0 : RamState} (G : Geometry s t0) {boundary : ReturnBoundary}
    (hOut : ¬ InProgram boundary.rip)
    (T0 : Track (framePointer s) (ctChanges (framePointer s)) t0 t0)
    (hrip : t0.RIP = 0x100916) {ptr : BitVec 64} {ct : ByteArray} {otk : Vector UInt8 32}
    {acc : Nat}
    (hlow : ptr.toNat + ct.size ≤ 2 ^ 32)
    (hmem : ∀ i < ct.size, t0.external[ptr + BitVec.ofNat 64 i]? = some ct[i]!)
    (hfar : ∀ c ∈ ctChanges (framePointer s), ∀ i < ct.size, ¬ c.Covers (ptr + BitVec.ofNat 64 i))
    (hr12 : (Operand.reg 12 : Operand 64).read t0 = ptr)
    (hr14 : (Operand.reg 14 : Operand 64).read t0 = BitVec.ofNat 64 ct.size)
    (hrbx : (Operand.reg 3 : Operand 64).read t0 = lengthLimit)
    (hr15 : (Operand.reg 15 : Operand 64).read t0 = polyBase s)
    (hpoly : PolyState t0 (polyBase s) otk acc) :
    ∃ fuel j, Advances boundary fuel t0 j ∧
      Track (framePointer s) (ctChanges (framePointer s)) t0 j ∧ j.RIP = 0x100945 ∧
      (Operand.reg 15 : Operand 64).read j = polyBase s ∧
      (Operand.reg 12 : Operand 64).read j = ptr ∧
      (Operand.reg 3 : Operand 64).read j = BitVec.ofNat 64 (ct.size / 16 * 16) ∧
      (Operand.reg 13 : Operand 64).read j = BitVec.ofNat 64 (ct.size % 16) ∧
      (∀ x : BitVec 64, (framePointer s).toNat ≤ x.toNat →
        (x.toNat < (framePointer s).toNat + 0x18 ∨
          ((framePointer s).toNat + 0x28 ≤ x.toNat ∧ x.toNat < (framePointer s).toNat + 0x174) ∨
          (framePointer s).toNat + 0x188 ≤ x.toNat) → j.external[x]? = t0.external[x]?) ∧
      PolyState j (polyBase s) otk
        (absorbBlocks (clampedR otk) acc (ct.extract 0 (16 * (ct.size / 16)))) := by
  have hP := frame_toNat s G.low
  have hglow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hP
  have hP0 : 96 ≤ (framePointer s).toNat := by omega
  have hP1 : (framePointer s).toNat + 0x200 < 2 ^ 64 := by omega
  obtain ⟨t1, a1, T1, e1, m1⟩ := T0.regStep
    (add_r64_imm8_effect_step 0x100916 0x48 0xc3 0x31 (by unfold RexWPrefix; decide) (by decide)
      (by decide))
    (code_at' T0.code _ 0x916 (by decide) _ (by decide) (by decide +kernel))
    hrip (ne_boundary hOut (a := 0x10091a) (by decide))
    (by simp [ctChanges, loopFoot, callFoot, Component.isMem]; decide)
  obtain ⟨t2, a2, T2, e2, m2⟩ := T1.regStep
    (and_r64_r64_effect_step 0x10091a 0x4c 0xf3 (by unfold RexWPrefix; decide) (by decide))
    (code_at' T1.code _ 0x91a (by decide) _ (by decide) (by decide +kernel))
    e1.rip (ne_boundary hOut (a := 0x10091d) (by decide))
    (by simp [ctChanges, loopFoot, callFoot, Component.isMem]; decide)
  obtain ⟨t3, a3, T3, e3, m3⟩ := T2.regStep
    (mov_r32_r32_rex_effect_step 0x10091d 0x45 0xf5 (by unfold RexNoWPrefix; decide) (by decide))
    (code_at' T2.code _ 0x91d (by decide) _ (by decide) (by decide +kernel))
    e2.rip (ne_boundary hOut (a := 0x100920) (by decide))
    (by simp [movR32R32Effect, Effect.components, ctChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  obtain ⟨t4, a4, T4, e4, m4⟩ := T3.regStep
    (and_r32_imm8_rex_effect_step 0x100920 0x41 0xe5 0x0f (by unfold RexNoWPrefix; decide)
      (by decide) (by decide))
    (code_at' T3.code _ 0x920 (by decide) _ (by decide) (by decide +kernel))
    e3.rip (ne_boundary hOut (a := 0x100924) (by decide))
    (by simp [ctChanges, loopFoot, callFoot, Component.isMem]; decide)
  obtain ⟨t5, a5, T5, e5, m5⟩ := T4.regStep
    (cmp_r64_imm8_effect_step 0x100924 0x49 0xfe 0x10 (by unfold RexWPrefix; decide) (by decide)
      (by decide))
    (code_at' T4.code _ 0x924 (by decide) _ (by decide) (by decide +kernel))
    e4.rip (ne_boundary hOut (a := 0x100928) (by decide))
    (by simp [ctChanges, loopFoot, callFoot, Component.isMem])
  have hmem05 : ∀ x : BitVec 64, t5.external[x]? = t0.external[x]? := fun x => by
    rw [m5, m4, m3, m2, m1]
  have hsz : ct.size ≤ 2 ^ 32 := by omega
  have hr14_2 : (Operand.reg 14 : Operand 64).read t2 = BitVec.ofNat 64 ct.size := by
    rw [e2.agrees.read (by simp; decide), e1.agrees.read (by simp; decide), hr14]
  have hrbx5 : (Operand.reg 3 : Operand 64).read t5 = BitVec.ofNat 64 (ct.size / 16 * 16) := by
    rw [e5.agrees.read (by simp), e4.agrees.read (by simp; decide),
      e3.agrees.read (by simp [movR32R32Effect, Effect.components]; decide)]
    have h2 : (Operand.reg 3 : Operand 64).read t2 =
        (Operand.reg 3 : Operand 64).read t1 &&& (Operand.reg 14 : Operand 64).read t1 := e2.writes
    have h1 : (Operand.reg 3 : Operand 64).read t1 =
        (Operand.reg 3 : Operand 64).read t0 + (0x31 : BitVec 8).signExtend 64 := e1.writes
    rw [h2, h1, e1.agrees.read (by simp; decide), hrbx, hr14]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (lengthLimit + (0x31 : BitVec 8).signExtend 64).toNat = 0x3ffffffff0 from rfl,
      Nat.mod_eq_of_lt (by omega), Nat.and_comm, land_mask38 _ (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hr13_5 : (Operand.reg 13 : Operand 64).read t5 = BitVec.ofNat 64 (ct.size % 16) := by
    rw [e5.agrees.read (by simp)]
    have h4 : (Operand.reg 13 : Operand 64).read t4 =
        ((Operand.reg 13 : Operand 32).read t3 &&& (0x0f : BitVec 8).signExtend 32).setWidth 64 :=
      e4.writes
    have h3 : (Operand.reg 13 : Operand 64).read t3 =
        ((Operand.reg 14 : Operand 32).read t2).setWidth 64 := e3.writes
    have h3' : (Operand.reg 13 : Operand 32).read t3 =
        ((Operand.reg 14 : Operand 64).read t2).setWidth 32 := by
      change ((Operand.reg 13 : Operand 64).read t3).setWidth 32 = _
      rw [h3]
      simp
    rw [h4, h3', hr14_2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth,
      show ((0x0f : BitVec 8).signExtend 32).toNat = 15 from rfl, land_15, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    omega
  have hkeep05 : ∀ r : BitVec 5, r ≠ 3 → r ≠ 13 →
      (Operand.reg r : Operand 64).read t5 = (Operand.reg r : Operand 64).read t0 := by
    intro r h3 h13
    rw [e5.agrees.read (by simp), e4.agrees.read (by simp; exact h13),
      e3.agrees.read (by simp [movR32R32Effect, Effect.components]; exact h13),
      e2.agrees.read (by simp; exact h3), e1.agrees.read (by simp; exact h3)]
  have hcf5 : (StatusFlags.ofRFLAGS t5.RFLAGS).CF = decide (ct.size < 16) := by
    have h := e5.flags
    simp only [cmpR64Imm8Effect, Effect.FlagsHold, StatusFlagsOutcome.ofStatusFlags,
      StatusFlagsOutcome.Allows, FlagAllows] at h
    rw [h.1, show ∀ x y : BitVec 64, (cmpSpec x y).CF = decide (x.toNat < y.toNat) from fun _ _ => rfl]
    show decide (((Operand.reg 14 : Operand 64).read t4).toNat <
      ((0x10 : BitVec 8).signExtend 64).toNat) = _
    rw [e4.agrees.read (by simp; decide),
      e3.agrees.read (by simp [movR32R32Effect, Effect.components]; decide), hr14_2,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rfl
  obtain ⟨t6, a6, T6, e6, m6⟩ := T5.regStep (jcc_rel8_effect_step 0x100928 2 0x1b)
    (code_at' T5.code _ 0x928 (by decide) _ (by decide) (by decide +kernel))
    ⟨e5.rip, fun _ => by decide⟩
    (by
      simp only [jccEffect, branchEffect]
      split
      · exact ne_boundary hOut (a := 0x100945) (by decide)
      · exact ne_boundary hOut (a := 0x10092a) (by decide))
    (by simp [jccEffect, ctChanges, loopFoot, callFoot, Component.isMem])
  have hrip6 : t6.RIP = if ct.size < 16 then 0x100945 else 0x10092a := by
    rw [e6.rip]
    simp only [jccEffect, branchEffect, condHolds_2, hcf5]
    by_cases h : ct.size < 16 <;> simp [h] <;> rfl
  have hl6 : AgreesExcept (loopFoot (framePointer s) 5) t5 t6 :=
    e6.agrees.mono (by simp [jccEffect, loopFoot, callFoot])
  have hreg6 : ∀ r : BitVec 5, (Operand.reg r : Operand 64).read t6 =
      (Operand.reg r : Operand 64).read t5 := fun r => e6.agrees.read (by simp [jccEffect])
  have hlf : ∀ c ∈ loopFoot (framePointer s) 5, c ∈ ctChanges (framePointer s) :=
    fun c hc => List.mem_append_left _ hc
  have finish : ∀ fuel j, Advances boundary fuel t0 j →
      Track (framePointer s) (ctChanges (framePointer s)) t0 j → j.RIP = 0x100945 →
      (Operand.reg 15 : Operand 64).read j = polyBase s →
      AgreesExcept (loopFoot (framePointer s) 5) t5 j →
      PolyState j (polyBase s) otk
        (absorbBlocks (clampedR otk) acc (ct.extract 0 (16 * (ct.size / 16)))) →
      ∃ fuel j, Advances boundary fuel t0 j ∧
        Track (framePointer s) (ctChanges (framePointer s)) t0 j ∧ j.RIP = 0x100945 ∧
        (Operand.reg 15 : Operand 64).read j = polyBase s ∧
        (Operand.reg 12 : Operand 64).read j = ptr ∧
        (Operand.reg 3 : Operand 64).read j = BitVec.ofNat 64 (ct.size / 16 * 16) ∧
        (Operand.reg 13 : Operand 64).read j = BitVec.ofNat 64 (ct.size % 16) ∧
        (∀ x : BitVec 64, (framePointer s).toNat ≤ x.toNat →
          (x.toNat < (framePointer s).toNat + 0x18 ∨
            ((framePointer s).toNat + 0x28 ≤ x.toNat ∧ x.toNat < (framePointer s).toNat + 0x174) ∨
            (framePointer s).toNat + 0x188 ≤ x.toNat) → j.external[x]? = t0.external[x]?) ∧
        PolyState j (polyBase s) otk
          (absorbBlocks (clampedR otk) acc (ct.extract 0 (16 * (ct.size / 16)))) := by
    intro fuel j a T hr h15 hl hp
    refine ⟨fuel, j, a, T, hr, h15, ?_, ?_, ?_, ?_, hp⟩
    · rw [hl.read (by simp [loopFoot, callFoot]), hkeep05 12 (by decide) (by decide), hr12]
    · rw [hl.read (by simp [loopFoot, callFoot]), hrbx5]
    · rw [hl.read (by simp [loopFoot, callFoot]), hr13_5]
    · intro x h1 h2
      rw [loopFoot_keep hl hP0 hP1 ⟨h1, h2⟩, hmem05]
  by_cases hs : ct.size < 16
  · have hn : ct.size / 16 = 0 := by omega
    refine finish _ t6 ((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6)) T6
      (by rw [hrip6, ite_t hs]) (by rw [hreg6, hkeep05 15 (by decide) (by decide), hr15]) hl6 ?_
    rw [hn, Nat.mul_zero, absorbBlocks_extract_zero]
    exact PolyState.of_mem hpoly fun i _ => by rw [m6, hmem05]
  · have hrip6' : t6.RIP = 0x10092a := by rw [hrip6, ite_f hs]
    obtain ⟨t7, a7, T7, e7, m7⟩ := T6.regStep
      (mov_r64_r64_effect_step 0x10092a 0x48 0xdd (by unfold RexWPrefix; decide) (by decide))
      (code_at' T6.code _ 0x92a (by decide) _ (by decide) (by decide +kernel))
      hrip6' (ne_boundary hOut (a := 0x10092d) (by decide))
      (by simp [movR64R64Effect, Effect.components, ctChanges, loopFoot, callFoot,
        Component.isMem]; decide)
    obtain ⟨t8, a8, T8, e8, m8⟩ := T7.regStep
      (mov_r64_r64_effect_step 0x10092d 0x4c 0xe6 (by unfold RexWPrefix; decide) (by decide))
      (code_at' T7.code _ 0x92d (by decide) _ (by decide) (by decide +kernel))
      e7.rip (ne_boundary hOut (a := 0x100930) (by decide))
      (by simp [movR64R64Effect, Effect.components, ctChanges, loopFoot, callFoot,
        Component.isMem]; decide)
    have hL : LoopAt ctSite s t0 t5 t8 (ctChanges (framePointer s)) ptr ct otk acc 0 := by
      refine ⟨T8, ?_, e8.rip, ?_, ?_, ?_, ?_⟩
      · refine loopExt (loopExt hl6 e7.agrees ?_) e8.agrees ?_
        · simp [movR64R64Effect, Effect.components, loopFoot, callFoot]
          decide
        · simp [movR64R64Effect, Effect.components, loopFoot, callFoot] <;> decide
      · have h : (Operand.reg 6 : Operand 64).read t8 = (Operand.reg 12 : Operand 64).read t7 :=
          e8.writes
        rw [show rsi = (Operand.reg 6 : Operand 64) from rfl, h,
          e7.agrees.read (by simp [movR64R64Effect, Effect.components]; decide), hreg6,
          hkeep05 12 (by decide) (by decide), hr12]
        simp
      · show (Operand.reg 5 : Operand 64).read t8 = _
        have h : (Operand.reg 5 : Operand 64).read t7 = (Operand.reg 3 : Operand 64).read t6 :=
          e7.writes
        rw [e8.agrees.read (by simp [movR64R64Effect, Effect.components]; decide), h, hreg6,
          hrbx5]
        congr 1
        omega
      · rw [e8.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
          e7.agrees.read (by simp [movR64R64Effect, Effect.components]; decide), hreg6,
          hkeep05 15 (by decide) (by decide), hr15]
      · rw [Nat.mul_zero, absorbBlocks_extract_zero]
        exact PolyState.of_mem hpoly fun i _ => by rw [m8, m7, m6, hmem05]
    obtain ⟨f, t9, a9, D⟩ := loop_run (Or.inr rfl) G hOut hlf hlow hmem hfar (ct.size / 16) 0 t8
      (by omega) (by omega) hL
    exact finish _ t9 ((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans
      a7).trans a8).trans a9) D.track D.rip D.r15 D.loop D.poly

set_option maxHeartbeats 8000000 in
theorem ct_tail [inst : Bindings] (hstride : UnitStringStride inst) {s t0 j : RamState}
    (G : Geometry s t0) {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip)
    (T : Track (framePointer s) (ctChanges (framePointer s)) t0 j)
    (hdf : DirectionFlagClear j.RFLAGS) (hrip : j.RIP = 0x100945)
    {ptr : BitVec 64} {ad : ByteArray} {otk : Vector UInt8 32} {acc : Nat}
    (hlow : ptr.toNat + ad.size ≤ 2 ^ 32)
    (hmem : ∀ i < ad.size, t0.external[ptr + BitVec.ofNat 64 i]? = some ad[i]!)
    (hstk : ∀ i < ad.size, ¬ InStack s (ptr + BitVec.ofNat 64 i))
    (hr13 : (Operand.reg 13 : Operand 64).read j = BitVec.ofNat 64 (ad.size % 16))
    (hrbx : (Operand.reg 3 : Operand 64).read j = BitVec.ofNat 64 (ad.size / 16 * 16))
    (hr12 : (Operand.reg 12 : Operand 64).read j = ptr)
    (hr15 : (Operand.reg 15 : Operand 64).read j = polyBase s)
    (hpoly : PolyState j (polyBase s) otk
      (absorbBlocks (clampedR otk) acc (ad.extract 0 (16 * (ad.size / 16))))) :
    ∃ fuel t, Advances boundary fuel j t ∧
      Track (framePointer s) (ctChanges (framePointer s)) t0 t ∧ t.RIP = 0x100984 ∧
      DirectionFlagClear t.RFLAGS ∧
      (Operand.reg 15 : Operand 64).read t = polyBase s ∧
      (∀ x : BitVec 64, ((framePointer s).toNat + 0x10 ≤ x.toNat ∧
          x.toNat < (framePointer s).toNat + 0x18) ∨
        ((framePointer s).toNat + 0x98 ≤ x.toNat ∧ x.toNat < (framePointer s).toNat + 0xb0) →
        t.external[x]? = j.external[x]?) ∧
      PolyState t (polyBase s) otk (absorbBlocks (clampedR otk) acc (ad ++ pad16 ad)) := by
  have hP := frame_toNat s G.low
  have hglow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hP
  have hrem : ad.size % 16 < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨u1, a1, T1, e1, m1⟩ := T.regStep
    (test_r64_r64_effect_step 0x100945 0x4d 0xed (by unfold RexWPrefix; decide) (by decide))
    (code_at' T.code _ 0x945 (by decide) _ (by decide) (by decide +kernel))
    hrip (ne_boundary hOut (a := 0x100948) (by decide))
    (by simp [ctChanges, loopFoot, callFoot, Component.isMem])
  have hzf : (StatusFlags.ofRFLAGS u1.RFLAGS).ZF = decide (ad.size % 16 = 0) := by
    have h := e1.flags
    simp only [testR64R64Effect, testFlags, Effect.FlagsHold, StatusFlagsOutcome.Allows,
      FlagAllows] at h
    rw [h.2.2.2.1]
    show ((Operand.reg 13 : Operand 64).read j &&& (Operand.reg 13 : Operand 64).read j == 0) = _
    rw [hr13, BitVec.and_self, ofNat_beq_zero _ (by omega)]
  obtain ⟨u2, a2, T2, e2, m2⟩ := T1.regStep (jcc_rel8_effect_step 0x100948 4 0x3a)
    (code_at' T1.code _ 0x948 (by decide) _ (by decide) (by decide +kernel))
    ⟨e1.rip, fun _ => by decide⟩
    (by
      simp only [jccEffect, branchEffect]
      split
      · exact ne_boundary hOut (a := 0x100984) (by decide)
      · exact ne_boundary hOut (a := 0x10094a) (by decide))
    (by simp [jccEffect, ctChanges, loopFoot, callFoot, Component.isMem])
  have hrip2 : u2.RIP = if ad.size % 16 = 0 then 0x100984 else 0x10094a := by
    rw [e2.rip]
    simp only [jccEffect, branchEffect, condHolds_4, hzf]
    by_cases h : ad.size % 16 = 0 <;> simp [h] <;> rfl
  have hreg2 : ∀ r : BitVec 5, (Operand.reg r : Operand 64).read u2 =
      (Operand.reg r : Operand 64).read j := fun r => by
    rw [e2.agrees.read (by simp [jccEffect]), e1.agrees.read (by simp)]
  have hdf2 : DirectionFlagClear u2.RFLAGS :=
    ((e1.agrees.trans e2.agrees).directionFlagClear (by simp [jccEffect]) ⟨hdf⟩).df
  by_cases hz : ad.size % 16 = 0
  · refine ⟨1 + 1, u2, a1.trans a2, T2, by rw [hrip2, ite_t hz], hdf2, by rw [hreg2, hr15],
      fun x _ => by rw [m2, m1], ?_⟩
    rw [absorb_padded, ite_t hz]
    exact PolyState.of_mem hpoly fun i _ => by rw [m2, m1]
  have hrip2' : u2.RIP = 0x10094a := by rw [hrip2, ite_f hz]
  obtain ⟨u4, a4, T4, e4, m4⟩ := T2.regStep
    (add_r64_r64_effect_step 0x10094a 0x49 0xdc (by unfold RexWPrefix; decide) (by decide))
    (code_at' T2.code _ 0x94a (by decide) _ (by decide) (by decide +kernel))
    hrip2' (ne_boundary hOut (a := 0x10094d) (by decide))
    (by simp [ctChanges, loopFoot, callFoot, Component.isMem]; decide)
  have hr12_4 : (Operand.reg 12 : Operand 64).read u4 =
      ptr + BitVec.ofNat 64 (ad.size / 16 * 16) := by
    have h : (Operand.reg 12 : Operand 64).read u4 =
        (Operand.reg 12 : Operand 64).read u2 + (Operand.reg 3 : Operand 64).read u2 := e4.writes
    rw [h, hreg2, hreg2, hr12, hrbx]
  obtain ⟨u5, a5, T5, e5, m5⟩ := T4.regStep
    (mov_r32_imm32_effect_step 0x10094d 0xba (by decide) 0x10)
    (code_at' T4.code _ 0x94d (by decide) _ (by decide) (by decide +kernel))
    e4.rip (ne_boundary hOut (a := 0x100952) (by decide))
    (by simp [movR32Imm32Effect, Effect.components, ctChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  obtain ⟨u6, a6, T6, e6, m6⟩ := T5.regStep
    (sub_r64_r64_effect_step 0x100952 0x4c 0xea (by unfold RexWPrefix; decide) (by decide))
    (code_at' T5.code _ 0x952 (by decide) _ (by decide) (by decide +kernel))
    e5.rip (ne_boundary hOut (a := 0x100955) (by decide))
    (by simp [ctChanges, loopFoot, callFoot, Component.isMem]; decide)
  have hrbp6 : (Operand.reg 13 : Operand 64).read u5 = BitVec.ofNat 64 (ad.size % 16) := by
    rw [e5.agrees.read (by simp [movR32Imm32Effect, Effect.components]; decide),
      e4.agrees.read (by simp; decide), hreg2, hr13]
  have hrdx6 : (Operand.reg 2 : Operand 64).read u6 = BitVec.ofNat 64 (16 - ad.size % 16) := by
    have h : (Operand.reg 2 : Operand 64).read u6 =
        (Operand.reg 2 : Operand 64).read u5 - (Operand.reg 13 : Operand 64).read u5 := e6.writes
    have h5 : (Operand.reg 2 : Operand 64).read u5 = (0x10 : BitVec 32).setWidth 64 := e5.writes
    rw [h, h5, hrbp6]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show ((0x10 : BitVec 32).setWidth 64).toNat = 16 from rfl]
    omega
  obtain ⟨u7, a7, T7, e7, m7⟩ := T6.regStep
    (lea_r64_effect_step 0x100955 0x4a (by unfold RexWPrefix; decide) 7
      (.sib 4 (some 13) 0 .none) ⟨by decide, fun _ => by decide⟩ (by decide) (by decide))
    (code_at' T6.code _ 0x955 (by decide) _ (by decide) (by decide +kernel))
    e6.rip (ne_boundary hOut (a := 0x100959) (by decide))
    (by simp [ctChanges, loopFoot, callFoot, Component.isMem]; decide)
  have hrdi7 : (Operand.reg 7 : Operand 64).read u7 =
      framePointer s + BitVec.ofNat 64 (ad.size % 16) := by
    have h : (Operand.reg 7 : Operand 64).read u7 = (AddrMode.sib 4 (some 13) 0 .none).addr u6
        (0x100955 + BitVec.ofNat 64 (leaLen (.sib 4 (some 13) 0 .none))) := e7.writes
    rw [h]
    simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
    rw [show ((4 : BitVec 4).setWidth 5) = (4 : BitVec 5) from rfl,
      show ((13 : BitVec 4).setWidth 5) = (13 : BitVec 5) from rfl, ← stackPtr_eq_read, T6.rsp,
      e6.agrees.read (by simp; decide), hrbp6]
    simp
  obtain ⟨u8, a8, T8, e8, m8⟩ := T7.regStep
    (add_r64_imm8_effect_step 0x100959 0x48 0xc7 0x18 (by unfold RexWPrefix; decide) (by decide)
      (by decide))
    (code_at' T7.code _ 0x959 (by decide) _ (by decide) (by decide +kernel))
    e7.rip (ne_boundary hOut (a := 0x10095d) (by decide))
    (by simp [ctChanges, loopFoot, callFoot, Component.isMem]; decide)
  have hrdi8 : (Operand.reg 7 : Operand 64).read u8 =
      framePointer s + BitVec.ofNat 64 (0x18 + ad.size % 16) := by
    have h : (Operand.reg 7 : Operand 64).read u8 =
        (Operand.reg 7 : Operand 64).read u7 + (0x18 : BitVec 8).signExtend 64 := e8.writes
    rw [h, hrdi7, show (0x18 : BitVec 8).signExtend 64 = BitVec.ofNat 64 0x18 from rfl,
      add_ofNat_add_ofNat, Nat.add_comm]
  obtain ⟨u9, a9, T9, e9, m9⟩ := T8.regStep
    (xor_r32_r32_effect_step 0x10095d 0xf6 (by decide))
    (code_at' T8.code _ 0x95d (by decide) _ (by decide) (by decide +kernel))
    e8.rip (ne_boundary hOut (a := 0x10095f) (by decide))
    (by simp [ctChanges, loopFoot, callFoot, Component.isMem]; decide)
  have hrsi9 : rsi.read u9 = 0 := by
    have h : (Operand.reg 6 : Operand 64).read u9 =
        ((Operand.reg 6 : Operand 32).read u8 ^^^ (Operand.reg 6 : Operand 32).read u8).setWidth 64 :=
      e9.writes
    rw [show rsi = (Operand.reg 6 : Operand 64) from rfl, h, BitVec.xor_self]
    rfl
  have hrdi9 : rdi.read u9 = framePointer s + BitVec.ofNat 64 (0x18 + ad.size % 16) := by
    rw [show rdi = (Operand.reg 7 : Operand 64) from rfl, e9.agrees.read (by simp; decide), hrdi8]
  have hrdx9 : MemoryRoutines.rdx.read u9 = BitVec.ofNat 64 (16 - ad.size % 16) := by
    rw [show MemoryRoutines.rdx = (Operand.reg 2 : Operand 64) from rfl,
      e9.agrees.read (by simp; decide), e8.agrees.read (by simp; decide),
      e7.agrees.read (by simp; decide), hrdx6]
  have hrdiN : (rdi.read u9).toNat = (framePointer s).toNat + 0x18 + ad.size % 16 := by
    rw [hrdi9, add_toNat _ _ (by omega)]; omega
  have hrdxN : (MemoryRoutines.rdx.read u9).toNat = 16 - ad.size % 16 := by
    rw [hrdx9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hag39 := ((((e4.agrees.trans e5.agrees).trans e6.agrees).trans
    e7.agrees).trans e8.agrees).trans e9.agrees
  have hdf9 : DirectionFlagClear u9.RFLAGS :=
    (hag39.directionFlagClear (by simp [movR32Imm32Effect, addR64R64Effect, subR64R64Effect, leaR64Effect, addR64Imm8Effect, xorR32R32Effect, Effect.components])
      ⟨hdf2⟩).df
  obtain ⟨f10, u10, a10, r10, c10, hrip10, hrsp10, hag10, hcs10, hdf10, hkeep10, hfill10⟩ :=
    memset_call hstride G hOut T9.agrees T9.ready T9.code T9.rsp hdf9 (p := 0x10095f)
      (d := 0x100a7b) e9.rip
      (code_at' T9.code _ 0x95f (by decide) _ (by decide) (by decide +kernel))
      (by decide) (by decide) (by omega)
  have T10 : Track (framePointer s) (ctChanges (framePointer s)) t0 u10 :=
    T9.extend r10 c10 hag10 hrsp10 (fun c hc _ => List.mem_append_left _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hc))) (fun x c hc hx => ⟨c, List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)), hx⟩)
  have hcs9 : ∀ r : BitVec 5, (r = 3 ∨ r = 5 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15) →
      (Operand.reg r : Operand 64).read u10 = (Operand.reg r : Operand 64).read u9 :=
    fun r hr => cs_read hcs10 hr
  have hr12_9 : (Operand.reg 12 : Operand 64).read u9 =
      ptr + BitVec.ofNat 64 (ad.size / 16 * 16) := by
    rw [e9.agrees.read (by simp; decide), e8.agrees.read (by simp; decide),
      e7.agrees.read (by simp; decide), e6.agrees.read (by simp; decide),
      e5.agrees.read (by simp [movR32Imm32Effect, Effect.components]; decide), hr12_4]
  have hrbp9 : (Operand.reg 13 : Operand 64).read u9 = BitVec.ofNat 64 (ad.size % 16) := by
    rw [e9.agrees.read (by simp; decide), e8.agrees.read (by simp; decide),
      e7.agrees.read (by simp; decide), e6.agrees.read (by simp; decide), hrbp6]
  obtain ⟨u11, a11, T11, e11, m11⟩ := T10.regStep
    (lea_r64_effect_step 0x100965 0x48 (by unfold RexWPrefix; decide) 3
      (.sib 4 none 0 (.d8 0x18)) ⟨by decide, fun _ => by decide⟩ (by decide) (by decide))
    (code_at' T10.code _ 0x965 (by decide) _ (by decide) (by decide +kernel))
    hrip10 (ne_boundary hOut (a := 0x10096a) (by decide))
    (by simp [ctChanges, loopFoot, callFoot, Component.isMem]; decide)
  have hr13_11 : (Operand.reg 3 : Operand 64).read u11 = framePointer s + BitVec.ofNat 64 0x18 := by
    have h : (Operand.reg 3 : Operand 64).read u11 = (AddrMode.sib 4 none 0 (.d8 0x18)).addr u10
        (0x100965 + BitVec.ofNat 64 (leaLen (.sib 4 none 0 (.d8 0x18)))) := e11.writes
    rw [h, sib_addr, hrsp10]; rfl
  obtain ⟨u12, a12, T12, e12, m12⟩ := T11.regStep
    (mov_r64_r64_effect_step 0x10096a 0x48 0xdf (by unfold RexWPrefix; decide) (by decide))
    (code_at' T11.code _ 0x96a (by decide) _ (by decide) (by decide +kernel))
    e11.rip (ne_boundary hOut (a := 0x10096d) (by decide))
    (by simp [movR64R64Effect, Effect.components, ctChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  obtain ⟨u13, a13, T13, e13, m13⟩ := T12.regStep
    (mov_r64_r64_effect_step 0x10096d 0x4c 0xe6 (by unfold RexWPrefix; decide) (by decide))
    (code_at' T12.code _ 0x96d (by decide) _ (by decide) (by decide +kernel))
    e12.rip (ne_boundary hOut (a := 0x100970) (by decide))
    (by simp [movR64R64Effect, Effect.components, ctChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  obtain ⟨u14, a14, T14, e14, m14⟩ := T13.regStep
    (mov_r64_r64_effect_step 0x100970 0x4c 0xea (by unfold RexWPrefix; decide) (by decide))
    (code_at' T13.code _ 0x970 (by decide) _ (by decide) (by decide +kernel))
    e13.rip (ne_boundary hOut (a := 0x100973) (by decide))
    (by simp [movR64R64Effect, Effect.components, ctChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  have hrdi14 : rdi.read u14 = framePointer s + BitVec.ofNat 64 0x18 := by
    have h : (Operand.reg 7 : Operand 64).read u12 = (Operand.reg 3 : Operand 64).read u11 :=
      e12.writes
    rw [show rdi = (Operand.reg 7 : Operand 64) from rfl,
      e14.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e13.agrees.read (by simp [movR64R64Effect, Effect.components]; decide), h, hr13_11]
  have hsrc : ptr + BitVec.ofNat 64 (ad.size / 16 * 16) = rsi.read u14 := by
    have h : (Operand.reg 6 : Operand 64).read u13 = (Operand.reg 12 : Operand 64).read u12 :=
      e13.writes
    rw [show rsi = (Operand.reg 6 : Operand 64) from rfl,
      e14.agrees.read (by simp [movR64R64Effect, Effect.components]; decide), h,
      e12.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e11.agrees.read (by simp; decide), hcs9 12 (by decide), hr12_9]
  have hrdx14 : MemoryRoutines.rdx.read u14 = BitVec.ofNat 64 (ad.size % 16) := by
    have h : (Operand.reg 2 : Operand 64).read u14 = (Operand.reg 13 : Operand 64).read u13 :=
      e14.writes
    rw [show MemoryRoutines.rdx = (Operand.reg 2 : Operand 64) from rfl, h,
      e13.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e12.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e11.agrees.read (by simp; decide), hcs9 13 (by decide), hrbp9]
  have hrdxN14 : (MemoryRoutines.rdx.read u14).toNat = ad.size % 16 := by
    rw [hrdx14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsrcN : (ptr + BitVec.ofNat 64 (ad.size / 16 * 16)).toNat = ptr.toNat + ad.size / 16 * 16 :=
    add_toNat _ _ (by omega)
  have hadByte : ∀ i < ad.size, u14.external[ptr + BitVec.ofNat 64 i]? = some ad[i]! := by
    intro i hi
    rw [T14.agrees.byte (fun c hc hcov => hstk i hi ((ctChanges_scratch G c hc _ hcov).inStack G)),
      hmem i hi]
  have hdf14 : DirectionFlagClear u14.RFLAGS :=
    ((((e11.agrees.trans e12.agrees).trans e13.agrees).trans e14.agrees).directionFlagClear
      (by simp [movR64R64Effect, leaR64Effect, Effect.components]) ⟨hdf10⟩).df
  have hrem0 : 0 < ad.size % 16 := Nat.pos_of_ne_zero hz
  obtain ⟨f15, u15, a15, r15, c15, hrip15, hrsp15, hag15, hcs15, hdf15, hkeep15, hcopy15⟩ :=
    memcpy_call hstride G hOut T14.agrees T14.ready T14.code T14.rsp hdf14 (p := 0x100973)
      (d := 0x100a2f) e14.rip
      (code_at' T14.code _ 0x973 (by decide) _ (by decide) (by decide +kernel))
      (by decide) (by decide)
      (by rw [hrdi14, hrdxN14, add_toNat _ _ (by omega)]; omega)
      (by rw [← hsrc, hrdxN14, hsrcN]; omega)
      (by
        intro i hi
        rw [hrdxN14] at hi
        rw [← hsrc, add_ofNat_add_ofNat, hadByte _ (by omega)]; rfl)
      (by
        intro i hi k hk he
        rw [hrdxN14] at hi
        rw [← hsrc, add_ofNat_add_ofNat] at he
        apply hstk _ (by omega : ad.size / 16 * 16 + i < ad.size)
        rw [he]
        unfold InStack
        rw [add_toNat _ _ (by rw [sub_toNat _ _ (by omega)]; omega), sub_toNat _ _ (by omega)]
        omega)
  have T15 : Track (framePointer s) (ctChanges (framePointer s)) t0 u15 :=
    T14.extend r15 c15 hag15 hrsp15 (fun c hc _ => List.mem_append_left _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hc))) (fun x c hc hx => ⟨c, List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)), hx⟩)
  obtain ⟨u16, a16, T16, e16, m16⟩ := T15.regStep
    (mov_r64_r64_effect_step 0x100979 0x4c 0xff (by unfold RexWPrefix; decide) (by decide))
    (code_at' T15.code _ 0x979 (by decide) _ (by decide) (by decide +kernel))
    hrip15 (ne_boundary hOut (a := 0x10097c) (by decide))
    (by simp [movR64R64Effect, Effect.components, ctChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  obtain ⟨u17, a17, T17, e17, m17⟩ := T16.regStep
    (mov_r64_r64_effect_step 0x10097c 0x48 0xde (by unfold RexWPrefix; decide) (by decide))
    (code_at' T16.code _ 0x97c (by decide) _ (by decide) (by decide +kernel))
    e16.rip (ne_boundary hOut (a := 0x10097f) (by decide))
    (by simp [movR64R64Effect, Effect.components, ctChanges, loopFoot, callFoot,
      Component.isMem]; decide)
  have hr15_14 : (Operand.reg 15 : Operand 64).read u14 = polyBase s := by
    rw [e14.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e13.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e12.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e11.agrees.read (by simp; decide), hcs9 15 (by decide),
      hag39.read (by simp [movR32Imm32Effect, addR64R64Effect, subR64R64Effect,
        leaR64Effect, addR64Imm8Effect, xorR32R32Effect, Effect.components] <;> decide), hreg2,
      hr15]
  have hr15_15 : (Operand.reg 15 : Operand 64).read u15 = polyBase s := by
    rw [cs_read hcs15 (by decide), hr15_14]
  have hrdi17 : rdi.read u17 = polyBase s := by
    have h : (Operand.reg 7 : Operand 64).read u16 = (Operand.reg 15 : Operand 64).read u15 :=
      e16.writes
    rw [show rdi = (Operand.reg 7 : Operand 64) from rfl,
      e17.agrees.read (by simp [movR64R64Effect, Effect.components]; decide), h, hr15_15]
  have hr13_15 : (Operand.reg 3 : Operand 64).read u15 = framePointer s + BitVec.ofNat 64 0x18 := by
    rw [cs_read hcs15 (by decide),
      e14.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e13.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e12.agrees.read (by simp [movR64R64Effect, Effect.components]; decide), hr13_11]
  have hrsi17 : rsi.read u17 = framePointer s + BitVec.ofNat 64 0x18 := by
    have h : (Operand.reg 6 : Operand 64).read u17 = (Operand.reg 3 : Operand 64).read u16 :=
      e17.writes
    rw [show rsi = (Operand.reg 6 : Operand 64) from rfl, h,
      e16.agrees.read (by simp [movR64R64Effect, Effect.components]; decide), hr13_15]
  have hmem17 : ∀ x : BitVec 64, u17.external[x]? = u15.external[x]? := fun x => by
    rw [m17, m16]
  have hmem14_10 : ∀ x : BitVec 64, u14.external[x]? = u10.external[x]? := fun x => by
    rw [m14, m13, m12, m11]
  have hmem9_2 : ∀ x : BitVec 64, u9.external[x]? = u2.external[x]? := fun x => by
    rw [m9, m8, m7, m6, m5, m4]
  have hP0 : 96 ≤ (framePointer s).toNat := by omega
  have hP1 : (framePointer s).toNat + 0x200 < 2 ^ 64 := by omega
  have hblk : ∀ i < 16, u17.external[rsi.read u17 + BitVec.ofNat 64 i]? =
      some (tailBlock ad)[i]! := by
    intro i hi
    rw [hrsi17, add_ofNat_add_ofNat, hmem17, tailBlock_byte ad hz i hi]
    split
    · rename_i hir
      have hc := hcopy15 i (by rw [hrdxN14]; exact hir)
      rw [hrdi14, add_ofNat_add_ofNat, ← hsrc, add_ofNat_add_ofNat] at hc
      rw [hc, hadByte _ (by omega)]
    · rename_i hir
      have hx : (framePointer s + BitVec.ofNat 64 (0x18 + i)).toNat =
          (framePointer s).toNat + 0x18 + i := by rw [add_toNat _ _ (by omega)]; omega
      rw [hkeep15 _ (by rw [hx]; omega) (by rw [hx, hrdi14, hrdxN14, add_toNat _ _ (by omega)]; omega),
        hmem14_10]
      have hf := hfill10 (i - ad.size % 16) (by rw [hrdxN]; omega)
      rw [hrdi9, add_ofNat_add_ofNat, hrsi9,
        show 0x18 + ad.size % 16 + (i - ad.size % 16) = 0x18 + i by omega] at hf
      rw [hf]
      rfl
  have hfar17 : ∀ x : BitVec 64, (framePointer s).toNat ≤ x.toNat →
      (x.toNat < (framePointer s).toNat + 0x18 ∨ (framePointer s).toNat + 0x28 ≤ x.toNat) →
      u17.external[x]? = j.external[x]? := by
    intro x h1 h2
    rw [hmem17, hkeep15 _ h1 (by rw [hrdi14, hrdxN14, add_toNat _ _ (by omega)]; omega),
      hmem14_10, hkeep10 _ h1 (by rw [hrdiN, hrdxN]; omega), hmem9_2, m2, m1]
  have hpolyN : (polyBase s).toNat = (framePointer s).toNat + 0x150 := by
    unfold polyBase polyOffset; rw [add_toNat _ _ (by omega)]
  have hpoly17 : PolyState u17 (polyBase s) otk
      (absorbBlocks (clampedR otk) acc (ad.extract 0 (16 * (ad.size / 16)))) :=
    PolyState.of_mem hpoly fun i hi => hfar17 _
      (by rw [add_toNat _ _ (by omega), hpolyN]; omega)
      (by rw [add_toNat _ _ (by omega), hpolyN]; omega)
  have hdf17 : DirectionFlagClear u17.RFLAGS :=
    ((e16.agrees.trans e17.agrees).directionFlagClear
      (by simp [movR64R64Effect, Effect.components]) ⟨hdf15⟩).df
  obtain ⟨f18, v, a18, r18, c18, hrip18, hrsp18, hag18, hcs18, hpoly18⟩ :=
    poly_call (p := 0x10097f) (disp := 0x14ac) G hOut T17.agrees T17.ready T17.code T17.rsp e17.rip
      (code_at' T17.code _ 0x97f (by decide) _ (by decide) (by decide +kernel))
      (by decide) (by decide) hrdi17 (tailBlock_size ad hz)
      (by rw [hrsi17, add_toNat _ _ (by omega)]; omega) hblk
      (rangeApart_of_toNat (by rw [hrsi17, add_toNat _ _ (by omega)]; omega)
        (by rw [sub_toNat _ _ (by omega)]; omega)
        (by rw [hrsi17, add_toNat _ _ (by omega), sub_toNat _ _ (by omega)]; omega))
      hpoly17
  have T18 : Track (framePointer s) (ctChanges (framePointer s)) t0 v :=
    T17.extend r18 c18 hag18 hrsp18 (fun c hc _ => List.mem_append_left _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hc))) (fun x c hc hx => ⟨c, List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)), hx⟩)
  have hreg1714 : (Operand.reg 15 : Operand 64).read u17 = (Operand.reg 15 : Operand 64).read u14 := by
    rw [e17.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      e16.agrees.read (by simp [movR64R64Effect, Effect.components]; decide),
      cs_read hcs15 (by simp)]
  refine ⟨1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + f10 + 1 + 1 + 1 + 1 + f15 + 1 + 1 + f18, v,
    (((((((((((((((a1.trans a2).trans a4).trans a5).trans a6).trans a7).trans a8).trans
      a9).trans a10).trans a11).trans a12).trans a13).trans a14).trans a15).trans a16).trans
      a17).trans a18, T18, by rw [hrip18]; rfl,
    (hag18.directionFlagClear (by simp [callFoot]) ⟨hdf17⟩).df, ?_, ?_, ?_⟩
  · rw [cs_read hcs18 (by decide), hreg1714, hr15_14]
  · intro x hx
    rw [callFoot_keep hag18 hP0 hP1 (by omega), hfar17 _ (by omega) (by omega)]
  · rw [absorb_padded, ite_f hz]
    exact hpoly18

set_option maxHeartbeats 8000000 in
theorem absorb_ciphertext [bindings : Machine.Bindings] {s : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    {inPtr outPtr : BitVec 64} (boundary : ReturnBoundary) {t : RamState}
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hBoundaryOutside : ¬ InProgram boundary.rip)
    (_hBoundaryDifferent : boundary.rip ≠ (returnBoundary s).rip)
    (hCut : Cut3 s t key nonce associatedData plaintext outPtr) :
    ∃ fuel u, Advances boundary fuel t u ∧
      Cut4 s u key nonce associatedData plaintext outPtr := by
  have hInv := hCut.toInv
  have G := geometry_of hPre hInv
  have hP := frame_toNat s G.low
  have hglow := G.low
  have hhigh := G.high
  simp only [frameBytes] at hP
  have hP0 : 96 ≤ (framePointer s).toNat := by omega
  have hP1 : (framePointer s).toNat + 0x200 < 2 ^ 64 := by omega
  have T0 : Track (framePointer s) (ctChanges (framePointer s)) t t :=
    Track.refl (ready_of hInv) hInv.code hInv.rsp
  have hrv := regValue_read t
  have hct := hCut.ciphertext
  have hlen : (ciphertext key nonce plaintext).size = plaintext.size := hct.1
  obtain ⟨hob, -⟩ := hPre.outputInMemory
  simp only [MemoryRegion.Bounded, userAddressLimit, messageRegion] at hob
  have hmem : ∀ i < (ciphertext key nonce plaintext).size,
      t.external[outPtr + BitVec.ofNat 64 i]? = some (ciphertext key nonce plaintext)[i]! := by
    intro i hi
    rw [← ofNat_toNat_add, getElem!_pos _ i hi]
    exact hct.2 ⟨i, hi⟩
  have hstk : ∀ i < (ciphertext key nonce plaintext).size,
      ¬ InStack s (outPtr + BitVec.ofNat 64 i) := by
    intro i hi hin
    rw [← ofNat_toNat_add] at hin
    have hn : (BitVec.ofNat 64 (outPtr.toNat + i)).toNat = outPtr.toNat + i := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hsep := hPre.separation.1
    simp only [coreWritten, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hsep
    apply hsep.2.1 (outPtr.toNat + i)
    · simp only [messageRegion, MemoryRegion.Contains]; omega
    · unfold InStack at hin
      rw [hn] at hin
      simp only [Stack.region, MemoryRegion.Contains, Stack.returnAddressBytes, coreStackBytes]
      have hsp : s.regValue .rsp = stackPtr s := rfl
      rw [hsp]
      omega
  have hfar : ∀ c ∈ ctChanges (framePointer s), ∀ i < (ciphertext key nonce plaintext).size,
      ¬ c.Covers (outPtr + BitVec.ofNat 64 i) :=
    fun c hc i hi hcov => hstk i hi ((ctChanges_scratch G c hc _ hcov).inStack G)
  obtain ⟨f1, j, a1, T1, hrip1, hr15j, hr12j, hrbxj, hr13j, hmemj, hpolyj⟩ :=
    ct_head G hBoundaryOutside T0 hCut.rip (by omega) hmem hfar
      (by rw [← hrv.2.2.2.2.2.2.2.2.1]; exact hCut.r12)
      (by rw [← hrv.2.2.2.2.2.2.2.2.2.2.1, hlen]; exact hCut.r14)
      (by rw [← hrv.2.2.2.2.2.2.1]; exact hCut.rbx)
      (by rw [← hrv.2.2.2.2.2.2.2.2.2.2.2.1]; exact hCut.r15) hCut.poly
  have hdfj : DirectionFlagClear j.RFLAGS :=
    (T1.agrees.directionFlagClear (by simp [ctChanges, loopFoot, callFoot])
      hInv.directionFlagUnset).df
  obtain ⟨f2, u, a2, T2, hrip2, -, hr15u, hslotsU, hpolyU⟩ :=
    ct_tail hInv.environment.stringStride G hBoundaryOutside T1 hdfj hrip1 (by omega) hmem hstk
      hr13j hrbxj hr12j hr15j hpolyj
  have hscr := ctChanges_scratch G
  have hdfc : Component.df ∉ ctChanges (framePointer s) := by simp [ctChanges, loopFoot, callFoot]
  have hfb : frameBase s = (framePointer s).toNat := by unfold frameBase; rw [hP]; rfl
  have hslotKeep : ∀ k, (0x10 ≤ k ∧ k + 8 ≤ 0x18) ∨ (0x98 ≤ k ∧ k + 8 ≤ 0xb0) → ∀ i < 8,
      u.external[BitVec.ofNat 64 (slot s k).start + BitVec.ofNat 64 i]? =
        t.external[BitVec.ofNat 64 (slot s k).start + BitVec.ofNat 64 i]? := by
    intro k hk i hi
    have hx : (BitVec.ofNat 64 (slot s k).start + BitVec.ofNat 64 i).toNat =
        (framePointer s).toNat + k + i := by
      simp only [slot]
      rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hfb]
    rw [hslotsU _ (by rw [hx]; omega), hmemj _ (by rw [hx]; omega) (by rw [hx]; omega)]
  refine ⟨f1 + f2, u, a1.trans a2, ?_⟩
  exact {
    toInv := inv_of_track hPre hInv G T2 hscr hdfc
    rip := hrip2
    r15 := by rw [← (regValue_read u).2.2.2.2.2.2.2.2.2.2.2.1] at hr15u; exact hr15u
    lengthSlot := word64At_keep hCut.lengthSlot (hslotKeep 0x10 (by omega))
    adLengthSlot := word64At_keep hCut.adLengthSlot (hslotKeep 0x98 (by omega))
    resultSlot := word64At_keep hCut.resultSlot (hslotKeep 0xa0 (by omega))
    ciphertext := hasBytes_keep hct fun i hi => T2.keep hscr fun hsc => by
      apply hstk i (by rw [hlen]; exact hi)
      rw [← ofNat_toNat_add]
      exact hsc.inStack G
    poly := hpolyU }

end ChaCha20Poly1305.Proofs.Core.Absorb
