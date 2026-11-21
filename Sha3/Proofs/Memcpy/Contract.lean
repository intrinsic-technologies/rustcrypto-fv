import Sha3.Proofs.Memcpy.Movs.Execution
import Sha3.Proofs.Movs
import Sha3.Proofs.Stores.Frame
import X86Proofs.Instructions.Call.Triple
import Sha3.Proofs.Memcpy.Basic

namespace Sha3.Proofs.Memcpy

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def memcpy200Steps (dst : BitVec 64) : Nat :=
  if dst.toNat % 8 = 0 then 40 else 45

theorem memcpy200Steps_le (dst : BitVec 64) : memcpy200Steps dst ≤ 45 := by
  unfold memcpy200Steps
  split <;> omega

theorem memcpy200Steps_eq (dst : BitVec 64) :
    memcpy200Steps dst =
      13 + max ((8 - dst.toNat % 8) % 8) 1 +
        max ((200 - (8 - dst.toNat % 8) % 8) / 8) 1 +
        max ((200 - (8 - dst.toNat % 8) % 8) % 8) 1 := by
  unfold memcpy200Steps
  split <;> omega

def clobbers (dst : BitVec 64) (len : Nat := 208) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .flags, .rip, .mem dst len]

theorem clobbers_writesWithin {dst : BitVec 64} {len : Nat} {regions : Vector MemoryRegion n}
    (h : ∀ i < len, ∃ region ∈ regions,
      region.Contains (dst + BitVec.ofNat 64 i).toNat) : WritesWithin (clobbers dst len) regions := by
  intro c hc x hcover
  simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    try exact hcover.elim
  obtain ⟨i, hi, rfl⟩ := hcover
  exact h i hi

structure Pre (boundary : ReturnBoundary) (s : RamState)
    (len : Nat := 208) (requireAligned : Bool := true) : Prop where
  rip : s.RIP = 0x106a70
  length : (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 len
  aligned : if requireAligned then ((Operand.reg 7 : Operand 64).read s).toNat % 8 = 0 else True
  direction : DirectionFlagUnset s
  source : MemReadable s ((Operand.reg 6 : Operand 64).read s) len
  destination : MemReadable s ((Operand.reg 7 : Operand 64).read s) len
  separate : ((Operand.reg 6 : Operand 64).read s).toNat + len ≤
      ((Operand.reg 7 : Operand 64).read s).toNat ∨
    ((Operand.reg 7 : Operand 64).read s).toNat + len ≤
      ((Operand.reg 6 : Operand 64).read s).toNat
  tables : (MemoryRegion.mk ((Operand.reg 7 : Operand 64).read s).toNat len).Avoids InPageTables
  program : (MemoryRegion.mk ((Operand.reg 7 : Operand 64).read s).toNat len).Avoids InProgram
  stack : MemReadable s (stackPtr s) 8
  returnLow : (stackTop s).toNat < 2^32
  disjoint : RangeApart ((Operand.reg 7 : Operand 64).read s) len (stackPtr s) 8
  inside : stackPtr s ≠ boundary.rsp
  afterReturn : stackTop s ≠ boundary.rip ∨ stackPtr s + 8 ≠ boundary.rsp

structure Done [Bindings] (s t : RamState) (len : Nat := 208) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = stackTop s
  rsp : stackPtr t = stackPtr s + 8
  result : (Operand.reg 0 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s
  copy : ∀ i < len,
    t.external[(Operand.reg 7 : Operand 64).read s + BitVec.ofNat 64 i]? =
      s.external[(Operand.reg 6 : Operand 64).read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept (clobbers ((Operand.reg 7 : Operand 64).read s) len) s t

theorem memcpyPointer_bytes {s : RamState} (loaded : ProgramLoaded s) :
    ∀ i : Fin 8, s.external[(0x200180 : BitVec 64) + BitVec.ofNat 64 i.val]? =
      some (storedByte (0x106a70 : BitVec 64) i.val) := by
  intro i
  exact programLoaded_fetchByte loaded
    ((by decide +kernel : ∀ i : Fin 8,
      Extracted.programSections.fetchByte ((0x200180 : BitVec 64) + BitVec.ofNat 64 i.val) =
        some (storedByte (0x106a70 : BitVec 64) i.val)) i)

theorem memcpyPointer_read {s : RamState} (loaded : ProgramLoaded s) :
    (Operand.mem 0x200180 : Operand 64).read s = 0x106a70 := by
  apply Bytes.memLoad (hn := by decide) (h128 := by decide)
  intro i hi
  exact memcpyPointer_bytes loaded ⟨i, hi⟩

theorem memcpyPointer_readable {s : RamState} (loaded : ProgramLoaded s) :
    MemReadable s 0x200180 8 := by
  refine ⟨by decide, ?_⟩
  intro i hi
  rw [memcpyPointer_bytes loaded ⟨i, hi⟩]
  rfl

theorem range_contains {dst : BitVec 64} {len i : Nat}
    (hlow : dst.toNat + len ≤ 2^32) (hi : i < len) :
    (MemoryRegion.mk dst.toNat len).Contains (dst + BitVec.ofNat 64 i).toNat := by
  rw [Stos.toNat_add_ofNat _ _ (by omega)]
  change dst.toNat ≤ dst.toNat + i ∧ dst.toNat + i < dst.toNat + len
  exact ⟨by omega, by omega⟩

theorem clobbers_code {s t : RamState} {dst : BitVec 64} {len : Nat}
    (h : AgreesExcept (clobbers dst len) s t) (hlow : dst.toNat + len ≤ 2^32)
    (ha : (MemoryRegion.mk dst.toNat len).Avoids InProgram)
    (hc : CodeIn Extracted.programImage s) : CodeIn Extracted.programImage t := by
  apply CodeIn.of_agreesExcept h ?_ hc
  intro x hx c hc hcover
  simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    try exact hcover
  obtain ⟨i, hi, he⟩ := hcover
  exact ha x.1 (he ▸ range_contains hlow hi) ⟨x.2, hx⟩

theorem agrees_clobbers_trans {s t u : RamState} {dst : BitVec 64} {len : Nat}
    (h : AgreesExcept (clobbers dst len) s t) (h' : AgreesExcept (clobbers dst len) t u) :
    AgreesExcept (clobbers dst len) s u :=
  (h.trans h').mono fun _ hc => (List.mem_append.mp hc).elim id id

theorem clobbers_subrange {s t : RamState} {dst : BitVec 64} {off count total : Nat}
    (h : AgreesExcept (clobbers (dst + BitVec.ofNat 64 off) count) s t)
    (hb : off + count ≤ total) : AgreesExcept (clobbers dst total) s t := by
  apply h.widen
  · intro c hc hm
    simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [clobbers, Component.isMem]
  · intro x c hc hcover
    simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      try exact hcover.elim
    obtain ⟨i, hi, he⟩ := hcover
    refine ⟨.mem dst total, by simp [clobbers], off + i, by omega, ?_⟩
    rw [he, add_ofNat_add_ofNat]

theorem clobbers_source {s t : RamState} {src dst : BitVec 64} {len : Nat}
    (h : AgreesExcept (clobbers dst len) s t)
    (hsrc : src.toNat + len ≤ 2^32) (hdst : dst.toNat + len ≤ 2^32)
    (hsep : src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat)
    (i : Nat) (hi : i < len) :
    t.external[src + BitVec.ofNat 64 i]? = s.external[src + BitVec.ofNat 64 i]? := by
  apply h.byte
  intro c hc hcov
  simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    try exact hcov.elim
  obtain ⟨j, hj, he⟩ := hcov
  have hn := congrArg BitVec.toNat he
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
  omega

theorem copy_extend {s t u : RamState} {src dst : BitVec 64} {off count total : Nat}
    (hsrc : src.toNat + total ≤ 2^32) (hdst : dst.toNat + total ≤ 2^32)
    (hsep : src.toNat + total ≤ dst.toNat ∨ dst.toNat + total ≤ src.toNat)
    (hbound : off + count ≤ total)
    (hst : AgreesExcept (clobbers dst total) s t)
    (htu : AgreesExcept (clobbers (dst + BitVec.ofNat 64 off) count) t u)
    (hbefore : ∀ i < off, t.external[dst + BitVec.ofNat 64 i]? =
      s.external[src + BitVec.ofNat 64 i]?)
    (hnew : ∀ i < count, u.external[dst + BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
      t.external[src + BitVec.ofNat 64 off + BitVec.ofNat 64 i]?) :
    ∀ i < off + count, u.external[dst + BitVec.ofNat 64 i]? =
      s.external[src + BitVec.ofNat 64 i]? := by
  intro i hi
  by_cases hp : i < off
  · rw [htu.byte, hbefore i hp]
    intro c hc hcov
    simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      try exact hcov.elim
    obtain ⟨j, hj, he⟩ := hcov
    rw [add_ofNat_add_ofNat] at he
    have hn := congrArg BitVec.toNat he
    rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
    omega
  · have hn := hnew (i - off) (by omega)
    rw [add_ofNat_add_ofNat, add_ofNat_add_ofNat,
      Nat.add_sub_of_le (by omega : off ≤ i)] at hn
    exact hn.trans (clobbers_source hst hsrc hdst hsep i (by omega))

theorem avoids_subrange {dst : BitVec 64} {off count total : Nat}
    {forbidden : BitVec 64 → Prop} (hlow : dst.toNat + total ≤ 2^32)
    (hbound : off + count ≤ total)
    (h : (MemoryRegion.mk dst.toNat total).Avoids forbidden) :
    (MemoryRegion.mk (dst + BitVec.ofNat 64 off).toNat count).Avoids forbidden := by
  intro x hx
  apply h x
  rw [toNat_add_ofNat _ _ (by omega)] at hx
  change dst.toNat + off ≤ x.toNat ∧ x.toNat < dst.toNat + off + count at hx
  change dst.toNat ≤ x.toNat ∧ x.toNat < dst.toNat + total
  omega

theorem Pre.movsPre {byte : Bool} {boundary : ReturnBoundary} {s t : RamState}
    {len off : Nat} {aligned : Bool} {p : BitVec 64} {rex : UInt8}
    (h : Pre boundary s len aligned)
    (hf : AgreesExcept (clobbers (rdi.read s) len) s t)
    (hip : t.RIP = p)
    (hsrc : rsi.read t = rsi.read s + BitVec.ofNat 64 off)
    (hdst : rdi.read t = rdi.read s + BitVec.ofNat 64 off)
    (hb : off + movsBytes byte * (rcx.read t).toNat ≤ len)
    (ha : (rdi.read t).toNat % movsBytes byte = 0)
    (hmem : (p, movsCode byte rex) ∈ instructionBytes) :
    RepMovsPre byte p t := by
  have hsl : (rsi.read s).toNat + len ≤ 2^32 := h.source.low
  have hdl : (rdi.read s).toNat + len ≤ 2^32 := h.destination.low
  have hsep : (rsi.read s).toNat + len ≤ (rdi.read s).toNat ∨
      (rdi.read s).toNat + len ≤ (rsi.read s).toNat := h.separate
  have hs := readable_slice (MemReadable.of_agreesExcept hf h.source) off
    (movsBytes byte * (rcx.read t).toNat) hb
  have hd := readable_slice (MemReadable.of_agreesExcept hf h.destination) off
    (movsBytes byte * (rcx.read t).toNat) hb
  rw [← hsrc] at hs
  rw [← hdst] at hd
  refine ⟨hip, (hf.directionFlagClear h.direction (by simp [clobbers])).df, hs.low, hd.low, ha, hs.mem, hd.mem, ?_, ?_, ?_⟩
  · rw [hsrc, hdst, toNat_add_ofNat _ _ (by omega),
      toNat_add_ofNat _ _ (by omega)]
    omega
  · rw [hdst]
    exact avoids_subrange h.destination.low hb h.tables
  · intro i hi j hj he
    apply h.program (rdi.read t + BitVec.ofNat 64 i)
    · rw [hdst, add_ofNat_add_ofNat]
      exact range_contains h.destination.low (by omega)
    · rw [he]
      refine ⟨(movsCode byte rex)[j]'(?_), instruction_subset hmem _
        (mem_codeRange p (movsCode byte rex) j ?_)⟩ <;>
        cases byte <;> simpa [movsCode, movsLength] using hj

theorem scalar_step [Bindings] {s : RamState} {pre : RamState → Prop} {e : RamState → Effect}
    {p : BitVec 64} {bs : List UInt8} (boundary : ReturnBoundary)
    (hstep : StepEffect pre (codeRange p bs) e)
    (hmem : (p, bs) ∈ instructionBytes) (hready : ReadyToStep s)
    (hcode : CodeIn Extracted.programImage s) (hp : pre s)
    (hsp : stackPtr s ≠ boundary.rsp)
    (hkeep : Component.reg 4 ∉ (e s).components)
    (hnoMem : ∀ c ∈ (e s).components, ∀ x, ¬ c.Covers x) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (e s).Holds s t := by
  obtain ⟨t, hs, hr, hh⟩ := hstep s hready (instruction_codeIn hcode hmem) hp
  refine ⟨t, Advances.of_step hs (.inr ?_), hr, hh.agrees.codeIn hnoMem hcode, hh⟩
  have he := hh.agrees.read (n := 64) (r := 4) hkeep
  exact (show t.GPR[4] = s.GPR[4] from he) ▸ hsp

theorem clobbers_stackTop {s t : RamState} {dst : BitVec 64} {len : Nat}
    (h : AgreesExcept (clobbers dst len) s t) (hsp : stackPtr t = stackPtr s)
    (hd : RangeApart dst len (stackPtr s) 8) : stackTop t = stackTop s := by
  unfold stackTop
  change memLoad t.external (stackPtr t) 64 = memLoad s.external (stackPtr s) 64
  rw [hsp]
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr s + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[stackPtr s + BitVec.ofNat 64 i]?).getD 0
  rw [h.byte]
  intro c hc hcov
  simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    try exact hcov
  obtain ⟨j, hj, he⟩ := hcov
  exact hd j hj i hi he.symm

theorem zero_steps [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hi : s.RIP = p) (hz : rcx.read s = 0) (hsp : stackPtr s ≠ boundary.rsp)
    (hmem : (p, [0xf3, 0xa4]) ∈ instructionBytes) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = p + (2 : BitVec 64) ∧ AgreesExcept [.rip] s t := by
  obtain ⟨t, ha, ht, hct, he⟩ := scalar_step boundary (Movs.rep_movsb_zero_effect_step p)
    hmem hr hc ⟨hi, hz⟩ hsp (by simp [Effect.components])
    (by simp [Effect.components, Component.Covers])
  exact ⟨t, ha, ht, hct, he.rip, he.agrees⟩

theorem movs_steps [inst : Bindings] (hstride : UnitStringStride inst)
    (boundary : ReturnBoundary) {byte : Bool} (p : BitVec 64) (rex : UInt8)
    (hrex : byte = false → RexWPrefix rex.toBitVec)
    (hmem : (p, movsCode byte rex) ∈ instructionBytes) (s : RamState) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hp : RepMovsPre byte p s)
    (hsp : stackPtr s ≠ boundary.rsp)
    (hprogram : (MemoryRegion.mk (rdi.read s).toNat (movsBytes byte * (rcx.read s).toNat)).Avoids InProgram) :
    ∃ t, Advances boundary (max (rcx.read s).toNat 1) s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (repMovsEffect byte p s).Holds s t ∧
      (∀ i < (movsBytes byte * (rcx.read s).toNat), t.external[rdi.read s + BitVec.ofNat 64 i]? =
        s.external[rsi.read s + BitVec.ofNat 64 i]?) ∧
      AgreesExcept (clobbers (rdi.read s) (movsBytes byte * (rcx.read s).toNat)) s t := by
  have hi : CodeIn (codeRange p (movsCode byte rex)) s :=
    instruction_codeIn hc hmem
  have hd := rep_movs_steps hstride p rex hrex s hr hi hp
  have ha := rep_movs_advances hstride boundary p rex hrex s hr hi hp hsp
  have hcopy := rep_movs_copy hstride p rex hrex s hr hi hp
  dsimp only at hd
  have hf : AgreesExcept (clobbers (rdi.read s) (movsBytes byte * (rcx.read s).toNat)) s (nextStates (max (rcx.read s).toNat 1) s) := by
    apply hd.2.2.agrees.mono
    rw [repMovsEffect_components]
    intro c h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [clobbers]
  refine ⟨_, ha, hd.1, clobbers_code hf ?_ hprogram hc, hd.2.2, hcopy, hf⟩
  exact hp.dstLow

theorem quad_steps_count [inst : Bindings] (hstride : UnitStringStride inst)
    (boundary : ReturnBoundary) (s : RamState) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hp : RepMovsPre false 0x106a93 s)
    (hsp : stackPtr s ≠ boundary.rsp)
    (hprogram : (MemoryRegion.mk (rdi.read s).toNat (8 * (rcx.read s).toNat)).Avoids InProgram) :
    ∃ t, Advances boundary (max (rcx.read s).toNat 1) s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (repMovsEffect false 0x106a93 s).Holds s t ∧
      (∀ i < (8 * (rcx.read s).toNat), t.external[rdi.read s + BitVec.ofNat 64 i]? =
        s.external[rsi.read s + BitVec.ofNat 64 i]?) ∧
      AgreesExcept (clobbers (rdi.read s) (8 * (rcx.read s).toNat)) s t := by
  exact movs_steps hstride boundary (byte := false) 0x106a93 0x48
    (by intro _; simp [RexWPrefix]) (by decide +kernel) s hr hc hp hsp hprogram

theorem quad_steps [inst : Bindings] (hstride : UnitStringStride inst)
    (boundary : ReturnBoundary) (s : RamState) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hp : RepMovsPre false 0x106a93 s)
    (hn : rcx.read s = 26) (hsp : stackPtr s ≠ boundary.rsp)
    (hprogram : (MemoryRegion.mk (rdi.read s).toNat 208).Avoids InProgram) :
    ∃ t, Advances boundary 26 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (repMovsEffect false 0x106a93 s).Holds s t ∧
      (∀ i < 208, t.external[rdi.read s + BitVec.ofNat 64 i]? =
        s.external[rsi.read s + BitVec.ofNat 64 i]?) ∧
      AgreesExcept (clobbers (rdi.read s)) s t := by
  have h := quad_steps_count hstride boundary s hr hc hp hsp (by
    simpa [hn] using hprogram)
  simpa [hn] using h

theorem Done.source [Bindings] {s t : RamState} {len : Nat} (h : Done s t len)
    (hr : MemReadable s ((Operand.reg 6 : Operand 64).read s) len)
    (hd : MemReadable s ((Operand.reg 7 : Operand 64).read s) len)
    (hsep : ((Operand.reg 6 : Operand 64).read s).toNat + len ≤
        ((Operand.reg 7 : Operand 64).read s).toNat ∨
      ((Operand.reg 7 : Operand 64).read s).toNat + len ≤
        ((Operand.reg 6 : Operand 64).read s).toNat)
    (i : Nat) (hi : i < len) :
    t.external[(Operand.reg 6 : Operand 64).read s + BitVec.ofNat 64 i]? =
      s.external[(Operand.reg 6 : Operand 64).read s + BitVec.ofNat 64 i]? :=
  clobbers_source h.agrees hr.low hd.low hsep i hi

end Sha3.Proofs.Memcpy
