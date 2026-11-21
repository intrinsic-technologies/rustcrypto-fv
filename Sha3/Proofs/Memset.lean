import Sha3.Proofs.Stos
import Sha3.Proofs.Stores.Frame
import X86Proofs.Instructions.Call.Triple
import Sha3.Proofs.Memset.Prefix

namespace Sha3.Proofs.Memset

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def clobbers (dst : BitVec 64) (len : Nat := 201) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .flags, .rip, .mem dst len]

theorem clobbers_writesWithin {len : Nat} {dst : BitVec 64} {regions : Vector MemoryRegion n}
    (h : ∀ i < len, ∃ region ∈ regions,
      region.Contains (dst + BitVec.ofNat 64 i).toNat) : WritesWithin (clobbers dst len) regions := by
  intro c hc x hcover
  simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    try exact hcover.elim
  obtain ⟨i, hi, rfl⟩ := hcover
  exact h i hi

structure Pre (boundary : ReturnBoundary) (s : RamState) (len : Nat := 201) : Prop where
  rip : s.RIP = 0x106a20
  length : (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 len
  value : (Operand.reg 6 : Operand 64).read s = 0
  aligned : ((Operand.reg 7 : Operand 64).read s).toNat % 8 = 0
  direction : DirectionFlagUnset s
  destination : MemReadable s ((Operand.reg 7 : Operand 64).read s) len
  tables : (MemoryRegion.mk ((Operand.reg 7 : Operand 64).read s).toNat len).Avoids InPageTables
  program : (MemoryRegion.mk ((Operand.reg 7 : Operand 64).read s).toNat len).Avoids InProgram
  stack : MemReadable s (stackPtr s) 8
  returnLow : (stackTop s).toNat < 2^32
  disjoint : RangeApart ((Operand.reg 7 : Operand 64).read s) len (stackPtr s) 8
  inside : stackPtr s ≠ boundary.rsp
  afterReturn : stackTop s ≠ boundary.rip ∨ stackPtr s + 8 ≠ boundary.rsp

structure Done [Bindings] (s t : RamState) (len : Nat := 201) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = stackTop s
  rsp : stackPtr t = stackPtr s + 8
  result : (Operand.reg 0 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s
  zero : ∀ i < len, t.external[(Operand.reg 7 : Operand 64).read s + BitVec.ofNat 64 i]? = some 0
  agrees : AgreesExcept (clobbers ((Operand.reg 7 : Operand 64).read s) len) s t

theorem range_contains {dst : BitVec 64} {len i : Nat}
    (hlow : dst.toNat + len ≤ 2^32) (hi : i < len) :
    (MemoryRegion.mk dst.toNat len).Contains (dst + BitVec.ofNat 64 i).toNat := by
  rw [Stos.toNat_add_ofNat _ _ (by omega)]
  change dst.toNat ≤ dst.toNat + i ∧ dst.toNat + i < dst.toNat + len
  exact ⟨by omega, by omega⟩

theorem clobbers_code {len : Nat} {s t : RamState} {dst : BitVec 64}
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

theorem agrees_clobbers_trans {len : Nat} {s t u : RamState} {dst : BitVec 64}
    (h : AgreesExcept (clobbers dst len) s t) (h' : AgreesExcept (clobbers dst len) t u) :
    AgreesExcept (clobbers dst len) s u :=
  (h.trans h').mono fun _ hc => (List.mem_append.mp hc).elim id id

theorem stos_ready {len : Nat} [Bindings] (kind : Stos.Kind) (count offset : Nat)
    {s : RamState} {dst : BitVec 64}
    (h : ReadyToStep s) (hdf : DirectionFlagUnset s)
    (hinst : CodeIn (codeRange s.RIP kind.code) s)
    (hsub : ∀ b ∈ codeRange s.RIP kind.code, b ∈ Extracted.programImage)
    (hc : Stos.rcx.read s = BitVec.ofNat 64 count)
    (hptr : Stos.rdi.read s = dst + BitVec.ofNat 64 offset)
    (hlen : offset + kind.bytes * count ≤ len) (hcount : count < 2^64)
    (hr : MemReadable s dst len)
    (ht : (MemoryRegion.mk dst.toNat len).Avoids InPageTables)
    (hp : (MemoryRegion.mk dst.toNat len).Avoids InProgram) :
    Stos.ReadyLoop kind s count := by
  have hl := hr.low
  have hd : (Stos.rdi.read s).toNat = dst.toNat + offset := by
    rw [hptr, Stos.toNat_add_ofNat _ _ (by omega)]
  refine ⟨h.midRep, hdf.df, hinst.bytesAt, ?_, hc, hcount, ?_, ?_, ?_, ?_⟩
  · exact hinst.low (by cases kind <;> decide) (by cases kind <;> decide)
  · rw [hd]; omega
  · intro i hi
    rw [hptr, Stos.add_ofNat_add_ofNat]
    exact hr.mem (offset + i) (by omega)
  · intro x hx
    apply ht x
    change dst.toNat ≤ x.toNat ∧ x.toNat < dst.toNat + len
    change (Stos.rdi.read s).toNat ≤ x.toNat ∧
      x.toNat < (Stos.rdi.read s).toNat + kind.bytes * count at hx
    rw [hd] at hx
    constructor <;> omega
  · intro i hi j hj he
    apply hp (dst + BitVec.ofNat 64 (offset + i)) (range_contains hl (by omega))
    rw [← Stos.add_ofNat_add_ofNat, ← hptr, he]
    exact ⟨kind.code[j], hsub _ (mem_codeRange s.RIP kind.code j hj)⟩

theorem stos_agrees {len : Nat} [Bindings] {kind : Stos.Kind} {count offset : Nat}
    {s t : RamState} {dst : BitVec 64} (hready : ReadyToStep s)
    (h : Stos.Done kind s t count)
    (hptr : Stos.rdi.read s = dst + BitVec.ofNat 64 offset)
    (hlen : offset + kind.bytes * count ≤ len) : AgreesExcept (clobbers dst len) s t := by
  have hag := h.agrees
  rw [Stos.clearRep_eq hready.ready.repeatClear] at hag
  apply hag.widen
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> simp_all [clobbers, Component.isMem]
  · intro x c hc hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> try exact hcover.elim
    obtain ⟨i, hi, he⟩ := hcover
    refine ⟨.mem dst len, by simp [clobbers], offset + i, by omega, ?_⟩
    rw [he, hptr, Stos.add_ofNat_add_ofNat]

theorem stos_read [Bindings] {kind : Stos.Kind} {count : Nat} {s t : RamState}
    (h : Stos.Done kind s t count) (r : BitVec 5) (h1 : r ≠ 1) (h7 : r ≠ 7) :
    (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read s := by
  apply h.agrees.read
  simpa only [List.mem_cons, List.not_mem_nil, Component.reg.injEq, reduceCtorEq,
    or_false, not_or] using And.intro h1 h7

theorem stos_rax8 {s : RamState} (h : (Operand.reg 0 : Operand 64).read s = 0) :
    (Operand.reg 0 : Operand 8).read s = 0 := by
  change s.GPR[0] = 0 at h
  change s.GPR[0].setWidth 8 = 0
  rw [h]
  rfl

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

theorem clobbers_stackTop {len : Nat} {s t : RamState} {dst : BitVec 64}
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

theorem rep_steps {len : Nat} [inst : Bindings] (hstride : UnitStringStride inst)
    (boundary : ReturnBoundary) {kind : Stos.Kind} {count offset : Nat}
    {s : RamState} {dst : BitVec 64} (hready : ReadyToStep s)
    (hcode : CodeIn Extracted.programImage s) (h : Stos.ReadyLoop kind s count)
    (hz : (Operand.reg 0 : Operand kind.bits).read s = 0)
    (hsp : stackPtr s ≠ boundary.rsp)
    (hptr : Stos.rdi.read s = dst + BitVec.ofNat 64 offset)
    (hlen : offset + kind.bytes * count ≤ len) (hlow : dst.toNat + len ≤ 2^32)
    (ha : (MemoryRegion.mk dst.toNat len).Avoids InProgram) :
    ∃ t, Advances boundary (max count 1) s t ∧ Stos.Done kind s t count ∧
      CodeIn Extracted.programImage t ∧ AgreesExcept (clobbers dst len) s t := by
  obtain ⟨t, hs, hd⟩ := Stos.rep_stos_steps hstride kind count s h hz boundary hsp
  have hf := stos_agrees hready hd hptr hlen
  exact ⟨t, hs, hd, clobbers_code hf hlow ha hcode, hf⟩

theorem tail_steps_general {tail : Nat} [inst : Bindings] (hstride : UnitStringStride inst)
    (htail : tail ≤ 1) (boundary : ReturnBoundary) (s a : RamState) (ha : ReadyToStep a)
    (hca : CodeIn Extracted.programImage a) (hp : Pre boundary s (200 + tail))
    (hprefix : PrefixPost s a tail) : ∃ t, Advances boundary 31 a t ∧ Done s t (200 + tail) := by
  let dst := (Operand.reg 7 : Operand 64).read s
  have hlow : dst.toNat + (200 + tail) ≤ 2^32 := hp.destination.low
  have aptr : Stos.rdi.read a = dst + BitVec.ofNat 64 0 := by
    rw [BitVec.add_zero]
    exact hprefix.agrees.read (n := 64) (r := 7) (by decide)
  have asp : stackPtr a = stackPtr s := hprefix.agrees.read (n := 64) (r := 4) (by decide)
  have aframe : AgreesExcept (clobbers dst (200 + tail)) s a := hprefix.agrees.mono (by
    intro c hc
    simp only [scalarClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [clobbers])
  have ar := stos_ready .byte 0 0 ha (aframe.directionFlagClear hp.direction (by simp [clobbers]))
    (by rw [hprefix.rip]; exact instruction_codeIn hca (by decide))
    (by rw [hprefix.rip]; exact instruction_subset (by decide))
    hprefix.rcx aptr (by omega) (by decide)
    (MemReadable.of_agreesExcept aframe hp.destination) hp.tables hp.program
  obtain ⟨b, hab, hb, hcb, hfb⟩ := rep_steps hstride boundary ha hca ar
    (stos_rax8 hprefix.rax) (asp ▸ hp.inside) aptr (by omega) hlow hp.program
  have bframe := agrees_clobbers_trans aframe hfb
  have bptr : Stos.rdi.read b = dst := by
    rw [hb.destination, aptr]
    simp only [Nat.mul_zero, BitVec.add_zero]
  have bsp : stackPtr b = stackPtr s := hb.rsp.trans asp
  have bip : b.RIP = 0x106a56 := by rw [hb.rip, hprefix.rip]; rfl
  obtain ⟨c, hbc, hc, hcc, hec⟩ := scalar_step boundary
    (show StepEffect (fun t => t.RIP = 0x106a56)
      (codeRange 0x106a56 [0x48, 0x89, 0xF1]) (movR64R64Effect 0x106a56 1 6) from
      mov_r64_r64_effect_step 0x106a56 0x48 0xF1 (by simp [RexWPrefix]) (by decide))
    (by decide) hb.ready hcb bip (bsp ▸ hp.inside) (by simp only [movR64R64Effect_components]; decide)
    (by
      intro c hc x
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact id)
  have cf := hec.agrees.mono (cs' := clobbers dst (200 + tail)) (by
    intro c hc
    simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [clobbers])
  have cframe := agrees_clobbers_trans bframe cf
  have cptr : Stos.rdi.read c = dst + BitVec.ofNat 64 0 := by
    rw [BitVec.add_zero]
    exact (hec.agrees.read (n := 64) (r := 7) (by simp only [movR64R64Effect_components]; decide)).trans bptr
  have csp : stackPtr c = stackPtr s :=
    (hec.agrees.read (n := 64) (r := 4) (by simp only [movR64R64Effect_components]; decide)).trans bsp
  have cip : c.RIP = 0x106a59 := hec.rip
  have crc : Stos.rcx.read c = 25 := by
    exact hec.writes.trans ((stos_read hb 6 (by decide) (by decide)).trans hprefix.rsi)
  have cz : (Operand.reg 0 : Operand 64).read c = 0 :=
    (hec.agrees.read (n := 64) (r := 0) (by simp only [movR64R64Effect_components]; decide)).trans
      ((stos_read hb 0 (by decide) (by decide)).trans hprefix.rax)
  have cr := stos_ready .quad 25 0 hc (cframe.directionFlagClear hp.direction (by simp [clobbers]))
    (by rw [cip]; exact instruction_codeIn hcc (by decide))
    (by rw [cip]; exact instruction_subset (by decide))
    crc cptr (by simp only [Stos.Kind.bytes, Stos.Kind.bits, Nat.reduceDiv]; omega) (by decide)
    (MemReadable.of_agreesExcept cframe hp.destination) hp.tables hp.program
  obtain ⟨d, hcd, hd, hcdcode, hfd⟩ := rep_steps hstride boundary hc hcc cr
    cz (csp ▸ hp.inside) cptr (by simp only [Stos.Kind.bytes, Stos.Kind.bits, Nat.reduceDiv]; omega) hlow hp.program
  have dframe := agrees_clobbers_trans cframe hfd
  have dptr : Stos.rdi.read d = dst + BitVec.ofNat 64 200 := by
    rw [hd.destination, cptr, BitVec.add_zero]
    rfl
  have dsp : stackPtr d = stackPtr s := hd.rsp.trans csp
  have dip : d.RIP = 0x106a5c := by rw [hd.rip, cip]; rfl
  obtain ⟨e, hde, he, hce, hee⟩ := scalar_step boundary
    (show StepEffect (fun t => t.RIP = 0x106a5c)
      (codeRange 0x106a5c [0x4C, 0x89, 0xC1]) (movR64R64Effect 0x106a5c 1 8) from
      mov_r64_r64_effect_step 0x106a5c 0x4C 0xC1 (by simp [RexWPrefix]) (by decide))
    (by decide) hd.ready hcdcode dip (dsp ▸ hp.inside) (by simp only [movR64R64Effect_components]; decide)
    (by
      intro c hc x
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact id)
  have ef := hee.agrees.mono (cs' := clobbers dst (200 + tail)) (by
    intro c hc
    simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [clobbers])
  have eframe := agrees_clobbers_trans dframe ef
  have eptr : Stos.rdi.read e = dst + BitVec.ofNat 64 200 :=
    (hee.agrees.read (n := 64) (r := 7) (by simp only [movR64R64Effect_components]; decide)).trans dptr
  have esp : stackPtr e = stackPtr s :=
    (hee.agrees.read (n := 64) (r := 4) (by simp only [movR64R64Effect_components]; decide)).trans dsp
  have eip : e.RIP = 0x106a5f := hee.rip
  have erc : Stos.rcx.read e = BitVec.ofNat 64 tail := by
    exact hee.writes.trans ((stos_read hd 8 (by decide) (by decide)).trans
      ((hec.agrees.read (n := 64) (r := 8) (by simp only [movR64R64Effect_components]; decide)).trans
        ((stos_read hb 8 (by decide) (by decide)).trans hprefix.r8)))
  have ez : (Operand.reg 0 : Operand 64).read e = 0 :=
    (hee.agrees.read (n := 64) (r := 0) (by simp only [movR64R64Effect_components]; decide)).trans
      ((stos_read hd 0 (by decide) (by decide)).trans cz)
  have er := stos_ready .byte tail 200 he (eframe.directionFlagClear hp.direction (by simp [clobbers]))
    (by rw [eip]; exact instruction_codeIn hce (by decide))
    (by rw [eip]; exact instruction_subset (by decide))
    erc eptr (by simp only [Stos.Kind.bytes, Stos.Kind.bits, Nat.reduceDiv, Nat.one_mul]; omega) (by omega)
    (MemReadable.of_agreesExcept eframe hp.destination) hp.tables hp.program
  obtain ⟨f, hef, hf, hcf, hff⟩ := rep_steps hstride boundary he hce er
    (stos_rax8 ez) (esp ▸ hp.inside) eptr (by simp only [Stos.Kind.bytes, Stos.Kind.bits, Nat.reduceDiv, Nat.one_mul]; omega) hlow hp.program
  have htailMax : max tail 1 = 1 := Nat.max_eq_right htail
  simp only [htailMax] at hef
  have fframe := agrees_clobbers_trans eframe hff
  have fsp : stackPtr f = stackPtr s := hf.rsp.trans esp
  have fip : f.RIP = 0x106a61 := by rw [hf.rip, eip]; rfl
  have fzero : ∀ i < (200 + tail), f.external[dst + BitVec.ofNat 64 i]? = some 0 := by
    intro i hi
    by_cases hsmall : i < 200
    · have hz := hd.zero i hsmall
      rw [cptr, BitVec.add_zero] at hz
      have hmem : e.external = d.external := hee.agrees.external (by
        intro c hc x
        simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> exact id)
      have hbyte := hf.agrees.byte (x := dst + BitVec.ofNat 64 i) (by
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, heq⟩ := hcov
        have hj0 : j = 0 := by simp only [Stos.Kind.bytes, Stos.Kind.bits, Nat.reduceDiv, Nat.one_mul] at hj; omega
        subst j
        rw [BitVec.add_zero, eptr] at heq
        have hn := congrArg BitVec.toNat heq
        rw [Stos.toNat_add_ofNat _ _ (by omega), Stos.toNat_add_ofNat _ _ (by omega)] at hn
        omega)
      change f.external[dst + BitVec.ofNat 64 i]? = e.external[dst + BitVec.ofNat 64 i]? at hbyte
      rw [hbyte, hmem]
      exact hz
    · have hi200 : i = 200 := by omega
      subst i
      have hz := hf.zero 0 (by change 0 < 1 * tail; omega)
      rw [BitVec.add_zero, eptr] at hz
      exact hz
  have fdx : (Operand.reg 2 : Operand 64).read f = dst :=
    (stos_read hf 2 (by decide) (by decide)).trans
      ((hee.agrees.read (n := 64) (r := 2) (by simp only [movR64R64Effect_components]; decide)).trans
        ((stos_read hd 2 (by decide) (by decide)).trans
          ((hec.agrees.read (n := 64) (r := 2) (by simp only [movR64R64Effect_components]; decide)).trans
            ((stos_read hb 2 (by decide) (by decide)).trans hprefix.rdx))))
  obtain ⟨g, hfg, hg, hcg, heg⟩ := scalar_step boundary
    (show StepEffect (fun t => t.RIP = 0x106a61)
      (codeRange 0x106a61 [0x48, 0x89, 0xD0]) (movR64R64Effect 0x106a61 0 2) from
      mov_r64_r64_effect_step 0x106a61 0x48 0xD0 (by simp [RexWPrefix]) (by decide))
    (by decide) hf.ready hcf fip (fsp ▸ hp.inside) (by simp only [movR64R64Effect_components]; decide)
    (by
      intro c hc x
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact id)
  have gf := heg.agrees.mono (cs' := clobbers dst (200 + tail)) (by
    intro c hc
    simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [clobbers])
  have gframe := agrees_clobbers_trans fframe gf
  have gsp : stackPtr g = stackPtr s :=
    (heg.agrees.read (n := 64) (r := 4) (by simp only [movR64R64Effect_components]; decide)).trans fsp
  have gip : g.RIP = 0x106a64 := heg.rip
  have gtop : stackTop g = stackTop s := clobbers_stackTop gframe gsp hp.disjoint
  have gr : RetPre 0x106a64 g := ⟨⟨gip, by
    rw [gsp]
    exact MemReadable.of_agreesExcept gframe hp.stack⟩, by rw [gtop]; exact hp.returnLow⟩
  obtain ⟨t, hgt, ht, het⟩ := ret_effect_step 0x106a64 g hg
    (instruction_codeIn hcg (by decide)) gr
  have tsp : stackPtr t = stackPtr s + 8 := by
    exact het.writes.trans (congrArg (· + 8) gsp)
  have hgtAdv : Advances boundary 1 g t := Advances.of_step hgt (by
    rcases hp.afterReturn with hip | hsp
    · exact .inl (het.rip.trans gtop ▸ hip)
    · apply Or.inr
      change stackPtr t ≠ boundary.rsp
      exact tsp ▸ hsp)
  have tf := het.agrees.mono (cs' := clobbers dst (200 + tail)) (by
    intro c hc
    simp only [retEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [clobbers])
  have tframe := agrees_clobbers_trans gframe tf
  refine ⟨t, hab.trans (hbc.trans (hcd.trans (hde.trans (hef.trans (hfg.trans hgtAdv))))),
    ⟨ht, het.agrees.codeIn (by
      intro c hc x
      simp only [retEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact id) hcg,
      het.rip.trans gtop, tsp, ?_, ?_, tframe⟩⟩
  · exact (het.agrees.read (n := 64) (r := 0) (by simp only [retEffect_components]; decide)).trans
      (heg.writes.trans fdx)
  · have hmemg : g.external = f.external := heg.agrees.external (by
      intro c hc x
      simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact id)
    have hmemt : t.external = g.external := het.agrees.external (by
      intro c hc x
      simp only [retEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact id)
    intro i hi
    rw [hmemt, hmemg]
    exact fzero i hi

theorem tail_steps [inst : Bindings] (hstride : UnitStringStride inst)
    (boundary : ReturnBoundary) (s a : RamState) (ha : ReadyToStep a)
    (hca : CodeIn Extracted.programImage a) (hp : Pre boundary s)
    (hprefix : PrefixPost s a) : ∃ t, Advances boundary 31 a t ∧ Done s t := by
  exact tail_steps_general (tail := 1) hstride (by decide) boundary s a ha hca hp hprefix

theorem memset_steps [inst : Bindings] {tail : Nat} (hstride : UnitStringStride inst)
    (htail : tail ≤ 1) (boundary : ReturnBoundary) (s : RamState) (hready : ReadyToStep s)
    (hcode : CodeIn Extracted.programImage s) (h : Pre boundary s (200 + tail)) :
    ∃ t, Advances boundary 45 s t ∧ Done s t (200 + tail) := by
  obtain ⟨a, hsa, ha, hca, hprefix⟩ := prefix_steps_general htail s hready hcode
    h.rip h.length h.value h.aligned boundary h.inside
  obtain ⟨t, hat, hd⟩ := tail_steps_general hstride htail boundary s a ha hca h hprefix
  exact ⟨t, hsa.trans hat, hd⟩

theorem memset201_steps [inst : Bindings] (hstride : UnitStringStride inst)
    (boundary : ReturnBoundary) (s : RamState) (hready : ReadyToStep s)
    (hcode : CodeIn Extracted.programImage s) (h : Pre boundary s) :
    ∃ t, Advances boundary 45 s t ∧ Done s t := by
  exact memset_steps (tail := 1) hstride (by decide) boundary s hready hcode h

theorem memset200_steps [inst : Bindings] (hstride : UnitStringStride inst)
    (boundary : ReturnBoundary) (s : RamState) (hready : ReadyToStep s)
    (hcode : CodeIn Extracted.programImage s) (h : Pre boundary s 200) :
    ∃ t, Advances boundary 45 s t ∧ Done s t 200 := by
  exact memset_steps (tail := 0) hstride (by decide) boundary s hready hcode h

end Sha3.Proofs.Memset
