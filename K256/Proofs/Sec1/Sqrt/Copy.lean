import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Program.Execution

set_option autoImplicit false

namespace K256.Proofs.Sec1.Sqrt

open X86 X86.Machine X86.UserProcess X86Proofs

def copy5Bytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20,
   0x48, 0x8b, 0x44, 0x24, 0x40, 0x48, 0x89, 0x44, 0x24, 0x18,
   0x48, 0x8b, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10,
   0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x8b, 0x4c, 0x24, 0x30,
   0x48, 0x89, 0x4c, 0x24, 0x08, 0x48, 0x89, 0x04, 0x24]

private def copyComponents (base : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .rip, .mem base 40]

private structure CopyProgress [Bindings] (boundary : ReturnBoundary)
    (s t : RamState) (fuel : Nat) (pc : BitVec 64) : Prop where
  advances : Advances boundary fuel s t
  ready : ReadyToStep t
  rip : t.RIP = pc
  frame : AgreesExcept (copyComponents (stackPtr s)) s t

private theorem CopyProgress.rsp [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {fuel : Nat} {pc : BitVec 64} (h : CopyProgress boundary s t fuel pc) :
    stackPtr t = stackPtr s :=
  h.frame.read (n := 64) (r := 4) (by simp [copyComponents])

private theorem copyCode [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {fuel : Nat} {pc : BitVec 64} {code : CodeMap}
    (h : CopyProgress boundary s t fuel pc) (hc : CodeIn code s)
    (hap : ∀ x ∈ code, ¬ Component.Covers (.mem (stackPtr s) 40) x.1) : CodeIn code t := by
  apply hc.of_agreesExcept h.frame
  intro x hx c hm
  simp only [copyComponents, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  all_goals first | exact hap x hx | exact fun h => h

private theorem offset_toNat {base : BitVec 64} {k : Nat} (h : base.toNat + k < 2^64) :
    (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt h]

private theorem copyRead {s t : RamState} {cs : List Component} {base : BitVec 64} {n k len : Nat}
    (h : AgreesExcept cs s t) (hr : MemReadable s base n) (hk : k + len ≤ n) :
    MemReadable t (base + BitVec.ofNat 64 k) len := by
  refine ⟨?_, ?_⟩
  · rw [offset_toNat (by have := hr.low; omega)]
    have := hr.low
    omega
  · intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.grow _ (hr.mem _ (by omega))

private theorem copyWrite {s t : RamState} {cs : List Component}
    {base : BitVec 64} {n k len : Nat} (h : AgreesExcept cs s t)
    (hw : MemWritable s base n) (hk : k + len ≤ n) :
    MemWritable t (base + BitVec.ofNat 64 k) len := by
  have hr := copyRead h hw.readable hk
  refine ⟨hr.low, hr.mem, hw.tables.sub ?_ ?_⟩
  all_goals
    rw [offset_toNat (by have := hw.low; omega)]
    omega

private theorem covers_of_subrange {base x : BitVec 64} {offset len total : Nat}
    (h : Component.Covers (.mem (base + BitVec.ofNat 64 offset) len) x)
    (hsub : offset + len ≤ total) : Component.Covers (.mem base total) x := by
  obtain ⟨i, hi, he⟩ := h
  exact ⟨offset + i, by omega, by simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he⟩

private theorem offsetApart {base : BitVec 64} {k l n m : Nat}
    (hap : k + n ≤ l ∨ l + m ≤ k) (hmax : k + n ≤ 2^64 ∧ l + m ≤ 2^64) :
    RangeApart (base + BitVec.ofNat 64 k) n (base + BitVec.ofNat 64 l) m := by
  intro i hi j hj he
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_right_inj] at he
  have hn := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat] at hn
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hn
  omega

private theorem sameWord {s t : RamState} {cs : List Component} {addr : BitVec 64}
    (h : AgreesExcept cs s t)
    (hap : ∀ i < 8, ∀ c ∈ cs, ¬ c.Covers (addr + BitVec.ofNat 64 i)) :
    memLoad t.external addr 64 = memLoad s.external addr 64 := by
  apply memLoad_congr
  intro i hi
  have he := h.byte (hap i hi)
  simp only [memByte]
  change (t.external[addr + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[addr + BitVec.ofNat 64 i]?).getD 0
  rw [he]

private theorem readSource {s t : RamState} {base : BitVec 64} {k : Nat}
    (h : AgreesExcept (copyComponents base) s t) (hk : 40 ≤ k ∧ k ≤ 72) :
    memLoad t.external (base + BitVec.ofNat 64 k) 64 =
      memLoad s.external (base + BitVec.ofNat 64 k) 64 := by
  apply sameWord h
  intro i hi c hm
  simp only [copyComponents, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  all_goals try exact fun h => h
  rintro ⟨j, hj, he⟩
  have apart : RangeApart (base + BitVec.ofNat 64 k) 8 (base + BitVec.ofNat 64 0) 40 :=
    offsetApart (.inr hk.1) (by omega)
  rw [BitVec.add_zero] at apart
  exact apart i hi j hj he

private theorem readOtherWord {s t : RamState} {base : BitVec 64} {k l : Nat}
    (h : AgreesExcept [.mem (base + BitVec.ofNat 64 k) 8, .rip] s t)
    (hk : k + 8 ≤ l ∨ l + 8 ≤ k) (hmax : k + 8 ≤ 2^64 ∧ l + 8 ≤ 2^64) :
    memLoad t.external (base + BitVec.ofNat 64 l) 64 =
      memLoad s.external (base + BitVec.ofNat 64 l) 64 := by
  apply sameWord h
  intro i hi c hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · rintro ⟨j, hj, he⟩
    exact offsetApart hk hmax j hj i hi he.symm
  · exact fun h => h

private theorem CopyProgress.step [Bindings] {boundary : ReturnBoundary} {s t u : RamState}
    {fuel : Nat} {pc next : BitVec 64} (h : CopyProgress boundary s t fuel pc)
    (hsp : stackPtr s ≠ boundary.rsp)
    (hs : Machine.step t = some (.next u)) (hr : ReadyToStep u) (hip : u.RIP = next)
    (hf : AgreesExcept (copyComponents (stackPtr s)) t u) :
    CopyProgress boundary s u (fuel + 1) next := by
  have hu : stackPtr u = stackPtr t := hf.read (n := 64) (r := 4) (by simp [copyComponents])
  have hne : u.GPR[4] ≠ boundary.rsp := by
    change stackPtr u ≠ boundary.rsp
    rwa [hu, h.rsp]
  refine ⟨h.advances.trans (Advances.of_step hs (.inr hne)), hr, hip, (h.frame.trans hf).mono ?_⟩
  simp only [List.mem_append, or_self]
  exact fun _ hm => hm

private def stackMode (d : Disp) : AddrMode := .sib 4 none 0 d

private theorem stackMode_valid (d : Disp) : (stackMode d).Valid := by
  simp [stackMode, AddrMode.Valid, regLow]

private theorem stackMode_addr (d : Disp) (t : RamState) (p : BitVec 64) :
    (stackMode d).addr t p = stackPtr t + d.value := rfl

private theorem loadWord [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {fuel : Nat} {pc : BitVec 64} {code : CodeMap} {k : Nat}
    (h : CopyProgress boundary s t fuel pc)
    (hsp : stackPtr s ≠ boundary.rsp) (hcode : CodeIn code s)
    (hap : ∀ x ∈ code, ¬ Component.Covers (.mem (stackPtr s) 40) x.1)
    (hr : MemReadable s (stackPtr s + 40) 40)
    (reg : BitVec 3) (d : Disp) (hd : d.value = BitVec.ofNat 64 k) (hk : 40 ≤ k ∧ k ≤ 72)
    (hreg : reg.setWidth 5 = 0 ∨ reg.setWidth 5 = 1)
    (hsub : ∀ x ∈ codeRange pc (0x48 :: 0x8b :: (stackMode d).modrm reg :: (stackMode d).tail),
      x ∈ code) :
    ∃ u, CopyProgress boundary s u (fuel + 1) (pc + BitVec.ofNat 64 (movLoadLen (stackMode d))) ∧
      (Operand.reg (reg.setWidth 5) : Operand 64).read u =
        memLoad s.external (stackPtr s + BitVec.ofNat 64 k) 64 ∧ u.external = t.external ∧
      AgreesExcept [.reg (reg.setWidth 5), .rip] t u := by
  have ha (next : BitVec 64) :
      (stackMode d).addr t next = stackPtr s + BitVec.ofNat 64 k := by
    rw [stackMode_addr, h.rsp, hd]
  have readable : MemReadable t (stackPtr s + BitVec.ofNat 64 k) 8 := by
    have hh := copyRead h.frame hr (k := k - 40) (len := 8) (by omega)
    change MemReadable t (stackPtr s + BitVec.ofNat 64 40 + BitVec.ofNat 64 (k - 40)) 8 at hh
    rwa [BitVec.add_assoc, ← BitVec.ofNat_add, show 40 + (k - 40) = k by omega] at hh
  obtain ⟨u, hs, hu, he⟩ := mov_r64_m64_effect_step pc 0x48 (by constructor <;> decide) reg (stackMode d)
    (stackMode_valid d) rfl rfl t h.ready
    ((copyCode h hcode hap).mono hsub) ⟨h.rip, by rw [ha]; exact readable⟩
  change (movR64M64Effect pc (gprNumber 0 0 reg) (stackMode d) t).Holds t u at he
  rw [gprNumber_zero_zero] at he
  have hf : AgreesExcept [.reg (reg.setWidth 5), .rip] t u := by
    simpa only [movR64M64Effect_components] using he.agrees
  have hv : (Operand.reg (reg.setWidth 5) : Operand 64).read u =
      memLoad t.external ((stackMode d).addr t (pc + BitVec.ofNat 64 (movLoadLen (stackMode d)))) 64 :=
    he.writes
  refine ⟨u, h.step hsp hs hu he.rip (hf.mono ?_), ?_, hf.external (by simp [Component.Covers]), hf⟩
  · rcases hreg with he | he <;> simp [he, copyComponents]
  · rw [hv, ha, readSource h.frame hk]

private theorem storeWord [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {fuel : Nat} {pc : BitVec 64} {code : CodeMap} {k : Nat}
    (h : CopyProgress boundary s t fuel pc)
    (hsp : stackPtr s ≠ boundary.rsp) (hcode : CodeIn code s)
    (hap : ∀ x ∈ code, ¬ Component.Covers (.mem (stackPtr s) 40) x.1)
    (hw : MemWritable s (stackPtr s) 40)
    (reg : BitVec 3) (d : Disp) (hd : d.value = BitVec.ofNat 64 k) (hk : k ≤ 32)
    (hsub : ∀ x ∈ codeRange pc (0x48 :: 0x89 :: (stackMode d).modrm reg :: (stackMode d).tail),
      x ∈ code) :
    ∃ u, CopyProgress boundary s u (fuel + 1) (pc + BitVec.ofNat 64 (movLoadLen (stackMode d))) ∧
      memLoad u.external (stackPtr s + BitVec.ofNat 64 k) 64 =
        (Operand.reg (reg.setWidth 5) : Operand 64).read t ∧
      AgreesExcept [.mem (stackPtr s + BitVec.ofNat 64 k) 8, .rip] t u := by
  let bytes := 0x48 :: 0x89 :: (stackMode d).modrm reg :: (stackMode d).tail
  have ha (next : BitVec 64) :
      (stackMode d).addr t next = stackPtr s + BitVec.ofNat 64 k := by
    rw [stackMode_addr, h.rsp, hd]
  have apart : RangeApart (stackPtr s + BitVec.ofNat 64 k) 8 pc bytes.length := by
    intro i hi j hj he
    exact hap _ (hsub _ (mem_codeRange pc bytes j hj))
      (covers_of_subrange ⟨i, hi, he.symm⟩ (by omega))
  have hlen : bytes.length = 3 + (stackMode d).tail.length := by
    simp only [bytes, List.length_cons, Nat.add_comm 3, Nat.add_assoc]
  obtain ⟨u, hs, hu, he⟩ := mov_m64_r64_effect_step pc 0x48 (by constructor <;> decide) reg (stackMode d)
    (stackMode_valid d) rfl rfl t h.ready
    ((copyCode h hcode hap).mono hsub)
    ⟨h.rip, by rw [storeAddrAt, ha]; exact copyWrite h.frame hw (by omega),
      by rw [storeAddrAt, ha, ← hlen]; exact apart⟩
  change (movM64R64Effect pc (gprNumber 0 0 reg) (stackMode d) t).Holds t u at he
  rw [gprNumber_zero_zero] at he
  have hf : AgreesExcept [.mem (stackPtr s + BitVec.ofNat 64 k) 8, .rip] t u := by
    simpa only [movM64R64Effect_components, storeAddrAt, ha] using he.agrees
  have hw' : memLoad u.external
      ((stackMode d).addr t (pc + BitVec.ofNat 64 (movLoadLen (stackMode d)))) 64 =
      (Operand.reg (reg.setWidth 5) : Operand 64).read t := he.writes
  refine ⟨u, h.step hsp hs hu he.rip ⟨?_, ?_, hf.rest, hf.grow⟩, by simpa only [ha] using hw', hf⟩
  · intro c hc hm
    apply hf.agree c _ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, fun eq => hc (eq ▸ by simp [copyComponents])⟩
    rintro rfl
    contradiction
  · intro x hx
    apply hf.memory x
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact fun hh => hx (.mem (stackPtr s) 40) (by simp [copyComponents])
        (covers_of_subrange hh (by omega))
    · exact fun hh => hh

theorem copy5 [Bindings] {boundary : ReturnBoundary} {s : RamState} {p : BitVec 64}
    {code : CodeMap} (hReady : ReadyToStep s) (hRip : s.RIP = p)
    (hRsp : stackPtr s ≠ boundary.rsp) (hCode : CodeIn code s)
    (hBlock : ∀ x ∈ codeRange p copy5Bytes, x ∈ code)
    (hApart : ∀ x ∈ code, ¬ Component.Covers (.mem (stackPtr s) 40) x.1)
    (hWrite : MemWritable s (stackPtr s) 40) (hRead : MemReadable s (stackPtr s + 40) 40) :
    ∃ t, Advances boundary 10 s t ∧ ReadyToStep t ∧ t.RIP = p + 49#64 ∧
      stackPtr t = stackPtr s ∧ CodeIn code t ∧ MemWritable t (stackPtr s) 40 ∧
      MemReadable t (stackPtr s + 40) 40 ∧
      AgreesExcept [.reg 0, .reg 1, .rip, .mem (stackPtr s) 40] s t ∧
      (∀ i : Fin 5,
        memLoad t.external (stackPtr s + BitVec.ofNat 64 (8 * i.val)) 64 =
        memLoad s.external (stackPtr s + BitVec.ofNat 64 (40 + 8 * i.val)) 64) := by
  have codeSlice (off : Nat) {bytes : List UInt8}
      (hb : (copy5Bytes.drop off).take bytes.length = bytes) :
      ∀ x ∈ codeRange (p + BitVec.ofNat 64 off) bytes, x ∈ code :=
    fun x hx => hBlock x (codeRange_mem_of_drop off hb x hx)
  have h0 : CopyProgress boundary s s 0 (p + BitVec.ofNat 64 0) :=
    ⟨(advances_zero boundary s s).2 rfl, hReady, by simpa using hRip, AgreesExcept.refl _ _⟩
  obtain ⟨t1, h1, v1, _, _⟩ :=
    loadWord h0 hRsp hCode hApart hRead (k := 72) 0 (.d8 72) rfl (by decide) (by decide)
      (codeSlice 0 (by decide))
  change CopyProgress boundary s t1 1 ((p + 0#64) + 5#64) at h1
  rw [BitVec.add_zero] at h1
  obtain ⟨t2, h2, w2, _⟩ :=
    storeWord h1 hRsp hCode hApart hWrite (k := 32) 0 (.d8 32) rfl (by decide)
      (codeSlice 5 (by decide))
  change CopyProgress boundary s t2 2 ((p + 5#64) + 5#64) at h2
  rw [BitVec.add_assoc] at h2
  obtain ⟨t3, h3, v3, m3, _⟩ :=
    loadWord h2 hRsp hCode hApart hRead (k := 64) 0 (.d8 64) rfl (by decide) (by decide)
      (codeSlice 10 (by decide))
  change CopyProgress boundary s t3 3 ((p + 10#64) + 5#64) at h3
  rw [BitVec.add_assoc] at h3
  obtain ⟨t4, h4, w4, f4⟩ :=
    storeWord h3 hRsp hCode hApart hWrite (k := 24) 0 (.d8 24) rfl (by decide)
      (codeSlice 15 (by decide))
  change CopyProgress boundary s t4 4 ((p + 15#64) + 5#64) at h4
  rw [BitVec.add_assoc] at h4
  obtain ⟨t5, h5, v5, m5, _⟩ :=
    loadWord h4 hRsp hCode hApart hRead (k := 56) 0 (.d8 56) rfl (by decide) (by decide)
      (codeSlice 20 (by decide))
  change CopyProgress boundary s t5 5 ((p + 20#64) + 5#64) at h5
  rw [BitVec.add_assoc] at h5
  obtain ⟨t6, h6, w6, f6⟩ :=
    storeWord h5 hRsp hCode hApart hWrite (k := 16) 0 (.d8 16) rfl (by decide)
      (codeSlice 25 (by decide))
  change CopyProgress boundary s t6 6 ((p + 25#64) + 5#64) at h6
  rw [BitVec.add_assoc] at h6
  obtain ⟨t7, h7, v7, m7, _⟩ :=
    loadWord h6 hRsp hCode hApart hRead (k := 40) 0 (.d8 40) rfl (by decide) (by decide)
      (codeSlice 30 (by decide))
  change CopyProgress boundary s t7 7 ((p + 30#64) + 5#64) at h7
  rw [BitVec.add_assoc] at h7
  obtain ⟨t8, h8, v8, m8, f8⟩ :=
    loadWord h7 hRsp hCode hApart hRead (k := 48) 1 (.d8 48) rfl (by decide) (by decide)
      (codeSlice 35 (by decide))
  change CopyProgress boundary s t8 8 ((p + 35#64) + 5#64) at h8
  rw [BitVec.add_assoc] at h8
  obtain ⟨t9, h9, w9, f9⟩ :=
    storeWord h8 hRsp hCode hApart hWrite (k := 8) 1 (.d8 8) rfl (by decide)
      (codeSlice 40 (by decide))
  change CopyProgress boundary s t9 9 ((p + 40#64) + 5#64) at h9
  rw [BitVec.add_assoc] at h9
  obtain ⟨t10, h10, w10, f10⟩ :=
    storeWord h9 hRsp hCode hApart hWrite (k := 0) 0 .none rfl (by decide)
      (codeSlice 45 (by decide))
  change CopyProgress boundary s t10 10 ((p + 45#64) + 4#64) at h10
  rw [BitVec.add_assoc] at h10
  refine ⟨t10, h10.advances, h10.ready, h10.rip, h10.rsp, copyCode h10 hCode hApart,
    ⟨hWrite.low, fun i hi => h10.frame.grow _ (hWrite.mem i hi), hWrite.tables⟩,
    ⟨hRead.low, fun i hi => h10.frame.grow _ (hRead.mem i hi)⟩, h10.frame, ?_⟩
  intro ⟨i, hi⟩
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases casesI with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceMul, Nat.reduceAdd]
  · exact w10.trans ((f9.read (by simp)).trans ((f8.read (by decide)).trans v7))
  · exact (readOtherWord f10 (l := 8) (by decide) (by decide)).trans (w9.trans v8)
  · rw [readOtherWord f10 (l := 16) (by decide) (by decide),
      readOtherWord f9 (l := 16) (by decide) (by decide), m8, m7]
    exact w6.trans v5
  · rw [readOtherWord f10 (l := 24) (by decide) (by decide),
      readOtherWord f9 (l := 24) (by decide) (by decide), m8, m7,
      readOtherWord f6 (l := 24) (by decide) (by decide), m5]
    exact w4.trans v3
  · rw [readOtherWord f10 (l := 32) (by decide) (by decide),
      readOtherWord f9 (l := 32) (by decide) (by decide), m8, m7,
      readOtherWord f6 (l := 32) (by decide) (by decide), m5,
      readOtherWord f4 (l := 32) (by decide) (by decide), m3]
    exact w2.trans v1

end K256.Proofs.Sec1.Sqrt
