import ChaCha20Poly1305.Spec
import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Execution
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.Mov.Generated.MR.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Shl.Generated.R.Triple
import X86Proofs.Instructions.Nop.Triple
import ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Rounds
import X86Proofs.Instructions.Mov.Generated.M8R8.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Xor.Generated.R8M8.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Inc.Generated.R.Triple

namespace ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Xor

open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305

def reg32 (t : RamState) (r : BitVec 5) : BitVec 32 := (Operand.reg r : Operand 32).read t

def reg64 (t : RamState) (r : BitVec 5) : BitVec 64 := (Operand.reg r : Operand 64).read t

def slot (t : RamState) (off : Nat) : BitVec 64 := stackPtr t + BitVec.ofNat 64 off

def slot32 (t : RamState) (off : Nat) : BitVec 32 := memLoad t.external (slot t off) 32

def slot64 (t : RamState) (off : Nat) : BitVec 64 := memLoad t.external (slot t off) 64

def keystream (mixed init : Vector UInt32 16) : Vector UInt8 64 :=
  serialize (Vector.ofFn fun i => mixed[i] + init[i])

def mixedReg : List (Fin 16 × BitVec 5) :=
  [(0, 3), (1, 13), (2, 12), (3, 10), (4, 5), (5, 1), (6, 2), (7, 11), (9, 0), (10, 6),
    (11, 8), (12, 9), (13, 7), (14, 14), (15, 15)]

def initSlot : List (Fin 16 × Nat) :=
  [(0, 0x58), (1, 0x10), (2, 0xc), (3, 0x40), (4, 0x38), (5, 0x34), (6, 0x30), (7, 0x2c),
    (8, 0x84), (9, 0x28), (10, 0x24), (11, 0x20), (12, 0x3c), (13, 0x80), (14, 0x1c),
    (15, 0x18)]

def codeLo : Nat := 0x100e19

def codeHi : Nat := 0x1010a8

def scratchOff : Nat := 0xb0

def scratchBytes : Nat := 0xc0

def frameBytes : Nat := 0x170

def inBlock (inBase : BitVec 64) (j : Nat) : BitVec 64 := inBase + BitVec.ofNat 64 (64 * j)

def outBlock (outBase : BitVec 64) (j : Nat) : BitVec 64 := outBase + BitVec.ofNat 64 (64 * j)

structure Frame (t : RamState) : Prop where
  writable : MemWritable t (stackPtr t) frameBytes
  program : ∀ i < frameBytes, ¬ InProgram (stackPtr t + BitVec.ofNat 64 i)

structure Blocks (t : RamState) (j : Nat) (inBase outBase : BitVec 64)
    (block : Vector UInt8 64) : Prop where
  index : slot64 t 0x70 = BitVec.ofNat 64 j
  inSlot : slot64 t 0x68 = inBase
  outSlot : slot64 t 0x60 = outBase
  inLow : inBase.toNat + 64 * j + 64 ≤ 2 ^ 32
  input : ∀ i : Fin 64, t.external[inBlock inBase j + BitVec.ofNat 64 i.val]? = some block[i]
  inStack : RangeApart (inBlock inBase j) 64 (stackPtr t) frameBytes
  output : MemWritable t (outBlock outBase j) 64
  outStack : RangeApart (outBlock outBase j) 64 (stackPtr t) frameBytes
  outProgram : ∀ i < 64, ¬ InProgram (outBlock outBase j + BitVec.ofNat 64 i)

                                                                                              
                                                                                            
         
structure FeedPre (mixed init : Vector UInt32 16) (j : Nat) (inBase outBase : BitVec 64)
    (block : Vector UInt8 64) (t : RamState) : Prop where
  rip : t.RIP = BitVec.ofNat 64 codeLo
  frame : Frame t
  mixedRegs : ∀ e ∈ mixedReg, reg32 t e.2 = mixed[e.1].toBitVec
  mixed8 : slot32 t 0x4 = mixed[8].toBitVec
  initSlots : ∀ e ∈ initSlot, slot32 t e.2 = init[e.1].toBitVec
  blocks : Blocks t j inBase outBase block

def changes (t : RamState) (outBase : BitVec 64) (j : Nat) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip,
    .mem (slot t scratchOff) scratchBytes, .mem (outBlock outBase j) 64]

                                                                                                
                                                                                             
                                                                                       
structure FeedPost (t u : RamState) (mixed init : Vector UInt32 16) (j : Nat)
    (outBase : BitVec 64) (block : Vector UInt8 64) : Prop where
  rip : u.RIP = BitVec.ofNat 64 codeHi
  agrees : AgreesExcept (changes t outBase j) t u
  output : ∀ i : Fin 64, u.external[outBlock outBase j + BitVec.ofNat 64 i.val]? =
    some (block[i] ^^^ (keystream mixed init)[i])
  rdi : reg64 u 7 = BitVec.ofNat 64 (j + 1)
  r12 : reg64 u 12 = (init[12] + 1).toBitVec.setWidth 64
  r10 : reg64 u 10 = init[4].toBitVec.setWidth 64
  r11 : reg64 u 11 = init[8].toBitVec.setWidth 64
  r8 : reg64 u 8 = init[13].toBitVec.setWidth 64


open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

theorem fr_readable {s : RamState} {a : BitVec 64} {n : Nat} (h : MemWritable s a n)
    (c : BitVec 64) (len : Nat) (hc : c.toNat + len ≤ n) : MemReadable s (a + c) len := by
  have hl := h.low
  refine ⟨?_, fun i hi => ?_⟩
  · rw [BitVec.toNat_add]; omega
  · have he : a + c + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (c.toNat + i) := by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [he]; exact h.mem _ (by omega)

theorem fr_writable {s : RamState} {a : BitVec 64} {n : Nat} (h : MemWritable s a n)
    (c : BitVec 64) (len : Nat) (hc : c.toNat + len ≤ n) : MemWritable s (a + c) len := by
  have hr := fr_readable h c len hc
  have hl := h.low
  have ha : (a + c).toNat = a.toNat + c.toNat := by rw [BitVec.toNat_add]; omega
  exact ⟨hr.low, hr.mem, by rw [ha]; exact h.tables.sub (by omega) (by omega)⟩

theorem fr_apart {a q p : BitVec 64} {n codeLen : Nat} (h : RangeApart a n p codeLen)
    (c : BitVec 64) (len : Nat) (hc : c.toNat + len ≤ n) (m : Nat)
    (hq : p.toNat ≤ q.toNat) (hm : q.toNat + m ≤ p.toNat + codeLen) :
    RangeApart (a + c) len q m := by
  intro i hi j hj he
  apply h (c.toNat + i) (by omega) (q.toNat - p.toNat + j) (by omega)
  have h1 : a + BitVec.ofNat 64 (c.toNat + i) = a + c + BitVec.ofNat 64 i := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
    have := c.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have h2 : p + BitVec.ofNat 64 (q.toNat - p.toNat + j) = q + BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq
    have := q.isLt
    have := p.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.add_mod_mod, Nat.add_mod_mod, show p.toNat + (q.toNat - p.toNat + j) = q.toNat + j by omega]
  rw [h1, h2]; exact he

theorem code_inProgram (p j : Nat) (hp : 0x100000 ≤ p) (h : p + j < 0x100000 + 11759) :
    InProgram (BitVec.ofNat 64 p + BitVec.ofNat 64 j) := by
  have hs : Extracted.textBytes.size = 11759 := by decide
  have hp' := text_address_in_program (p - 0x100000 + j) (by omega)
  have he : BitVec.ofNat 64 p + BitVec.ofNat 64 j =
      Extracted.textAddress + BitVec.ofNat 64 (p - 0x100000 + j) := by
    apply BitVec.eq_of_toNat_eq
    have h0 : Extracted.textAddress.toNat = 1048576 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_add, h0, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    omega
  rw [he]
  exact hp'

theorem apart_code {a : BitVec 64} {n : Nat} (h : ∀ i < n, ¬ InProgram (a + BitVec.ofNat 64 i))
    (p m : Nat) (hp : 0x100000 ≤ p) (hm : p + m ≤ 0x100000 + 11759) :
    RangeApart a n (BitVec.ofNat 64 p) m := by
  intro i hi j hj he
  apply h i hi
  rw [he]
  exact code_inProgram p j hp (by omega)

theorem stack_not_covers (a : BitVec 64) (c n d len i : Nat) (hc : c + n < 2 ^ 64)
    (hd : d + len < 2 ^ 64) (hi : i < len) (h : d + len ≤ c ∨ c + n ≤ d) :
    ¬ (Component.mem (a + BitVec.ofNat 64 c) n).Covers (a + BitVec.ofNat 64 d + BitVec.ofNat 64 i) := by
  rintro ⟨k, hk, he⟩
  rw [BitVec.add_assoc, BitVec.add_assoc] at he
  have he' := congrArg BitVec.toNat ((BitVec.add_right_inj a).mp he)
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at he'
  rw [Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (a := c + k) (by omega)] at he'
  omega

theorem stack_covers_sub (a : BitVec 64) (c n lo len : Nat) (hc : lo ≤ c) (hn : c + n ≤ lo + len)
    (hl : lo + len < 2 ^ 64) (x : BitVec 64)
    (h : (Component.mem (a + BitVec.ofNat 64 c) n).Covers x) :
    (Component.mem (a + BitVec.ofNat 64 lo) len).Covers x := by
  obtain ⟨k, hk, rfl⟩ := h
  refine ⟨c - lo + k, by omega, ?_⟩
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2
  omega

theorem apart_not_covers {b a : BitVec 64} {n : Nat} (h : RangeApart b 64 a n) (c len : Nat)
    (hc : c + len ≤ n) (i : Nat) (hi : i < 64) :
    ¬ (Component.mem (a + BitVec.ofNat 64 c) len).Covers (b + BitVec.ofNat 64 i) := by
  rintro ⟨k, hk, he⟩
  apply h i hi (c + k) (by omega)
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem load_keep {cs : List Component} {s t : RamState} (h : AgreesExcept cs s t) {a : BitVec 64}
    {n : Nat} (hc : ∀ i < n / 8, ∀ c ∈ cs, ¬ c.Covers (a + BitVec.ofNat 64 i)) :
    memLoad t.external a n = memLoad s.external a n :=
  memLoad_congr fun i hi => by
    simp only [memByte]
    exact congrArg (fun o => Option.getD o 0) (h.byte (hc i hi))

theorem sw_32_64 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  omega

theorem mem32_of_write {t : RamState} {a : BitVec 64} {x : BitVec 32}
    (h : (Operand.mem a : Operand 32).read t = BitVec.setWidth 32 (BitVec.setWidth 64 x)) :
    memLoad t.external a 32 = x := by
  rw [sw_32_64] at h
  exact h

theorem reg32_of_write {t : RamState} {r : BitVec 5} {x : BitVec 32}
    (h : (Operand.reg r : Operand 64).read t = BitVec.setWidth 64 x) :
    reg32 t r = x := by
  unfold reg32
  simp only [Operand.read] at h ⊢
  have h' : t.GPR[gprIndex r] = BitVec.setWidth 64 x := by
    rw [← h]; exact (BitVec.setWidth_eq _).symm
  rw [h', sw_32_64]

theorem rexR44 : rexR (UInt8.toBitVec 68) = 1 := by decide
theorem rexR45 : rexR (UInt8.toBitVec 69) = 1 := by decide
theorem rexR4c : rexR (UInt8.toBitVec 76) = 1 := by decide
theorem rexR48 : rexR (UInt8.toBitVec 72) = 0 := by decide
theorem rexR40 : rexR (UInt8.toBitVec 64) = 0 := by decide
theorem rexR41 : rexR (UInt8.toBitVec 65) = 0 := by decide


structure Within (c : Component) (cs : List Component) : Prop where
  reg : c.isMem = false → c ∈ cs
  mem : ∀ x, c.Covers x → ∃ c' ∈ cs, c'.Covers x

theorem within_reg {r : BitVec 5} {cs : List Component} (h : Component.reg r ∈ cs) :
    Within (.reg r) cs := ⟨fun _ => h, fun _ hx => absurd hx (by simp [Component.Covers])⟩

theorem within_flags {cs : List Component} (h : Component.flags ∈ cs) : Within .flags cs :=
  ⟨fun _ => h, fun _ hx => absurd hx (by simp [Component.Covers])⟩

theorem within_rip {cs : List Component} (h : Component.rip ∈ cs) : Within .rip cs :=
  ⟨fun _ => h, fun _ hx => absurd hx (by simp [Component.Covers])⟩

theorem within_mem {a : BitVec 64} {c n lo len : Nat} {cs : List Component}
    (hm : Component.mem (a + BitVec.ofNat 64 lo) len ∈ cs) (hc : lo ≤ c) (hn : c + n ≤ lo + len)
    (hl : lo + len < 2 ^ 64) : Within (.mem (a + BitVec.ofNat 64 c) n) cs :=
  ⟨fun h => by simp [Component.isMem] at h,
    fun x hx => ⟨_, hm, stack_covers_sub a c n lo len hc hn hl x hx⟩⟩

theorem widen_trans {cs₁ cs₂ cs : List Component} {s₀ s t : RamState}
    (h₁ : AgreesExcept cs s₀ s) (h₂ : AgreesExcept cs₂ s t) (hw : ∀ c ∈ cs₂, Within c cs)
    (hcs : cs₁ = cs := by rfl) : AgreesExcept cs s₀ t := by
  subst hcs
  refine (h₁.trans h₂).widen (fun c hc hm => ?_) (fun x c hc hx => ?_)
  · rcases List.mem_append.mp hc with hc | hc
    · exact hc
    · exact (hw c hc).1 hm
  · rcases List.mem_append.mp hc with hc | hc
    · exact ⟨c, hc, hx⟩
    · exact (hw c hc).2 x hx

structure FeedA (t0 t : RamState) (pc : Nat) (mixed init : Vector UInt32 16) (j : Nat)
    (inBase outBase : BitVec 64) (block : Vector UInt8 64)
    (mr : List (Fin 16 × BitVec 5)) (ksw : List (Fin 16)) (ir : List (Fin 16 × BitVec 5)) :
    Prop where
  rip : t.RIP = BitVec.ofNat 64 pc
  sp : stackPtr t = stackPtr t0
  agrees : AgreesExcept (changes t0 outBase j) t0 t
  mregs : ∀ e ∈ mr, reg32 t e.2 = mixed[e.1].toBitVec
  ks : ∀ w ∈ ksw, memLoad t.external (stackPtr t0 + BitVec.ofNat 64 (0xf0 + 4 * w.val)) 32 =
    (mixed[w] + init[w]).toBitVec
  iregs : ∀ e ∈ ir, reg64 t e.2 = init[e.1].toBitVec.setWidth 64
  input : ∀ i : Fin 64, t.external[inBlock inBase j + BitVec.ofNat 64 i.val]? = some block[i]

section FeedA

variable {t0 s : RamState} {pc : Nat} {mixed init : Vector UInt32 16} {j : Nat}
  {inBase outBase : BitVec 64} {block : Vector UInt8 64} {mr : List (Fin 16 × BitVec 5)}
  {ksw : List (Fin 16)} {ir : List (Fin 16 × BitVec 5)}

theorem FeedA.fr (h0 : FeedPre mixed init j inBase outBase block t0)
    (h : FeedA t0 s pc mixed init j inBase outBase block mr ksw ir) :
    MemWritable s (stackPtr s) 0x170 := by
  rw [h.sp]
  have w := h0.frame.writable
  exact ⟨w.low, fun i hi => h.agrees.grow _ (w.mem i hi), w.tables⟩

theorem FeedA.ap (h0 : FeedPre mixed init j inBase outBase block t0)
    (h : FeedA t0 s pc mixed init j inBase outBase block mr ksw ir) :
    RangeApart (stackPtr s) 0x170 (BitVec.ofNat 64 codeLo) (codeHi - codeLo) := by
  rw [h.sp]
  exact apart_code h0.frame.program _ _ (by decide) (by decide)

theorem changes_not_covers (h0 : FeedPre mixed init j inBase outBase block t0) (off len : Nat)
    (hoff : off + len ≤ scratchOff) :
    ∀ i < len, ∀ c ∈ changes t0 outBase j, ¬ c.Covers (stackPtr t0 + BitVec.ofNat 64 off + BitVec.ofNat 64 i) := by
  intro i hi c hc
  simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
  unfold scratchOff at hoff
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals first | (simp [Component.Covers]; done) | skip
  · exact stack_not_covers (stackPtr t0) 0xb0 0xc0 off len i (by decide) (by omega) hi (Or.inl hoff)
  · rintro ⟨k, hk, he⟩
    apply h0.blocks.outStack k hk (off + i) (by unfold frameBytes; omega)
    rw [← he, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem FeedA.slot32_eq (h0 : FeedPre mixed init j inBase outBase block t0)
    (h : FeedA t0 s pc mixed init j inBase outBase block mr ksw ir) (off : Nat)
    (hoff : off + 4 ≤ scratchOff) : slot32 s off = slot32 t0 off := by
  unfold slot32 slot
  rw [h.sp]
  exact load_keep h.agrees fun i hi => changes_not_covers h0 off 4 hoff i (by omega)

theorem FeedA.slot64_eq (h0 : FeedPre mixed init j inBase outBase block t0)
    (h : FeedA t0 s pc mixed init j inBase outBase block mr ksw ir) (off : Nat)
    (hoff : off + 8 ≤ scratchOff) : slot64 s off = slot64 t0 off := by
  unfold slot64 slot
  rw [h.sp]
  exact load_keep h.agrees fun i hi => changes_not_covers h0 off 8 hoff i (by omega)

theorem FeedA.initv (h0 : FeedPre mixed init j inBase outBase block t0)
    (h : FeedA t0 s pc mixed init j inBase outBase block mr ksw ir) :
    ∀ e ∈ initSlot, slot32 s e.2 = init[e.1].toBitVec := by
  intro e he
  rw [h.slot32_eq h0 e.2 ?_]
  · exact h0.initSlots e he
  · simp only [initSlot, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> decide

theorem FeedA.mixed8 (h0 : FeedPre mixed init j inBase outBase block t0)
    (h : FeedA t0 s pc mixed init j inBase outBase block mr ksw ir) :
    slot32 s 4 = mixed[8].toBitVec := by
  rw [h.slot32_eq h0 4 (by decide)]
  exact h0.mixed8

theorem FeedA.start (h0 : FeedPre mixed init j inBase outBase block t0) :
    FeedA t0 t0 codeLo mixed init j inBase outBase block mixedReg [] [] :=
  ⟨h0.rip, rfl, AgreesExcept.refl _ _, h0.mixedRegs, by simp, by simp, h0.blocks.input⟩

end FeedA

macro "xf_pre_load " hfr:term : tactic => `(tactic| (
  intro s hP; refine ⟨hP.rip, ?_⟩; x86_norm; exact fr_readable ($hfr s hP) _ _ (by decide)))

macro "xf_load_mid " hfr:term : tactic => `(tactic| (
  intro s s' hP hH hO
  refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
    Effect.Local.avoids (by x86_local) (hO true) ?_⟩
  · x86_norm; exact fr_readable ($hfr s hP) _ _ (by decide)
  · exact Effect.Avoids.of_noMem (by x86_norm; simp [Component.Covers]) _))

macro "xf_store_mid " hfr:term:max hap:term:max hlen:term : tactic => `(tactic| (
  intro s s' hP hH hO
  refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_,
    Effect.Local.avoids (by x86_local) (hO true) ?_⟩
  · x86_norm; exact fr_writable ($hfr s hP) _ _ (by decide)
  · x86_norm; exact fr_apart ($hap s hP) _ _ (by decide) _ (by decide) (by decide)
  · apply Effect.avoids_of_components_mem_rip (by rfl)
    rw [$hlen:term]; x86_norm; exact fr_apart ($hap s hP) _ _ (by decide) _ (by decide) (by decide)))

macro "xf_boundary " hne:term : tactic => `(tactic| (
  intro _ _; x86_norm; exact $hne _ (by decide) (by decide)))

macro "xf_norm_holds " hH:ident hrip:ident hw:ident hag:ident : tactic => `(tactic| (
  x86_norm at $hH:ident
  obtain ⟨$hrip, $hw, -, $hag⟩ := $hH:ident
  dsimp only [Write.AllHold] at $hrip:ident $hw:ident $hag:ident
  simp only [Effect.components, List.map, Write.component, Operand.component, List.cons_append,
    List.nil_append] at $hag:ident
  simp only [rexR44, rexR45, rexR4c, rexR48, rexR40, rexR41, gprNumber, BitVec.reduceToNat,
    Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat, Nat.reduceMod] at $hw:ident $hag:ident))


macro "xf_within " hrs:ident : tactic => `(tactic| (
  repeat' apply And.intro
  all_goals first
    | exact within_reg (by simp [changes])
    | exact within_flags (by simp [changes])
    | exact within_rip (by simp [changes])
    | (intro x hx; simp at hx)
    | (rw [$hrs:ident]
       exact within_mem (lo := 0xb0) (len := 0xc0) (by simp [changes, slot, scratchOff, scratchBytes])
         (by decide) (by decide) (by decide))))

macro "xf_nc_stack " hrs:ident hi:ident : tactic => `(tactic| (
  all_goals first
    | (simp [Component.Covers]; done)
    | (rw [$hrs:ident]
       exact stack_not_covers _ _ _ _ _ _ (by decide) (by decide) $hi (by decide))))

macro "xf_nc_input " hrs:ident h0:ident i:ident : tactic => `(tactic| (
  all_goals first
    | (simp [Component.Covers]; done)
    | (rw [$hrs:ident]
       exact apart_not_covers (FeedPre.blocks $h0).inStack _ _ (by decide) _ (Fin.isLt $i))))

macro "xf_ks_word " w:ident r:term:max sl:term:max h0:ident hP:ident hrs:ident : tactic => `(tactic| (
  have e := mem32_of_write $w
  rw [$hrs:ident] at e
  refine (Eq.trans ?_ e).trans ?_
  · rfl
  · rw [UInt32.toBitVec_add]
    congr 1
    · exact FeedA.mregs $hP $r (by decide)
    · have h' := FeedA.initv $h0 $hP $sl (by decide)
      unfold slot32 slot at h'
      rw [FeedA.sp $hP] at h'
      exact h'))
def AdvancesTo [Bindings] (boundary : ReturnBoundary) (pre : RamState → Prop)
    (code : CodeMap) (Q : RamState → RamState → Prop) : Prop :=
  ∀ s, ReadyToStep s → CodeIn code s → pre s →
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn code t ∧ Q s t

theorem advancesTo_of_block [Bindings] {boundary : ReturnBoundary} {P : RamState → Prop}
    {code : CodeMap} {Q : RamState → RamState → Prop} {E : RamState → Effect}
    (hB : AdvancesBlock boundary P code E) (hQ : ∀ s t, P s → (E s).Holds s t → Q s t) :
    AdvancesTo boundary P code Q := by
  intro s hr hc hp
  obtain ⟨n, t, h1, h2, h3, h4⟩ := hB s hr hc hp
  exact ⟨n, t, h1, h2, h3, hQ s t hp h4⟩

def a1a_bytes : List UInt8 := [0x03, 0x5c, 0x24, 0x58, 0x89, 0x9c, 0x24, 0xf0, 0x00, 0x00, 0x00, 0x44, 0x03, 0x6c, 0x24, 0x10, 0x44, 0x89, 0xac, 0x24, 0xf4, 0x00, 0x00, 0x00, 0x44, 0x03, 0x64, 0x24, 0x0c, 0x44, 0x89, 0xa4, 0x24, 0xf8, 0x00, 0x00, 0x00, 0x44, 0x03, 0x54, 0x24, 0x40, 0x44, 0x89, 0x94, 0x24, 0xfc, 0x00, 0x00, 0x00]

theorem a1a_bytes_length : a1a_bytes.length = 50 := rfl

set_option maxHeartbeats 0 in
theorem a1a [Bindings] (boundary : ReturnBoundary)
    (hne : ∀ pc : BitVec 64, codeLo ≤ pc.toNat → pc.toNat ≤ codeHi → pc ≠ boundary.rip)
    {t0 : RamState} {mixed init : Vector UInt32 16} {j : Nat} {inBase outBase : BitVec 64}
    {block : Vector UInt8 64} (h0 : FeedPre mixed init j inBase outBase block t0) :
    AdvancesTo boundary (fun s => FeedA t0 s codeLo mixed init j inBase outBase block mixedReg [] []) (codeRange 0x100e19 a1a_bytes)
      (fun _ t => FeedA t0 t 0x100e4b mixed init j inBase outBase block [(4, 5), (5, 1), (6, 2), (7, 11), (9, 0), (10, 6), (11, 8), (12, 9), (13, 7), (14, 14), (15, 15)] [0, 1, 2, 3] []) := by
  have hfr : ∀ s, (FeedA t0 s codeLo mixed init j inBase outBase block mixedReg [] []) → MemWritable s (stackPtr s) 0x170 := fun _ hP => hP.fr h0
  have hap : ∀ s, (FeedA t0 s codeLo mixed init j inBase outBase block mixedReg [] []) → RangeApart (stackPtr s) 0x170 (BitVec.ofNat 64 codeLo) (codeHi - codeLo) :=
    fun _ hP => hP.ap h0
  refine advancesTo_of_block (E := ?E) ?blk ?imp
  case blk =>
                                      
    routine_run_begin add_r32_m32_effect_step 0x100e19 3 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)
    case pre => xf_pre_load hfr
    case boundary => xf_boundary hne
                                      
    routine_run_then mov_m32_r32_low_effect_step 0x100e1d 3 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100e19) 4 (by decide +kernel)
    case mid => xf_store_mid hfr hap a1a_bytes_length
    case boundary => xf_boundary hne
                                       
    routine_run_then add_r32_m32_rex_effect_step 0x100e24 0x44 (by unfold RexNoWPrefix; decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100e19) 11 (by decide +kernel)
    case mid => xf_load_mid hfr
    case boundary => xf_boundary hne
                                       
    routine_run_then mov_m32_r32_effect_step 0x100e29 0x44 (by unfold RexNoWPrefix; decide) 5 (.sib 4 none 0 (.d32 0xf4)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100e19) 16 (by decide +kernel)
    case mid => xf_store_mid hfr hap a1a_bytes_length
    case boundary => xf_boundary hne
                                      
    routine_run_then add_r32_m32_rex_effect_step 0x100e31 0x44 (by unfold RexNoWPrefix; decide) 4 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100e19) 24 (by decide +kernel)
    case mid => xf_load_mid hfr
    case boundary => xf_boundary hne
                                       
    routine_run_then mov_m32_r32_effect_step 0x100e36 0x44 (by unfold RexNoWPrefix; decide) 4 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100e19) 29 (by decide +kernel)
    case mid => xf_store_mid hfr hap a1a_bytes_length
    case boundary => xf_boundary hne
                                       
    routine_run_then add_r32_m32_rex_effect_step 0x100e3e 0x44 (by unfold RexNoWPrefix; decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100e19) 37 (by decide +kernel)
    case mid => xf_load_mid hfr
    case boundary => xf_boundary hne
                                       
    routine_run_then mov_m32_r32_effect_step 0x100e43 0x44 (by unfold RexNoWPrefix; decide) 2 (.sib 4 none 0 (.d32 0xfc)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100e19) 42 (by decide +kernel)
    case mid => xf_store_mid hfr hap a1a_bytes_length
    case boundary => xf_boundary hne
    exact id
  case imp =>
    intro s t hP hH
    xf_norm_holds hH hrip hw hag
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ := hw
    have hsp : stackPtr t = stackPtr s := by
      rw [stackPtr_eq_read, stackPtr_eq_read]; exact hag.read (by simp)
    have hrs : (Operand.reg (4#5) : Operand 64).read s = stackPtr t0 := by
      exact (stackPtr_eq_read s).symm.trans hP.sp
    refine ⟨hrip, hsp.trans hP.sp, ?_, ?_, ?_, ?_, ?_⟩
    · refine widen_trans hP.agrees hag ?_
      simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
      xf_within hrs
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals (unfold reg32; rw [hag.read (by simp (config := { decide := true }))]
                 exact hP.mregs _ (by decide))
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · xf_ks_word w1 (0, 3) (0, 0x58) h0 hP hrs
      · xf_ks_word w3 (1, 13) (1, 0x10) h0 hP hrs
      · xf_ks_word w5 (2, 12) (2, 0xc) h0 hP hrs
      · xf_ks_word w7 (3, 10) (3, 0x40) h0 hP hrs
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      all_goals exact absurd he (by simp)
    · intro i
      rw [hag.byte ?_]
      · exact hP.input i
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      xf_nc_input hrs h0 i

                                                      
structure XF (sp : BitVec 64) (s : RamState) : Prop where
  rsp : (Operand.reg 4 : Operand 64).read s = sp
  wr : MemWritable s sp 0x170
  code : ∀ i < 0x170, ¬ InProgram (sp + BitVec.ofNat 64 i)

theorem XF.rd {sp : BitVec 64} {s : RamState} (hx : XF sp s) {c : BitVec 64} {n : Nat}
    (hc : c.toNat + n ≤ 0x170) : MemReadable s ((Operand.reg 4 : Operand 64).read s + c) n := by
  rw [hx.rsp]; exact fr_readable hx.wr c n hc

theorem XF.wrt {sp : BitVec 64} {s : RamState} (hx : XF sp s) {c : BitVec 64} {n : Nat}
    (hc : c.toNat + n ≤ 0x170) : MemWritable s ((Operand.reg 4 : Operand 64).read s + c) n := by
  rw [hx.rsp]; exact fr_writable hx.wr c n hc

theorem XF.ap {sp : BitVec 64} {s : RamState} (hx : XF sp s) {c : BitVec 64} {n : Nat}
    (hc : c.toNat + n ≤ 0x170) (q : BitVec 64) (m : Nat) (hq : codeLo ≤ q.toNat)
    (hm : q.toNat + m ≤ codeHi) :
    RangeApart ((Operand.reg 4 : Operand 64).read s + c) n q m := by
  rw [hx.rsp]
  exact fr_apart (apart_code hx.code codeLo (codeHi - codeLo) (by decide) (by decide)) c n hc m
    (by rw [BitVec.toNat_ofNat]; exact hq) (by rw [BitVec.toNat_ofNat]; unfold codeLo codeHi at *; omega)

theorem lp_addr {sp x c : BitVec 64} {m : Nat} (hx : x = BitVec.ofNat 64 m) :
    sp + (x <<< 0 + c) = sp + BitVec.ofNat 64 (m + c.toNat) := by
  subst hx; simp only [BitVec.shiftLeft_zero]
  congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem XF.lrd {sp : BitVec 64} {s : RamState} (hx : XF sp s) {k : Nat}
    (h1 : (Operand.reg 1 : Operand 64).read s = BitVec.ofNat 64 (3 + 4 * k)) (hk : k < 16)
    {c : BitVec 64} {n : Nat} (hc : 3 + 4 * k + c.toNat + n ≤ 0x170) :
    MemReadable s ((Operand.reg 4 : Operand 64).read s +
      ((Operand.reg 1 : Operand 64).read s <<< 0 + c)) n := by
  rw [hx.rsp, lp_addr h1]; exact fr_readable hx.wr _ n (by simp; omega)

theorem XF.lwr {sp : BitVec 64} {s : RamState} (hx : XF sp s) {k : Nat}
    (h1 : (Operand.reg 1 : Operand 64).read s = BitVec.ofNat 64 (3 + 4 * k)) (hk : k < 16)
    {c : BitVec 64} {n : Nat} (hc : 3 + 4 * k + c.toNat + n ≤ 0x170) :
    MemWritable s ((Operand.reg 4 : Operand 64).read s +
      ((Operand.reg 1 : Operand 64).read s <<< 0 + c)) n := by
  rw [hx.rsp, lp_addr h1]; exact fr_writable hx.wr _ n (by simp; omega)

theorem XF.lap {sp : BitVec 64} {s : RamState} (hx : XF sp s) {k : Nat}
    (h1 : (Operand.reg 1 : Operand 64).read s = BitVec.ofNat 64 (3 + 4 * k)) (hk : k < 16)
    {c : BitVec 64} {n : Nat} (hc : 3 + 4 * k + c.toNat + n ≤ 0x170) (q : BitVec 64) (m : Nat)
    (hq : codeLo ≤ q.toNat) (hm : q.toNat + m ≤ codeHi) :
    RangeApart ((Operand.reg 4 : Operand 64).read s +
      ((Operand.reg 1 : Operand 64).read s <<< 0 + c)) n q m := by
  rw [hx.rsp, lp_addr h1]
  exact fr_apart (apart_code hx.code codeLo (codeHi - codeLo) (by decide) (by decide)) _ n
    (by simp; omega) m (by rw [BitVec.toNat_ofNat]; exact hq)
    (by rw [BitVec.toNat_ofNat]; unfold codeLo codeHi at *; omega)

theorem ne_bd {boundary : ReturnBoundary}
    (hb : boundary.rip.toNat < codeLo ∨ codeHi < boundary.rip.toNat) {p : BitVec 64}
    (h1 : 0x100e19 ≤ p.toNat) (h2 : p.toNat ≤ 0x1010a8) : p ≠ boundary.rip := by
  rintro rfl; unfold codeLo codeHi at hb; omega

theorem mm_apart (mem : Ram) (base x c₁ c₂ : BitVec 64) {n : Nat}
    (v : BitVec n) (k : Nat) (h : OffsetsApart c₁ (n / 8) c₂ (k / 8)) (hn : n ≤ 128)
    (hk : k ≤ 128) :
    memLoad (memStore mem (base + (x + c₁)) v) (base + (x + c₂)) k =
      memLoad mem (base + (x + c₂)) k := by
  rw [← BitVec.add_assoc, ← BitVec.add_assoc]
  exact memLoad_memStore_apart mem (base + x) c₁ c₂ v k h hn hk

                                                                                      
structure EX (outBase : BitVec 64) (j : Nat) (s : RamState) : Prop where
  out : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x60) : Operand 64).read s = outBase
  rax : (Operand.reg 0 : Operand 64).read s = BitVec.ofNat 64 (64 * j)
  wr : MemWritable s (outBlock outBase j) 64
  prog : ∀ i < 64, ¬ InProgram (outBlock outBase j + BitVec.ofNat 64 i)

theorem EX.addr {outBase : BitVec 64} {j : Nat} {s : RamState} (he : EX outBase j s)
    (c : BitVec 64) :
    (Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x60) : Operand 64).read s +
      ((Operand.reg 0 : Operand 64).read s <<< 0 + c) = outBlock outBase j + c := by
  rw [he.out, he.rax, BitVec.shiftLeft_zero, ← BitVec.add_assoc]; rfl

theorem EX.wrt {outBase : BitVec 64} {j : Nat} {s : RamState} (he : EX outBase j s)
    {c : BitVec 64} {n : Nat} (hc : c.toNat + n ≤ 64) :
    MemWritable s ((Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x60) : Operand 64).read s +
      ((Operand.reg 0 : Operand 64).read s <<< 0 + c)) n := by
  rw [he.addr]; exact fr_writable he.wr c n hc

theorem EX.ap {outBase : BitVec 64} {j : Nat} {s : RamState} (he : EX outBase j s)
    {c : BitVec 64} {n : Nat} (hc : c.toNat + n ≤ 64) (q : BitVec 64) (m : Nat)
    (hq : 0x100000 ≤ q.toNat) (hm : q.toNat + m ≤ 0x100000 + 11759) :
    RangeApart ((Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x60) : Operand 64).read s +
      ((Operand.reg 0 : Operand 64).read s <<< 0 + c)) n q m := by
  rw [he.addr]
  exact fr_apart (apart_code he.prog 0x100000 11759 (by decide) (by decide)) c n hc m
    (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat]; omega)

theorem EX.wrt0 {outBase : BitVec 64} {j : Nat} {s : RamState} (he : EX outBase j s) {n : Nat}
    (hc : n ≤ 64) :
    MemWritable s ((Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x60) : Operand 64).read s +
      (Operand.reg 0 : Operand 64).read s <<< 0) n := by
  rw [show (Operand.reg 0 : Operand 64).read s <<< 0 = (Operand.reg 0 : Operand 64).read s <<< 0 + 0
    from (BitVec.add_zero _).symm]
  exact he.wrt (by simpa using hc)

theorem EX.ap0 {outBase : BitVec 64} {j : Nat} {s : RamState} (he : EX outBase j s)
    {n : Nat} (hc : n ≤ 64) (q : BitVec 64) (m : Nat)
    (hq : 0x100000 ≤ q.toNat) (hm : q.toNat + m ≤ 0x100000 + 11759) :
    RangeApart ((Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x60) : Operand 64).read s +
      (Operand.reg 0 : Operand 64).read s <<< 0) n q m := by
  rw [show (Operand.reg 0 : Operand 64).read s <<< 0 = (Operand.reg 0 : Operand 64).read s <<< 0 + 0
    from (BitVec.add_zero _).symm]
  exact he.ap (by simpa using hc) q m hq hm

macro "xs_loop" : tactic => `(tactic| (
  try x86_norm
  first
  | exact XF.lrd (by assumption) (by assumption) (by assumption) (by simp; omega)
  | exact XF.lwr (by assumption) (by assumption) (by assumption) (by simp; omega)
  | exact XF.lap (by assumption) (by assumption) (by assumption) (by simp; omega) _ _
      (by decide) (by decide)))

macro "xs_out" : tactic => `(tactic| (
  try x86_norm
  first
  | exact EX.wrt (by assumption) (by decide)
  | exact EX.ap (by assumption) (by decide) _ _ (by decide) (by decide)
  | exact XF.rd (by assumption) (by decide)))

macro "xs_out0" : tactic => `(tactic| (
  try x86_norm
  try simp only [BitVec.add_zero]
  first
  | exact EX.wrt0 (by assumption) (by decide)
  | exact EX.ap0 (by assumption) (by decide) _ _ (by decide) (by decide)))

macro "xs_stack" : tactic => `(tactic| (
  try x86_norm
  first
  | exact XF.rd (by assumption) (by decide)
  | exact XF.wrt (by assumption) (by decide)
  | exact XF.ap (by assumption) (by decide) _ _ (by decide) (by decide)))

macro "xb_bd" : tactic => `(tactic| (
  intro _ _; exact ne_bd (by assumption) (by x86_norm) (by x86_norm)))

macro "xb_begin " t:term " using " side:tacticSeq : tactic => `(tactic| (
  refine AdvancesBlock.block_first ?k $t ?sub ?pre ?av ?boundary
  case sub => first | x86_sub | rr_sub
  case pre =>
    intro s hP
    obtain ⟨hrip, hx, he⟩ := hP
    first
    | (refine LoadPre.of_holds (Effect.start_holds s) (Effect.start_obs s) hrip
         (by x86_addr_obs) ?_
       ($side))
    | (refine StorePre.of_holds (Effect.start_holds s) (Effect.start_obs s) hrip
         (by x86_addr_obs) ?_ ?_ <;> ($side))
    | exact hrip
    | exact ⟨hrip⟩
  case av =>
    intro s hP
    obtain ⟨hrip, hx, he⟩ := hP
    first
    | (solve | apply Effect.Avoids.of_noMem; simp [Component.Covers])
    | (x86_avoid
       all_goals ($side))
  case boundary => xb_bd
  case' k => skip))

macro "xb_begin_r " t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_first ?k $t ?sub ?pre ?av ?boundary
  case sub => first | x86_sub | rr_sub
  case pre => intro s hP; exact hP.1
  case av => intro s hP; apply Effect.Avoids.of_noMem; simp [Component.Covers]
  case boundary => xb_bd
  case' k => skip))

macro "xb_then " t:term " using " side:tacticSeq : tactic => `(tactic| (
  refine AdvancesBlock.block_then ?k $t ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case sub => first | x86_sub | rr_sub
  case full =>
    first
    | (intro s _
       apply Effect.Local.full
       repeat' first
         | (solve | x86_local)
         | apply Effect.Local.seq
       done)
    | x86_full
  case mid =>
    intro s s' hP hH hO
    obtain ⟨hrip, hx, he⟩ := hP
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · first
      | (refine StorePre.of_holds hH (hO true) (by first | rfl | x86_norm) (by x86_addr_obs)
           ?_ ?_ <;> ($side))
      | (refine LoadPre.of_holds hH (hO true) (by first | rfl | x86_norm) (by x86_addr_obs) ?_
         ($side))
      | exact hH.rip_of (by first | rfl | x86_norm)
      | exact ⟨hH.rip_of (by first | rfl | x86_norm)⟩
    · first
      | (solve | apply Effect.Avoids.of_noMem; simp [Component.Covers])
      | (x86_avoid
         all_goals ($side))
  case boundary => xb_bd
  case' k => skip))

def loopBytes : List UInt8 := [0x0f, 0xb6, 0x94, 0x0c, 0xed, 0x00, 0x00, 0x00, 0x0f, 0xb6, 0xb4, 0x0c, 0xee, 0x00, 0x00, 0x00, 0x32, 0x94, 0x0c, 0x2d, 0x01, 0x00, 0x00, 0x40, 0x32, 0xb4, 0x0c, 0x2e, 0x01, 0x00, 0x00, 0x88, 0x94, 0x0c, 0xad, 0x00, 0x00, 0x00, 0x0f, 0xb6, 0x94, 0x0c, 0xef, 0x00, 0x00, 0x00, 0x32, 0x94, 0x0c, 0x2f, 0x01, 0x00, 0x00, 0x40, 0x88, 0xb4, 0x0c, 0xae, 0x00, 0x00, 0x00, 0x0f, 0xb6, 0xb4, 0x0c, 0xf0, 0x00, 0x00, 0x00, 0x40, 0x32, 0xb4, 0x0c, 0x30, 0x01, 0x00, 0x00, 0x88, 0x94, 0x0c, 0xaf, 0x00, 0x00, 0x00, 0x40, 0x88, 0xb4, 0x0c, 0xb0, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc1, 0x04, 0x48, 0x83, 0xf9, 0x43]

theorem agrees_widen {cs cs' : List Component} {s t : RamState} (h : AgreesExcept cs s t)
    (hw : ∀ c ∈ cs, Within c cs') : AgreesExcept cs' s t :=
  h.widen (fun c hc hm => (hw c hc).1 hm) (fun x c hc hx => (hw c hc).2 x hx)

theorem read8 (t : RamState) (a : BitVec 64) :
    (Operand.mem a : Operand 8).read t = (memByte t.external a).toBitVec := memLoad_8 _ _

                                                                                          
structure LoopQ (sp : BitVec 64) (k : Nat) (s t : RamState) : Prop where
  rip : t.RIP = 0x101034
  agrees : AgreesExcept [.reg 2, .reg 6, .reg 1, .flags, .rip,
    .mem (sp + BitVec.ofNat 64 (0xb0 + 4 * k)) 4] s t
  rcx : (Operand.reg 1 : Operand 64).read t = BitVec.ofNat 64 (3 + 4 * (k + 1))
  zf : (StatusFlags.ofRFLAGS t.RFLAGS).ZF = decide (k + 1 = 16)
  out : ∀ b < 4, memByte t.external (sp + BitVec.ofNat 64 (0xb0 + 4 * k + b)) =
    memByte s.external (sp + BitVec.ofNat 64 (0xf0 + 4 * k + b)) ^^^
      memByte s.external (sp + BitVec.ofNat 64 (0x130 + 4 * k + b))

set_option maxHeartbeats 1000000 in
theorem loopRun [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < codeLo ∨ codeHi < boundary.rip.toNat) (sp : BitVec 64) (k : Nat)
    (hk : k < 16) :
    AdvancesTo boundary (fun s => s.RIP = 0x100fd0 ∧ XF sp s ∧
      (Operand.reg 1 : Operand 64).read s = BitVec.ofNat 64 (3 + 4 * k))
      (codeRange 0x100fd0 loopBytes) (LoopQ sp k) := by
  refine advancesTo_of_block (E := ?E) ?blk ?imp
  case blk =>
    unfold loopBytes
    xb_begin (movzx_r32_m8_effect_step 0x100fd0 2 (.sib 4 (some 1) 0 (.d32 0xed)) (by decide) (by decide) (by decide)) using xs_loop
    xb_then (movzx_r32_m8_effect_step 0x100fd8 6 (.sib 4 (some 1) 0 (.d32 0xee)) (by decide) (by decide) (by decide)) using xs_loop
    xb_then (xor_r8_m8_effect_step 0x100fe0 2 (by decide) (.sib 4 (some 1) 0 (.d32 0x12d)) (by decide) (by decide) (by decide)) using xs_loop
    xb_then (xor_r8_m8_rex_effect_step 0x100fe7 0x40 (by unfold RexPrefix; decide) 6 (.sib 4 (some 1) 0 (.d32 0x12e)) (by decide) (by decide) (by decide)) using xs_loop
    xb_then (mov_m8_r8_effect_step 0x100fef 2 (by decide) (.sib 4 (some 1) 0 (.d32 0xad)) (by decide) (by decide) (by decide)) using xs_loop
    xb_then (movzx_r32_m8_effect_step 0x100ff6 2 (.sib 4 (some 1) 0 (.d32 0xef)) (by decide) (by decide) (by decide)) using xs_loop
    xb_then (xor_r8_m8_effect_step 0x100ffe 2 (by decide) (.sib 4 (some 1) 0 (.d32 0x12f)) (by decide) (by decide) (by decide)) using xs_loop
    xb_then (mov_m8_r8_rex_effect_step 0x101005 0x40 (by unfold RexPrefix; decide) 6 (.sib 4 (some 1) 0 (.d32 0xae)) (by decide) (by decide) (by decide)) using xs_loop
    xb_then (movzx_r32_m8_effect_step 0x10100d 6 (.sib 4 (some 1) 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) using xs_loop
    xb_then (xor_r8_m8_rex_effect_step 0x101015 0x40 (by unfold RexPrefix; decide) 6 (.sib 4 (some 1) 0 (.d32 0x130)) (by decide) (by decide) (by decide)) using xs_loop
    xb_then (mov_m8_r8_effect_step 0x10101d 2 (by decide) (.sib 4 (some 1) 0 (.d32 0xaf)) (by decide) (by decide) (by decide)) using xs_loop
    xb_then (mov_m8_r8_rex_effect_step 0x101024 0x40 (by unfold RexPrefix; decide) 6 (.sib 4 (some 1) 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) using xs_loop
    xb_then (add_r64_imm8_effect_step 0x10102c 0x48 0xc1 0x04 (by unfold RexWPrefix; decide) (by decide) (by decide)) using xs_loop
    xb_then (cmp_r64_imm8_effect_step 0x101030 0x48 0xf9 0x43 (by unfold RexWPrefix; decide) (by decide) (by decide)) using xs_loop
    exact id
  case imp =>
    intro s t hP hH
    obtain ⟨hrip, hx, h1⟩ := hP
    have hfull : ∀ w ∈ (?E s).writes, w.Full := by
      simp (config := { decide := true }) only [x86_compose, List.forall_mem_cons,
        List.forall_mem_nil, List.forall_mem_append, and_true, true_and]
    have ho := hH.obsAfter hfull true
    have h4 := hx.rsp
    have ha : ∀ b < 4, sp + BitVec.ofNat 64 (0xb0 + 4 * k + b) =
        (Operand.reg 4 : Operand 64).read s + ((Operand.reg 1 : Operand 64).read s <<< 0 +
          BitVec.ofNat 64 (0xad + b)) := by
      intro b hb; rw [h4, lp_addr h1]; congr 2; simp; omega
    have hl : ∀ b < 4, ∀ c, c < 0x200 → (Operand.reg 4 : Operand 64).read s + ((Operand.reg 1 : Operand 64).read s <<< 0 +
          BitVec.ofNat 64 c) = sp + BitVec.ofNat 64 (3 + 4 * k + c) := by
      intro b hb c hc; rw [h4, lp_addr h1]; congr 2; simp; omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hH.rip.trans (by x86_norm)
    · have hag := hH.agrees
      x86_norm at hag
      x86_norm at hl
      refine agrees_widen hag ?_
      simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first
        | (intro x hx; simp at hx)
        | exact within_reg (by simp (config := {decide := true}))
        | exact within_flags (by simp)
        | exact within_rip (by simp)
        | (rw [hl 0 (by decide) _ (by decide)]
           exact within_mem (lo := 0xb0 + 4 * k) (len := 4) (by simp) (by omega) (by omega) (by omega))
    · rw [← ho.read_reg]
      x86_norm
      change (Operand.reg 1 : Operand 64).read s + 4#64 = _
      rw [h1]
      apply BitVec.eq_of_toNat_eq; simp; omega
    · x86_norm at hH
      have hfl := Effect.Holds.flag hH StatusFlag.ZF
      simp only [Effect.flag, StatusFlagsOutcome.get, FlagAllows] at hfl
      change _ = (cmpSpec ((Operand.reg 1 : Operand 64).read s + 4#64) 67#64).ZF at hfl
      rw [h1] at hfl
      refine hfl.trans ?_
      simp only [cmpSpec, subSpec]
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
      constructor
      · intro he
        have := congrArg BitVec.toNat he
        simp [BitVec.toNat_sub, BitVec.toNat_add] at this
        omega
      · intro h
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_sub, BitVec.toNat_add]
        omega
    · intro b hb
      have e := read8 t (sp + BitVec.ofNat 64 (0xb0 + 4 * k + b))
      rw [ha b hb, ← ho.read_mem] at e
      rw [show 0xb0 + 4 * k + b = 3 + 4 * k + (0xad + b) by omega,
        show 0xf0 + 4 * k + b = 3 + 4 * k + (0xed + b) by omega,
        show 0x130 + 4 * k + b = 3 + 4 * k + (0x12d + b) by omega]
      rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
      all_goals
        simp only [Nat.reduceAdd] at e ⊢
        x86_norm [mm_apart] at e
        x86_norm at hl
        simp (config := {decide := true}) only [read8, BitVec.setWidth_setWidth_of_le,
          BitVec.setWidth_eq] at e
        rw [hl 0 (by decide) _ (by decide), hl 0 (by decide) _ (by decide),
          hl 0 (by decide) _ (by decide)] at e
        apply UInt8.toBitVec_inj.mp
        rw [UInt8.toBitVec_xor]
        exact e.symm

theorem text_at {s : RamState} (hc : CodeIn Extracted.programImage s) (off count : Nat)
    (p : BitVec 64) (bytes : List UInt8) (hp : Extracted.textAddress + BitVec.ofNat 64 off = p)
    (hb : Extracted.textBytes.toListFrom off count = bytes)
    (h : off + count ≤ Extracted.textBytes.size) : CodeIn (codeRange p bytes) s := by
  subst hp hb; exact program_text_slice hc off count h

theorem nc_mem (a : BitVec 64) (c n d : Nat) (hc : c + n < 2 ^ 64) (hd : d < 2 ^ 64)
    (h : d < c ∨ c + n ≤ d) :
    ¬ (Component.mem (a + BitVec.ofNat 64 c) n).Covers (a + BitVec.ofNat 64 d) := by
  rintro ⟨k, hk, he⟩
  rw [BitVec.add_assoc] at he
  have he' := congrArg BitVec.toNat ((BitVec.add_right_inj a).mp he)
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at he'
  rw [Nat.mod_eq_of_lt (a := d) hd, Nat.mod_eq_of_lt (a := c) (by omega),
    Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := c + k) (by omega)] at he'
  omega

                                                  
theorem codeIn_of_changes {t0 s t : RamState} {mixed init : Vector UInt32 16} {j : Nat}
    {inBase outBase : BitVec 64} {block : Vector UInt8 64} {cs : List Component}
    (h0 : FeedPre mixed init j inBase outBase block t0) (hag : AgreesExcept cs s t)
    (hw : ∀ c ∈ cs, Within c (changes t0 outBase j)) (hc : CodeIn Extracted.programImage s) :
    CodeIn Extracted.programImage t := by
  refine CodeIn.of_agreesExcept hag (fun x hx c hc' hcov => ?_) hc
  obtain ⟨c', hc'', hcov'⟩ := (hw c hc').2 x.1 hcov
  have hp := inProgram_of_mem hx
  simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc''
  rcases hc'' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (simp [Component.Covers] at hcov'; done) | skip
  · obtain ⟨i, hi, he⟩ := hcov'
    apply h0.frame.program (0xb0 + i) (by unfold frameBytes; unfold scratchBytes at hi; omega)
    have e : slot t0 scratchOff + BitVec.ofNat 64 i = stackPtr t0 + BitVec.ofNat 64 (0xb0 + i) := by
      unfold slot scratchOff; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [← e, ← he]; exact hp
  · obtain ⟨i, hi, he⟩ := hcov'
    exact h0.blocks.outProgram i hi (he ▸ hp)

def kst (mixed init : Vector UInt32 16) : Vector UInt8 64 := keystream mixed init

                                                                                          
structure Loop (t0 : RamState) (mixed init : Vector UInt32 16) (j : Nat) (outBase : BitVec 64)
    (block : Vector UInt8 64) (k : Nat) (t : RamState) : Prop where
  sp : stackPtr t = stackPtr t0
  agrees : AgreesExcept (changes t0 outBase j) t0 t
  rcx : reg64 t 1 = BitVec.ofNat 64 (3 + 4 * k)
  rdi : reg64 t 7 = BitVec.ofNat 64 j
  rax : reg64 t 0 = BitVec.ofNat 64 (64 * j)
  r10 : reg64 t 10 = init[4].toBitVec.setWidth 64
  r11 : reg64 t 11 = init[8].toBitVec.setWidth 64
  r12 : reg64 t 12 = init[12].toBitVec.setWidth 64
  r8 : reg64 t 8 = init[13].toBitVec.setWidth 64
  ks : ∀ i : Fin 64, memByte t.external (stackPtr t0 + BitVec.ofNat 64 (0xf0 + i.val)) =
    (keystream mixed init)[i]
  inp : ∀ i : Fin 64, memByte t.external (stackPtr t0 + BitVec.ofNat 64 (0x130 + i.val)) =
    block[i]
  out : ∀ i : Fin 64, i.val < 4 * k →
    memByte t.external (stackPtr t0 + BitVec.ofNat 64 (0xb0 + i.val)) =
      block[i] ^^^ (keystream mixed init)[i]

theorem Loop.xf {t0 t : RamState} {mixed init : Vector UInt32 16} {j : Nat} {inBase outBase : BitVec 64}
    {block : Vector UInt8 64} {k : Nat} (h0 : FeedPre mixed init j inBase outBase block t0)
    (h : Loop t0 mixed init j outBase block k t) : XF (stackPtr t0) t :=
  ⟨(stackPtr_eq_read t).symm.trans h.sp,
    ⟨h0.frame.writable.low, fun i hi => h.agrees.grow _ (h0.frame.writable.mem i hi),
      h0.frame.writable.tables⟩, h0.frame.program⟩

theorem Loop.rip_step {t0 t u : RamState} {mixed init : Vector UInt32 16} {j : Nat}
    {outBase : BitVec 64} {block : Vector UInt8 64} {k : Nat}
    (h : Loop t0 mixed init j outBase block k t) (g : AgreesExcept [.rip] t u) :
    Loop t0 mixed init j outBase block k u := by
  have hr : ∀ r : BitVec 5, reg64 u r = reg64 t r := fun r => g.read (by simp)
  have hm : ∀ a, memByte u.external a = memByte t.external a := fun a => by
    simp only [memByte, PhysicalMemory.read]
    rw [g.byte (by simp [Component.Covers])]
  refine ⟨?_, widen_trans h.agrees g (fun c hc => by
      simp only [List.mem_singleton] at hc; subst hc; exact within_rip (by simp [changes])),
    (hr 1).trans h.rcx, (hr 7).trans h.rdi, (hr 0).trans h.rax, (hr 10).trans h.r10,
    (hr 11).trans h.r11, (hr 12).trans h.r12, (hr 8).trans h.r8,
    fun i => (hm _).trans (h.ks i), fun i => (hm _).trans (h.inp i),
    fun i hi => (hm _).trans (h.out i hi)⟩
  rw [stackPtr_eq_read, ← h.sp, stackPtr_eq_read]; exact g.read (by simp)

set_option maxHeartbeats 1000000 in
theorem loop_step [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < codeLo ∨ codeHi < boundary.rip.toNat)
    {t0 : RamState} {mixed init : Vector UInt32 16} {j : Nat} {inBase outBase : BitVec 64}
    {block : Vector UInt8 64} (h0 : FeedPre mixed init j inBase outBase block t0) {k : Nat}
    (hk : k < 16) {s : RamState} (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hrip : s.RIP = 0x100fd0) (hL : Loop t0 mixed init j outBase block k s) :
    ∃ fuel u, Advances boundary fuel s u ∧ ReadyToStep u ∧ CodeIn Extracted.programImage u ∧
      Loop t0 mixed init j outBase block (k + 1) u ∧
      u.RIP = if k + 1 = 16 then 0x101036 else 0x100fd0 := by
  have hx := hL.xf h0
  obtain ⟨n, t, ha, hr', _, hQ⟩ := loopRun boundary hb (stackPtr t0) k hk s hr
    (text_at hc 0xfd0 100 _ _ (by decide) (by decide +kernel) (by decide)) ⟨hrip, hx, hL.rcx⟩
  have hw : ∀ c ∈ [Component.reg 2, .reg 6, .reg 1, .flags, .rip,
      .mem (stackPtr t0 + BitVec.ofNat 64 (0xb0 + 4 * k)) 4], Within c (changes t0 outBase j) := by
    simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
    refine ⟨within_reg (by simp [changes]), within_reg (by simp [changes]),
      within_reg (by simp [changes]), within_flags (by simp [changes]),
      within_rip (by simp [changes]), ?_, fun _ h => by simp at h⟩
    exact within_mem (a := stackPtr t0) (c := 0xb0 + 4 * k) (n := 4) (lo := 0xb0) (len := 0xc0)
      (cs := changes t0 outBase j)
      (by unfold changes slot scratchOff scratchBytes; simp) (by omega) (by omega) (by omega)
  have hct : CodeIn Extracted.programImage t := codeIn_of_changes h0 hQ.agrees hw hc
  have hag : AgreesExcept (changes t0 outBase j) t0 t := widen_trans hL.agrees hQ.agrees hw
  have hkeep : ∀ d, d < 0x170 → (d < 0xb0 + 4 * k ∨ 0xb0 + 4 * k + 4 ≤ d) →
      memByte t.external (stackPtr t0 + BitVec.ofNat 64 d) =
        memByte s.external (stackPtr t0 + BitVec.ofNat 64 d) := by
    intro d hd hd'
    simp only [memByte, PhysicalMemory.read]
    rw [hQ.agrees.byte]
    intro c hc' hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | (simp [Component.Covers] at hcov; done) | skip
    exact nc_mem _ _ _ _ (by omega) (by omega) hd' hcov
  have hrd : ∀ r : BitVec 5, r ≠ 2 → r ≠ 6 → r ≠ 1 → reg64 t r = reg64 s r := by
    intro r h2 h6 h1
    exact hQ.agrees.read (by simp; exact ⟨h2, h6, h1⟩)
  have hL' : Loop t0 mixed init j outBase block (k + 1) t := by
    refine ⟨?_, hag, hQ.rcx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have e : stackPtr t = stackPtr s := by
        rw [stackPtr_eq_read, stackPtr_eq_read]; exact hQ.agrees.read (by simp)
      exact e.trans hL.sp
    · rw [hrd 7 (by decide) (by decide) (by decide)]; exact hL.rdi
    · rw [hrd 0 (by decide) (by decide) (by decide)]; exact hL.rax
    · rw [hrd 10 (by decide) (by decide) (by decide)]; exact hL.r10
    · rw [hrd 11 (by decide) (by decide) (by decide)]; exact hL.r11
    · rw [hrd 12 (by decide) (by decide) (by decide)]; exact hL.r12
    · rw [hrd 8 (by decide) (by decide) (by decide)]; exact hL.r8
    · intro i
      rw [hkeep _ (by omega) (by omega)]; exact hL.ks i
    · intro i
      rw [hkeep _ (by omega) (by omega)]; exact hL.inp i
    · intro i hi
      by_cases h : i.val < 4 * k
      · rw [hkeep _ (by omega) (by omega)]; exact hL.out i h
      · have hb4 : i.val - 4 * k < 4 := by omega
        have e := hQ.out (i.val - 4 * k) hb4
        rw [show 0xb0 + 4 * k + (i.val - 4 * k) = 0xb0 + i.val by omega,
          show 0xf0 + 4 * k + (i.val - 4 * k) = 0xf0 + i.val by omega,
          show 0x130 + 4 * k + (i.val - 4 * k) = 0x130 + i.val by omega] at e
        rw [e, hL.ks i, hL.inp i, UInt8.xor_comm]
  have hcode : CodeIn (codeRange 0x101034 (jccOpcode8 5 :: immBytes 8 0x9a)) t :=
    text_at hct 0x1034 2 _ _ (by decide) (by decide +kernel) (by decide)
  have hcond : condHolds 5 (StatusFlags.ofRFLAGS t.RFLAGS) = !decide (k + 1 = 16) := by
    simp only [condHolds, BitVec.reduceToNat]; rw [hQ.zf]
  obtain ⟨u, a2, r2, e2⟩ := (jcc_rel8_effect_step 0x101034 5 0x9a).advances hr' hcode
    ⟨hQ.rip, fun _ => by decide⟩ (by
      simp only [jccEffect, branchEffect, hcond]
      split <;> exact ne_bd hb (by decide) (by decide))
  have hu : u.RIP = if k + 1 = 16 then 0x101036 else 0x100fd0 := by
    rw [e2.rip]; simp only [jccEffect, branchEffect, hcond]
    by_cases h : k + 1 = 16 <;> simp [h] <;> decide
  have ag2 : AgreesExcept [.rip] t u := by simpa [jccEffect] using e2.agrees
  refine ⟨n + 1, u, ha.trans a2, r2, ?_, ?_, hu⟩
  · exact CodeIn.of_agreesExcept ag2 (fun x _ c hc' hcov => by
      simp only [List.mem_singleton] at hc'; subst hc'; exact hcov) hct
  · exact hL'.rip_step ag2

theorem loop_all [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < codeLo ∨ codeHi < boundary.rip.toNat)
    {t0 : RamState} {mixed init : Vector UInt32 16} {j : Nat} {inBase outBase : BitVec 64}
    {block : Vector UInt8 64} (h0 : FeedPre mixed init j inBase outBase block t0) :
    ∀ n k s, k + n + 1 = 16 → ReadyToStep s → CodeIn Extracted.programImage s →
      s.RIP = 0x100fd0 → Loop t0 mixed init j outBase block k s →
      ∃ fuel u, Advances boundary fuel s u ∧ ReadyToStep u ∧ CodeIn Extracted.programImage u ∧
        Loop t0 mixed init j outBase block 16 u ∧ u.RIP = 0x101036 := by
  intro n
  induction n with
  | zero =>
    intro k s hk hr hc hrip hL
    obtain ⟨f, u, a, r, c, l, hu⟩ := loop_step boundary hb h0 (by omega) hr hc hrip hL
    rw [show k + 1 = 16 by omega] at l hu
    exact ⟨f, u, a, r, c, l, by simpa using hu⟩
  | succ n ih =>
    intro k s hk hr hc hrip hL
    obtain ⟨f, u, a, r, c, l, hu⟩ := loop_step boundary hb h0 (by omega) hr hc hrip hL
    rw [if_neg (by omega)] at hu
    obtain ⟨f', v, a', r', c', l', hv⟩ := ih (k + 1) u (by omega) r c hu l
    exact ⟨f + f', v, a.trans a', r', c', l', hv⟩


theorem keystream_byte (mixed init : Vector UInt32 16) (w : Nat) (hw : w < 16) (b : Nat)
    (hb : b < 4) :
    (keystream mixed init)[4 * w + b]'(by omega) = storedByte (mixed[w] + init[w]).toBitVec b := by
  have e1 : (4 * w + b) / 4 = w := by omega
  have e2 : (4 * w + b) % 4 = b := by omega
  simp only [keystream, serialize, Vector.getElem_ofFn, e1, e2]
  apply UInt8.toNat_inj.mp
  simp only [storedByte, UInt8.toNat_ofNat', UInt32.toNat_toUInt8, UInt32.toNat_shiftRight]
  have : (8 * b).toUInt32.toNat % 32 = 8 * b := by simp [Nat.toUInt32]; omega
  rw [this]
  rfl

theorem byte_of_load {m : Ram} {a : BitVec 64} {n : Nat} {v : BitVec n}
    (h : memLoad m a n = v) (b : Nat) (hb : b < n / 8) :
    memByte m (a + BitVec.ofNat 64 b) = storedByte v b := by
  rw [← storedByte_memLoad m a b hb, h]

theorem memByte_of_get {m : Ram} {a : BitVec 64} {v : UInt8} (h : m[a]? = some v) :
    memByte m a = v := by
  simp [memByte, PhysicalMemory.read, h]

theorem get_of_memByte {m : Ram} {a : BitVec 64} {v : UInt8} (hs : (m[a]?).isSome)
    (h : memByte m a = v) : m[a]? = some v := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
  simp only [memByte, PhysicalMemory.read, hc, Option.getD_some] at h
  rw [hc, h]

theorem add_ofNat_add (a : BitVec 64) (c d : Nat) :
    a + BitVec.ofNat 64 c + BitVec.ofNat 64 d = a + BitVec.ofNat 64 (c + d) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem within_self {c : Component} {cs : List Component} (h : c ∈ cs) : Within c cs :=
  ⟨fun _ => h, fun x hx => ⟨c, h, hx⟩⟩

theorem mem_allW (w : Fin 16) : w ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List (Fin 16)) := by
  revert w; decide

                                                                
theorem ks_bytes {m : Ram} {a : BitVec 64} {mixed init : Vector UInt32 16}
    (h : ∀ w : Fin 16, memLoad m (a + BitVec.ofNat 64 (0xf0 + 4 * w.val)) 32 =
      (mixed[w] + init[w]).toBitVec) (i : Fin 64) :
    memByte m (a + BitVec.ofNat 64 (0xf0 + i.val)) = (keystream mixed init)[i] := by
  have hw : i.val / 4 < 16 := by omega
  have e := byte_of_load (h ⟨i.val / 4, hw⟩) (i.val % 4) (by omega)
  rw [add_ofNat_add, show 0xf0 + 4 * (i.val / 4) + i.val % 4 = 0xf0 + i.val by omega] at e
  rw [e]
  have k := keystream_byte mixed init (i.val / 4) hw (i.val % 4) (by omega)
  simp only [show 4 * (i.val / 4) + i.val % 4 = i.val by omega] at k
  exact k.symm

                                    
theorem copy_bytes {m m' : Ram} {a b : BitVec 64} {ca cb : Nat}
    (h : ∀ k < 8, memLoad m (a + BitVec.ofNat 64 (ca + 8 * k)) 64 =
      memLoad m' (b + BitVec.ofNat 64 (cb + 8 * k)) 64) (i : Nat) (hi : i < 64) :
    memByte m (a + BitVec.ofNat 64 (ca + i)) = memByte m' (b + BitVec.ofNat 64 (cb + i)) := by
  have e := memByte_of_memLoad_eq (h (i / 8) (by omega)) (i % 8) (by omega)
  rw [add_ofNat_add, add_ofNat_add, show ca + 8 * (i / 8) + i % 8 = ca + i by omega,
    show cb + 8 * (i / 8) + i % 8 = cb + i by omega] at e
  exact e



def ffABytes : List UInt8 := [0x44, 0x8b, 0x54, 0x24, 0x38, 0x44, 0x01, 0xd5, 0x89, 0xac, 0x24, 0x00, 0x01, 0x00, 0x00, 0x03, 0x4c, 0x24, 0x34, 0x89, 0x8c, 0x24, 0x04, 0x01, 0x00, 0x00, 0x03, 0x54, 0x24, 0x30, 0x89, 0x94, 0x24, 0x08, 0x01, 0x00, 0x00, 0x44, 0x03, 0x5c, 0x24, 0x2c, 0x44, 0x89, 0x9c, 0x24, 0x0c, 0x01, 0x00, 0x00, 0x44, 0x8b, 0x9c, 0x24, 0x84, 0x00, 0x00, 0x00, 0x8b, 0x4c, 0x24, 0x04, 0x44, 0x01, 0xd9, 0x89, 0x8c, 0x24, 0x10, 0x01, 0x00, 0x00]

def ffBBytes : List UInt8 := [0x03, 0x44, 0x24, 0x28, 0x89, 0x84, 0x24, 0x14, 0x01, 0x00, 0x00, 0x03, 0x74, 0x24, 0x24, 0x89, 0xb4, 0x24, 0x18, 0x01, 0x00, 0x00, 0x44, 0x03, 0x44, 0x24, 0x20, 0x44, 0x89, 0x84, 0x24, 0x1c, 0x01, 0x00, 0x00, 0x44, 0x8b, 0x64, 0x24, 0x3c, 0x45, 0x01, 0xe1, 0x44, 0x89, 0x8c, 0x24, 0x20, 0x01, 0x00, 0x00, 0x44, 0x8b, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x44, 0x01, 0xc7, 0x44, 0x03, 0x74, 0x24, 0x1c, 0x44, 0x03, 0x7c, 0x24, 0x18, 0x89, 0xbc, 0x24, 0x24, 0x01, 0x00, 0x00, 0x44, 0x89, 0xb4, 0x24, 0x28, 0x01, 0x00, 0x00, 0x44, 0x89, 0xbc, 0x24, 0x2c, 0x01, 0x00, 0x00]

def mrB : List (Fin 16 × BitVec 5) :=
  [(4, 5), (5, 1), (6, 2), (7, 11), (9, 0), (10, 6), (11, 8), (12, 9), (13, 7), (14, 14), (15, 15)]

def mrC : List (Fin 16 × BitVec 5) := [(9, 0), (10, 6), (11, 8), (12, 9), (13, 7), (14, 14), (15, 15)]

def ksC : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

def irB : List (Fin 16 × BitVec 5) := [(4, 10), (8, 11)]

def irA : List (Fin 16 × BitVec 5) := [(4, 10), (8, 11), (12, 12), (13, 8)]

def allW : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

theorem rexB68 : rexB (UInt8.toBitVec 68) = 0 := by decide
theorem rexB69 : rexB (UInt8.toBitVec 69) = 1 := by decide
theorem rexB72 : rexB (UInt8.toBitVec 72) = 0 := by decide
theorem rexB65 : rexB (UInt8.toBitVec 65) = 1 := by decide
theorem rm213 : modrmRm 213 = 5 := by decide
theorem rm217 : modrmRm 217 = 1 := by decide
theorem rm225 : modrmRm 225 = 1 := by decide
theorem rm199 : modrmRm 199 = 7 := by decide
theorem rm193 : modrmRm 193 = 1 := by decide
theorem rm196 : modrmRm 196 = 4 := by decide
theorem rm224 : modrmRm 224 = 0 := by decide

macro "gpr_norm" : tactic => `(tactic| (
  simp only [rexB68, rexB69, rexB72, rexB65, rexR44, rexR45, rexR48, rexR40, rexR41, rm213, rm217,
    rm225, rm199, rm193, rm196, rm224, gprNumber, BitVec.reduceToNat, Nat.reduceShiftLeft,
    Nat.reduceAdd, BitVec.reduceOfNat, Nat.reduceMod]))

macro "sw_norm" : tactic => `(tactic| (
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    UInt32.toBitVec_add]))

theorem within_stack {t0 : RamState} {outBase : BitVec 64} {j : Nat} {c : BitVec 64} {n : Nat}
    (h1 : 0xb0 ≤ c.toNat) (h2 : c.toNat + n ≤ 0x170) :
    Within (.mem ((Operand.reg 4 : Operand 64).read t0 + c) n) (changes t0 outBase j) := by
  rw [← stackPtr_eq_read, show c = BitVec.ofNat 64 c.toNat by simp]
  exact within_mem (lo := 0xb0) (len := 0xc0) (by unfold changes slot scratchOff scratchBytes; simp)
    (by simpa using h1) (by simp; omega) (by omega)

theorem in_nc {t0 : RamState} {mixed init : Vector UInt32 16} {j : Nat} {inBase outBase : BitVec 64}
    {block : Vector UInt8 64} (h0 : FeedPre mixed init j inBase outBase block t0) {c : BitVec 64}
    {n : Nat} (hc : c.toNat + n ≤ 0x170) {i : Nat} (hi : i < 64) :
    ¬ (Component.mem ((Operand.reg 4 : Operand 64).read t0 + c) n).Covers
      (inBlock inBase j + BitVec.ofNat 64 i) := by
  rw [← stackPtr_eq_read, show c = BitVec.ofNat 64 c.toNat by simp]
  exact apart_not_covers h0.blocks.inStack _ _ hc i hi

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem ffRunA [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < codeLo ∨ codeHi < boundary.rip.toNat)
    {t0 : RamState} {mixed init : Vector UInt32 16} {j : Nat} {inBase outBase : BitVec 64}
    {block : Vector UInt8 64} (h0 : FeedPre mixed init j inBase outBase block t0) :
    AdvancesTo boundary (fun s => s.RIP = 0x100e4b ∧ XF (stackPtr t0) s ∧
      FeedA t0 s 0x100e4b mixed init j inBase outBase block mrB [0, 1, 2, 3] [])
      (codeRange 0x100e4b ffABytes)
      (fun _ u => FeedA t0 u 0x100e93 mixed init j inBase outBase block mrC ksC irB) := by
  refine advancesTo_of_block (E := ?E) ?blk ?imp
  case blk =>
    unfold ffABytes
    xb_begin (mov_r32_m32_effect_step 0x100e4b 0x44 (by unfold RexNoWPrefix; decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (add_r32_r32_rex_effect_step 0x100e50 0x44 0xd5 (by unfold RexNoWPrefix; decide) (by decide)) using xs_stack
    xb_then (mov_m32_r32_low_effect_step 0x100e53 5 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (add_r32_m32_effect_step 0x100e5a 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (mov_m32_r32_low_effect_step 0x100e5e 1 (.sib 4 none 0 (.d32 0x104)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (add_r32_m32_effect_step 0x100e65 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (mov_m32_r32_low_effect_step 0x100e69 2 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (add_r32_m32_rex_effect_step 0x100e70 0x44 (by unfold RexNoWPrefix; decide) 3 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (mov_m32_r32_effect_step 0x100e75 0x44 (by unfold RexNoWPrefix; decide) 3 (.sib 4 none 0 (.d32 0x10c)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (mov_r32_m32_effect_step 0x100e7d 0x44 (by unfold RexNoWPrefix; decide) 3 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (mov_r32_m32_low_effect_step 0x100e85 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (add_r32_r32_rex_effect_step 0x100e89 0x44 0xd9 (by unfold RexNoWPrefix; decide) (by decide)) using xs_stack
    xb_then (mov_m32_r32_low_effect_step 0x100e8c 1 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) using xs_stack
    exact id
  case imp =>
    intro s u hP hH
    obtain ⟨hrip, hx, hF⟩ := hP
    have hfull : ∀ w ∈ (?E s).writes, w.Full := by
      simp (config := { decide := true }) only [x86_compose, List.forall_mem_cons,
        List.forall_mem_nil, List.forall_mem_append, and_true, true_and]
    have ho := hH.obsAfter hfull true
    have hag := hH.agrees
    have h4 := hx.rsp
    x86_norm at hag h4
    have mr := hF.mregs
    have kw := hF.ks
    have iv := hF.initv h0
    have ir := hF.iregs
    have m8 := hF.mixed8 h0
    simp only [mrB, mrC, ksC, irB, initSlot, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, reg32, reg64, slot32, slot, stackPtr_eq_read, false_imp_iff,
      implies_true, and_true] at mr kw iv ir m8
    x86_norm at mr kw iv ir m8
    have k0 : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 240) : Operand 32).read s =
        (mixed[0] + init[0]).toBitVec := by rw [hx.rsp]; exact hF.ks 0 (by decide)
    have k1 : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 244) : Operand 32).read s =
        (mixed[1] + init[1]).toBitVec := by rw [hx.rsp]; exact hF.ks 1 (by decide)
    have k2 : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 248) : Operand 32).read s =
        (mixed[2] + init[2]).toBitVec := by rw [hx.rsp]; exact hF.ks 2 (by decide)
    have k3 : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 252) : Operand 32).read s =
        (mixed[3] + init[3]).toBitVec := by rw [hx.rsp]; exact hF.ks 3 (by decide)
    x86_norm at k0 k1 k2 k3
    refine ⟨hH.rip.trans (by x86_norm), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [stackPtr_eq_read, ← ho.read_reg, stackPtr_eq_read t0]; x86_norm; exact h4
    · refine widen_trans hF.agrees hag ?_
      simp only [List.forall_mem_cons]
      repeat' apply And.intro
      all_goals first
        | (intro x hx; simp at hx)
        | exact within_reg (by simp (config := {decide := true}) [changes])
        | exact within_flags (by simp [changes])
        | exact within_rip (by simp [changes])
        | (rw [h4]; exact within_stack (by decide) (by decide))
    · simp only [mrB, mrC, List.forall_mem_cons, List.forall_mem_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_imp_iff, implies_true, and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (unfold reg32; rw [← ho.read_reg]; x86_norm; (try gpr_norm); x86_norm [mr])
    · simp only [ksC, allW, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 240) : Operand 32).read u =
          (mixed[0] + init[0]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 244) : Operand 32).read u =
          (mixed[1] + init[1]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 248) : Operand 32).read u =
          (mixed[2] + init[2]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 252) : Operand 32).read u =
          (mixed[3] + init[3]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 256) : Operand 32).read u =
          (mixed[4] + init[4]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 260) : Operand 32).read u =
          (mixed[5] + init[5]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 264) : Operand 32).read u =
          (mixed[6] + init[6]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 268) : Operand 32).read u =
          (mixed[7] + init[7]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 272) : Operand 32).read u =
          (mixed[8] + init[8]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3,  m8]
        try sw_norm
        try rfl
    · simp only [irA, irB, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_imp_iff, implies_true]
      refine ⟨?_, ?_⟩
      all_goals (unfold reg64; rw [← ho.read_reg]; x86_norm; (try gpr_norm); x86_norm [iv]; (try sw_norm))
    · intro i
      refine (hag.byte fun c hc hcov => ?_).trans (hF.input i)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      repeat' (rcases hc with rfl | hc)
      all_goals first
        | (simp [Component.Covers] at hcov; done)
        | (rw [h4] at hcov; exact in_nc h0 (by decide) i.isLt hcov)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem ffRunB [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < codeLo ∨ codeHi < boundary.rip.toNat)
    {t0 : RamState} {mixed init : Vector UInt32 16} {j : Nat} {inBase outBase : BitVec 64}
    {block : Vector UInt8 64} (h0 : FeedPre mixed init j inBase outBase block t0) :
    AdvancesTo boundary (fun s => s.RIP = 0x100e93 ∧ XF (stackPtr t0) s ∧
      FeedA t0 s 0x100e93 mixed init j inBase outBase block mrC ksC irB)
      (codeRange 0x100e93 ffBBytes)
      (fun _ u => FeedA t0 u 0x100ef2 mixed init j inBase outBase block [] allW irA) := by
  refine advancesTo_of_block (E := ?E) ?blk ?imp
  case blk =>
    unfold ffBBytes
    xb_begin (add_r32_m32_effect_step 0x100e93 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (mov_m32_r32_low_effect_step 0x100e97 0 (.sib 4 none 0 (.d32 0x114)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (add_r32_m32_effect_step 0x100e9e 6 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (mov_m32_r32_low_effect_step 0x100ea2 6 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (add_r32_m32_rex_effect_step 0x100ea9 0x44 (by unfold RexNoWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (mov_m32_r32_effect_step 0x100eae 0x44 (by unfold RexNoWPrefix; decide) 0 (.sib 4 none 0 (.d32 0x11c)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (mov_r32_m32_effect_step 0x100eb6 0x44 (by unfold RexNoWPrefix; decide) 4 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (add_r32_r32_rex_effect_step 0x100ebb 0x45 0xe1 (by unfold RexNoWPrefix; decide) (by decide)) using xs_stack
    xb_then (mov_m32_r32_effect_step 0x100ebe 0x44 (by unfold RexNoWPrefix; decide) 1 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (mov_r32_m32_effect_step 0x100ec6 0x44 (by unfold RexNoWPrefix; decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (add_r32_r32_rex_effect_step 0x100ece 0x44 0xc7 (by unfold RexNoWPrefix; decide) (by decide)) using xs_stack
    xb_then (add_r32_m32_rex_effect_step 0x100ed1 0x44 (by unfold RexNoWPrefix; decide) 6 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (add_r32_m32_rex_effect_step 0x100ed6 0x44 (by unfold RexNoWPrefix; decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (mov_m32_r32_low_effect_step 0x100edb 7 (.sib 4 none 0 (.d32 0x124)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (mov_m32_r32_effect_step 0x100ee2 0x44 (by unfold RexNoWPrefix; decide) 6 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) using xs_stack
    xb_then (mov_m32_r32_effect_step 0x100eea 0x44 (by unfold RexNoWPrefix; decide) 7 (.sib 4 none 0 (.d32 0x12c)) (by decide) (by decide) (by decide)) using xs_stack
    exact id
  case imp =>
    intro s u hP hH
    obtain ⟨hrip, hx, hF⟩ := hP
    have hfull : ∀ w ∈ (?E s).writes, w.Full := by
      simp (config := { decide := true }) only [x86_compose, List.forall_mem_cons,
        List.forall_mem_nil, List.forall_mem_append, and_true, true_and]
    have ho := hH.obsAfter hfull true
    have hag := hH.agrees
    have h4 := hx.rsp
    x86_norm at hag h4
    have mr := hF.mregs
    have kw := hF.ks
    have iv := hF.initv h0
    have ir := hF.iregs
    have m8 := hF.mixed8 h0
    simp only [mrB, mrC, ksC, irB, initSlot, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, reg32, reg64, slot32, slot, stackPtr_eq_read, false_imp_iff,
      implies_true, and_true] at mr kw iv ir m8
    x86_norm at mr kw iv ir m8
    have k0 : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 240) : Operand 32).read s =
        (mixed[0] + init[0]).toBitVec := by rw [hx.rsp]; exact hF.ks 0 (by decide)
    have k1 : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 244) : Operand 32).read s =
        (mixed[1] + init[1]).toBitVec := by rw [hx.rsp]; exact hF.ks 1 (by decide)
    have k2 : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 248) : Operand 32).read s =
        (mixed[2] + init[2]).toBitVec := by rw [hx.rsp]; exact hF.ks 2 (by decide)
    have k3 : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 252) : Operand 32).read s =
        (mixed[3] + init[3]).toBitVec := by rw [hx.rsp]; exact hF.ks 3 (by decide)
    have k4 : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 256) : Operand 32).read s =
        (mixed[4] + init[4]).toBitVec := by rw [hx.rsp]; exact hF.ks 4 (by decide)
    have k5 : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 260) : Operand 32).read s =
        (mixed[5] + init[5]).toBitVec := by rw [hx.rsp]; exact hF.ks 5 (by decide)
    have k6 : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 264) : Operand 32).read s =
        (mixed[6] + init[6]).toBitVec := by rw [hx.rsp]; exact hF.ks 6 (by decide)
    have k7 : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 268) : Operand 32).read s =
        (mixed[7] + init[7]).toBitVec := by rw [hx.rsp]; exact hF.ks 7 (by decide)
    have k8 : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 272) : Operand 32).read s =
        (mixed[8] + init[8]).toBitVec := by rw [hx.rsp]; exact hF.ks 8 (by decide)
    x86_norm at k0 k1 k2 k3 k4 k5 k6 k7 k8
    refine ⟨hH.rip.trans (by x86_norm), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [stackPtr_eq_read, ← ho.read_reg, stackPtr_eq_read t0]; x86_norm; exact h4
    · refine widen_trans hF.agrees hag ?_
      simp only [List.forall_mem_cons]
      repeat' apply And.intro
      all_goals first
        | (intro x hx; simp at hx)
        | exact within_reg (by simp (config := {decide := true}) [changes])
        | exact within_flags (by simp [changes])
        | exact within_rip (by simp [changes])
        | (rw [h4]; exact within_stack (by decide) (by decide))
    · simp only [mrB, mrC, List.forall_mem_cons, List.forall_mem_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_imp_iff, implies_true, and_true]
    · simp only [ksC, allW, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 240) : Operand 32).read u =
          (mixed[0] + init[0]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 244) : Operand 32).read u =
          (mixed[1] + init[1]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 248) : Operand 32).read u =
          (mixed[2] + init[2]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 252) : Operand 32).read u =
          (mixed[3] + init[3]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 256) : Operand 32).read u =
          (mixed[4] + init[4]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 260) : Operand 32).read u =
          (mixed[5] + init[5]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 264) : Operand 32).read u =
          (mixed[6] + init[6]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 268) : Operand 32).read u =
          (mixed[7] + init[7]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 272) : Operand 32).read u =
          (mixed[8] + init[8]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 276) : Operand 32).read u =
          (mixed[9] + init[9]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 280) : Operand 32).read u =
          (mixed[10] + init[10]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 284) : Operand 32).read u =
          (mixed[11] + init[11]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 288) : Operand 32).read u =
          (mixed[12] + init[12]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 292) : Operand 32).read u =
          (mixed[13] + init[13]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 296) : Operand 32).read u =
          (mixed[14] + init[14]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
      · rw [← hx.rsp]
        show (Operand.mem ((Operand.reg 4 : Operand 64).read s + 300) : Operand 32).read u =
          (mixed[15] + init[15]).toBitVec
        rw [← ho.read_mem]
        x86_norm
        try gpr_norm
        x86_norm [mr, iv, k0, k1, k2, k3, k4, k5, k6, k7, k8,  m8]
        try sw_norm
        try rfl
    · simp only [irA, irB, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_imp_iff, implies_true]
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals (unfold reg64; rw [← ho.read_reg]; x86_norm; (try gpr_norm); x86_norm [iv, ir]; (try sw_norm))
    · intro i
      refine (hag.byte fun c hc hcov => ?_).trans (hF.input i)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      repeat' (rcases hc with rfl | hc)
      all_goals first
        | (simp [Component.Covers] at hcov; done)
        | (rw [h4] at hcov; exact in_nc h0 (by decide) i.isLt hcov)



theorem shl6 (j : Nat) (h : 64 * j < 2 ^ 64) :
    BitVec.ofNat 64 j <<< shiftCount 64 (UInt8.toBitVec 6) = BitVec.ofNat 64 (64 * j) := by
  rw [show shiftCount 64 (UInt8.toBitVec 6) = 6 from by decide]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem rd_slice {s : RamState} {a : BitVec 64} {n : Nat} (h : MemReadable s a n)
    (c : BitVec 64) (len : Nat) (hc : c.toNat + len ≤ n) : MemReadable s (a + c) len := by
  have hl := h.low
  refine ⟨?_, fun i hi => ?_⟩
  · rw [BitVec.toNat_add]; omega
  · have he : a + c + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (c.toNat + i) := by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [he]; exact h.mem _ (by omega)

theorem add0 (x : BitVec 64) : x + 0 = x := by simp

                                                                             
structure BX (inBase : BitVec 64) (j : Nat) (s : RamState) : Prop where
  idx : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x70) : Operand 64).read s =
    BitVec.ofNat 64 j
  inp : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x68) : Operand 64).read s = inBase
  low : inBase.toNat + 64 * j + 64 ≤ 2 ^ 32
  rd : MemReadable s (inBlock inBase j) 64

theorem BX.addr {inBase : BitVec 64} {j : Nat} {s : RamState} (he : BX inBase j s) (c : BitVec 64) :
    (Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x68) : Operand 64).read s +
      ((Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x70) : Operand 64).read s <<<
        shiftCount 64 (UInt8.toBitVec 6) <<< 0 + c) = inBlock inBase j + c := by
  have := he.low
  rw [he.inp, he.idx, shl6 j (by omega), BitVec.shiftLeft_zero, ← BitVec.add_assoc]; rfl

theorem BX.addr0 {inBase : BitVec 64} {j : Nat} {s : RamState} (he : BX inBase j s) :
    (Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x68) : Operand 64).read s +
      (Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x70) : Operand 64).read s <<<
        shiftCount 64 (UInt8.toBitVec 6) <<< 0 = inBlock inBase j + 0 := by
  have := he.addr 0
  simp only [add0] at this ⊢
  exact this

theorem BX.rdc {inBase : BitVec 64} {j : Nat} {s : RamState} (he : BX inBase j s)
    {c : BitVec 64} {n : Nat} (hc : c.toNat + n ≤ 64) :
    MemReadable s ((Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x68) : Operand 64).read s +
      ((Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x70) : Operand 64).read s <<<
        shiftCount 64 (UInt8.toBitVec 6) <<< 0 + c)) n := by
  rw [he.addr]; exact rd_slice he.rd c n hc

theorem BX.rd0 {inBase : BitVec 64} {j : Nat} {s : RamState} (he : BX inBase j s) {n : Nat}
    (hc : n ≤ 64) :
    MemReadable s ((Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x68) : Operand 64).read s +
      (Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x70) : Operand 64).read s <<<
        shiftCount 64 (UInt8.toBitVec 6) <<< 0) n := by
  rw [he.addr0]; exact rd_slice he.rd 0 n (by simpa using hc)

macro "xs_in" : tactic => `(tactic| (
  try x86_norm
  first
  | exact XF.rd (by assumption) (by decide)
  | exact XF.wrt (by assumption) (by decide)
  | exact XF.ap (by assumption) (by decide) _ _ (by decide) (by decide)
  | exact BX.rdc (by assumption) (by decide)
  | exact BX.rd0 (by assumption) (by decide)))

theorem ia {sp inBase : BitVec 64} {j : Nat} {s : RamState} (hx : XF sp s) (he : BX inBase j s)
    (hap : RangeApart (inBlock inBase j) 64 sp 0x170) (mem : Ram) (c₁ c₂ : BitVec 64)
    (v : BitVec 64) (h1 : c₁.toNat + 8 ≤ 0x170) (h2 : c₂.toNat + 8 ≤ 64) :
    memLoad (memStore mem ((Operand.reg 4 : Operand 64).read s + c₁) v)
      ((Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x68) : Operand 64).read s +
        ((Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x70) : Operand 64).read s <<<
          shiftCount 64 (UInt8.toBitVec 6) <<< 0 + c₂)) 64 =
    memLoad mem
      ((Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x68) : Operand 64).read s +
        ((Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x70) : Operand 64).read s <<<
          shiftCount 64 (UInt8.toBitVec 6) <<< 0 + c₂)) 64 := by
  rw [he.addr, hx.rsp]
  apply memLoad_memStore_of_rangeApart
  have hl := hx.wr.low
  have h := fr_apart hap c₂ 8 h2 8 (q := sp + c₁) (by rw [BitVec.toNat_add]; omega)
    (by rw [BitVec.toNat_add]; omega)
  exact fun i hi k hk e => h k hk i hi e.symm

theorem ia0 {sp inBase : BitVec 64} {j : Nat} {s : RamState} (hx : XF sp s) (he : BX inBase j s)
    (hap : RangeApart (inBlock inBase j) 64 sp 0x170) (mem : Ram) (c₁ : BitVec 64)
    (v : BitVec 64) (h1 : c₁.toNat + 8 ≤ 0x170) :
    memLoad (memStore mem ((Operand.reg 4 : Operand 64).read s + c₁) v)
      ((Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x68) : Operand 64).read s +
        (Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x70) : Operand 64).read s <<<
          shiftCount 64 (UInt8.toBitVec 6) <<< 0) 64 =
    memLoad mem
      ((Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x68) : Operand 64).read s +
        (Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x70) : Operand 64).read s <<<
          shiftCount 64 (UInt8.toBitVec 6) <<< 0) 64 := by
  have := ia hx he hap mem c₁ 0 v h1 (by decide)
  simpa using this

                                                                         
structure CX (inBase : BitVec 64) (j : Nat) (s : RamState) : Prop where
  rax : (Operand.reg 0 : Operand 64).read s = BitVec.ofNat 64 (64 * j)
  rdx : (Operand.reg 2 : Operand 64).read s = inBase
  rd : MemReadable s (inBlock inBase j) 64

theorem CX.addr {inBase : BitVec 64} {j : Nat} {s : RamState} (he : CX inBase j s) (c : BitVec 64) :
    (Operand.reg 2 : Operand 64).read s + ((Operand.reg 0 : Operand 64).read s <<< 0 + c) =
      inBlock inBase j + c := by
  rw [he.rax, he.rdx, BitVec.shiftLeft_zero, ← BitVec.add_assoc]; rfl

theorem CX.rdc {inBase : BitVec 64} {j : Nat} {s : RamState} (he : CX inBase j s)
    {c : BitVec 64} {n : Nat} (hc : c.toNat + n ≤ 64) :
    MemReadable s ((Operand.reg 2 : Operand 64).read s + ((Operand.reg 0 : Operand 64).read s <<< 0 + c)) n := by
  rw [he.addr]; exact rd_slice he.rd c n hc

theorem CX.rd0 {inBase : BitVec 64} {j : Nat} {s : RamState} (he : CX inBase j s) {n : Nat}
    (hc : n ≤ 64) :
    MemReadable s ((Operand.reg 2 : Operand 64).read s + (Operand.reg 0 : Operand 64).read s <<< 0) n := by
  have := he.rdc (c := 0) (n := n) (by simpa using hc)
  simp only [add0] at this
  exact this

theorem ca {sp inBase : BitVec 64} {j : Nat} {s : RamState} (hx : XF sp s) (he : CX inBase j s)
    (hap : RangeApart (inBlock inBase j) 64 sp 0x170) (mem : Ram) (c₁ c₂ : BitVec 64)
    (v : BitVec 64) (h1 : c₁.toNat + 8 ≤ 0x170) (h2 : c₂.toNat + 8 ≤ 64) :
    memLoad (memStore mem ((Operand.reg 4 : Operand 64).read s + c₁) v)
      ((Operand.reg 2 : Operand 64).read s + ((Operand.reg 0 : Operand 64).read s <<< 0 + c₂)) 64 =
    memLoad mem
      ((Operand.reg 2 : Operand 64).read s + ((Operand.reg 0 : Operand 64).read s <<< 0 + c₂)) 64 := by
  rw [he.addr, hx.rsp]
  apply memLoad_memStore_of_rangeApart
  have hl := hx.wr.low
  have h := fr_apart hap c₂ 8 h2 8 (q := sp + c₁) (by rw [BitVec.toNat_add]; omega)
    (by rw [BitVec.toNat_add]; omega)
  exact fun i hi k hk e => h k hk i hi e.symm

theorem ca0 {sp inBase : BitVec 64} {j : Nat} {s : RamState} (hx : XF sp s) (he : CX inBase j s)
    (hap : RangeApart (inBlock inBase j) 64 sp 0x170) (mem : Ram) (c₁ : BitVec 64)
    (v : BitVec 64) (h1 : c₁.toNat + 8 ≤ 0x170) :
    memLoad (memStore mem ((Operand.reg 4 : Operand 64).read s + c₁) v)
      ((Operand.reg 2 : Operand 64).read s + (Operand.reg 0 : Operand 64).read s <<< 0) 64 =
    memLoad mem
      ((Operand.reg 2 : Operand 64).read s + (Operand.reg 0 : Operand 64).read s <<< 0) 64 := by
  have := ca hx he hap mem c₁ 0 v h1 (by decide)
  simp only [add0] at this
  exact this

macro "xs_cx" : tactic => `(tactic| (
  try x86_norm
  first
  | exact XF.rd (by assumption) (by decide)
  | exact XF.wrt (by assumption) (by decide)
  | exact XF.ap (by assumption) (by decide) _ _ (by decide) (by decide)
  | exact CX.rdc (by assumption) (by decide)
  | exact CX.rd0 (by assumption) (by decide)))

structure BC1Q (sp inBase : BitVec 64) (j : Nat) (s u : RamState) : Prop where
  rip : u.RIP = 0x100f37
  agrees : AgreesExcept [.reg 7, .reg 0, .reg 2, .reg 1, .flags, .rip,
    .mem (sp + BitVec.ofNat 64 0x150) 0x20] s u
  rdi : reg64 u 7 = BitVec.ofNat 64 j
  rax : reg64 u 0 = BitVec.ofNat 64 (64 * j)
  rdx : reg64 u 2 = inBase
  words : ∀ m, 4 ≤ m → m < 8 → memLoad u.external (sp + BitVec.ofNat 64 (0x130 + 8 * m)) 64 =
    memLoad s.external (inBlock inBase j + BitVec.ofNat 64 (0 + 8 * m)) 64

structure BC2Q (sp inBase : BitVec 64) (j : Nat) (s u : RamState) : Prop where
  rip : u.RIP = 0x100f6a
  agrees : AgreesExcept [.reg 1, .reg 2, .rip, .mem (sp + BitVec.ofNat 64 0x130) 0x20] s u
  words : ∀ m < 4, memLoad u.external (sp + BitVec.ofNat 64 (0x130 + 8 * m)) 64 =
    memLoad s.external (inBlock inBase j + BitVec.ofNat 64 (0 + 8 * m)) 64

structure BC3Q (sp : BitVec 64) (s u : RamState) : Prop where
  rip : u.RIP = 0x100fcf
  agrees : AgreesExcept [.reg 1, .rip, .mem (sp + BitVec.ofNat 64 0xb0) 0x40] s u
  rcx : reg64 u 1 = 3

def bc1Bytes : List UInt8 := [0x48, 0x8b, 0x7c, 0x24, 0x70, 0x48, 0x89, 0xf8, 0x48, 0xc1, 0xe0, 0x06, 0x48, 0x8b, 0x54, 0x24, 0x68, 0x48, 0x8b, 0x4c, 0x02, 0x38, 0x48, 0x89, 0x8c, 0x24, 0x68, 0x01, 0x00, 0x00, 0x48, 0x8b, 0x4c, 0x02, 0x30, 0x48, 0x89, 0x8c, 0x24, 0x60, 0x01, 0x00, 0x00, 0x48, 0x8b, 0x4c, 0x02, 0x28, 0x48, 0x89, 0x8c, 0x24, 0x58, 0x01, 0x00, 0x00, 0x48, 0x8b, 0x4c, 0x02, 0x20, 0x48, 0x89, 0x8c, 0x24, 0x50, 0x01, 0x00, 0x00]

def bc2Bytes : List UInt8 := [0x48, 0x8b, 0x4c, 0x02, 0x18, 0x48, 0x89, 0x8c, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0x8b, 0x4c, 0x02, 0x10, 0x48, 0x89, 0x8c, 0x24, 0x40, 0x01, 0x00, 0x00, 0x48, 0x8b, 0x0c, 0x02, 0x48, 0x8b, 0x54, 0x02, 0x08, 0x48, 0x89, 0x94, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0x89, 0x8c, 0x24, 0x30, 0x01, 0x00, 0x00]

def bc3Bytes : List UInt8 := [0x48, 0xc7, 0x84, 0x24, 0xe8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0xe0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0xd8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0xd0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0xc8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0xb8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0xb0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb9, 0x03, 0x00, 0x00, 0x00]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem bc1Run [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < codeLo ∨ codeHi < boundary.rip.toNat) (sp inBase : BitVec 64)
    (j : Nat) (hap : RangeApart (inBlock inBase j) 64 sp 0x170) :
    AdvancesTo boundary (fun s => s.RIP = 0x100ef2 ∧ XF sp s ∧ BX inBase j s)
      (codeRange 0x100ef2 bc1Bytes) (BC1Q sp inBase j) := by
  refine advancesTo_of_block (E := ?E) ?blk ?imp
  case blk =>
    unfold bc1Bytes
    xb_begin (mov_r64_m64_effect_step 0x100ef2 0x48 (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) using xs_in
    xb_then (mov_r64_r64_effect_step 0x100ef7 0x48 0xf8 (by unfold RexWPrefix; decide) (by decide)) using xs_in
    xb_then (shl_r64_imm8_effect_step 0x100efa 0x48 0xe0 0x06 (by unfold RexWPrefix; decide) (by decide) (by decide)) using xs_in
    xb_then (mov_r64_m64_effect_step 0x100efe 0x48 (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) using xs_in
    xb_then (mov_r64_m64_effect_step 0x100f03 0x48 (by unfold RexWPrefix; decide) 1 (.sib 2 (some 0) 0 (.d8 0x38)) (by decide) (by decide) (by decide)) using xs_in
    xb_then (mov_m64_r64_effect_step 0x100f08 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide)) using xs_in
    xb_then (mov_r64_m64_effect_step 0x100f10 0x48 (by unfold RexWPrefix; decide) 1 (.sib 2 (some 0) 0 (.d8 0x30)) (by decide) (by decide) (by decide)) using xs_in
    xb_then (mov_m64_r64_effect_step 0x100f15 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) using xs_in
    xb_then (mov_r64_m64_effect_step 0x100f1d 0x48 (by unfold RexWPrefix; decide) 1 (.sib 2 (some 0) 0 (.d8 0x28)) (by decide) (by decide) (by decide)) using xs_in
    xb_then (mov_m64_r64_effect_step 0x100f22 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) using xs_in
    xb_then (mov_r64_m64_effect_step 0x100f2a 0x48 (by unfold RexWPrefix; decide) 1 (.sib 2 (some 0) 0 (.d8 0x20)) (by decide) (by decide) (by decide)) using xs_in
    xb_then (mov_m64_r64_effect_step 0x100f2f 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) using xs_in
    exact id
  case imp =>
    intro s u hP hH
    obtain ⟨hrip, hx, he⟩ := hP
    have hfull : ∀ w ∈ (?E s).writes, w.Full := by
      simp (config := { decide := true }) only [x86_compose, List.forall_mem_cons,
        List.forall_mem_nil, List.forall_mem_append, and_true, true_and]
    have ho := hH.obsAfter hfull true
    have hag := hH.agrees
    have h4 := hx.rsp
    x86_norm at hag h4
    have hl := he.low
    refine ⟨hH.rip.trans (by x86_norm), ?_, ?_, ?_, ?_, ?_⟩
    · refine agrees_widen hag ?_
      simp only [List.forall_mem_cons]
      repeat' apply And.intro
      all_goals first
        | (intro x hx; simp at hx)
        | exact within_reg (by simp (config := {decide := true}))
        | exact within_flags (by simp)
        | exact within_rip (by simp)
        | (rw [h4]; exact within_mem (a := sp) (lo := 0x150) (len := 0x20) (by simp) (by decide) (by decide) (by decide))
    · unfold reg64; rw [← ho.read_reg]; x86_norm
      exact he.idx
    · unfold reg64; rw [← ho.read_reg]; x86_norm
      have hi := he.idx
      x86_norm at hi
      rw [hi]; exact shl6 j (by omega)
    · unfold reg64; rw [← ho.read_reg]; x86_norm
      exact he.inp
    · intro m hm1 hm2
      have hia := ia hx he hap
      have hea := he.addr
      x86_norm at hia hea
      rw [← hea, ← h4]
      change (Operand.mem _ : Operand 64).read u = (Operand.mem _ : Operand 64).read s
      rw [← ho.read_mem]
      rcases (by omega : m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7) with rfl | rfl | rfl | rfl
      all_goals
        x86_norm [hia]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem bc2Run [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < codeLo ∨ codeHi < boundary.rip.toNat) (sp inBase : BitVec 64)
    (j : Nat) (hap : RangeApart (inBlock inBase j) 64 sp 0x170) :
    AdvancesTo boundary (fun s => s.RIP = 0x100f37 ∧ XF sp s ∧ CX inBase j s)
      (codeRange 0x100f37 bc2Bytes) (BC2Q sp inBase j) := by
  refine advancesTo_of_block (E := ?E) ?blk ?imp
  case blk =>
    unfold bc2Bytes
    xb_begin (mov_r64_m64_effect_step 0x100f37 0x48 (by unfold RexWPrefix; decide) 1 (.sib 2 (some 0) 0 (.d8 0x18)) (by decide) (by decide) (by decide)) using xs_cx
    xb_then (mov_m64_r64_effect_step 0x100f3c 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) using xs_cx
    xb_then (mov_r64_m64_effect_step 0x100f44 0x48 (by unfold RexWPrefix; decide) 1 (.sib 2 (some 0) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) using xs_cx
    xb_then (mov_m64_r64_effect_step 0x100f49 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) using xs_cx
    xb_then (mov_r64_m64_effect_step 0x100f51 0x48 (by unfold RexWPrefix; decide) 1 (.sib 2 (some 0) 0 .none) (by decide) (by decide) (by decide)) using xs_cx
    xb_then (mov_r64_m64_effect_step 0x100f55 0x48 (by unfold RexWPrefix; decide) 2 (.sib 2 (some 0) 0 (.d8 0x08)) (by decide) (by decide) (by decide)) using xs_cx
    xb_then (mov_m64_r64_effect_step 0x100f5a 0x48 (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) using xs_cx
    xb_then (mov_m64_r64_effect_step 0x100f62 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) using xs_cx
    exact id
  case imp =>
    intro s u hP hH
    obtain ⟨hrip, hx, he⟩ := hP
    have hfull : ∀ w ∈ (?E s).writes, w.Full := by
      simp (config := { decide := true }) only [x86_compose, List.forall_mem_cons,
        List.forall_mem_nil, List.forall_mem_append, and_true, true_and]
    have ho := hH.obsAfter hfull true
    have hag := hH.agrees
    have h4 := hx.rsp
    x86_norm at hag h4
    refine ⟨hH.rip.trans (by x86_norm), ?_, ?_⟩
    · refine agrees_widen hag ?_
      simp only [List.forall_mem_cons]
      repeat' apply And.intro
      all_goals first
        | (intro x hx; simp at hx)
        | exact within_reg (by simp (config := {decide := true}))
        | exact within_flags (by simp)
        | exact within_rip (by simp)
        | (rw [h4]; exact within_mem (a := sp) (lo := 0x130) (len := 0x20) (by simp) (by decide) (by decide) (by decide))
    · intro m hm
      have hia := ca hx he hap
      have hia0 := ca0 hx he hap
      have hea := he.addr
      x86_norm at hia hia0 hea
      rw [← hea, ← h4]
      change (Operand.mem _ : Operand 64).read u = (Operand.mem _ : Operand 64).read s
      rw [← ho.read_mem]
      rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl
      all_goals
        x86_norm [hia, hia0]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem bc3Run [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < codeLo ∨ codeHi < boundary.rip.toNat) (sp : BitVec 64) :
    AdvancesTo boundary (fun s => s.RIP = 0x100f6a ∧ XF sp s ∧ True)
      (codeRange 0x100f6a bc3Bytes) (BC3Q sp) := by
  refine advancesTo_of_block (E := ?E) ?blk ?imp
  case blk =>
    unfold bc3Bytes
    xb_begin (mov_m64_imm32_effect_step 0x100f6a 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide) 0x0) using xs_stack
    xb_then (mov_m64_imm32_effect_step 0x100f76 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide) 0x0) using xs_stack
    xb_then (mov_m64_imm32_effect_step 0x100f82 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide) 0x0) using xs_stack
    xb_then (mov_m64_imm32_effect_step 0x100f8e 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide) 0x0) using xs_stack
    xb_then (mov_m64_imm32_effect_step 0x100f9a 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide) 0x0) using xs_stack
    xb_then (mov_m64_imm32_effect_step 0x100fa6 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide) 0x0) using xs_stack
    xb_then (mov_m64_imm32_effect_step 0x100fb2 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide) 0x0) using xs_stack
    xb_then (mov_m64_imm32_effect_step 0x100fbe 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide) 0x0) using xs_stack
    xb_then (mov_r32_imm32_effect_step 0x100fca 0xb9 (by decide) 3) using xs_stack
    exact id
  case imp =>
    intro s u hP hH
    obtain ⟨hrip, hx, he⟩ := hP
    have hfull : ∀ w ∈ (?E s).writes, w.Full := by
      simp (config := { decide := true }) only [x86_compose, List.forall_mem_cons,
        List.forall_mem_nil, List.forall_mem_append, and_true, true_and]
    have ho := hH.obsAfter hfull true
    have hag := hH.agrees
    have h4 := hx.rsp
    x86_norm at hag h4
    refine ⟨hH.rip.trans (by x86_norm), ?_, ?_⟩
    · refine agrees_widen hag ?_
      simp only [List.forall_mem_cons]
      repeat' apply And.intro
      all_goals first
        | (intro x hx; simp at hx)
        | exact within_reg (by simp (config := {decide := true}))
        | exact within_rip (by simp)
        | (rw [h4]; exact within_mem (a := sp) (lo := 0xb0) (len := 0x40) (by simp) (by decide) (by decide) (by decide))
    · unfold reg64; rw [← ho.read_reg]; x86_norm



theorem oa {sp outBase : BitVec 64} {j : Nat} {s : RamState} (hx : XF sp s) (he : EX outBase j s)
    (hap : RangeApart (outBlock outBase j) 64 sp 0x170) (mem : Ram) (c₁ c₂ : BitVec 64) (v : BitVec 64) (h1 : c₁.toNat + 8 ≤ 64)
    (h2 : c₂.toNat + 8 ≤ 0x170) :
    memLoad (memStore mem ((Operand.mem ((Operand.reg 4 : Operand 64).read s + 0x60) : Operand 64).read s +
      ((Operand.reg 0 : Operand 64).read s <<< 0 + c₁)) v) ((Operand.reg 4 : Operand 64).read s + c₂) 64 =
    memLoad mem ((Operand.reg 4 : Operand 64).read s + c₂) 64 := by
  rw [he.addr, hx.rsp]
  apply memLoad_memStore_of_rangeApart
  have hl := hx.wr.low
  exact fr_apart hap c₁ 8 h1 8 (by rw [BitVec.toNat_add]; omega) (by rw [BitVec.toNat_add]; omega)

theorem mm_apart0 (mem : Ram) (base x c₂ : BitVec 64) {n : Nat}
    (v : BitVec n) (k : Nat) (h : OffsetsApart 0 (n / 8) c₂ (k / 8)) (hn : n ≤ 128)
    (hk : k ≤ 128) :
    memLoad (memStore mem (base + x) v) (base + (x + c₂)) k =
      memLoad mem (base + (x + c₂)) k := by
  have := mm_apart mem base x 0 c₂ v k h hn hk
  simpa using this

theorem within_out {a c : BitVec 64} {n : Nat} {cs : List Component}
    (hm : Component.mem a 64 ∈ cs) (hc : c.toNat + n ≤ 64) : Within (.mem (a + c) n) cs := by
  refine ⟨fun h => by simp [Component.isMem] at h, fun x hx => ⟨_, hm, ?_⟩⟩
  obtain ⟨k, hk, rfl⟩ := hx
  refine ⟨c.toNat + k, by omega, ?_⟩
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

def outBytes : List UInt8 := [0x41, 0xff, 0xc4, 0x48, 0xff, 0xc7, 0x48, 0x8b, 0x8c, 0x24, 0xe8, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x74, 0x24, 0x60, 0x48, 0x89, 0x4c, 0x06, 0x38, 0x48, 0x8b, 0x8c, 0x24, 0xe0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4c, 0x06, 0x30, 0x48, 0x8b, 0x8c, 0x24, 0xd8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4c, 0x06, 0x28, 0x48, 0x8b, 0x8c, 0x24, 0xd0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4c, 0x06, 0x20, 0x48, 0x8b, 0x8c, 0x24, 0xc8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4c, 0x06, 0x18, 0x48, 0x8b, 0x8c, 0x24, 0xc0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4c, 0x06, 0x10, 0x48, 0x8b, 0x8c, 0x24, 0xb0, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x94, 0x24, 0xb8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x54, 0x06, 0x08, 0x48, 0x89, 0x0c, 0x06]

structure OutQ (sp outBase : BitVec 64) (j : Nat) (s u : RamState) : Prop where
  rip : u.RIP = 0x1010a8
  agrees : AgreesExcept [.reg 12, .reg 7, .reg 1, .reg 6, .reg 2, .flags, .rip,
    .mem (outBlock outBase j) 64] s u
  rdi : reg64 u 7 = reg64 s 7 + 1
  r12 : reg64 u 12 = (reg32 s 12 + 1).setWidth 64
  words : ∀ m < 8, memLoad u.external (outBlock outBase j + BitVec.ofNat 64 (8 * m)) 64 =
    memLoad s.external (sp + BitVec.ofNat 64 (0xb0 + 8 * m)) 64

set_option maxHeartbeats 8000000 in
theorem outRun [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < codeLo ∨ codeHi < boundary.rip.toNat) (sp outBase : BitVec 64)
    (j : Nat) (hap : RangeApart (outBlock outBase j) 64 sp 0x170) :
    AdvancesTo boundary (fun s => s.RIP = 0x101036 ∧ XF sp s ∧ EX outBase j s)
      (codeRange 0x101036 outBytes) (OutQ sp outBase j) := by
  refine advancesTo_of_block (E := ?E) ?blk ?imp
  case blk =>
    unfold outBytes
    xb_begin_r (inc_r32_rex_effect_step 0x101036 0x41 0xc4 (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    xb_then (inc_r64_effect_step 0x101039 0x48 0xc7 (by unfold RexWPrefix; decide) (by decide) (by decide)) using xs_out
    xb_then (mov_r64_m64_effect_step 0x10103c 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_r64_m64_effect_step 0x101044 0x48 (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_m64_r64_effect_step 0x101049 0x48 (by unfold RexWPrefix; decide) 1 (.sib 6 (some 0) 0 (.d8 0x38)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_r64_m64_effect_step 0x10104e 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_m64_r64_effect_step 0x101056 0x48 (by unfold RexWPrefix; decide) 1 (.sib 6 (some 0) 0 (.d8 0x30)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_r64_m64_effect_step 0x10105b 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_m64_r64_effect_step 0x101063 0x48 (by unfold RexWPrefix; decide) 1 (.sib 6 (some 0) 0 (.d8 0x28)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_r64_m64_effect_step 0x101068 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_m64_r64_effect_step 0x101070 0x48 (by unfold RexWPrefix; decide) 1 (.sib 6 (some 0) 0 (.d8 0x20)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_r64_m64_effect_step 0x101075 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_m64_r64_effect_step 0x10107d 0x48 (by unfold RexWPrefix; decide) 1 (.sib 6 (some 0) 0 (.d8 0x18)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_r64_m64_effect_step 0x101082 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_m64_r64_effect_step 0x10108a 0x48 (by unfold RexWPrefix; decide) 1 (.sib 6 (some 0) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_r64_m64_effect_step 0x10108f 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_r64_m64_effect_step 0x101097 0x48 (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_m64_r64_effect_step 0x10109f 0x48 (by unfold RexWPrefix; decide) 2 (.sib 6 (some 0) 0 (.d8 0x08)) (by decide) (by decide) (by decide)) using xs_out
    xb_then (mov_m64_r64_effect_step 0x1010a4 0x48 (by unfold RexWPrefix; decide) 1 (.sib 6 (some 0) 0 .none) (by decide) (by decide) (by decide)) using xs_out0
    exact id
  case imp =>
    intro s t hP hH
    obtain ⟨hrip, hx, he⟩ := hP
    have hfull : ∀ w ∈ (?E s).writes, w.Full := by
      simp (config := { decide := true }) only [x86_compose, List.forall_mem_cons,
        List.forall_mem_nil, List.forall_mem_append, and_true, true_and]
    have ho := hH.obsAfter hfull true
    have hag := hH.agrees
    x86_norm at hag
    have hea := he.addr
    x86_norm at hea
    refine ⟨hH.rip.trans (by x86_norm), ?_, ?_, ?_, ?_⟩
    · refine agrees_widen hag ?_
      simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first
        | (intro x hx; simp at hx)
        | exact within_reg (by simp (config := {decide := true}))
        | exact within_flags (by simp)
        | exact within_rip (by simp)
        | (rw [hea]; exact within_out (by simp) (by decide))
        | (rw [show ∀ x : BitVec 64, x <<< 0 = x <<< 0 + 0 from fun x => (BitVec.add_zero _).symm,
            hea]; exact within_out (by simp) (by decide))
    · unfold reg64; rw [← ho.read_reg]; x86_norm
      rfl
    · unfold reg64; rw [← ho.read_reg]; x86_norm
      rfl
    · intro m hm
      have h4 := hx.rsp
      x86_norm at h4
      have hoa := oa hx he hap
      x86_norm at hoa
      rw [← hea, ← h4]
      change (Operand.mem _ : Operand 64).read t = (Operand.mem _ : Operand 64).read s
      rw [← ho.read_mem]
      rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        x86_norm [mm_apart, mm_apart0, hoa]


section Compose

variable {t0 : RamState} {mixed init : Vector UInt32 16} {j : Nat} {inBase outBase : BitVec 64}
  {block : Vector UInt8 64}

theorem FeedA.xf {s : RamState} {pc : Nat} {mr : List (Fin 16 × BitVec 5)} {ksw : List (Fin 16)}
    {ir : List (Fin 16 × BitVec 5)} (h0 : FeedPre mixed init j inBase outBase block t0)
    (h : FeedA t0 s pc mixed init j inBase outBase block mr ksw ir) : XF (stackPtr t0) s := by
  have w := h.fr h0
  rw [h.sp] at w
  exact ⟨(stackPtr_eq_read s).symm.trans h.sp, w, h0.frame.program⟩

theorem FeedA.bx {s : RamState} {pc : Nat} {mr : List (Fin 16 × BitVec 5)} {ksw : List (Fin 16)}
    {ir : List (Fin 16 × BitVec 5)} (h0 : FeedPre mixed init j inBase outBase block t0)
    (h : FeedA t0 s pc mixed init j inBase outBase block mr ksw ir) : BX inBase j s := by
  have hi := (h.slot64_eq h0 0x70 (by decide)).trans h0.blocks.index
  have hn := (h.slot64_eq h0 0x68 (by decide)).trans h0.blocks.inSlot
  unfold slot64 slot at hi hn
  rw [stackPtr_eq_read] at hi hn
  have hl := h0.blocks.inLow
  refine ⟨hi, hn, hl, ?_, fun i hi' => ?_⟩
  · unfold inBlock; rw [BitVec.toNat_add]; simp; omega
  · rw [h.input ⟨i, hi'⟩]; rfl

theorem codeIn_t0 {t : RamState} (h0 : FeedPre mixed init j inBase outBase block t0)
    (hc0 : CodeIn Extracted.programImage t0) (hag : AgreesExcept (changes t0 outBase j) t0 t) :
    CodeIn Extracted.programImage t :=
  codeIn_of_changes h0 hag (fun _ hc => within_self hc) hc0

theorem mb_keep {cs : List Component} {s t : RamState} (h : AgreesExcept cs s t) {a : BitVec 64}
    (hn : ∀ c ∈ cs, ¬ c.Covers a) : memByte t.external a = memByte s.external a := by
  simp only [memByte, PhysicalMemory.read]; rw [h.byte hn]

theorem within_scr (c n : Nat) (h1 : 0xb0 ≤ c) (h2 : c + n ≤ 0x170) :
    Within (.mem (stackPtr t0 + BitVec.ofNat 64 c) n) (changes t0 outBase j) :=
  within_mem (a := stackPtr t0) (c := c) (n := n) (lo := 0xb0) (len := 0xc0)
    (cs := changes t0 outBase j) (by unfold changes slot scratchOff scratchBytes; simp)
    h1 (by omega) (by omega)

theorem bc1_within : ∀ c ∈ [Component.reg 7, .reg 0, .reg 2, .reg 1, .flags, .rip,
    .mem (stackPtr t0 + BitVec.ofNat 64 0x150) 0x20], Within c (changes t0 outBase j) := by
  simp only [List.forall_mem_cons]
  exact ⟨within_reg (by simp [changes]), within_reg (by simp [changes]),
    within_reg (by simp [changes]), within_reg (by simp [changes]), within_flags (by simp [changes]),
    within_rip (by simp [changes]), within_scr _ _ (by omega) (by omega), fun _ h => by simp at h⟩

theorem bc2_within : ∀ c ∈ [Component.reg 1, .reg 2, .rip,
    .mem (stackPtr t0 + BitVec.ofNat 64 0x130) 0x20], Within c (changes t0 outBase j) := by
  simp only [List.forall_mem_cons]
  exact ⟨within_reg (by simp [changes]), within_reg (by simp [changes]),
    within_rip (by simp [changes]), within_scr _ _ (by omega) (by omega), fun _ h => by simp at h⟩

theorem bc3_within : ∀ c ∈ [Component.reg 1, .rip,
    .mem (stackPtr t0 + BitVec.ofNat 64 0xb0) 0x40], Within c (changes t0 outBase j) := by
  simp only [List.forall_mem_cons]
  exact ⟨within_reg (by simp [changes]), within_rip (by simp [changes]),
    within_scr _ _ (by omega) (by omega), fun _ h => by simp at h⟩

theorem xf_of_agrees {s : RamState} (h0 : FeedPre mixed init j inBase outBase block t0)
    (hag : AgreesExcept (changes t0 outBase j) t0 s) : XF (stackPtr t0) s := by
  have e : (Operand.reg 4 : Operand 64).read s = (Operand.reg 4 : Operand 64).read t0 :=
    hag.read (by simp [changes])
  exact ⟨e.trans (stackPtr_eq_read t0).symm,
    ⟨h0.frame.writable.low, fun i hi => hag.grow _ (h0.frame.writable.mem i hi),
      h0.frame.writable.tables⟩, h0.frame.program⟩

theorem kp1 {s0 s1 : RamState} (q : BC1Q (stackPtr t0) inBase j s0 s1) (d : Nat) (hd : d < 0x200)
    (h : d < 0x150 ∨ 0x150 + 0x20 ≤ d) :
    memByte s1.external (stackPtr t0 + BitVec.ofNat 64 d) =
      memByte s0.external (stackPtr t0 + BitVec.ofNat 64 d) := by
  refine mb_keep q.agrees fun c hc hcov => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (simp [Component.Covers] at hcov; done)
    | exact nc_mem _ _ _ _ (by omega) (by omega) h hcov

theorem kp2 {s0 s1 : RamState} (q : BC2Q (stackPtr t0) inBase j s0 s1) (d : Nat) (hd : d < 0x200)
    (h : d < 0x130 ∨ 0x130 + 0x20 ≤ d) :
    memByte s1.external (stackPtr t0 + BitVec.ofNat 64 d) =
      memByte s0.external (stackPtr t0 + BitVec.ofNat 64 d) := by
  refine mb_keep q.agrees fun c hc hcov => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals first
    | (simp [Component.Covers] at hcov; done)
    | exact nc_mem _ _ _ _ (by omega) (by omega) h hcov

theorem kp3 {s0 s1 : RamState} (q : BC3Q (stackPtr t0)  s0 s1) (d : Nat) (hd : d < 0x200)
    (h : d < 0xb0 ∨ 0xb0 + 0x40 ≤ d) :
    memByte s1.external (stackPtr t0 + BitVec.ofNat 64 d) =
      memByte s0.external (stackPtr t0 + BitVec.ofNat 64 d) := by
  refine mb_keep q.agrees fun c hc hcov => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  all_goals first
    | (simp [Component.Covers] at hcov; done)
    | exact nc_mem _ _ _ _ (by omega) (by omega) h hcov

theorem in_keep1 {s0 s1 : RamState} (h0 : FeedPre mixed init j inBase outBase block t0)
    (q1 : BC1Q (stackPtr t0) inBase j s0 s1) (i : Nat) (hi : i < 64) :
    s1.external[inBlock inBase j + BitVec.ofNat 64 i]? =
      s0.external[inBlock inBase j + BitVec.ofNat 64 i]? := by
  refine q1.agrees.byte fun c hc hcov => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (simp [Component.Covers] at hcov; done)
    | exact apart_not_covers h0.blocks.inStack 0x150 0x20 (by decide) i hi hcov

theorem loop0 {s0 s1 s2 s3 : RamState} (h0 : FeedPre mixed init j inBase outBase block t0)
    (hF : FeedA t0 s0 0x100ef2 mixed init j inBase outBase block [] allW irA)
    (q1 : BC1Q (stackPtr t0) inBase j s0 s1) (q2 : BC2Q (stackPtr t0) inBase j s1 s2)
    (q3 : BC3Q (stackPtr t0) s2 s3) : Loop t0 mixed init j outBase block 0 s3 := by
  have g1 := widen_trans hF.agrees q1.agrees bc1_within
  have g2 := widen_trans g1 q2.agrees bc2_within
  have g3 := widen_trans g2 q3.agrees bc3_within
  have r1 : ∀ r : BitVec 5, r ≠ 7 → r ≠ 0 → r ≠ 2 → r ≠ 1 → reg64 s1 r = reg64 s0 r :=
    fun r a b c d => q1.agrees.read (by simp; exact ⟨a, b, c, d⟩)
  have r2 : ∀ r : BitVec 5, r ≠ 1 → r ≠ 2 → reg64 s2 r = reg64 s1 r :=
    fun r a b => q2.agrees.read (by simp; exact ⟨a, b⟩)
  have r3 : ∀ r : BitVec 5, r ≠ 1 → reg64 s3 r = reg64 s2 r :=
    fun r a => q3.agrees.read (by simp; exact a)
  have hir := hF.iregs
  simp only [irA, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hir
  obtain ⟨i4, i8, i12, i13⟩ := hir
  have hin : ∀ i : Fin 64, memByte s1.external (inBlock inBase j + BitVec.ofNat 64 i.val) = block[i] := by
    intro i
    rw [memByte_of_get ((in_keep1 h0 q1 i.val i.isLt).trans (hF.input i))]
  refine ⟨?_, g3, q3.rcx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : stackPtr s1 = stackPtr s0 := by
      rw [stackPtr_eq_read, stackPtr_eq_read]; exact q1.agrees.read (by simp)
    have e2 : stackPtr s2 = stackPtr s1 := by
      rw [stackPtr_eq_read, stackPtr_eq_read]; exact q2.agrees.read (by simp)
    have e3 : stackPtr s3 = stackPtr s2 := by
      rw [stackPtr_eq_read, stackPtr_eq_read]; exact q3.agrees.read (by simp)
    rw [e3, e2, e1]; exact hF.sp
  · rw [r3 7 (by decide), r2 7 (by decide) (by decide)]; exact q1.rdi
  · rw [r3 0 (by decide), r2 0 (by decide) (by decide)]; exact q1.rax
  · rw [r3 10 (by decide), r2 10 (by decide) (by decide),
      r1 10 (by decide) (by decide) (by decide) (by decide)]; exact i4
  · rw [r3 11 (by decide), r2 11 (by decide) (by decide),
      r1 11 (by decide) (by decide) (by decide) (by decide)]; exact i8
  · rw [r3 12 (by decide), r2 12 (by decide) (by decide),
      r1 12 (by decide) (by decide) (by decide) (by decide)]; exact i12
  · rw [r3 8 (by decide), r2 8 (by decide) (by decide),
      r1 8 (by decide) (by decide) (by decide) (by decide)]; exact i13
  · intro i
    rw [kp3 q3 _ (by omega) (by omega), kp2 q2 _ (by omega) (by omega), kp1 q1 _ (by omega) (by omega)]
    exact ks_bytes (fun w => hF.ks w (mem_allW w)) i
  · intro i
    rw [kp3 q3 _ (by omega) (by omega)]
    by_cases hi : 4 ≤ i.val / 8
    · rw [kp2 q2 _ (by omega) (by omega)]
      have e := memByte_of_memLoad_eq (q1.words (i.val / 8) hi (by omega)) (i.val % 8) (by omega)
      rw [add_ofNat_add, add_ofNat_add, show 0x130 + 8 * (i.val / 8) + i.val % 8 = 0x130 + i.val by omega,
        show 0 + 8 * (i.val / 8) + i.val % 8 = i.val by omega] at e
      rw [e]
      exact memByte_of_get (hF.input i)
    · have e := memByte_of_memLoad_eq (q2.words (i.val / 8) (by omega)) (i.val % 8) (by omega)
      rw [add_ofNat_add, add_ofNat_add, show 0x130 + 8 * (i.val / 8) + i.val % 8 = 0x130 + i.val by omega,
        show 0 + 8 * (i.val / 8) + i.val % 8 = i.val by omega] at e
      rw [e]
      exact hin i
  · intro i hi; omega

theorem FeedA.cx {s0 s1 : RamState} (h0 : FeedPre mixed init j inBase outBase block t0)
    (hF : FeedA t0 s0 0x100ef2 mixed init j inBase outBase block [] allW irA)
    (q1 : BC1Q (stackPtr t0) inBase j s0 s1) : CX inBase j s1 := by
  have hl := h0.blocks.inLow
  refine ⟨q1.rax, q1.rdx, ?_, fun i hi => ?_⟩
  · unfold inBlock; rw [BitVec.toNat_add]; simp; omega
  · rw [show s1.external[inBlock inBase j + BitVec.ofNat 64 i]? =
        s0.external[inBlock inBase j + BitVec.ofNat 64 i]? from in_keep1 h0 q1 i hi]
    rw [hF.input ⟨i, hi⟩]; rfl

theorem Loop.ex {u : RamState} {k : Nat} (h0 : FeedPre mixed init j inBase outBase block t0)
    (h : Loop t0 mixed init j outBase block k u) : EX outBase j u := by
  have hs : memLoad u.external (stackPtr t0 + BitVec.ofNat 64 0x60) 64 = outBase := by
    rw [load_keep h.agrees fun i hi => changes_not_covers h0 0x60 8 (by decide) i (by omega)]
    exact h0.blocks.outSlot
  refine ⟨?_, h.rax, ⟨h0.blocks.output.low, fun i hi => h.agrees.grow _ (h0.blocks.output.mem i hi),
    h0.blocks.output.tables⟩, h0.blocks.outProgram⟩
  rw [← stackPtr_eq_read, h.sp]; exact hs

theorem post_of {u v : RamState} (h0 : FeedPre mixed init j inBase outBase block t0)
    (hL : Loop t0 mixed init j outBase block 16 u) (hQ : OutQ (stackPtr t0) outBase j u v) :
    FeedPost t0 v mixed init j outBase block := by
  have hw : ∀ c ∈ [Component.reg 12, .reg 7, .reg 1, .reg 6, .reg 2, .flags, .rip,
      .mem (outBlock outBase j) 64], Within c (changes t0 outBase j) := by
    simp only [List.forall_mem_cons]
    exact ⟨within_reg (by simp [changes]), within_reg (by simp [changes]),
      within_reg (by simp [changes]), within_reg (by simp [changes]), within_reg (by simp [changes]),
      within_flags (by simp [changes]), within_rip (by simp [changes]),
      within_self (by simp [changes]), fun _ h => by simp at h⟩
  have hag := widen_trans hL.agrees hQ.agrees hw
  have hrd : ∀ r : BitVec 5, r ≠ 12 → r ≠ 7 → r ≠ 1 → r ≠ 6 → r ≠ 2 → reg64 v r = reg64 u r := by
    intro r a b c d e
    exact hQ.agrees.read (by simp; exact ⟨a, b, c, d, e⟩)
  refine ⟨hQ.rip, hag, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have e := copy_bytes (ca := 0) (cb := 0xb0) (m := v.external) (m' := u.external)
      (a := outBlock outBase j) (b := stackPtr t0) (fun k hk => by
        rw [Nat.zero_add]; exact hQ.words k hk) i.val i.isLt
    rw [Nat.zero_add, hL.out i (by omega)] at e
    exact get_of_memByte (hag.grow _ (h0.blocks.output.mem i.val i.isLt)) e
  · rw [hQ.rdi, hL.rdi]; apply BitVec.eq_of_toNat_eq; simp
  · rw [hQ.r12]
    have : reg32 u 12 = init[12].toBitVec := reg32_of_write hL.r12
    rw [this, UInt32.toBitVec_add]; rfl
  · rw [hrd 10 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.r10
  · rw [hrd 11 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.r11
  · rw [hrd 8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.r8

end Compose

                                                                          
theorem full_block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < codeLo ∨ codeHi < boundary.rip.toNat)
    {t : RamState} {mixed init : Vector UInt32 16} {j : Nat} {inBase outBase : BitVec 64}
    {block : Vector UInt8 64}
    (hr : ReadyToStep t) (hc : CodeIn Extracted.programImage t)
    (h : FeedPre mixed init j inBase outBase block t) :
    ∃ fuel u, Advances boundary fuel t u ∧ ReadyToStep u ∧
      CodeIn Extracted.programImage u ∧ FeedPost t u mixed init j outBase block := by
  have hne : ∀ pc : BitVec 64, codeLo ≤ pc.toNat → pc.toNat ≤ codeHi → pc ≠ boundary.rip := by
    rintro pc h1 h2 rfl; omega
  obtain ⟨f1, s1, a1, r1, -, q1⟩ := a1a boundary hne h t hr
    (text_at hc 0xe19 50 _ _ (by decide) (by decide +kernel) (by decide)) (FeedA.start h)
  have c1 := codeIn_t0 h hc q1.agrees
  obtain ⟨f2, s2, a2, r2, -, q2⟩ := ffRunA boundary hb h s1 r1
    (text_at c1 0xe4b 72 _ _ (by decide) (by decide +kernel) (by decide))
    ⟨q1.rip, q1.xf h, q1⟩
  have c2 := codeIn_t0 h hc q2.agrees
  obtain ⟨f3, s3, a3, r3, -, q3⟩ := ffRunB boundary hb h s2 r2
    (text_at c2 0xe93 95 _ _ (by decide) (by decide +kernel) (by decide))
    ⟨q2.rip, q2.xf h, q2⟩
  have c3 := codeIn_t0 h hc q3.agrees
  obtain ⟨f4, s4, a4, r4, -, b1⟩ := bc1Run boundary hb (stackPtr t) inBase j h.blocks.inStack s3 r3
    (text_at c3 0xef2 69 _ _ (by decide) (by decide +kernel) (by decide))
    ⟨q3.rip, q3.xf h, q3.bx h⟩
  have g4 := widen_trans q3.agrees b1.agrees bc1_within
  have c4 := codeIn_t0 h hc g4
  obtain ⟨f5, s5, a5, r5, -, b2⟩ := bc2Run boundary hb (stackPtr t) inBase j h.blocks.inStack s4 r4
    (text_at c4 0xf37 51 _ _ (by decide) (by decide +kernel) (by decide))
    ⟨b1.rip, xf_of_agrees h g4, FeedA.cx h q3 b1⟩
  have g5 := widen_trans g4 b2.agrees bc2_within
  have c5 := codeIn_t0 h hc g5
  obtain ⟨f6, s6, a6, r6, -, b3⟩ := bc3Run boundary hb (stackPtr t) s5 r5
    (text_at c5 0xf6a 101 _ _ (by decide) (by decide +kernel) (by decide))
    ⟨b2.rip, xf_of_agrees h g5, trivial⟩
  have l0 := loop0 h q3 b1 b2 b3
  have c6 := codeIn_t0 h hc l0.agrees
  obtain ⟨s7, a7, r7, e7⟩ := (nop_effect_step 0x100fcf).advances r6
    (text_at c6 0xfcf 1 _ _ (by decide) (by decide +kernel) (by decide)) b3.rip
    (by simp only [nopEffect]; exact ne_bd hb (by decide) (by decide))
  have ag7 : AgreesExcept [.rip] s6 s7 := by simpa only [nopEffect_components] using e7.agrees
  have l0' := l0.rip_step ag7
  have c7 := codeIn_t0 h hc l0'.agrees
  have rip7 : s7.RIP = 0x100fd0 := by rw [e7.rip]; simp only [nopEffect]; decide
  obtain ⟨f8, s8, a8, r8, c8, l16, hr8⟩ := loop_all boundary hb h 15 0 s7 rfl r7 c7 rip7 l0'
  obtain ⟨f9, s9, a9, r9, -, q9⟩ := outRun boundary hb (stackPtr t) outBase j h.blocks.outStack s8 r8
    (text_at c8 0x1036 114 _ _ (by decide) (by decide +kernel) (by decide))
    ⟨hr8, l16.xf h, l16.ex h⟩
  have post := post_of h l16 q9
  exact ⟨f1 + f2 + f3 + f4 + f5 + f6 + 1 + f8 + f9, s9,
    (((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9, r9,
    codeIn_t0 h hc post.agrees, post⟩

end ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Xor
