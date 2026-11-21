import ChaCha20Poly1305.Spec
import ChaCha20Poly1305.Proofs.Common.Poly1305State
import ChaCha20Poly1305.Proofs.Common.WritableRange
import X86Proofs.Program.Execution
import X86Proofs.Program.Agrees
import X86Proofs.Program.Code
import X86Proofs.Step.ReadyToStep
import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Execution
import ChaCha20Poly1305.Proofs.Poly1305.BlockArith
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Movzx.Generated.RR8.Triple
import X86Proofs.Instructions.Shl.Generated.R.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.Mov.Generated.MR.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple
import X86Proofs.Instructions.And.Generated.RM.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.And.Generated.Imm32.Triple
import X86Proofs.Instructions.Imul.Generated.RR.Triple
import X86Proofs.Instructions.Imul.Generated.RM.Triple
import X86Proofs.Instructions.And.Generated.AccImm32.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Branch.Triple

namespace ChaCha20Poly1305.Proofs.Poly1305.Callee101e30

set_option linter.unusedSimpArgs false

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Standards.RFC.ChaCha20Poly1305
open ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Poly1305State
  ChaCha20Poly1305.Proofs.Common

def entry : BitVec 64 := 0x101e30

def bodyEntry : BitVec 64 := 0x101ab0

def InCode (address : BitVec 64) : Prop :=
  (entry.toNat ≤ address.toNat ∧ address.toNat < entry.toNat + 7) ∨
    (bodyEntry.toNat ≤ address.toNat ∧ address.toNat < 0x101cd2)

def stackBytes : Nat := 88

def rAddress (s : RamState) : BitVec 64 := rdi.read s + rOffset

def hAddress (s : RamState) : BitVec 64 := rdi.read s + hOffset

def block (s : RamState) : ByteArray :=
  ⟨Array.ofFn fun i : Fin 16 => (s.external[rsi.read s + BitVec.ofNat 64 i.val]?).getD 0⟩

def stackBase (s : RamState) : BitVec 64 := stackPtr s - BitVec.ofNat 64 stackBytes

structure CallPre (s : RamState) : Prop where
  rip : s.RIP = entry
  stack : WritableRange s (stackBase s) stackBytes
  returnSlot : MemReadable s (stackPtr s) 8
  stackLow : stackBytes ≤ (stackPtr s).toNat
  rLimbsReadable : MemReadable s (rAddress s) 20
  hLimbsWritable : WritableRange s (hAddress s) 20
  blockReadable : MemReadable s (rsi.read s) 16
  rApart : RangeApart (rAddress s) 20 (stackBase s) (stackBytes + 8)
  hApart : RangeApart (hAddress s) 20 (stackBase s) (stackBytes + 8)
  blockApart : RangeApart (rsi.read s) 16 (stackBase s) (stackBytes + 8)
  rClamped : ClampedLimbs (rLimbs s (rdi.read s))
  hBounded : BoundedLimbs (hLimbs s (rdi.read s))
  returnLow : (returnBoundary s).rip.toNat < 2 ^ 32
  returnOutside : ¬ InCode (returnBoundary s).rip

def callChanges (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip, .mem (stackBase s) stackBytes, .mem (hAddress s) 20]

structure CallResult [Bindings] (s t : RamState) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = (returnBoundary s).rip
  rsp : stackPtr t = stackPtr s + 8
  agrees : AgreesExcept (callChanges s) s t
  calleeSaved : CalleeSavedRegistersUnchanged s t
  bounded : BoundedLimbs (hLimbs t (rdi.read s))
  value : limbValue (hLimbs t (rdi.read s)) % prime =
    ((limbValue (hLimbs s (rdi.read s)) + leBytesToNum (block s ++ ⟨#[0x01]⟩)) *
      limbValue (rLimbs s (rdi.read s))) % prime

section Body

open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305.BlockArith

def bodyBytes : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xec, 0x28, 0x49, 0x89,
    0xfa, 0x80, 0xf2, 0x01, 0x0f, 0xb6, 0xfa, 0xc1, 0xe7, 0x18, 0x45, 0x8b, 0x42, 0x10, 0x41,
    0x8b, 0x42, 0x18, 0x48, 0x89, 0x44, 0x24, 0x10, 0x41, 0x8b, 0x4a, 0x1c, 0x48, 0x89, 0x4c,
    0x24, 0x18, 0x41, 0x8b, 0x52, 0x20, 0x48, 0x89, 0x54, 0x24, 0x20, 0x8d, 0x04, 0x80, 0x48,
    0x89, 0x44, 0x24, 0x08, 0x44, 0x8d, 0x0c, 0x89, 0x4c, 0x89, 0x0c, 0x24, 0x8d, 0x1c, 0x92,
    0x41, 0xbf, 0xff, 0xff, 0xff, 0x03, 0x44, 0x23, 0x3e, 0x45, 0x03, 0x7a, 0x24, 0x8b, 0x56,
    0x03, 0x44, 0x8b, 0x66, 0x06, 0xc1, 0xea, 0x02, 0x81, 0xe2, 0xff, 0xff, 0xff, 0x03, 0x41,
    0x03, 0x52, 0x28, 0x41, 0xc1, 0xec, 0x04, 0x41, 0x81, 0xe4, 0xff, 0xff, 0xff, 0x03, 0x45,
    0x03, 0x62, 0x2c, 0x8b, 0x4e, 0x09, 0xc1, 0xe9, 0x06, 0x41, 0x03, 0x4a, 0x30, 0x8b, 0x76,
    0x0c, 0xc1, 0xee, 0x08, 0x41, 0x03, 0x7a, 0x34, 0x01, 0xf7, 0x4c, 0x89, 0xfe, 0x49, 0x0f,
    0xaf, 0xf0, 0x48, 0x89, 0xd5, 0x48, 0x0f, 0xaf, 0xeb, 0x48, 0x01, 0xf5, 0x4c, 0x89, 0xe6,
    0x49, 0x0f, 0xaf, 0xf1, 0x49, 0x89, 0xcd, 0x4c, 0x0f, 0xaf, 0xe8, 0x49, 0x01, 0xf5, 0x49,
    0x01, 0xed, 0x41, 0x8b, 0x6a, 0x14, 0x44, 0x8d, 0x5c, 0xad, 0x00, 0x4c, 0x0f, 0xaf, 0xdf,
    0x4d, 0x01, 0xeb, 0x4d, 0x89, 0xfd, 0x4c, 0x0f, 0xaf, 0xed, 0x49, 0x89, 0xd6, 0x4d, 0x0f,
    0xaf, 0xf0, 0x4d, 0x89, 0xc1, 0x4d, 0x01, 0xee, 0x4d, 0x89, 0xe5, 0x4c, 0x0f, 0xaf, 0xeb,
    0x48, 0x89, 0xc8, 0x4c, 0x8b, 0x04, 0x24, 0x49, 0x0f, 0xaf, 0xc0, 0x4c, 0x01, 0xe8, 0x4c,
    0x01, 0xf0, 0x48, 0x8b, 0x74, 0x24, 0x08, 0x48, 0x0f, 0xaf, 0xf7, 0x48, 0x01, 0xc6, 0x48,
    0x89, 0x74, 0x24, 0x08, 0x4c, 0x89, 0xf8, 0x48, 0x8b, 0x74, 0x24, 0x10, 0x48, 0x0f, 0xaf,
    0xc6, 0x49, 0x89, 0xd6, 0x4c, 0x0f, 0xaf, 0xf5, 0x49, 0x01, 0xc6, 0x4c, 0x89, 0xe0, 0x49,
    0x0f, 0xaf, 0xc1, 0x49, 0x89, 0xcd, 0x4c, 0x0f, 0xaf, 0xeb, 0x49, 0x01, 0xc5, 0x4d, 0x01,
    0xf5, 0x4c, 0x89, 0xc0, 0x48, 0x0f, 0xaf, 0xc7, 0x4c, 0x01, 0xe8, 0x48, 0x89, 0x04, 0x24,
    0x4c, 0x89, 0xf8, 0x4c, 0x8b, 0x44, 0x24, 0x18, 0x49, 0x0f, 0xaf, 0xc0, 0x49, 0x89, 0xd6,
    0x4c, 0x0f, 0xaf, 0xf6, 0x49, 0x01, 0xc6, 0x4c, 0x89, 0xe0, 0x48, 0x0f, 0xaf, 0xc5, 0x49,
    0x89, 0xcd, 0x4d, 0x0f, 0xaf, 0xe9, 0x49, 0x01, 0xc5, 0x4d, 0x01, 0xf5, 0x48, 0x0f, 0xaf,
    0xdf, 0x4c, 0x01, 0xeb, 0x4c, 0x0f, 0xaf, 0x7c, 0x24, 0x20, 0x49, 0x0f, 0xaf, 0xd0, 0x4c,
    0x01, 0xfa, 0x4c, 0x0f, 0xaf, 0xe6, 0x48, 0x0f, 0xaf, 0xcd, 0x4c, 0x01, 0xe1, 0x48, 0x01,
    0xd1, 0x49, 0x0f, 0xaf, 0xf9, 0x48, 0x01, 0xcf, 0x4c, 0x89, 0xd8, 0x48, 0xc1, 0xe8, 0x1a,
    0x41, 0x81, 0xe3, 0xff, 0xff, 0xff, 0x03, 0x41, 0x89, 0xc0, 0x4c, 0x03, 0x44, 0x24, 0x08,
    0x4c, 0x89, 0xc0, 0x48, 0xc1, 0xe8, 0x1a, 0x41, 0x81, 0xe0, 0xff, 0xff, 0xff, 0x03, 0x41,
    0x89, 0xc1, 0x4c, 0x03, 0x0c, 0x24, 0x4c, 0x89, 0xc8, 0x48, 0xc1, 0xe8, 0x1a, 0x89, 0xc2,
    0x48, 0x01, 0xda, 0x48, 0x89, 0xd0, 0x48, 0xc1, 0xe8, 0x1a, 0x89, 0xc0, 0x48, 0x01, 0xf8,
    0x48, 0x89, 0xc1, 0x48, 0xc1, 0xe9, 0x1a, 0x8d, 0x0c, 0x89, 0x44, 0x01, 0xd9, 0x89, 0xce,
    0xc1, 0xee, 0x1a, 0x44, 0x01, 0xc6, 0x81, 0xe1, 0xff, 0xff, 0xff, 0x03, 0x41, 0x89, 0x4a,
    0x24, 0x41, 0x89, 0x72, 0x28, 0x41, 0x81, 0xe1, 0xff, 0xff, 0xff, 0x03, 0x45, 0x89, 0x4a,
    0x2c, 0x81, 0xe2, 0xff, 0xff, 0xff, 0x03, 0x41, 0x89, 0x52, 0x30, 0x25, 0xff, 0xff, 0xff,
    0x03, 0x41, 0x89, 0x42, 0x34, 0x48, 0x83, 0xc4, 0x28, 0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41,
    0x5e, 0x41, 0x5f, 0x5d, 0xc3]

structure Env where
  sp : BitVec 64
  st : BitVec 64
  bp : BitVec 64
  rbx : BitVec 64
  rbp : BitVec 64
  r12 : BitVec 64
  r13 : BitVec 64
  r14 : BitVec 64
  r15 : BitVec 64
  r0 : BitVec 32
  r1 : BitVec 32
  r2 : BitVec 32
  r3 : BitVec 32
  r4 : BitVec 32
  h0 : BitVec 32
  h1 : BitVec 32
  h2 : BitVec 32
  h3 : BitVec 32
  h4 : BitVec 32
  w0 : BitVec 32
  w1 : BitVec 32
  w2 : BitVec 32
  w3 : BitVec 32
  w4 : BitVec 32

structure Frame (e : Env) (s : RamState) : Prop where
  spNat : 88 ≤ e.sp.toNat ∧ e.sp.toNat + 8 ≤ 2 ^ 32
  stNat : (e.st + 0x10).toNat + 0x28 ≤ 2 ^ 32
  bpNat : e.bp.toNat + 16 ≤ 2 ^ 32
  stApart : (e.st + 0x10).toNat + 0x28 ≤ e.sp.toNat - 88 ∨ e.sp.toNat + 8 ≤ (e.st + 0x10).toNat
  bpApart : e.bp.toNat + 16 ≤ e.sp.toNat - 88 ∨ e.sp.toNat + 8 ≤ e.bp.toNat
  stack : WritableRange s (e.sp - 88) 88
  ret : MemReadable s e.sp 8
  rRead : MemReadable s (e.st + 0x10) 20
  hWrite : WritableRange s (e.st + 0x24) 20
  blockRead : MemReadable s e.bp 16
  rv0 : (Operand.mem (e.st + 0x10) : Operand 32).read s = e.r0
  rv1 : (Operand.mem (e.st + 0x14) : Operand 32).read s = e.r1
  rv2 : (Operand.mem (e.st + 0x18) : Operand 32).read s = e.r2
  rv3 : (Operand.mem (e.st + 0x1c) : Operand 32).read s = e.r3
  rv4 : (Operand.mem (e.st + 0x20) : Operand 32).read s = e.r4
  hv0 : (Operand.mem (e.st + 0x24) : Operand 32).read s = e.h0
  hv1 : (Operand.mem (e.st + 0x28) : Operand 32).read s = e.h1
  hv2 : (Operand.mem (e.st + 0x2c) : Operand 32).read s = e.h2
  hv3 : (Operand.mem (e.st + 0x30) : Operand 32).read s = e.h3
  hv4 : (Operand.mem (e.st + 0x34) : Operand 32).read s = e.h4
  wv0 : (Operand.mem (e.bp) : Operand 32).read s = e.w0
  wv1 : (Operand.mem (e.bp + 0x3) : Operand 32).read s = e.w1
  wv2 : (Operand.mem (e.bp + 0x6) : Operand 32).read s = e.w2
  wv3 : (Operand.mem (e.bp + 0x9) : Operand 32).read s = e.w3
  wv4 : (Operand.mem (e.bp + 0xc) : Operand 32).read s = e.w4

def bodyChanges (e : Env) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10,
    .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip, .mem (e.sp - 88) 88]

theorem sp88_toNat {e : Env} (h : 88 ≤ e.sp.toNat) : (e.sp - 88).toNat = e.sp.toNat - 88 := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]
  rfl

theorem Frame.not_stack {e : Env} {s : RamState} (hF : Frame e s) {x : BitVec 64}
    (hx : x.toNat < e.sp.toNat - 88 ∨ e.sp.toNat + 8 ≤ x.toNat) :
    ¬ (Component.mem (e.sp - 88) 88).Covers x := by
  rintro ⟨i, hi, rfl⟩
  have := hF.spNat
  rw [toNat_add_ofNat _ _ (by rw [sp88_toNat this.1]; omega), sp88_toNat this.1] at hx
  omega

theorem toNat_add_lit (a : BitVec 64) (i : Nat) (h : a.toNat + i < 2 ^ 64) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i := toNat_add_ofNat a i h

theorem Frame.of_agrees {e : Env} {s t : RamState} (hF : Frame e s)
    (ha : AgreesExcept (bodyChanges e) s t) : Frame e t := by
  have hsp := hF.spNat
  have hst := hF.stNat
  have hbp := hF.bpNat
  have hsa := hF.stApart
  have hba := hF.bpApart
  have hbyte : ∀ x : BitVec 64, (x.toNat < e.sp.toNat - 88 ∨ e.sp.toNat + 8 ≤ x.toNat) →
      t.external[x]? = s.external[x]? := by
    intro x hx
    apply ha.byte
    intro c hc hcov
    simp only [bodyChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hcov | exact hF.not_stack hx hcov
  have hread : ∀ a : BitVec 64, a.toNat + 4 ≤ 2 ^ 32 →
      (a.toNat + 4 ≤ e.sp.toNat - 88 ∨ e.sp.toNat + 8 ≤ a.toNat) →
      (Operand.mem a : Operand 32).read t = (Operand.mem a : Operand 32).read s := by
    intro a h1 h2
    change memLoad t.external a 32 = memLoad s.external a 32
    apply memLoad_congr
    intro i hi
    have hi' : i < 4 := hi
    exact congrArg (fun b : Option UInt8 ↦ b.getD 0) (hbyte _ (by
      rw [toNat_add_ofNat _ _ (by omega)]
      omega))
  exact ⟨hsp, hst, hbp, hsa, hba, hF.stack.of_agrees ha,
    ⟨hF.ret.low, fun i hi ↦ ha.grow _ (hF.ret.mem i hi)⟩,
    ⟨hF.rRead.low, fun i hi ↦ ha.grow _ (hF.rRead.mem i hi)⟩, hF.hWrite.of_agrees ha,
    ⟨hF.blockRead.low, fun i hi ↦ ha.grow _ (hF.blockRead.mem i hi)⟩,
    (hread _ (by bv_omega) (by bv_omega)).trans hF.rv0,
    (hread _ (by bv_omega) (by bv_omega)).trans hF.rv1,
    (hread _ (by bv_omega) (by bv_omega)).trans hF.rv2,
    (hread _ (by bv_omega) (by bv_omega)).trans hF.rv3,
    (hread _ (by bv_omega) (by bv_omega)).trans hF.rv4,
    (hread _ (by bv_omega) (by bv_omega)).trans hF.hv0,
    (hread _ (by bv_omega) (by bv_omega)).trans hF.hv1,
    (hread _ (by bv_omega) (by bv_omega)).trans hF.hv2,
    (hread _ (by bv_omega) (by bv_omega)).trans hF.hv3,
    (hread _ (by bv_omega) (by bv_omega)).trans hF.hv4,
    (hread _ (by bv_omega) (by bv_omega)).trans hF.wv0,
    (hread _ (by bv_omega) (by bv_omega)).trans hF.wv1,
    (hread _ (by bv_omega) (by bv_omega)).trans hF.wv2,
    (hread _ (by bv_omega) (by bv_omega)).trans hF.wv3,
    (hread _ (by bv_omega) (by bv_omega)).trans hF.wv4⟩

def Seg [Bindings] (boundary : ReturnBoundary) (e : Env) (p q : BitVec 64)
    (before after : List Write) : Prop :=
  ∀ s, ReadyToStep s → CodeIn Extracted.programImage s → s.RIP = p → Frame e s →
    Write.AllHold s before →
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = q ∧ Frame e t ∧ Write.AllHold t after ∧ AgreesExcept (bodyChanges e) s t

theorem Seg.seq [Bindings] {boundary : ReturnBoundary} {e : Env} {p q r : BitVec 64}
    {a b c : List Write} (h₁ : Seg boundary e p q a b) (h₂ : Seg boundary e q r b c) :
    Seg boundary e p r a c := by
  intro s hr hc hp hf hw
  obtain ⟨n, t, ha, hr', hc', hq, hf', hw', hag⟩ := h₁ s hr hc hp hf hw
  obtain ⟨m, u, ha', hr'', hc'', hq', hf'', hw'', hag'⟩ := h₂ t hr' hc' hq hf' hw'
  exact ⟨n + m, u, ha.trans ha', hr'', hc'', hq', hf'', hw'',
    (hag.trans hag').mono (by simp only [List.mem_append, or_self]; exact fun _ h ↦ h)⟩

theorem cover_stack {e : Env} {a x : BitVec 64} {n : Nat}
    (hsp : 88 ≤ e.sp.toNat ∧ e.sp.toNat + 8 ≤ 2 ^ 32)
    (ha : e.sp.toNat - 88 ≤ a.toNat ∧ a.toNat + n ≤ e.sp.toNat)
    (hx : (Component.mem a n).Covers x) : ∃ c ∈ bodyChanges e, c.Covers x := by
  obtain ⟨i, hi, rfl⟩ := hx
  refine ⟨.mem (e.sp - 88) 88, by simp [bodyChanges], a.toNat - (e.sp.toNat - 88) + i, by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by rw [sp88_toNat hsp.1]; omega),
    sp88_toNat hsp.1]
  omega

def finalChanges (e : Env) : List Component :=
  bodyChanges e ++ [.mem (e.st + 0x24) 20]

theorem cover_final_stack {e : Env} {a x : BitVec 64} {n : Nat}
    (hsp : 88 ≤ e.sp.toNat ∧ e.sp.toNat + 8 ≤ 2 ^ 32)
    (ha : e.sp.toNat - 88 ≤ a.toNat ∧ a.toNat + n ≤ e.sp.toNat)
    (hx : (Component.mem a n).Covers x) : ∃ c ∈ finalChanges e, c.Covers x := by
  obtain ⟨c, hc, hcx⟩ := cover_stack hsp ha hx
  exact ⟨c, List.mem_append_left _ hc, hcx⟩

theorem cover_final_h {e : Env} {a x : BitVec 64} {n : Nat}
    (hst : (e.st + 0x24).toNat + 20 ≤ 2 ^ 64)
    (ha : (e.st + 0x24).toNat ≤ a.toNat ∧ a.toNat + n ≤ (e.st + 0x24).toNat + 20)
    (hx : (Component.mem a n).Covers x) : ∃ c ∈ finalChanges e, c.Covers x := by
  obtain ⟨i, hi, rfl⟩ := hx
  refine ⟨.mem (e.st + 0x24) 20, by simp [finalChanges], a.toNat - (e.st + 0x24).toNat + i,
    by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)]
  omega

theorem Frame.codeIn {e : Env} {s t : RamState} (hF : Frame e s)
    (ha : AgreesExcept (bodyChanges e) s t) (hc : CodeIn Extracted.programImage s) :
    CodeIn Extracted.programImage t := by
  refine CodeIn.of_agreesExcept ha (fun x hx c hc' hcov ↦ ?_) hc
  simp only [bodyChanges, List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hcov | skip
  obtain ⟨i, hi, he⟩ := hcov
  exact hF.stack.code i hi (he ▸ inProgram_of_mem hx)

theorem Frame.codeIn_final {e : Env} {s t : RamState} (hF : Frame e s)
    (ha : AgreesExcept (finalChanges e) s t) (hc : CodeIn Extracted.programImage s) :
    CodeIn Extracted.programImage t := by
  refine CodeIn.of_agreesExcept ha (fun x hx c hc' hcov ↦ ?_) hc
  simp only [finalChanges, bodyChanges, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hcov | skip
  · obtain ⟨i, hi, he⟩ := hcov
    exact hF.stack.code i hi (he ▸ inProgram_of_mem hx)
  · obtain ⟨i, hi, he⟩ := hcov
    exact hF.hWrite.code i hi (he ▸ inProgram_of_mem hx)

def SegF [Bindings] (boundary : ReturnBoundary) (e : Env) (p q : BitVec 64)
    (before after : List Write) : Prop :=
  ∀ s, ReadyToStep s → CodeIn Extracted.programImage s → s.RIP = p → Frame e s →
    Write.AllHold s before →
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = q ∧ Write.AllHold t after ∧ AgreesExcept (finalChanges e) s t

theorem SegF.of_block [Bindings] {boundary : ReturnBoundary} {e : Env} {p q : BitVec 64}
    {before after : List Write} {bytes : List UInt8} {E : RamState → Effect}
    (hBlock : AdvancesBlock boundary
      (fun s ↦ s.RIP = p ∧ Frame e s ∧ Write.AllHold s before) (codeRange p bytes) E)
    (hSub : ∀ x ∈ codeRange p bytes, x ∈ Extracted.programImage)
    (hPost : ∀ s t, s.RIP = p ∧ Frame e s ∧ Write.AllHold s before → (E s).Holds s t →
      t.RIP = q ∧ Write.AllHold t after ∧ AgreesExcept (finalChanges e) s t) :
    SegF boundary e p q before after := by
  intro s hr hc hp hf hw
  obtain ⟨fuel, t, ha, hr', _, hh⟩ := hBlock s hr (hc.mono hSub) ⟨hp, hf, hw⟩
  obtain ⟨hq, hw', hag⟩ := hPost s t ⟨hp, hf, hw⟩ hh
  exact ⟨fuel, t, ha, hr', hf.codeIn_final hag hc, hq, hw', hag⟩

theorem Seg.seqF [Bindings] {boundary : ReturnBoundary} {e : Env} {p q r : BitVec 64}
    {a b c : List Write} (h₁ : Seg boundary e p q a b) (h₂ : SegF boundary e q r b c) :
    SegF boundary e p r a c := by
  intro s hr hc hp hf hw
  obtain ⟨n, t, ha, hr', hc', hq, hf', hw', hag⟩ := h₁ s hr hc hp hf hw
  obtain ⟨m, u, ha', hr'', hc'', hq', hw'', hag'⟩ := h₂ t hr' hc' hq hf' hw'
  refine ⟨n + m, u, ha.trans ha', hr'', hc'', hq', hw'', (hag.trans hag').mono ?_⟩
  intro c hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · exact List.mem_append_left _ hc
  · exact hc

theorem Seg.of_block [Bindings] {boundary : ReturnBoundary} {e : Env} {p q : BitVec 64}
    {before after : List Write} {bytes : List UInt8} {E : RamState → Effect}
    (hBlock : AdvancesBlock boundary
      (fun s ↦ s.RIP = p ∧ Frame e s ∧ Write.AllHold s before) (codeRange p bytes) E)
    (hSub : ∀ x ∈ codeRange p bytes, x ∈ Extracted.programImage)
    (hPost : ∀ s t, s.RIP = p ∧ Frame e s ∧ Write.AllHold s before → (E s).Holds s t →
      t.RIP = q ∧ Write.AllHold t after ∧ AgreesExcept (bodyChanges e) s t) :
    Seg boundary e p q before after := by
  intro s hr hc hp hf hw
  obtain ⟨fuel, t, ha, hr', _, hh⟩ := hBlock s hr (hc.mono hSub) ⟨hp, hf, hw⟩
  obtain ⟨hq, hw', hag⟩ := hPost s t ⟨hp, hf, hw⟩ hh
  exact ⟨fuel, t, ha, hr', hf.codeIn hag hc, hq, hf.of_agrees hag, hw', hag⟩

theorem snap_get {s : RamState} {w : Write} {ws : List Write} (h : Write.AllHold s (w :: ws)) :
    w.dst.read s = w.val := by
  cases ws with
  | nil => exact h
  | cons _ _ => exact h.1

theorem snap_drop {s : RamState} {w : Write} {ws : List Write} (h : Write.AllHold s (w :: ws)) :
    Write.AllHold s ws := by
  cases ws with
  | nil => trivial
  | cons _ _ => exact h.2

theorem snap_reg {s : RamState} {r : BitVec 5} {v : BitVec 64} {ws : List Write}
    (h : Write.AllHold s (⟨(Operand.reg r : Operand 64), v⟩ :: ws)) :
    (Operand.reg r : Operand 64).read s = v :=
  snap_get h

theorem readable_at {s : RamState} {base a : BitVec 64} {L : Nat} (h : MemReadable s base L)
    (k n : Nat) (hk : k + n ≤ L) (ha : a = base + BitVec.ofNat 64 k) : MemReadable s a n :=
  ha ▸ memReadable_slice h k n hk

theorem writable_at {s : RamState} {base a : BitVec 64} {L : Nat} (h : WritableRange s base L)
    (k n : Nat) (hk : k + n ≤ L) (hn : 0 < n) (ha : a = base + BitVec.ofNat 64 k) :
    MemWritable s a n := by
  subst ha
  have hw := h.slice k n hk
  refine ⟨hw.readable.low, hw.readable.mem, ?_⟩
  have hlow := hw.readable.low
  have hbyte (i : Nat) (hi : i < n) :
      ¬ (0x1000 ≤ (base + BitVec.ofNat 64 k).toNat + i ∧
        (base + BitVec.ofNat 64 k).toNat + i < 0x2020) := by
    have ht := hw.tables i hi
    rw [inPageTables_iff, toNat_add_ofNat _ _ (by omega)] at ht
    exact ht
  generalize (base + BitVec.ofNat 64 k).toNat = x at hlow hbyte ⊢
  unfold PageTableEntriesApart
  by_cases h1 : 0x1000 ≤ x
  · have := hbyte 0 hn
    omega
  · by_cases h2 : x + n ≤ 0x1000
    · omega
    · have := hbyte (0x1000 - x) (by omega)
      omega

theorem program_text_subset (offset : Nat) {bytes : List UInt8}
    (h : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (hBound : offset + bytes.length ≤ Extracted.textBytes.size) :
    ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes,
      x ∈ Extracted.programImage := by
  intro x hx
  apply List.mem_flatMap.mpr
  refine ⟨⟨Extracted.textAddress, Extracted.textBytes⟩,
    by simp [Extracted.programSections], ?_⟩
  rw [← h, ← chunked_toList_slice _ _ _ hBound] at hx
  exact codeRange_slice_subset _ _ offset bytes.length x hx

theorem body_inProgram (j : Nat) (hj : j < 0x222) :
    InProgram (bodyEntry + BitVec.ofNat 64 j) := by
  have h := text_address_in_program (0x1ab0 + j) (by
    have : 0x1ab0 + 0x222 ≤ Extracted.textBytes.size := by decide +kernel
    omega)
  have he : Extracted.textAddress + BitVec.ofNat 64 (0x1ab0 + j) =
      bodyEntry + BitVec.ofNat 64 j := by
    simp only [Extracted.textAddress, bodyEntry]
    bv_omega
  rwa [he] at h

theorem apart_at {s : RamState} {base a : BitVec 64} {L : Nat} (h : WritableRange s base L)
    (k n : Nat) (hk : k + n ≤ L) (ha : a = base + BitVec.ofNat 64 k) (p : BitVec 64)
    (off len : Nat) (hp : p = bodyEntry + BitVec.ofNat 64 off) (hoff : off + len ≤ 0x222) :
    RangeApart a n p len := by
  intro i hi j hj he
  apply h.code (k + i) (by omega)
  rw [← add_ofNat_add_ofNat, ← ha, he, hp, add_ofNat_add_ofNat]
  exact body_inProgram (off + j) (by omega)

macro "e30_dec" : tactic => `(tactic| first
  | decide
  | (unfold RexWPrefix; decide)
  | (unfold RexNoWPrefix; decide)
  | (unfold RexPrefix; decide)
  | decide +kernel)

theorem Effect.seq_unfold (e₁ e₂ : RamState → Effect) :
    Effect.seq e₁ e₂ = fun s =>
      { rip := (e₂ ((e₁ s).after s true)).rip
        writes := ((e₁ s).writes.filter fun w =>
            !Write.shadowed (e₂ ((e₁ s).after s true)).writes w).map
            (Write.reread (applyWrites ((e₁ s).after s true)
              (e₂ ((e₁ s).after s true)).writes)) ++
          (e₂ ((e₁ s).after s true)).writes
        flags := if (e₁ s).flags.isNone && (e₂ ((e₁ s).after s true)).flags.isNone then none
          else some (StatusFlagsOutcome.ofFun fun i =>
            Effect.pick ((e₂ ((e₁ s).after s true)).flag ((e₁ s).after s true) i)
              ((e₂ ((e₁ s).after s false)).flag ((e₁ s).after s false) i)) } := rfl

theorem external_write_reg {n : Nat} (s : RamState) (r : BitVec 5) (v : BitVec n) :
    (Operand.write s (Operand.reg r) v).external = s.external := rfl

theorem external_write_mem {n : Nat} (s : RamState) (a : BitVec 64) (v : BitVec n) :
    (Operand.write s (Operand.mem a) v).external = memStore s.external a v := rfl

theorem lea5 (y : BitVec 64) : BitVec.setWidth 32 (y + y <<< 2) = y.setWidth 32 * 5#32 := by
  bv_omega

theorem u8_toBitVec_lit (n : Nat) : (OfNat.ofNat n : UInt8).toBitVec = BitVec.ofNat 8 n := rfl

syntax "e30_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| e30_norm $[[$ls,*]]? $[$loc]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| simp (config := { decide := true, implicitDefEqProofs := false }) only [x86_compose, BitVec.sub_eq_add_neg,
      gprNumber, rexR, rexB, modrmReg, modrmRm, opcodeReg, u8_toBitVec_lit, UInt8.toBitVec_ofNat, pushAddr_eq_read, BitVec.add_zero,
      BitVec.reduceExtractLsb', Nat.reduceShiftLeft, $ls,*] $[$loc]?)

macro "e30_addr" : tactic => `(tactic| (
  (try e30_norm) <;>
  (try simp only [stackBase, stackPtr_eq_read, rAddress, hAddress, rOffset, hOffset, stackBytes, rdi,
    rsi, bodyEntry, pushAddr]) <;>
  bv_omega))

macro "e30_clean" : tactic => `(tactic| simp (config := { decide := true, implicitDefEqProofs := false }) only [shiftCount, leaSpec, lea5, ofInt_toInt_mul, external_write_reg, external_write_mem,
  BitVec.setWidth_setWidth_of_le, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd,
  BitVec.reduceNeg, BitVec.reduceSetWidth, BitVec.reduceXOr, BitVec.reduceShiftLeft, BitVec.reduceAnd,
  BitVec.reduceHShiftLeft, BitVec.reduceUShiftRight, BitVec.reduceHShiftRight, Nat.reduceMod, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
  true_and, and_true, Nat.reduceLeDiff, x86_compose])

macro "e30_apart" : tactic => `(tactic| (
  (try simp only [Nat.reduceDiv])
  apply RangeApart.of_toNat <;> bv_omega))

macro "e30_then " t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_then ?k $t ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case full => x86_full
  ))

theorem AdvancesBlock.post [Bindings] {boundary : ReturnBoundary} {P : RamState → Prop}
    {code : CodeMap} {E : RamState → Effect} {Q : RamState → RamState → Prop}
    (h : AdvancesBlock boundary P code E) (hq : ∀ s t, P s → (E s).Holds s t → Q s t) :
    ∀ s, ReadyToStep s → CodeIn code s → P s →
      ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn code t ∧ Q s t := by
  intro s hr hc hp
  obtain ⟨fuel, t, ha, hr', hc', hh⟩ := h s hr hc hp
  exact ⟨fuel, t, ha, hr', hc', hq s t hp hh⟩

def c24_r0 (e : Env) : BitVec 64 :=
  ((e.r2 * (0x5#32))).setWidth 64

def c24_r3 (e : Env) : BitVec 64 :=
  ((e.r4 * (0x5#32))).setWidth 64

def c24_r8 (e : Env) : BitVec 64 :=
  (e.r0).setWidth 64

def c24_r9 (e : Env) : BitVec 64 :=
  ((e.r3 * (0x5#32))).setWidth 64

def c24_s56 (e : Env) : BitVec 64 :=
  (e.r4).setWidth 64

def c24_s64 (e : Env) : BitVec 64 :=
  (e.r3).setWidth 64

def c24_s72 (e : Env) : BitVec 64 :=
  (e.r2).setWidth 64

def c24_s80 (e : Env) : BitVec 64 :=
  ((e.r2 * (0x5#32))).setWidth 64

def c24_s88 (e : Env) : BitVec 64 :=
  ((e.r3 * (0x5#32))).setWidth 64

def c41_r7 (e : Env) : BitVec 64 :=
  ((((0x1000000#32) + e.h4) + (e.w4 >>> 8))).setWidth 64

def c41_r1 (e : Env) : BitVec 64 :=
  (((e.w3 >>> 6) + e.h3)).setWidth 64

def c41_r2 (e : Env) : BitVec 64 :=
  ((((e.w1 >>> 2) &&& (0x3ffffff#32)) + e.h1)).setWidth 64

def c41_r12 (e : Env) : BitVec 64 :=
  ((((e.w2 >>> 4) &&& (0x3ffffff#32)) + e.h2)).setWidth 64

def c41_r15 (e : Env) : BitVec 64 :=
  ((((0x3ffffff#32) &&& e.w0) + e.h0)).setWidth 64

def c56_r5 (e : Env) : BitVec 64 :=
  (e.r1).setWidth 64

def c56_r11 (e : Env) : BitVec 64 :=
  ((((e.r1 * (0x5#32))).setWidth 64 * (c41_r7 e)) + ((((c41_r1 e) * (c24_r0 e)) + ((c41_r12 e) * (c24_r9 e))) + (((c41_r2 e) * (c24_r3 e)) + ((c41_r15 e) * (c24_r8 e)))))

def c73_s80 (e : Env) : BitVec 64 :=
  (((c24_s80 e) * (c41_r7 e)) + ((((c41_r1 e) * (c24_s88 e)) + ((c41_r12 e) * (c24_r3 e))) + (((c41_r2 e) * (c24_r8 e)) + ((c41_r15 e) * (c56_r5 e)))))

def c89_s88 (e : Env) : BitVec 64 :=
  (((c24_s88 e) * (c41_r7 e)) + ((((c41_r1 e) * (c24_r3 e)) + ((c41_r12 e) * (c24_r8 e))) + (((c41_r2 e) * (c56_r5 e)) + ((c41_r15 e) * (c24_s72 e)))))

def c103_r3 (e : Env) : BitVec 64 :=
  (((c24_r3 e) * (c41_r7 e)) + ((((c41_r1 e) * (c24_r8 e)) + ((c41_r12 e) * (c56_r5 e))) + (((c41_r2 e) * (c24_s72 e)) + ((c41_r15 e) * (c24_s64 e)))))

def c112_r7 (e : Env) : BitVec 64 :=
  (((c41_r7 e) * (c24_r8 e)) + ((((c41_r1 e) * (c56_r5 e)) + ((c41_r12 e) * (c24_s72 e))) + (((c41_r2 e) * (c24_s64 e)) + ((c41_r15 e) * (c24_s56 e)))))

def c124_r0 (e : Env) : BitVec 64 :=
  ((((((((((c56_r11 e) >>> 26)).setWidth 32).setWidth 64 + (c73_s80 e)) >>> 26)).setWidth 32).setWidth 64 + (c89_s88 e)) >>> 26)

def c124_r8 (e : Env) : BitVec 64 :=
  ((((((((c56_r11 e) >>> 26)).setWidth 32).setWidth 64 + (c73_s80 e))).setWidth 32 &&& (0x3ffffff#32))).setWidth 64

def c124_r9 (e : Env) : BitVec 64 :=
  (((((((((c56_r11 e) >>> 26)).setWidth 32).setWidth 64 + (c73_s80 e)) >>> 26)).setWidth 32).setWidth 64 + (c89_s88 e))

def c124_r11 (e : Env) : BitVec 64 :=
  ((((c56_r11 e)).setWidth 32 &&& (0x3ffffff#32))).setWidth 64

def c138_r6 (e : Env) : BitVec 64 :=
  (((((((((((((((c124_r0 e)).setWidth 32).setWidth 64 + (c103_r3 e)) >>> 26)).setWidth 32).setWidth 64 + (c112_r7 e)) >>> 26)).setWidth 32 * (0x5#32)) + ((c124_r11 e)).setWidth 32) >>> 26) + ((c124_r8 e)).setWidth 32)).setWidth 64

def c138_r0 (e : Env) : BitVec 64 :=
  ((((((((c124_r0 e)).setWidth 32).setWidth 64 + (c103_r3 e)) >>> 26)).setWidth 32).setWidth 64 + (c112_r7 e))

def c138_r1 (e : Env) : BitVec 64 :=
  ((((((((((((((c124_r0 e)).setWidth 32).setWidth 64 + (c103_r3 e)) >>> 26)).setWidth 32).setWidth 64 + (c112_r7 e)) >>> 26)).setWidth 32 * (0x5#32)) + ((c124_r11 e)).setWidth 32) &&& (0x3ffffff#32))).setWidth 64

def c138_r2 (e : Env) : BitVec 64 :=
  ((((c124_r0 e)).setWidth 32).setWidth 64 + (c103_r3 e))

def cut0 (e : Env) : List Write :=
  [⟨(.reg 4 : Operand 64), e.sp⟩,
    ⟨(.reg 7 : Operand 64), e.st⟩,
    ⟨(.reg 6 : Operand 64), e.bp⟩,
    ⟨(.reg 2 : Operand 64), 0x0#64⟩,
    ⟨(.reg 3 : Operand 64), e.rbx⟩,
    ⟨(.reg 5 : Operand 64), e.rbp⟩,
    ⟨(.reg 12 : Operand 64), e.r12⟩,
    ⟨(.reg 13 : Operand 64), e.r13⟩,
    ⟨(.reg 14 : Operand 64), e.r14⟩,
    ⟨(.reg 15 : Operand 64), e.r15⟩]

def cut11 (e : Env) : List Write :=
  [⟨(.reg 4 : Operand 64), e.sp - 0x58#64⟩,
    ⟨(.reg 10 : Operand 64), e.st⟩,
    ⟨(.reg 7 : Operand 64), 0x1000000#64⟩,
    ⟨(.reg 6 : Operand 64), e.bp⟩,
    ⟨(.mem (e.sp - 0x8#64) : Operand 64), e.rbp⟩,
    ⟨(.mem (e.sp - 0x10#64) : Operand 64), e.r15⟩,
    ⟨(.mem (e.sp - 0x18#64) : Operand 64), e.r14⟩,
    ⟨(.mem (e.sp - 0x20#64) : Operand 64), e.r13⟩,
    ⟨(.mem (e.sp - 0x28#64) : Operand 64), e.r12⟩,
    ⟨(.mem (e.sp - 0x30#64) : Operand 64), e.rbx⟩]

def cut24 (e : Env) : List Write :=
  [⟨(.reg 4 : Operand 64), e.sp - 0x58#64⟩,
    ⟨(.reg 10 : Operand 64), e.st⟩,
    ⟨(.reg 7 : Operand 64), 0x1000000#64⟩,
    ⟨(.reg 6 : Operand 64), e.bp⟩,
    ⟨(.reg 0 : Operand 64), (c24_r0 e)⟩,
    ⟨(.reg 3 : Operand 64), (c24_r3 e)⟩,
    ⟨(.reg 8 : Operand 64), (c24_r8 e)⟩,
    ⟨(.reg 9 : Operand 64), (c24_r9 e)⟩,
    ⟨(.reg 15 : Operand 64), 0x3ffffff#64⟩,
    ⟨(.mem (e.sp - 0x8#64) : Operand 64), e.rbp⟩,
    ⟨(.mem (e.sp - 0x10#64) : Operand 64), e.r15⟩,
    ⟨(.mem (e.sp - 0x18#64) : Operand 64), e.r14⟩,
    ⟨(.mem (e.sp - 0x20#64) : Operand 64), e.r13⟩,
    ⟨(.mem (e.sp - 0x28#64) : Operand 64), e.r12⟩,
    ⟨(.mem (e.sp - 0x30#64) : Operand 64), e.rbx⟩,
    ⟨(.mem (e.sp - 0x38#64) : Operand 64), (c24_s56 e)⟩,
    ⟨(.mem (e.sp - 0x40#64) : Operand 64), (c24_s64 e)⟩,
    ⟨(.mem (e.sp - 0x48#64) : Operand 64), (c24_s72 e)⟩,
    ⟨(.mem (e.sp - 0x50#64) : Operand 64), (c24_s80 e)⟩,
    ⟨(.mem (e.sp - 0x58#64) : Operand 64), (c24_s88 e)⟩]

def cut41 (e : Env) : List Write :=
  [⟨(.reg 4 : Operand 64), e.sp - 0x58#64⟩,
    ⟨(.reg 10 : Operand 64), e.st⟩,
    ⟨(.reg 7 : Operand 64), (c41_r7 e)⟩,
    ⟨(.reg 0 : Operand 64), (c24_r0 e)⟩,
    ⟨(.reg 1 : Operand 64), (c41_r1 e)⟩,
    ⟨(.reg 2 : Operand 64), (c41_r2 e)⟩,
    ⟨(.reg 3 : Operand 64), (c24_r3 e)⟩,
    ⟨(.reg 8 : Operand 64), (c24_r8 e)⟩,
    ⟨(.reg 9 : Operand 64), (c24_r9 e)⟩,
    ⟨(.reg 12 : Operand 64), (c41_r12 e)⟩,
    ⟨(.reg 15 : Operand 64), (c41_r15 e)⟩,
    ⟨(.mem (e.sp - 0x8#64) : Operand 64), e.rbp⟩,
    ⟨(.mem (e.sp - 0x10#64) : Operand 64), e.r15⟩,
    ⟨(.mem (e.sp - 0x18#64) : Operand 64), e.r14⟩,
    ⟨(.mem (e.sp - 0x20#64) : Operand 64), e.r13⟩,
    ⟨(.mem (e.sp - 0x28#64) : Operand 64), e.r12⟩,
    ⟨(.mem (e.sp - 0x30#64) : Operand 64), e.rbx⟩,
    ⟨(.mem (e.sp - 0x38#64) : Operand 64), (c24_s56 e)⟩,
    ⟨(.mem (e.sp - 0x40#64) : Operand 64), (c24_s64 e)⟩,
    ⟨(.mem (e.sp - 0x48#64) : Operand 64), (c24_s72 e)⟩,
    ⟨(.mem (e.sp - 0x50#64) : Operand 64), (c24_s80 e)⟩,
    ⟨(.mem (e.sp - 0x58#64) : Operand 64), (c24_s88 e)⟩]

def cut56 (e : Env) : List Write :=
  [⟨(.reg 4 : Operand 64), e.sp - 0x58#64⟩,
    ⟨(.reg 10 : Operand 64), e.st⟩,
    ⟨(.reg 7 : Operand 64), (c41_r7 e)⟩,
    ⟨(.reg 1 : Operand 64), (c41_r1 e)⟩,
    ⟨(.reg 2 : Operand 64), (c41_r2 e)⟩,
    ⟨(.reg 3 : Operand 64), (c24_r3 e)⟩,
    ⟨(.reg 5 : Operand 64), (c56_r5 e)⟩,
    ⟨(.reg 8 : Operand 64), (c24_r8 e)⟩,
    ⟨(.reg 11 : Operand 64), (c56_r11 e)⟩,
    ⟨(.reg 12 : Operand 64), (c41_r12 e)⟩,
    ⟨(.reg 15 : Operand 64), (c41_r15 e)⟩,
    ⟨(.mem (e.sp - 0x8#64) : Operand 64), e.rbp⟩,
    ⟨(.mem (e.sp - 0x10#64) : Operand 64), e.r15⟩,
    ⟨(.mem (e.sp - 0x18#64) : Operand 64), e.r14⟩,
    ⟨(.mem (e.sp - 0x20#64) : Operand 64), e.r13⟩,
    ⟨(.mem (e.sp - 0x28#64) : Operand 64), e.r12⟩,
    ⟨(.mem (e.sp - 0x30#64) : Operand 64), e.rbx⟩,
    ⟨(.mem (e.sp - 0x38#64) : Operand 64), (c24_s56 e)⟩,
    ⟨(.mem (e.sp - 0x40#64) : Operand 64), (c24_s64 e)⟩,
    ⟨(.mem (e.sp - 0x48#64) : Operand 64), (c24_s72 e)⟩,
    ⟨(.mem (e.sp - 0x50#64) : Operand 64), (c24_s80 e)⟩,
    ⟨(.mem (e.sp - 0x58#64) : Operand 64), (c24_s88 e)⟩]

def cut73 (e : Env) : List Write :=
  [⟨(.reg 4 : Operand 64), e.sp - 0x58#64⟩,
    ⟨(.reg 10 : Operand 64), e.st⟩,
    ⟨(.reg 7 : Operand 64), (c41_r7 e)⟩,
    ⟨(.reg 1 : Operand 64), (c41_r1 e)⟩,
    ⟨(.reg 2 : Operand 64), (c41_r2 e)⟩,
    ⟨(.reg 3 : Operand 64), (c24_r3 e)⟩,
    ⟨(.reg 5 : Operand 64), (c56_r5 e)⟩,
    ⟨(.reg 8 : Operand 64), (c24_s88 e)⟩,
    ⟨(.reg 9 : Operand 64), (c24_r8 e)⟩,
    ⟨(.reg 11 : Operand 64), (c56_r11 e)⟩,
    ⟨(.reg 12 : Operand 64), (c41_r12 e)⟩,
    ⟨(.reg 15 : Operand 64), (c41_r15 e)⟩,
    ⟨(.mem (e.sp - 0x8#64) : Operand 64), e.rbp⟩,
    ⟨(.mem (e.sp - 0x10#64) : Operand 64), e.r15⟩,
    ⟨(.mem (e.sp - 0x18#64) : Operand 64), e.r14⟩,
    ⟨(.mem (e.sp - 0x20#64) : Operand 64), e.r13⟩,
    ⟨(.mem (e.sp - 0x28#64) : Operand 64), e.r12⟩,
    ⟨(.mem (e.sp - 0x30#64) : Operand 64), e.rbx⟩,
    ⟨(.mem (e.sp - 0x38#64) : Operand 64), (c24_s56 e)⟩,
    ⟨(.mem (e.sp - 0x40#64) : Operand 64), (c24_s64 e)⟩,
    ⟨(.mem (e.sp - 0x48#64) : Operand 64), (c24_s72 e)⟩,
    ⟨(.mem (e.sp - 0x50#64) : Operand 64), (c73_s80 e)⟩]

def cut89 (e : Env) : List Write :=
  [⟨(.reg 4 : Operand 64), e.sp - 0x58#64⟩,
    ⟨(.reg 10 : Operand 64), e.st⟩,
    ⟨(.reg 7 : Operand 64), (c41_r7 e)⟩,
    ⟨(.reg 6 : Operand 64), (c24_s72 e)⟩,
    ⟨(.reg 1 : Operand 64), (c41_r1 e)⟩,
    ⟨(.reg 2 : Operand 64), (c41_r2 e)⟩,
    ⟨(.reg 3 : Operand 64), (c24_r3 e)⟩,
    ⟨(.reg 5 : Operand 64), (c56_r5 e)⟩,
    ⟨(.reg 9 : Operand 64), (c24_r8 e)⟩,
    ⟨(.reg 11 : Operand 64), (c56_r11 e)⟩,
    ⟨(.reg 12 : Operand 64), (c41_r12 e)⟩,
    ⟨(.reg 15 : Operand 64), (c41_r15 e)⟩,
    ⟨(.mem (e.sp - 0x8#64) : Operand 64), e.rbp⟩,
    ⟨(.mem (e.sp - 0x10#64) : Operand 64), e.r15⟩,
    ⟨(.mem (e.sp - 0x18#64) : Operand 64), e.r14⟩,
    ⟨(.mem (e.sp - 0x20#64) : Operand 64), e.r13⟩,
    ⟨(.mem (e.sp - 0x28#64) : Operand 64), e.r12⟩,
    ⟨(.mem (e.sp - 0x30#64) : Operand 64), e.rbx⟩,
    ⟨(.mem (e.sp - 0x38#64) : Operand 64), (c24_s56 e)⟩,
    ⟨(.mem (e.sp - 0x40#64) : Operand 64), (c24_s64 e)⟩,
    ⟨(.mem (e.sp - 0x50#64) : Operand 64), (c73_s80 e)⟩,
    ⟨(.mem (e.sp - 0x58#64) : Operand 64), (c89_s88 e)⟩]

def cut103 (e : Env) : List Write :=
  [⟨(.reg 4 : Operand 64), e.sp - 0x58#64⟩,
    ⟨(.reg 10 : Operand 64), e.st⟩,
    ⟨(.reg 7 : Operand 64), (c41_r7 e)⟩,
    ⟨(.reg 6 : Operand 64), (c24_s72 e)⟩,
    ⟨(.reg 1 : Operand 64), (c41_r1 e)⟩,
    ⟨(.reg 2 : Operand 64), (c41_r2 e)⟩,
    ⟨(.reg 3 : Operand 64), (c103_r3 e)⟩,
    ⟨(.reg 5 : Operand 64), (c56_r5 e)⟩,
    ⟨(.reg 8 : Operand 64), (c24_s64 e)⟩,
    ⟨(.reg 9 : Operand 64), (c24_r8 e)⟩,
    ⟨(.reg 11 : Operand 64), (c56_r11 e)⟩,
    ⟨(.reg 12 : Operand 64), (c41_r12 e)⟩,
    ⟨(.reg 15 : Operand 64), (c41_r15 e)⟩,
    ⟨(.mem (e.sp - 0x8#64) : Operand 64), e.rbp⟩,
    ⟨(.mem (e.sp - 0x10#64) : Operand 64), e.r15⟩,
    ⟨(.mem (e.sp - 0x18#64) : Operand 64), e.r14⟩,
    ⟨(.mem (e.sp - 0x20#64) : Operand 64), e.r13⟩,
    ⟨(.mem (e.sp - 0x28#64) : Operand 64), e.r12⟩,
    ⟨(.mem (e.sp - 0x30#64) : Operand 64), e.rbx⟩,
    ⟨(.mem (e.sp - 0x38#64) : Operand 64), (c24_s56 e)⟩,
    ⟨(.mem (e.sp - 0x50#64) : Operand 64), (c73_s80 e)⟩,
    ⟨(.mem (e.sp - 0x58#64) : Operand 64), (c89_s88 e)⟩]

def cut112 (e : Env) : List Write :=
  [⟨(.reg 4 : Operand 64), e.sp - 0x58#64⟩,
    ⟨(.reg 10 : Operand 64), e.st⟩,
    ⟨(.reg 7 : Operand 64), (c112_r7 e)⟩,
    ⟨(.reg 3 : Operand 64), (c103_r3 e)⟩,
    ⟨(.reg 11 : Operand 64), (c56_r11 e)⟩,
    ⟨(.mem (e.sp - 0x8#64) : Operand 64), e.rbp⟩,
    ⟨(.mem (e.sp - 0x10#64) : Operand 64), e.r15⟩,
    ⟨(.mem (e.sp - 0x18#64) : Operand 64), e.r14⟩,
    ⟨(.mem (e.sp - 0x20#64) : Operand 64), e.r13⟩,
    ⟨(.mem (e.sp - 0x28#64) : Operand 64), e.r12⟩,
    ⟨(.mem (e.sp - 0x30#64) : Operand 64), e.rbx⟩,
    ⟨(.mem (e.sp - 0x50#64) : Operand 64), (c73_s80 e)⟩,
    ⟨(.mem (e.sp - 0x58#64) : Operand 64), (c89_s88 e)⟩]

def cut124 (e : Env) : List Write :=
  [⟨(.reg 4 : Operand 64), e.sp - 0x58#64⟩,
    ⟨(.reg 10 : Operand 64), e.st⟩,
    ⟨(.reg 7 : Operand 64), (c112_r7 e)⟩,
    ⟨(.reg 0 : Operand 64), (c124_r0 e)⟩,
    ⟨(.reg 3 : Operand 64), (c103_r3 e)⟩,
    ⟨(.reg 8 : Operand 64), (c124_r8 e)⟩,
    ⟨(.reg 9 : Operand 64), (c124_r9 e)⟩,
    ⟨(.reg 11 : Operand 64), (c124_r11 e)⟩,
    ⟨(.mem (e.sp - 0x8#64) : Operand 64), e.rbp⟩,
    ⟨(.mem (e.sp - 0x10#64) : Operand 64), e.r15⟩,
    ⟨(.mem (e.sp - 0x18#64) : Operand 64), e.r14⟩,
    ⟨(.mem (e.sp - 0x20#64) : Operand 64), e.r13⟩,
    ⟨(.mem (e.sp - 0x28#64) : Operand 64), e.r12⟩,
    ⟨(.mem (e.sp - 0x30#64) : Operand 64), e.rbx⟩]

def cut138 (e : Env) : List Write :=
  [⟨(.reg 4 : Operand 64), e.sp - 0x58#64⟩,
    ⟨(.reg 10 : Operand 64), e.st⟩,
    ⟨(.reg 6 : Operand 64), (c138_r6 e)⟩,
    ⟨(.reg 0 : Operand 64), (c138_r0 e)⟩,
    ⟨(.reg 1 : Operand 64), (c138_r1 e)⟩,
    ⟨(.reg 2 : Operand 64), (c138_r2 e)⟩,
    ⟨(.reg 9 : Operand 64), (c124_r9 e)⟩,
    ⟨(.mem (e.sp - 0x8#64) : Operand 64), e.rbp⟩,
    ⟨(.mem (e.sp - 0x10#64) : Operand 64), e.r15⟩,
    ⟨(.mem (e.sp - 0x18#64) : Operand 64), e.r14⟩,
    ⟨(.mem (e.sp - 0x20#64) : Operand 64), e.r13⟩,
    ⟨(.mem (e.sp - 0x28#64) : Operand 64), e.r12⟩,
    ⟨(.mem (e.sp - 0x30#64) : Operand 64), e.rbx⟩]

def fin_h0 (e : Env) : BitVec 32 :=
  ((c138_r1 e)).setWidth 32

def fin_h1 (e : Env) : BitVec 32 :=
  ((c138_r6 e)).setWidth 32

def fin_h2 (e : Env) : BitVec 32 :=
  (((c124_r9 e)).setWidth 32 &&& (0x3ffffff#32))

def fin_h3 (e : Env) : BitVec 32 :=
  (((c138_r2 e)).setWidth 32 &&& (0x3ffffff#32))

def fin_h4 (e : Env) : BitVec 32 :=
  (((c138_r0 e)).setWidth 32 &&& (0x3ffffff#32))

def cut153 (e : Env) : List Write :=
  [⟨(.reg 4 : Operand 64), e.sp⟩,
    ⟨(.reg 3 : Operand 64), e.rbx⟩,
    ⟨(.reg 5 : Operand 64), e.rbp⟩,
    ⟨(.reg 12 : Operand 64), e.r12⟩,
    ⟨(.reg 13 : Operand 64), e.r13⟩,
    ⟨(.reg 14 : Operand 64), e.r14⟩,
    ⟨(.reg 15 : Operand 64), e.r15⟩,
    ⟨(.mem (e.st + 0x24) : Operand 32), fin_h0 e⟩,
    ⟨(.mem (e.st + 0x28) : Operand 32), fin_h1 e⟩,
    ⟨(.mem (e.st + 0x2c) : Operand 32), fin_h2 e⟩,
    ⟨(.mem (e.st + 0x30) : Operand 32), fin_h3 e⟩,
    ⟨(.mem (e.st + 0x34) : Operand 32), fin_h4 e⟩]

theorem fin_eq0 (e : Env) :
    fin_h0 e = blockStep (limbs5 e.r0 e.r1 e.r2 e.r3 e.r4) (limbs5 e.h0 e.h1 e.h2 e.h3 e.h4)
      (limbs5 e.w0 e.w1 e.w2 e.w3 e.w4) 0x1000000 0 := by
  simp only [fin_h4, fin_h3, fin_h2, fin_h1, fin_h0, c138_r2, c138_r1, c138_r0, c138_r6, c124_r11, c124_r9, c124_r8, c124_r0, c112_r7, c103_r3, c89_s88, c73_s80, c56_r11, c56_r5, c41_r15, c41_r12, c41_r2, c41_r1, c41_r7, c24_s88, c24_s80, c24_s72, c24_s64, c24_s56, c24_r9, c24_r8, c24_r3, c24_r0]
  simp only [blockStep, mac5, wide, lo26, hi26, mask26, msgLimbs, limbs5_0, limbs5_1, limbs5_2,
    limbs5_3, limbs5_4, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
    Nat.reduceLeDiff]
  ac_rfl

theorem fin_eq1 (e : Env) :
    fin_h1 e = blockStep (limbs5 e.r0 e.r1 e.r2 e.r3 e.r4) (limbs5 e.h0 e.h1 e.h2 e.h3 e.h4)
      (limbs5 e.w0 e.w1 e.w2 e.w3 e.w4) 0x1000000 1 := by
  simp only [fin_h4, fin_h3, fin_h2, fin_h1, fin_h0, c138_r2, c138_r1, c138_r0, c138_r6, c124_r11, c124_r9, c124_r8, c124_r0, c112_r7, c103_r3, c89_s88, c73_s80, c56_r11, c56_r5, c41_r15, c41_r12, c41_r2, c41_r1, c41_r7, c24_s88, c24_s80, c24_s72, c24_s64, c24_s56, c24_r9, c24_r8, c24_r3, c24_r0]
  simp only [blockStep, mac5, wide, lo26, hi26, mask26, msgLimbs, limbs5_0, limbs5_1, limbs5_2,
    limbs5_3, limbs5_4, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
    Nat.reduceLeDiff]
  ac_rfl

theorem fin_eq2 (e : Env) :
    fin_h2 e = blockStep (limbs5 e.r0 e.r1 e.r2 e.r3 e.r4) (limbs5 e.h0 e.h1 e.h2 e.h3 e.h4)
      (limbs5 e.w0 e.w1 e.w2 e.w3 e.w4) 0x1000000 2 := by
  simp only [fin_h4, fin_h3, fin_h2, fin_h1, fin_h0, c138_r2, c138_r1, c138_r0, c138_r6, c124_r11, c124_r9, c124_r8, c124_r0, c112_r7, c103_r3, c89_s88, c73_s80, c56_r11, c56_r5, c41_r15, c41_r12, c41_r2, c41_r1, c41_r7, c24_s88, c24_s80, c24_s72, c24_s64, c24_s56, c24_r9, c24_r8, c24_r3, c24_r0]
  simp only [blockStep, mac5, wide, lo26, hi26, mask26, msgLimbs, limbs5_0, limbs5_1, limbs5_2,
    limbs5_3, limbs5_4, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
    Nat.reduceLeDiff]
  ac_rfl

theorem fin_eq3 (e : Env) :
    fin_h3 e = blockStep (limbs5 e.r0 e.r1 e.r2 e.r3 e.r4) (limbs5 e.h0 e.h1 e.h2 e.h3 e.h4)
      (limbs5 e.w0 e.w1 e.w2 e.w3 e.w4) 0x1000000 3 := by
  simp only [fin_h4, fin_h3, fin_h2, fin_h1, fin_h0, c138_r2, c138_r1, c138_r0, c138_r6, c124_r11, c124_r9, c124_r8, c124_r0, c112_r7, c103_r3, c89_s88, c73_s80, c56_r11, c56_r5, c41_r15, c41_r12, c41_r2, c41_r1, c41_r7, c24_s88, c24_s80, c24_s72, c24_s64, c24_s56, c24_r9, c24_r8, c24_r3, c24_r0]
  simp only [blockStep, mac5, wide, lo26, hi26, mask26, msgLimbs, limbs5_0, limbs5_1, limbs5_2,
    limbs5_3, limbs5_4, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
    Nat.reduceLeDiff]
  ac_rfl

theorem fin_eq4 (e : Env) :
    fin_h4 e = blockStep (limbs5 e.r0 e.r1 e.r2 e.r3 e.r4) (limbs5 e.h0 e.h1 e.h2 e.h3 e.h4)
      (limbs5 e.w0 e.w1 e.w2 e.w3 e.w4) 0x1000000 4 := by
  simp only [fin_h4, fin_h3, fin_h2, fin_h1, fin_h0, c138_r2, c138_r1, c138_r0, c138_r6, c124_r11, c124_r9, c124_r8, c124_r0, c112_r7, c103_r3, c89_s88, c73_s80, c56_r11, c56_r5, c41_r15, c41_r12, c41_r2, c41_r1, c41_r7, c24_s88, c24_s80, c24_s72, c24_s64, c24_s56, c24_r9, c24_r8, c24_r3, c24_r0]
  simp only [blockStep, mac5, wide, lo26, hi26, mask26, msgLimbs, limbs5_0, limbs5_1, limbs5_2,
    limbs5_3, limbs5_4, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
    Nat.reduceLeDiff]
  ac_rfl

end Body

end ChaCha20Poly1305.Proofs.Poly1305.Callee101e30
