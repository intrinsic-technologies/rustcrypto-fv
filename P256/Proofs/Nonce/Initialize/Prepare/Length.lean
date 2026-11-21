import P256.Proofs.Nonce.Initialize.Prepare.Scan
import P256.Proofs.Nonce.Initialize.Prepare.Length.Setup
import P256.Proofs.Nonce.Initialize.Prepare.Length.Middle
import P256.Proofs.Nonce.Initialize.Prepare.Length.Tail

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Encoding.Serialize

structure LengthReady [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop where
  stage : Stage initial s boundary
  output : memLoad s.external (stackPtr s + 192) 64 = initial.regValue .rdi
  secret : memLoad s.external (stackPtr s + 184) 64 = initial.regValue .rsi
  length : memLoad s.external (stackPtr s + 176) 64 = 32
  entropy : memLoad s.external (stackPtr s + 168) 64 = 1
  source : s.regValue .rax = initial.regValue .rcx
  order0 : s.regValue .r15 = 0xf3b9cac2fc632551
  order1 : s.regValue .r14 = 0xbce6faada7179e84
  order2 : s.regValue .r13 = 0xffffffffffffffff
  order3 : s.regValue .rbx = 0xffffffff00000000
  count : s.regValue .rsi = 32
  bits : s.regValue .r9 = 256
  shift : s.regValue .rbp = 0

theorem length_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (state : Scanned initial s boundary) (rip : s.RIP = 0x107858) :
    ∃ t, LengthReady initial t boundary ∧ t.RIP = 0x107916 := by
  obtain ⟨a, aa, ar, ap, ag⟩ := Length.guards
    (readyToStep state.stage.machine state.stage.bindingsSupported) state.stage.loaded rip
    state.count pre.outerBoundary
  have af := state.stage.after_registers aa ar ag (by simp [Component.Covers]) (by simp)
  obtain ⟨b, bf, bp, word, bg⟩ := Length.setup pre af ap
  have spa : stackPtr a = stackPtr s := by rw [af.rsp, state.stage.rsp]
  have spb : stackPtr b = stackPtr s := by rw [bf.rsp, state.stage.rsp]
  have bg' : AgreesExcept [.mem (stackPtr s + 168) 8, .reg 7, .rip] a b := by
    simpa only [spa] using bg
  obtain ⟨c, ca, cr, cp, cs, cg⟩ := Length.high_limb
    (readyToStep bf.machine bf.bindingsSupported) bf.loaded bp
    (((ag.trans bg').read (n := 64) (r := 3) (by simp)).trans state.order3) pre.outerBoundary
  have cf := bf.after_registers ca cr cg (by simp [Component.Covers]) (by simp)
  have abc := (ag.trans bg').trans cg
  obtain ⟨d, da, dr, dp, dc, dd, dg⟩ := Length.middle_limbs cr cf.loaded cp
    ((abc.read (n := 64) (r := 1) (by simp)).trans state.rcx)
    ((abc.read (n := 64) (r := 2) (by simp)).trans state.rdx) cs pre.outerBoundary
  have df := cf.after_registers da dr dg (by simp [Component.Covers]) (by simp)
  have spd : stackPtr d = stackPtr s := by rw [df.rsp, state.stage.rsp]
  have abcd := abc.trans dg
  have scratch : memLoad d.external (stackPtr d + 8) 8 = 0 := by
    rw [spd]
    refine (read_mem_of_agrees abcd _ ?_).trans state.scratch
    intro i hi component hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (((rfl | rfl | rfl) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl | rfl)) | (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals try exact id
    rintro ⟨j, hj, he⟩
    exact OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide)
      (by unfold OffsetsApart; decide +kernel) he
  obtain ⟨e, ef, ep, ec, eg⟩ := Length.low_limb pre df dp dc dd scratch
  have abcde := abcd.trans eg
  obtain ⟨t, tf, tp, tb, ts, tn, tw, tg⟩ := Length.tail pre ef ep
    ((abcde.read (n := 64) (r := 8) (by simp)).trans state.count) ec
    ((abcde.read (n := 64) (r := 11) (by simp)).trans state.length)
  have spe : stackPtr e = stackPtr s := by rw [ef.rsp, state.stage.rsp]
  have spt : stackPtr t = stackPtr s := by rw [tf.rsp, state.stage.rsp]
  have tg' : AgreesExcept [.mem (stackPtr s + 176) 8, .reg 9, .reg 2, .reg 5,
      .reg 6, .flags, .rip] e t := by simpa only [spe] using tg
  have total : AgreesExcept [.mem (stackPtr s + 168) 8, .mem (stackPtr s + 176) 8,
      .reg 7, .reg 9, .reg 6, .reg 1, .reg 2, .reg 5, .flags, .rip] s t :=
    (abcde.trans tg').mono (by simp)
  have outputPreserved (offset : Nat) (ho : offset = 184 ∨ offset = 192) :
      memLoad t.external (stackPtr s + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr s + BitVec.ofNat 64 offset) 64 := by
    apply read_mem_of_agrees total
    intro i hi component hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact id
    all_goals rintro ⟨j, hj, he⟩
    all_goals apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide) _ he
    all_goals rcases ho with rfl | rfl <;> unfold OffsetsApart <;> decide +kernel
  refine ⟨t, ⟨tf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ts, tn, tb⟩, tp⟩
  · rw [spt]
    exact (outputPreserved 192 (.inr rfl)).trans state.output
  · rw [spt]
    exact (outputPreserved 184 (.inl rfl)).trans state.secret
  · rw [spt]
    simpa only [spe] using tw
  · rw [spt]
    have later : AgreesExcept [.mem (stackPtr s + 176) 8, .reg 9, .reg 6, .reg 1,
        .reg 2, .reg 7, .reg 5, .flags, .rip] b t :=
      (((cg.trans dg).trans eg).trans tg').mono (by simp)
    refine (read_mem_of_agrees later _ ?_).trans ?_
    · intro i hi component hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact id
      rintro ⟨j, hj, he⟩
      exact OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide)
        (by unfold OffsetsApart; decide +kernel) he
    · have nine : a.regValue .r9 = 1 := (ag.read (n := 64) (r := 9) (by simp)).trans state.entropy
      change memLoad b.external (stackPtr s + 168) 64 = 1
      simpa only [spa, nine] using word
  · exact (total.read (n := 64) (r := 0) (by simp)).trans state.source
  · exact (total.read (n := 64) (r := 15) (by simp)).trans state.order0
  · exact (total.read (n := 64) (r := 14) (by simp)).trans state.order1
  · exact (total.read (n := 64) (r := 13) (by simp)).trans state.order2
  · exact (total.read (n := 64) (r := 3) (by simp)).trans state.order3

end P256.Proofs.Nonce.Initialize.Prepare
