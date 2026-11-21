import P256.Proofs.Nonce.Initialize.Prepare.Scan.Tail

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Encoding.Serialize

structure Scanned [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop where
  stage : Stage initial s boundary
  output : memLoad s.external (stackPtr s + 192) 64 = initial.regValue .rdi
  secret : memLoad s.external (stackPtr s + 184) 64 = initial.regValue .rsi
  length : s.regValue .r11 = 32
  count : s.regValue .r8 = 32
  source : s.regValue .rax = initial.regValue .rcx
  entropy : s.regValue .r9 = 1
  order0 : s.regValue .r15 = 0xf3b9cac2fc632551
  order1 : s.regValue .r14 = 0xbce6faada7179e84
  order2 : s.regValue .r13 = 0xffffffffffffffff
  order3 : s.regValue .rbx = 0xffffffff00000000
  rcx : s.regValue .rcx = 0
  rdx : s.regValue .rdx = 0
  rbp : s.regValue .rbp = 0
  scratch : memLoad s.external (stackPtr s + 8) 8 = 0

theorem scan_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (state : OrderLoaded initial s boundary orderAddress) (rip : s.RIP = 0x107808) :
    ∃ t, Scanned initial t boundary ∧ t.RIP = 0x107858 := by
  have high : s.regValue .rbp = 0xffffffff00000000 := by
    exact state.order3.trans ((pre.order.memLoad_limb 3 (by decide)).trans (by decide +kernel))
  obtain ⟨a, fa, ra, ca, sa, secret, ga⟩ := Scan.setup pre state.stage rip
  obtain ⟨b, fb, rb, bb, cb, pb, tb, sb, gb⟩ := Scan.head pre fa ra (ca.trans high)
  obtain ⟨t, ft, rt, dt, pt, st, gt⟩ := Scan.tail pre fb rb pb tb
  have spa : stackPtr a = stackPtr s := ga.read (n := 64) (r := 4) (by simp)
  have spb : stackPtr b = stackPtr s := (gb.read (n := 64) (r := 4) (by simp)).trans spa
  have spt : stackPtr t = stackPtr s := (gt.read (n := 64) (r := 4) (by simp)).trans spb
  have gbc : AgreesExcept [.mem (stackPtr s + 8) 1, .reg 5, .reg 3, .reg 1,
      .reg 10, .flags, .rip] a b := by simpa only [spa] using gb
  have gtc : AgreesExcept [.mem (stackPtr s + 8) 1, .reg 5, .reg 2, .flags, .rip] b t := by
    simpa only [spb] using gt
  have total : AgreesExcept [.mem (stackPtr s + 184) 8, .mem (stackPtr s + 8) 1,
      .reg 7, .reg 6, .reg 1, .reg 5, .reg 3, .reg 10, .reg 2, .flags, .rip] s t :=
    ((ga.trans gbc).trans gtc).mono (by simp)
  refine ⟨t, ⟨ft, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, dt, pt, ?_⟩, rt⟩
  · rw [spt]
    refine (read_mem_of_agrees total _ ?_).trans state.output
    intro i hi c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact id
    all_goals rintro ⟨j, hj, he⟩
    all_goals apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide) _ he
    all_goals unfold OffsetsApart; decide +kernel
  · rw [spt]
    refine (read_mem_of_agrees (gbc.trans gtc) _ ?_).trans (secret.trans state.secret)
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)
    all_goals try exact id
    all_goals rintro ⟨j, hj, he⟩
    all_goals apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide) _ he
    all_goals unfold OffsetsApart; decide +kernel
  · exact (total.read (n := 64) (r := 11) (by simp)).trans state.length
  · exact (total.read (n := 64) (r := 8) (by simp)).trans state.count
  · exact (total.read (n := 64) (r := 0) (by simp)).trans state.source
  · exact (total.read (n := 64) (r := 9) (by simp)).trans state.entropy
  · have h := pre.order.memLoad_limb 0 (by decide)
    simp only [Nat.mul_zero, BitVec.add_zero] at h
    exact ((total.read (n := 64) (r := 15) (by simp)).trans state.order0).trans
      (h.trans (by decide +kernel))
  · exact ((total.read (n := 64) (r := 14) (by simp)).trans state.order1).trans
      ((pre.order.memLoad_limb 1 (by decide)).trans (by decide +kernel))
  · exact ((total.read (n := 64) (r := 13) (by simp)).trans state.order2).trans
      ((pre.order.memLoad_limb 2 (by decide)).trans (by decide +kernel))
  · exact (gt.read (n := 64) (r := 3) (by simp)).trans bb
  · exact (gt.read (n := 64) (r := 1) (by simp)).trans cb
  · rw [spt]
    simpa only [spb] using st

end P256.Proofs.Nonce.Initialize.Prepare
