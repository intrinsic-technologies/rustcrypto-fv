import P256.Proofs.Program.Copy.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Program.Copy

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem CopyState.step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {count : Nat} {code : CodeMap} {pre : RamState → Prop} {effect : RamState → Effect}
    (h : CopyState s t count) (hi : StepEffect pre code effect) (hc : CodeIn code t)
    (hp : pre t) (hne : (effect t).rip ≠ boundary.rip)
    (hcomp : ∀ c ∈ (effect t).components, c ∈ registerComponents) :
    ∃ u, Advances boundary 1 t u ∧ CopyState s u count ∧ (effect t).Holds t u := by
  obtain ⟨u, ha, hr, he⟩ := hi.advances h.ready hc hp hne
  exact ⟨u, ha, h.registers hr (he.agrees.mono hcomp), he⟩

theorem middle [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n reserve count : Nat} (hp : CalleePre s boundary 0x11c930 n n reserve)
    (h : CopyState s t count) (hcount : count ≤ n) (hn : n < 2^64)
    (hrip : t.RIP = 0x11c949) (hdx : t.regValue .rdx = BitVec.ofNat 64 n)
    (h8 : t.regValue .r8 = BitVec.ofNat 64 count) :
    ∃ u, Advances boundary 3 t u ∧ CopyState s u count ∧ u.RIP = 0x11c953 ∧
      u.regValue .rdx = BitVec.ofNat 64 (n-count) ∧
      rcx.read u = BitVec.ofNat 64 ((n-count)/8) := by
  have i1 := sub_r64_r64_effect_step 0x11c949 0x4c 0xc2 (by simp [RexWPrefix]) (by decide)
  have c1 := programText_slice (programLoaded_codeIn (h.loaded hp hcount))
    0x1c949 [0x4c,0x29,0xc2] (by decide) (by decide +kernel)
  obtain ⟨t1, a1, h1, e1⟩ := h.step i1 c1 hrip
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x1c94c (by decide)))
    (by change ∀ c ∈ [Component.reg 2, .flags, .rip], c ∈ registerComponents; simp [registerComponents])
  have dx1 : t1.regValue .rdx = BitVec.ofNat 64 (n-count) := by
    have hw := e1.writes
    change t1.regValue .rdx = t.regValue .rdx - t.regValue .r8 at hw
    rw [hw, hdx, h8, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hcount]
  have i2 := mov_r64_r64_effect_step 0x11c94c 0x48 0xd1 (by simp [RexWPrefix]) (by decide)
  have c2 := programText_slice (programLoaded_codeIn (h1.loaded hp hcount))
    0x1c94c [0x48,0x89,0xd1] (by decide) (by decide +kernel)
  obtain ⟨t2, a2, h2, e2⟩ := h1.step i2 c2 e1.rip
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x1c94f (by decide)))
    (by change ∀ c ∈ [Component.reg 1, .rip], c ∈ registerComponents; simp [registerComponents])
  have dx2 : t2.regValue .rdx = BitVec.ofNat 64 (n-count) :=
    (e2.agrees.read (n := 64) (r := 2) (by simp only [movR64R64Effect_components]; decide)).trans dx1
  have cx2 : rcx.read t2 = BitVec.ofNat 64 (n-count) := e2.writes.trans dx1
  have i3 := shr_r64_imm8_effect_step 0x11c94f 0x48 0xe9 3
    (by simp [RexWPrefix]) (by decide) (by decide)
  have c3 := programText_slice (programLoaded_codeIn (h2.loaded hp hcount))
    0x1c94f [0x48,0xc1,0xe9,3] (by decide) (by decide +kernel)
  obtain ⟨t3, a3, h3, e3⟩ := h2.step i3 c3 e2.rip
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x1c953 (by decide)))
    (by change ∀ c ∈ [Component.reg 1, .flags, .rip], c ∈ registerComponents; simp [registerComponents])
  refine ⟨t3, (a1.trans a2).trans a3, h3, e3.rip,
    (e3.agrees.read (n := 64) (r := 2) (by simp only [shrR64Effect_components]; decide)).trans dx2, ?_⟩
  have hw := e3.writes
  change rcx.read t3 = rcx.read t2 >>> 3 at hw
  rw [hw, cx2]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem tailCount [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n reserve count remaining : Nat} (hp : CalleePre s boundary 0x11c930 n n reserve)
    (h : CopyState s t count) (hcount : count ≤ n) (hn : remaining < 2^32)
    (hrip : t.RIP = 0x11c956) (hdx : t.regValue .rdx = BitVec.ofNat 64 remaining) :
    ∃ u, Advances boundary 2 t u ∧ CopyState s u count ∧ u.RIP = 0x11c95c ∧
      rcx.read u = BitVec.ofNat 64 (remaining % 8) := by
  have i1 := and_r32_imm8_effect_step 0x11c956 0xe2 7 (by decide) (by decide)
  have c1 := programText_slice (programLoaded_codeIn (h.loaded hp hcount))
    0x1c956 [0x83,0xe2,7] (by decide) (by decide +kernel)
  obtain ⟨t1, a1, h1, e1⟩ := h.step i1 c1 hrip
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x1c959 (by decide)))
    (by change ∀ c ∈ [Component.reg 2, .flags, .rip], c ∈ registerComponents; simp [registerComponents])
  have dx1 : t1.regValue .rdx = BitVec.ofNat 64 (remaining%8) := by
    have hw := e1.writes
    change t1.regValue .rdx = ((t.regValue .rdx).setWidth 32 &&& (7#32)).setWidth 64 at hw
    rw [hw, hdx]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
    change ((remaining % 18446744073709551616 % 4294967296) &&& (2^3-1)) %
      18446744073709551616 = remaining % 8 % 18446744073709551616
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have i2 := mov_r64_r64_effect_step 0x11c959 0x48 0xd1 (by simp [RexWPrefix]) (by decide)
  have c2 := programText_slice (programLoaded_codeIn (h1.loaded hp hcount))
    0x1c959 [0x48,0x89,0xd1] (by decide) (by decide +kernel)
  obtain ⟨t2, a2, h2, e2⟩ := h1.step i2 c2 e1.rip
    (boundary_ne_program hp.outerBoundary (inProgram_of_textOffset 0x1c95c (by decide)))
    (by change ∀ c ∈ [Component.reg 1, .rip], c ∈ registerComponents; simp [registerComponents])
  exact ⟨t2, a1.trans a2, h2, e2.rip, e2.writes.trans dx1⟩

end P256.Proofs.Program.Copy
