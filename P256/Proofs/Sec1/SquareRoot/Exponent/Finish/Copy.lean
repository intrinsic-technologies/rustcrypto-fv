import P256.Proofs.Sec1.SquareRoot.Exponent.Finish.Memory
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Program.ReadWrite.RepString

set_option autoImplicit false

open P256.Proofs.Sec1.SquareRoot.ExponentTail (components frame frame_readable frame_word output_code output_contains output_writable widen_output word_of_registers word_of_store)
open P256.Proofs.Program
open P256.Proofs.Field (MontgomeryAt)

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem exponent_copy_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : CalleePre s boundary 0x114ba0 144 32 1584) (h : ExponentFinishState s t x) :
    ∃ u, Advances boundary 9 t u ∧ ExponentFrame s u ∧ u.RIP = 0x11592a ∧
      MontgomeryAt u (s.regValue .rdi)
        (x ^ sqrtExponent % P256.Spec.Operations.domain.p) := by
  have hf0 := h.frame
  have hr0 := readyToStep hf0.machine hf0.bindingsSupported
  have hag0 : AgreesExcept (components s) t t := AgreesExcept.refl _ _
  have hn (off : Nat) (ho : off < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 off ≠ boundary.rip :=
    boundary_ne_program pre.outerBoundary (inProgram_of_textOffset off ho)
  let am1 : AddrMode := (.sib 4 none 0 (.d8 72))
  have hc1 : CodeIn (codeRange 0x1158ff (0x48 :: 0x8b :: am1.modrm 1 :: am1.tail)) t :=
    programText_slice (programLoaded_codeIn hf0.loaded) 0x158ff _ (by decide +kernel) (by decide +kernel)
  have hp1 : LoadPre 0x1158ff (fun q => am1.addr q (0x1158ff + BitVec.ofNat 64 (movLoadLen am1))) 8 t := by
    refine ⟨h.rip, ?_⟩
    change MemReadable t (t.regValue .rsp + 72) 8
    rw [hf0.rsp]
    exact frame_readable pre hf0 (off := 72) (by decide)
  obtain ⟨t1, ha1, hr1, he1⟩ :=
    (mov_r64_m64_effect_step 0x1158ff 0x48 (by simp [RexWPrefix]) 1 am1
      (by constructor <;> decide) rfl rfl).advances hr0 hc1 hp1 (hn 0x15904 (by decide))
  change (movR64M64Effect 0x1158ff 1 am1 t).Holds t t1 at he1
  have hs1 : AgreesExcept (components s) t t1 := he1.agrees.mono (by simp [components])
  have hf1 := frame pre hf0 hr1 hs1
  have hag1 : AgreesExcept (components s) t t1 := (hag0.trans hs1).mono (by simp)
  have hv1 : t1.regValue .rcx = (Operand.mem (exponentFrameBase s + 72) : Operand 64).read t := by
    have hw : t1.regValue .rcx = (Operand.mem (t.regValue .rsp + 72) : Operand 64).read t := he1.writes
    rw [hf0.rsp] at hw
    exact hw.trans (frame_word pre hag0 (off := 72) (by decide))
  let am2 : AddrMode := (.sib 4 none 0 (.d32 672))
  have hc2 : CodeIn (codeRange 0x115904 (0x48 :: 0x8b :: am2.modrm 0 :: am2.tail)) t1 :=
    programText_slice (programLoaded_codeIn hf1.loaded) 0x15904 _ (by decide +kernel) (by decide +kernel)
  have hp2 : LoadPre 0x115904 (fun q => am2.addr q (0x115904 + BitVec.ofNat 64 (movLoadLen am2))) 8 t1 := by
    refine ⟨he1.rip, ?_⟩
    change MemReadable t1 (t1.regValue .rsp + 672) 8
    rw [hf1.rsp]
    exact frame_readable pre hf1 (off := 672) (by decide)
  obtain ⟨t2, ha2, hr2, he2⟩ :=
    (mov_r64_m64_effect_step 0x115904 0x48 (by simp [RexWPrefix]) 0 am2
      (by constructor <;> decide) rfl rfl).advances hr1 hc2 hp2 (hn 0x1590c (by decide))
  change (movR64M64Effect 0x115904 0 am2 t1).Holds t1 t2 at he2
  have hs2 : AgreesExcept (components s) t1 t2 := he2.agrees.mono (by simp [components])
  have hf2 := frame pre hf1 hr2 hs2
  have hag2 : AgreesExcept (components s) t t2 := (hag1.trans hs2).mono (by simp)
  have hv2 : t2.regValue .rax = s.regValue .rdi := by
    have hw : t2.regValue .rax = (Operand.mem (t1.regValue .rsp + 672) : Operand 64).read t1 := he2.writes
    rw [hf1.rsp] at hw
    exact hw.trans hf1.outputPointer
  let am3 : AddrMode := (.base 0 (.d8 24))
  have hc3 : CodeIn (codeRange 0x11590c (0x48 :: 0x89 :: am3.modrm 1 :: am3.tail)) t2 :=
    programText_slice (programLoaded_codeIn hf2.loaded) 0x1590c _ (by decide +kernel) (by decide +kernel)
  have hrax3 : t2.regValue .rax = s.regValue .rdi := by
    exact hv2
  have hp3 : P256.Proofs.Common.Instructions.CrossPageStore.Pre 0x11590c (3+am3.tail.length)
      (storeAddrAt 0x11590c am3 (3+am3.tail.length)) 8 t2 := by
    refine ⟨he2.rip, ?_, ?_⟩
    · change P256.Proofs.Common.Instructions.CrossPageStore.Writable t2 (t2.regValue .rax + 24) 8
      rw [hrax3]
      exact output_writable pre hf2 (off := 24) (by decide) (by decide)
    · change RangeApart (t2.regValue .rax + 24) 8 0x11590c 4
      rw [hrax3]
      exact output_code pre (off := 24) (len := 8) (pc := 0x1590c) (n := 4) (by decide) (by decide)
  obtain ⟨t3, ha3, hr3, he3⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x11590c 0x48 (by simp [RexWPrefix]) 1 am3
      (by constructor <;> decide) rfl rfl).advances hr2 hc3 hp3 (hn 0x15910 (by decide))
  change (movM64R64Effect 0x11590c 1 am3 t2).Holds t2 t3 at he3
  have hstore3 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 24) 8, .rip] t2 t3 := by
    have hh := he3.agrees
    rw [movM64R64Effect_components] at hh
    change AgreesExcept [.mem (t2.regValue .rax + 24) 8, .rip] t2 t3 at hh
    rw [hrax3] at hh
    exact hh
  have hs3 : AgreesExcept (components s) t2 t3 :=
    widen_output (hstore3.mono (by simp)) (cs := [.rip]) (len := 8) (off := 24) (by simp [components]) (by decide)
  have hf3 := frame pre hf2 hr3 hs3
  have hag3 : AgreesExcept (components s) t t3 := (hag2.trans hs3).mono (by simp)
  have hw3 : exponentWordAt t3 (s.regValue .rdi + 24)
      ((Operand.mem (exponentFrameBase s + 72) : Operand 64).read t) := by
    have hw : (Operand.mem (t2.regValue .rax + 24) : Operand 64).read t3 =
        t2.regValue .rcx := he3.writes
    rw [hrax3] at hw
    apply hw.trans
    change (Operand.reg 1 : Operand 64).read t2 = _
    rw [he2.agrees.read (by simp)]
    exact hv1
  let am4 : AddrMode := (.sib 4 none 0 (.d8 64))
  have hc4 : CodeIn (codeRange 0x115910 (0x48 :: 0x8b :: am4.modrm 1 :: am4.tail)) t3 :=
    programText_slice (programLoaded_codeIn hf3.loaded) 0x15910 _ (by decide +kernel) (by decide +kernel)
  have hp4 : LoadPre 0x115910 (fun q => am4.addr q (0x115910 + BitVec.ofNat 64 (movLoadLen am4))) 8 t3 := by
    refine ⟨he3.rip, ?_⟩
    change MemReadable t3 (t3.regValue .rsp + 64) 8
    rw [hf3.rsp]
    exact frame_readable pre hf3 (off := 64) (by decide)
  obtain ⟨t4, ha4, hr4, he4⟩ :=
    (mov_r64_m64_effect_step 0x115910 0x48 (by simp [RexWPrefix]) 1 am4
      (by constructor <;> decide) rfl rfl).advances hr3 hc4 hp4 (hn 0x15915 (by decide))
  change (movR64M64Effect 0x115910 1 am4 t3).Holds t3 t4 at he4
  have hs4 : AgreesExcept (components s) t3 t4 := he4.agrees.mono (by simp [components])
  have hf4 := frame pre hf3 hr4 hs4
  have hag4 : AgreesExcept (components s) t t4 := (hag3.trans hs4).mono (by simp)
  have hv4 : t4.regValue .rcx = (Operand.mem (exponentFrameBase s + 64) : Operand 64).read t := by
    have hw : t4.regValue .rcx = (Operand.mem (t3.regValue .rsp + 64) : Operand 64).read t3 := he4.writes
    rw [hf3.rsp] at hw
    exact hw.trans (frame_word pre hag3 (off := 64) (by decide))
  let am5 : AddrMode := (.base 0 (.d8 16))
  have hc5 : CodeIn (codeRange 0x115915 (0x48 :: 0x89 :: am5.modrm 1 :: am5.tail)) t4 :=
    programText_slice (programLoaded_codeIn hf4.loaded) 0x15915 _ (by decide +kernel) (by decide +kernel)
  have hrax5 : t4.regValue .rax = s.regValue .rdi := by
    change (Operand.reg 0 : Operand 64).read t4 = _
    rw [he4.agrees.read (by simp), he3.agrees.read (by simp)]
    exact hv2
  have hp5 : P256.Proofs.Common.Instructions.CrossPageStore.Pre 0x115915 (3+am5.tail.length)
      (storeAddrAt 0x115915 am5 (3+am5.tail.length)) 8 t4 := by
    refine ⟨he4.rip, ?_, ?_⟩
    · change P256.Proofs.Common.Instructions.CrossPageStore.Writable t4 (t4.regValue .rax + 16) 8
      rw [hrax5]
      exact output_writable pre hf4 (off := 16) (by decide) (by decide)
    · change RangeApart (t4.regValue .rax + 16) 8 0x115915 4
      rw [hrax5]
      exact output_code pre (off := 16) (len := 8) (pc := 0x15915) (n := 4) (by decide) (by decide)
  obtain ⟨t5, ha5, hr5, he5⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x115915 0x48 (by simp [RexWPrefix]) 1 am5
      (by constructor <;> decide) rfl rfl).advances hr4 hc5 hp5 (hn 0x15919 (by decide))
  change (movM64R64Effect 0x115915 1 am5 t4).Holds t4 t5 at he5
  have hstore5 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 16) 8, .rip] t4 t5 := by
    have hh := he5.agrees
    rw [movM64R64Effect_components] at hh
    change AgreesExcept [.mem (t4.regValue .rax + 16) 8, .rip] t4 t5 at hh
    rw [hrax5] at hh
    exact hh
  have hs5 : AgreesExcept (components s) t4 t5 :=
    widen_output (hstore5.mono (by simp)) (cs := [.rip]) (len := 8) (off := 16) (by simp [components]) (by decide)
  have hf5 := frame pre hf4 hr5 hs5
  have hag5 : AgreesExcept (components s) t t5 := (hag4.trans hs5).mono (by simp)
  have hw5 : exponentWordAt t5 (s.regValue .rdi + 16)
      ((Operand.mem (exponentFrameBase s + 64) : Operand 64).read t) := by
    have hw : (Operand.mem (t4.regValue .rax + 16) : Operand 64).read t5 =
        t4.regValue .rcx := he5.writes
    rw [hrax5] at hw
    apply hw.trans
    exact hv4
  let am6 : AddrMode := (.sib 4 none 0 (.d8 48))
  have hc6 : CodeIn (codeRange 0x115919 (0x48 :: 0x8b :: am6.modrm 2 :: am6.tail)) t5 :=
    programText_slice (programLoaded_codeIn hf5.loaded) 0x15919 _ (by decide +kernel) (by decide +kernel)
  have hp6 : LoadPre 0x115919 (fun q => am6.addr q (0x115919 + BitVec.ofNat 64 (movLoadLen am6))) 8 t5 := by
    refine ⟨he5.rip, ?_⟩
    change MemReadable t5 (t5.regValue .rsp + 48) 8
    rw [hf5.rsp]
    exact frame_readable pre hf5 (off := 48) (by decide)
  obtain ⟨t6, ha6, hr6, he6⟩ :=
    (mov_r64_m64_effect_step 0x115919 0x48 (by simp [RexWPrefix]) 2 am6
      (by constructor <;> decide) rfl rfl).advances hr5 hc6 hp6 (hn 0x1591e (by decide))
  change (movR64M64Effect 0x115919 2 am6 t5).Holds t5 t6 at he6
  have hs6 : AgreesExcept (components s) t5 t6 := he6.agrees.mono (by simp [components])
  have hf6 := frame pre hf5 hr6 hs6
  have hag6 : AgreesExcept (components s) t t6 := (hag5.trans hs6).mono (by simp)
  have hv6 : t6.regValue .rdx = (Operand.mem (exponentFrameBase s + 48) : Operand 64).read t := by
    have hw : t6.regValue .rdx = (Operand.mem (t5.regValue .rsp + 48) : Operand 64).read t5 := he6.writes
    rw [hf5.rsp] at hw
    exact hw.trans (frame_word pre hag5 (off := 48) (by decide))
  let am7 : AddrMode := (.sib 4 none 0 (.d8 56))
  have hc7 : CodeIn (codeRange 0x11591e (0x48 :: 0x8b :: am7.modrm 1 :: am7.tail)) t6 :=
    programText_slice (programLoaded_codeIn hf6.loaded) 0x1591e _ (by decide +kernel) (by decide +kernel)
  have hp7 : LoadPre 0x11591e (fun q => am7.addr q (0x11591e + BitVec.ofNat 64 (movLoadLen am7))) 8 t6 := by
    refine ⟨he6.rip, ?_⟩
    change MemReadable t6 (t6.regValue .rsp + 56) 8
    rw [hf6.rsp]
    exact frame_readable pre hf6 (off := 56) (by decide)
  obtain ⟨t7, ha7, hr7, he7⟩ :=
    (mov_r64_m64_effect_step 0x11591e 0x48 (by simp [RexWPrefix]) 1 am7
      (by constructor <;> decide) rfl rfl).advances hr6 hc7 hp7 (hn 0x15923 (by decide))
  change (movR64M64Effect 0x11591e 1 am7 t6).Holds t6 t7 at he7
  have hs7 : AgreesExcept (components s) t6 t7 := he7.agrees.mono (by simp [components])
  have hf7 := frame pre hf6 hr7 hs7
  have hag7 : AgreesExcept (components s) t t7 := (hag6.trans hs7).mono (by simp)
  have hv7 : t7.regValue .rcx = (Operand.mem (exponentFrameBase s + 56) : Operand 64).read t := by
    have hw : t7.regValue .rcx = (Operand.mem (t6.regValue .rsp + 56) : Operand 64).read t6 := he7.writes
    rw [hf6.rsp] at hw
    exact hw.trans (frame_word pre hag6 (off := 56) (by decide))
  let am8 : AddrMode := (.base 0 (.d8 8))
  have hc8 : CodeIn (codeRange 0x115923 (0x48 :: 0x89 :: am8.modrm 1 :: am8.tail)) t7 :=
    programText_slice (programLoaded_codeIn hf7.loaded) 0x15923 _ (by decide +kernel) (by decide +kernel)
  have hrax8 : t7.regValue .rax = s.regValue .rdi := by
    change (Operand.reg 0 : Operand 64).read t7 = _
    rw [he7.agrees.read (by simp), he6.agrees.read (by simp), he5.agrees.read (by simp), he4.agrees.read (by simp), he3.agrees.read (by simp)]
    exact hv2
  have hp8 : P256.Proofs.Common.Instructions.CrossPageStore.Pre 0x115923 (3+am8.tail.length)
      (storeAddrAt 0x115923 am8 (3+am8.tail.length)) 8 t7 := by
    refine ⟨he7.rip, ?_, ?_⟩
    · change P256.Proofs.Common.Instructions.CrossPageStore.Writable t7 (t7.regValue .rax + 8) 8
      rw [hrax8]
      exact output_writable pre hf7 (off := 8) (by decide) (by decide)
    · change RangeApart (t7.regValue .rax + 8) 8 0x115923 4
      rw [hrax8]
      exact output_code pre (off := 8) (len := 8) (pc := 0x15923) (n := 4) (by decide) (by decide)
  obtain ⟨t8, ha8, hr8, he8⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x115923 0x48 (by simp [RexWPrefix]) 1 am8
      (by constructor <;> decide) rfl rfl).advances hr7 hc8 hp8 (hn 0x15927 (by decide))
  change (movM64R64Effect 0x115923 1 am8 t7).Holds t7 t8 at he8
  have hstore8 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 8) 8, .rip] t7 t8 := by
    have hh := he8.agrees
    rw [movM64R64Effect_components] at hh
    change AgreesExcept [.mem (t7.regValue .rax + 8) 8, .rip] t7 t8 at hh
    rw [hrax8] at hh
    exact hh
  have hs8 : AgreesExcept (components s) t7 t8 :=
    widen_output (hstore8.mono (by simp)) (cs := [.rip]) (len := 8) (off := 8) (by simp [components]) (by decide)
  have hf8 := frame pre hf7 hr8 hs8
  have hag8 : AgreesExcept (components s) t t8 := (hag7.trans hs8).mono (by simp)
  have hw8 : exponentWordAt t8 (s.regValue .rdi + 8)
      ((Operand.mem (exponentFrameBase s + 56) : Operand 64).read t) := by
    have hw : (Operand.mem (t7.regValue .rax + 8) : Operand 64).read t8 =
        t7.regValue .rcx := he8.writes
    rw [hrax8] at hw
    apply hw.trans
    exact hv7
  let am9 : AddrMode := (.base 0 .none)
  have hc9 : CodeIn (codeRange 0x115927 (0x48 :: 0x89 :: am9.modrm 2 :: am9.tail)) t8 :=
    programText_slice (programLoaded_codeIn hf8.loaded) 0x15927 _ (by decide +kernel) (by decide +kernel)
  have hrax9 : t8.regValue .rax = s.regValue .rdi := by
    change (Operand.reg 0 : Operand 64).read t8 = _
    rw [he8.agrees.read (by simp), he7.agrees.read (by simp), he6.agrees.read (by simp), he5.agrees.read (by simp), he4.agrees.read (by simp), he3.agrees.read (by simp)]
    exact hv2
  have hp9 : P256.Proofs.Common.Instructions.CrossPageStore.Pre 0x115927 (3+am9.tail.length)
      (storeAddrAt 0x115927 am9 (3+am9.tail.length)) 8 t8 := by
    refine ⟨he8.rip, ?_, ?_⟩
    · change P256.Proofs.Common.Instructions.CrossPageStore.Writable t8 (t8.regValue .rax + 0) 8
      rw [hrax9]
      exact output_writable pre hf8 (off := 0) (by decide) (by decide)
    · change RangeApart (t8.regValue .rax + 0) 8 0x115927 3
      rw [hrax9]
      exact output_code pre (off := 0) (len := 8) (pc := 0x15927) (n := 3) (by decide) (by decide)
  obtain ⟨t9, ha9, hr9, he9⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x115927 0x48 (by simp [RexWPrefix]) 2 am9
      (by constructor <;> decide) rfl rfl).advances hr8 hc9 hp9 (hn 0x1592a (by decide))
  change (movM64R64Effect 0x115927 2 am9 t8).Holds t8 t9 at he9
  have hstore9 : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 0) 8, .rip] t8 t9 := by
    have hh := he9.agrees
    rw [movM64R64Effect_components] at hh
    change AgreesExcept [.mem (t8.regValue .rax + 0) 8, .rip] t8 t9 at hh
    rw [hrax9] at hh
    exact hh
  have hs9 : AgreesExcept (components s) t8 t9 :=
    widen_output (hstore9.mono (by simp)) (cs := [.rip]) (len := 8) (off := 0) (by simp [components]) (by decide)
  have hf9 := frame pre hf8 hr9 hs9
  have hag9 : AgreesExcept (components s) t t9 := (hag8.trans hs9).mono (by simp)
  have hw9 : exponentWordAt t9 (s.regValue .rdi + 0)
      ((Operand.mem (exponentFrameBase s + 48) : Operand 64).read t) := by
    have hw : (Operand.mem (t8.regValue .rax + 0) : Operand 64).read t9 =
        t8.regValue .rdx := he9.writes
    rw [hrax9] at hw
    apply hw.trans
    change (Operand.reg 2 : Operand 64).read t8 = _
    rw [he8.agrees.read (by simp), he7.agrees.read (by simp)]
    exact hv6
  have hout0 : exponentWordAt t9 (s.regValue .rdi + 0)
      ((Operand.mem (exponentFrameBase s + 48) : Operand 64).read t) := by
    exact hw9
  have hout8 : exponentWordAt t9 (s.regValue .rdi + 8)
      ((Operand.mem (exponentFrameBase s + 56) : Operand 64).read t) := by
    apply word_of_store pre (off := 8) (storeOff := 0) (len := 8) (by decide) (by decide) (by decide) hstore9
    exact hw8
  have hout16 : exponentWordAt t9 (s.regValue .rdi + 16)
      ((Operand.mem (exponentFrameBase s + 64) : Operand 64).read t) := by
    apply word_of_store pre (off := 16) (storeOff := 0) (len := 8) (by decide) (by decide) (by decide) hstore9
    apply word_of_store pre (off := 16) (storeOff := 8) (len := 8) (by decide) (by decide) (by decide) hstore8
    apply word_of_registers he7.agrees (by simp [Component.Covers])
    apply word_of_registers he6.agrees (by simp [Component.Covers])
    exact hw5
  have hout24 : exponentWordAt t9 (s.regValue .rdi + 24)
      ((Operand.mem (exponentFrameBase s + 72) : Operand 64).read t) := by
    apply word_of_store pre (off := 24) (storeOff := 0) (len := 8) (by decide) (by decide) (by decide) hstore9
    apply word_of_store pre (off := 24) (storeOff := 8) (len := 8) (by decide) (by decide) (by decide) hstore8
    apply word_of_registers he7.agrees (by simp [Component.Covers])
    apply word_of_registers he6.agrees (by simp [Component.Covers])
    apply word_of_store pre (off := 24) (storeOff := 16) (len := 8) (by decide) (by decide) (by decide) hstore5
    apply word_of_registers he4.agrees (by simp [Component.Covers])
    exact hw3
  refine ⟨t9, ?_, hf9, he9.rip, ?_⟩
  · exact ((((((((ha1.trans ha2).trans ha3).trans ha4).trans ha5).trans ha6).trans ha7).trans ha8).trans ha9)
  · refine ⟨h.accumulator.1, h.accumulator.2.1, ?_⟩
    intro i hi
    have hw : memLoad t9.external (s.regValue .rdi + BitVec.ofNat 64 (i / 8 * 8)) 64 =
        memLoad t.external (exponentFrameBase s + 48 + BitVec.ofNat 64 (i / 8 * 8)) 64 := by
      have hd : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 := by omega
      rcases hd with hd | hd | hd | hd
      · simpa [hd, exponentWordAt, Operand.read, BitVec.add_assoc] using hout0
      · simpa [hd, exponentWordAt, Operand.read, BitVec.add_assoc] using hout8
      · simpa [hd, exponentWordAt, Operand.read, BitVec.add_assoc] using hout16
      · simpa [hd, exponentWordAt, Operand.read, BitVec.add_assoc] using hout24
    have hb := memByte_of_memLoad_eq hw (i % 8) (by omega)
    have hi' : i / 8 * 8 + i % 8 = i := by omega
    simp only [add_ofNat_add_ofNat, hi'] at hb
    obtain ⟨b, hdest⟩ := Option.isSome_iff_exists.mp
      (hf9.allocated _ (Option.isSome_iff_exists.mpr
        (pre.outputAllocated _ (output_contains pre (i := i) (by omega)))))
    have hsrc := h.accumulator.2.2 i hi
    have he : b = UInt8.ofNat (((x ^ sqrtExponent % P256.Spec.Operations.domain.p) * 2^256 % P256.Spec.Operations.domain.p) / 256^i % 256) := by
      simpa only [memByte, PhysicalMemory.read, hdest, hsrc, Option.getD_some] using hb
    exact hdest.trans (congrArg some he)

end P256.Proofs.Sec1.SquareRoot
