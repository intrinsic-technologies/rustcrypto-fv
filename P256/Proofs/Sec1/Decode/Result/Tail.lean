import P256.Proofs.Sec1.Decode.Frame
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Instructions.RepMovsqAny
import P256.Proofs.Sec1.Decode.Reject
import P256.Proofs.Sec1.Representation
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Result

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem tail_setup [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x10e676) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ t.RIP = 0x10e684 ∧
      t.regValue .rdi = s.regValue .r15 + 8 ∧ t.regValue .rsi = stackPtr s + 80 ∧
      t.regValue .rcx = 9 ∧ AgreesExcept [.reg 7, .reg 6, .reg 1, .flags, .rip] s t := by
  obtain ⟨a, aa, ra, ea⟩ := (lea_r64_effect_step 0x10e676 0x49 (by simp [RexWPrefix]) 7
    (.base 15 (.d8 8)) (by decide) rfl rfl).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0xe676 _
      (by decide) (by decide +kernel)) rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe67a (by decide)))
  have ga : AgreesExcept [.reg 7, .rip] s a := ea.agrees
  have ma := ga.external (by simp [Component.Covers])
  obtain ⟨b, ab, rb, eb⟩ := (lea_r64_effect_step 0x10e67a 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma) 0xe67a _
      (by decide) (by decide +kernel)) ea.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe67f (by decide)))
  have gb : AgreesExcept [.reg 6, .rip] a b := eb.agrees
  have mb := (ga.trans gb).external (by simp [Component.Covers])
  obtain ⟨t, at_, rt, et⟩ := (mov_r32_imm32_effect_step 0x10e67f 0xb9 (by decide) 9).advances rb
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq mb) 0xe67f _
      (by decide) (by decide +kernel)) eb.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe684 (by decide)))
  have gt : AgreesExcept [.reg 1, .rip] b t := et.agrees
  refine ⟨t, (aa.trans ab).trans at_, rt, et.rip, ?_, ?_, et.writes,
    ((ga.trans gb).trans gt).mono (by simp)⟩
  · exact ((gb.trans gt).read (n := 64) (r := 7) (by simp)).trans ea.writes
  · exact (gt.read (n := 64) (r := 6) (by simp)).trans
      (eb.writes.trans (congrArg (· + 80) (ga.read (n := 64) (r := 4) (by simp))))

end P256.Proofs.Sec1.Decode.Result

set_option autoImplicit false

open P256.Proofs.Program P256.Proofs.Program.ScalarFrame

namespace P256.Proofs.Sec1.Decode.Result

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.RepMovsqAny

def tailCopyComponents (s : RamState) : List Component :=
  [.reg 6, .reg 7, .reg 1, .mem (s.regValue .rdi + 8) 72, .rip]

theorem tail_copy [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : DecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x10e684) (src : t.regValue .rsi = stackPtr s - 232)
    (dst : t.regValue .rdi = s.regValue .rdi + 8) (count : t.regValue .rcx = 9)
    :
    ∃ u, Advances boundary 9 t u ∧ Frame s u ∧ u.RIP = 0x10e687 ∧
      (∀ i < 72, u.external[s.regValue .rdi + 8 + BitVec.ofNat 64 i]? =
        t.external[stackPtr s - 232 + BitVec.ofNat 64 i]?) ∧
      AgreesExcept (tailCopyComponents s) t u := by
  have hn : (rcx.read t).toNat = 9 := by rw [show rcx.read t = 9#64 from count]; rfl
  have source : MemReadable t (rsi.read t) 72 := by
    change MemReadable t (t.regValue .rsi) 72
    rw [src]
    exact readable_of_grow (stack_sub_readable pre.stack
      (offset := 232) (len := 72) (by decide) (by decide)) state.allocated
  have dest : P256.Proofs.Common.Instructions.CrossPageStore.Writable t (rdi.read t) 72 := by
    change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rdi) 72
    rw [dst]
    exact (ScalarFrame.output_writable pre.toCalleePre (by decide) state.allocated).add
      8 (len := 72) (by decide)
  have bounds := stack_bounds pre.stack
  have sn : (stackPtr s - 232).toNat = (stackPtr s).toNat - 232 :=
    stack_sub_toNat pre.stack (by decide)
  have dn : (s.regValue .rdi + 8).toNat = (s.regValue .rdi).toNat + 8 := by
    have hb := pre.outputBounded
    change (s.regValue .rdi).toNat + 80 < 2 ^ 32 at hb
    change ((s.regValue .rdi).toNat + 8) % 2^64 = (s.regValue .rdi).toNat + 8
    omega
  have disjoint : (rsi.read t).toNat + 72 ≤ (rdi.read t).toNat ∨
      (rdi.read t).toNat + 72 ≤ (rsi.read t).toNat := by
    change (t.regValue .rsi).toNat + 72 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 72 ≤ (t.regValue .rsi).toNat
    rw [src, dst, sn, dn]
    by_cases h : (stackPtr s).toNat - 232 + 72 ≤ (s.regValue .rdi).toNat + 8
    · exact Or.inl h
    right
    apply Nat.le_of_not_lt
    intro h'
    let address := max ((stackPtr s).toNat - 232) ((s.regValue .rdi).toNat + 8)
    have sep := pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) address
    apply sep
    · change (s.regValue .rdi).toNat ≤ address ∧ address < (s.regValue .rdi).toNat + 80
      dsimp only [address]
      constructor <;> omega
    · change (stackPtr s).toNat - 3680 ≤ address ∧
        address < (Stack.region s 3680).start + (Stack.region s 3680).size
      rw [stack_region_end]
      dsimp only [address]
      constructor <;> omega
  have apart : RangeApart (rdi.read t) 72 0x10e684 3 := by
    change RangeApart (t.regValue .rdi) 72 0x10e684#64 3
    rw [dst]
    have ha := P256.Proofs.Common.Instructions.RangeApart.add_left
      (ScalarFrame.output_code pre.toCalleePre (offset := 0xe684) (len := 3) (by decide))
      8 (len := 72) (by decide)
    exact ha
  have pc := pre_of_memory rip state.directionFlag.df hn source dest disjoint apart
  obtain ⟨run, ready, effect, copied⟩ := rep_movsq_execution state.bindingsSupported.stringStride
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xe684 [0xf3,0x48,0xa5]
      (by decide) (by decide +kernel)) pc hn
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe684 (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe687 (by decide)))
  simp only [show max 9 1 = 9 from rfl] at run ready effect copied
  generalize hu : nextStates 9 t = u at run ready effect copied
  have frame : AgreesExcept (tailCopyComponents s) t u := by
    simpa only [repMovsqEffect_components, hn, show rdi.read t = s.regValue .rdi + 8 from dst,
      Nat.reduceMul, tailCopyComponents] using effect.agrees
  have writes : WritesWithin (tailCopyComponents s)
      #v[registerRegion s .rdi 80, ScalarFrame.Work.region s 3680 32] := by
    intro c hc a ha
    simp only [tailCopyComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨registerRegion s .rdi 80, by simp,
      ScalarFrame.output_contains pre.toCalleePre (offset := 8) (len := 72) (by decide) ha⟩
  refine ⟨u, run, state.after_effect pre ready frame writes (by simp [tailCopyComponents]),
    effect.rip, ?_, frame⟩
  intro i hi
  have hb := copied i (by omega)
  change u.external[t.regValue .rdi + BitVec.ofNat 64 i]? =
    t.external[t.regValue .rsi + BitVec.ofNat 64 i]? at hb
  simpa only [src, dst] using hb

end P256.Proofs.Sec1.Decode.Result

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Result

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.CrossPageStore

theorem tail_store [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x10e687)
    (writable : Writable s (s.regValue .r15) 8)
    (apart : RangeApart (s.regValue .r15) 8 0x10e693 3) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ t.RIP = 0x10e696 ∧
      t.regValue .rdi = s.regValue .r15 ∧ memLoad t.external (s.regValue .r15) 64 = 0 ∧
      AgreesExcept [.reg 7, .reg 0, .flags, .mem (s.regValue .r15) 8, .rip] s t := by
  obtain ⟨a, aa, ra, ea⟩ := (mov_r64_r64_effect_step 0x10e687 0x4c 0xff
    (by simp [RexWPrefix]) rfl).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0xe687 _
      (by decide) (by decide +kernel)) rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe68a (by decide)))
  have ga : AgreesExcept [.reg 7, .rip] s a := ea.agrees
  have ma := ga.external (by simp [Component.Covers])
  have di : a.regValue .rdi = s.regValue .r15 := ea.writes
  obtain ⟨b, ab, rb, eb⟩ := (xor_r32_r32_effect_step 0x10e68a 0xc0 rfl).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma) 0xe68a _
      (by decide) (by decide +kernel)) ea.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe68c (by decide)))
  have gb : AgreesExcept [.reg 0, .flags, .rip] a b := eb.agrees
  have mb := (ga.trans gb).external (by simp [Component.Covers])
  have ax : b.regValue .rax = 0 := by
    have h : b.regValue .rax = (((a.regValue .rax).setWidth 32) ^^^
      ((a.regValue .rax).setWidth 32)).setWidth 64 := eb.writes
    rw [h, BitVec.xor_self]
    rfl
  obtain ⟨c, ac, rc, ec⟩ := (jmp_rel8_effect_step 0x10e68c 5 (by decide)).advances rb
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq mb) 0xe68c _
      (by decide) (by decide +kernel)) eb.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe693 (by decide)))
  have gc : AgreesExcept [.rip] b c := ec.agrees
  have mc := ((ga.trans gb).trans gc).external (by simp [Component.Covers])
  have dic : c.regValue .rdi = s.regValue .r15 :=
    ((gb.trans gc).read (n := 64) (r := 7) (by simp)).trans di
  have axc : c.regValue .rax = 0 := (gc.read (n := 64) (r := 0) (by simp)).trans ax
  have address (v : RamState) : storeAddrAt 0x10e693 (.base 7 .none) 3 v = v.regValue .rdi := by
    change v.regValue .rdi + 0#64 = v.regValue .rdi
    exact BitVec.add_zero _
  obtain ⟨t, at_, rt, et⟩ :=
    (mov_m64_r64_effect_step_any 0x10e693 0x48 (by simp [RexWPrefix]) 0
      (.base 7 .none) (by decide) rfl rfl).advances rc
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq mc) 0xe693 _
        (by decide) (by decide +kernel))
      ⟨ec.rip, by
        change Writable c (storeAddrAt 0x10e693 (.base 7 .none) 3 c) 8
        rw [address, dic]
        exact writable.of_external_eq mc,
       by
        change RangeApart (storeAddrAt 0x10e693 (.base 7 .none) 3 c) 8 0x10e693 3
        rw [address, dic]
        exact apart⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe696 (by decide)))
  change (storeEffect (n := 64) 0x10e693 3 (storeAddrAt 0x10e693 (.base 7 .none) 3)
    (fun v ↦ (Operand.reg 0 : Operand 64).read v) c).Holds c t at et
  have gt : AgreesExcept [.mem (s.regValue .r15) 8, .rip] c t := by
    simpa only [storeEffect_components, Nat.reduceDiv, address, dic] using et.agrees
  refine ⟨t, ((aa.trans ab).trans ac).trans at_, rt, et.rip,
    (gt.read (n := 64) (r := 7) (by simp)).trans dic, ?_,
    (((ga.trans gb).trans gc).trans gt).mono (by simp)⟩
  have hw : memLoad t.external (storeAddrAt 0x10e693 (.base 7 .none) 3 c) 64 =
      c.regValue .rax := et.writes
  simpa only [address, dic, axc] using hw

end P256.Proofs.Sec1.Decode.Result

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Result

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem success_tail [Bindings] {original s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {x y : Nat}
    (pre : DecodePre original boundary bytes) (state : Frame original s)
    (rip : s.RIP = 0x10e676)
    (output : s.regValue .r15 = original.regValue .rdi)
    (affine : AffineAt s (stackPtr original - 232) (.affine x y)) :
    ∃ fuel t, Advances boundary fuel s t ∧ Frame original t ∧ t.RIP = 0x10e696 ∧
      PublicKeyResultAt t (original.regValue .rdi) (some (.affine x y)) ∧
      t.regValue .rdi = original.regValue .rdi := by
  obtain ⟨a, aa, ra, ia, da, sa, ca, ga⟩ := tail_setup
    (readyToStep state.machine state.bindingsSupported) state.loaded pre.outerBoundary rip
  have stateA := state.after_registers pre ra ga (by simp [Component.Covers]) (by simp)
  have ma := ga.external (by simp [Component.Covers])
  obtain ⟨b, ab, stateB, ib, copied, gb⟩ := tail_copy pre stateA ia
    (sa.trans (ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)))
    (by rw [da, output]) ca
  have affineB : AffineAt b (original.regValue .rdi + 8) (.affine x y) := by
    apply affine.of_bytes_eq
    intro i hi
    rw [copied i (by omega), ma]
  have outputB : b.regValue .r15 = original.regValue .rdi :=
    ((ga.trans gb).read (n := 64) (r := 15) (by simp [tailCopyComponents])).trans output
  have writable := (ScalarFrame.output_writable pre.toCalleePre (by decide) stateB.allocated).add
    0 (len := 8) (by decide)
  have apart := P256.Proofs.Common.Instructions.RangeApart.add_left
    (ScalarFrame.output_code pre.toCalleePre (offset := 0xe693) (len := 3) (by decide))
    0 (len := 8) (by decide)
  change RangeApart (original.regValue .rdi + 0#64) 8 0x10e693 3 at apart
  obtain ⟨t, at_, rt, it, dt, tag, gt⟩ := tail_store
    (readyToStep stateB.machine stateB.bindingsSupported) stateB.loaded pre.outerBoundary ib
    (by simpa only [outputB, BitVec.add_zero] using writable)
    (by simpa only [outputB, BitVec.add_zero] using apart)
  rw [outputB] at tag gt dt
  have writes : WritesWithin
      [.reg 7, .reg 0, .flags, .mem (original.regValue .rdi) 8, .rip]
      #v[registerRegion original .rdi 80, ScalarFrame.Work.region original 3680 32] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    refine ⟨registerRegion original .rdi 80, by simp, ?_⟩
    exact ScalarFrame.output_contains pre.toCalleePre (offset := 0) (len := 8)
      (by decide) (by simpa only [BitVec.add_zero] using ha)
  refine ⟨16, t, (aa.trans ab).trans at_, stateB.after_effect pre rt gt writes (by simp),
    it, ⟨tag, ?_⟩, dt⟩
  apply affineB.of_bytes_eq
  intro i hi
  apply gt.byte
  intro c hc covered
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  obtain ⟨j, hj, eq⟩ := covered
  have apart : OffsetsApart 0 8 8 65 := by unfold OffsetsApart; decide +kernel
  exact apart.ne (original.regValue .rdi) hj hi (by decide)
    (by
      change original.regValue .rdi + 0#64 + BitVec.ofNat 64 j = _
      rw [BitVec.add_zero]
      exact eq.symm)

open P256.Proofs.Common.Instructions.CrossPageStore

theorem failure_tag [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x10e6a8)
    (writable : Writable s (s.regValue .r15) 8)
    (apart : RangeApart (s.regValue .r15) 8 0x10e693 3) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ t.RIP = 0x10e696 ∧
      t.regValue .rdi = s.regValue .r15 ∧ memLoad t.external (s.regValue .r15) 64 = 1 ∧
      AgreesExcept [.reg 0, .reg 7, .mem (s.regValue .r15) 8, .rip] s t := by
  obtain ⟨u, hu, ru, eu⟩ :=
    (mov_r32_imm32_effect_step 0x10e6a8 0xb8 (by decide) 1).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0xe6a8 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0xe6ad (by decide)))
  have gu : AgreesExcept [.reg 0, .rip] s u := eu.agrees
  have mu : u.external = s.external := gu.external (by simp [Component.Covers])
  obtain ⟨v, hv, rv, ev⟩ :=
    (mov_r64_r64_effect_step 0x10e6ad 0x4c 0xff (by simp [RexWPrefix]) rfl).advances ru
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq mu) 0xe6ad _
        (by decide) (by decide +kernel)) eu.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0xe6b0 (by decide)))
  have gv : AgreesExcept [.reg 7, .rip] u v := ev.agrees
  have mv := (gu.trans gv).external (by simp [Component.Covers])
  obtain ⟨w, hw, rw_, ew⟩ := (jmp_rel8_effect_step 0x10e6b0 0xe1 (by decide)).advances rv
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq mv) 0xe6b0 _
      (by decide) (by decide +kernel)) ev.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe693 (by decide)))
  have gw : AgreesExcept [.rip] v w := ew.agrees
  have mw := ((gu.trans gv).trans gw).external (by simp [Component.Covers])
  have di : w.regValue .rdi = s.regValue .r15 :=
    (gw.read (n := 64) (r := 7) (by simp)).trans
      (ev.writes.trans (gu.read (n := 64) (r := 15) (by simp)))
  have ax : w.regValue .rax = 1 :=
    ((gv.trans gw).read (n := 64) (r := 0) (by simp)).trans eu.writes
  have address (v : RamState) : storeAddrAt 0x10e693 (.base 7 .none) 3 v = v.regValue .rdi := by
    change v.regValue .rdi + 0#64 = v.regValue .rdi
    exact BitVec.add_zero _
  obtain ⟨t, ht, rt, et⟩ :=
    (mov_m64_r64_effect_step_any 0x10e693 0x48 (by simp [RexWPrefix]) 0
      (.base 7 .none) (by decide) rfl rfl).advances rw_
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq mw) 0xe693 _
        (by decide) (by decide +kernel))
      ⟨ew.rip, by
        change Writable w (storeAddrAt 0x10e693 (.base 7 .none) 3 w) 8
        rw [address, di]
        exact writable.of_external_eq mw,
       by
        change RangeApart (storeAddrAt 0x10e693 (.base 7 .none) 3 w) 8 0x10e693 3
        rw [address, di]
        exact apart⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe696 (by decide)))
  change (storeEffect (n := 64) 0x10e693 3 (storeAddrAt 0x10e693 (.base 7 .none) 3)
    (fun v ↦ (Operand.reg 0 : Operand 64).read v) w).Holds w t at et
  have gt : AgreesExcept [.mem (s.regValue .r15) 8, .rip] w t := by
    simpa only [storeEffect_components, Nat.reduceDiv, address, di] using et.agrees
  refine ⟨t, ((hu.trans hv).trans hw).trans ht, rt, et.rip, (gt.read (n := 64) (r := 7) (by simp)).trans di, ?_, (((gu.trans gv).trans gw).trans gt).mono (by simp)⟩
  have hw : memLoad t.external (storeAddrAt 0x10e693 (.base 7 .none) 3 w) 64 = w.regValue .rax := et.writes
  simpa only [address, di, ax] using hw


theorem failure_tail [Bindings] {original s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : DecodePre original boundary bytes) (state : Frame original s)
    (rip : s.RIP = 0x10e6a8) (output : s.regValue .r15 = original.regValue .rdi) :
    ∃ fuel t, Advances boundary fuel s t ∧ Frame original t ∧ t.RIP = 0x10e696 ∧
      PublicKeyResultAt t (original.regValue .rdi) none ∧
      t.regValue .rdi = original.regValue .rdi := by
  have writable := (ScalarFrame.output_writable pre.toCalleePre (by decide) state.allocated).add
    0 (len := 8) (by decide)
  have apart := P256.Proofs.Common.Instructions.RangeApart.add_left
    (ScalarFrame.output_code pre.toCalleePre (offset := 0xe693) (len := 3) (by decide))
    0 (len := 8) (by decide)
  change RangeApart (original.regValue .rdi + 0#64) 8 0x10e693 3 at apart
  obtain ⟨t, at_, rt, it, dt, tag, gt⟩ := failure_tag
    (readyToStep state.machine state.bindingsSupported) state.loaded pre.outerBoundary rip
    (by simpa only [output, BitVec.add_zero] using writable)
    (by simpa only [output, BitVec.add_zero] using apart)
  rw [output] at tag gt dt
  have writes : WritesWithin [.reg 0, .reg 7, .mem (original.regValue .rdi) 8, .rip]
      #v[registerRegion original .rdi 80, ScalarFrame.Work.region original 3680 32] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    refine ⟨registerRegion original .rdi 80, by simp, ?_⟩
    exact ScalarFrame.output_contains pre.toCalleePre (offset := 0) (len := 8)
      (by decide) (by simpa only [BitVec.add_zero] using ha)
  exact ⟨4, t, at_, state.after_effect pre rt gt writes (by simp), it, tag,
    dt⟩

end P256.Proofs.Sec1.Decode.Result