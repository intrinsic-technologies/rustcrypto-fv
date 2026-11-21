import P256.Proofs.Sec1.Decompress.State
import P256.Proofs.Sec1.Decompress.Select.Parity.Model
import P256.Proofs.Program.ScalarFrame.Choice
import P256.Proofs.Common.Instructions.ByteLogic.Unary
import P256.Proofs.Common.Instructions.ByteLogic.XorLoad
import P256.Proofs.Common.Instructions.MovzxByte
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Sec1.Decompress.Cubic.Support

set_option autoImplicit false
open P256.Proofs.Sec1.Decompress.Cubic (input_stack_address)
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.ByteLogic (notAlEffect not_al_effect_step xorR8M8LegacyEffect xor_al_rsp4c_effect_step)
open P256.Proofs.Common.Instructions.MovzxByte (movzxR32R8Effect movzx_r32_r8_effect_step)
open P256.Proofs.Program
open P256.Proofs.Field (MontgomeryAt)

namespace P256.Proofs.Sec1.Decompress.Select.Sign
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def components (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .flags, .rip,
    .mem (stackPtr s - 417) 9]

theorem byte_preserved {s t u : RamState} (h : AgreesExcept (components s) t u)
    {offset len : Nat} (ho : offset ≤ 408) (hl : len ≤ offset+8) {i : Nat} (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply h.byte
  intro c hc hv
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  obtain ⟨j,hj,he⟩ := hv
  have ha : stackPtr s - BitVec.ofNat 64 offset =
      (stackPtr s - 417) + BitVec.ofNat 64 (417-offset) := by
    rw [← BitVec.ofNat_sub_ofNat_of_le 417 offset (by omega) (by omega)]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rw [← BitVec.add_assoc (-(417 : BitVec 64)),
      show -(417 : BitVec 64)+417#64=0#64 by decide +kernel, BitVec.zero_add]
  apply RangeApart.offsets (stackPtr s-417) (a := 0) (b := 417-offset)
    (len := 9) (count := len) (by decide) (by omega) (.inl (by omega)) j hj i hi
  rw [show BitVec.ofNat 64 0 = 0#64 by rfl, BitVec.add_zero, ← ha]
  exact he.symm

theorem read_preserved {s t u : RamState} (h : AgreesExcept (components s) t u)
    {offset n : Nat} (ho : offset ≤ 408) (hl : n/8 ≤ offset+8) :
    (Operand.mem (stackPtr s-BitVec.ofNat 64 offset) : Operand n).read u =
      (Operand.mem (stackPtr s-BitVec.ofNat 64 offset) : Operand n).read t := by
  apply memLoad_congr
  intro i hi
  exact congrArg (fun x : Option UInt8 => x.getD 0) (byte_preserved h ho hl hi)

theorem choice_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (offset : Nat) (disp : BitVec 32) (hsize : offset+5 < 118431)
    (hbytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress+BitVec.ofNat 64 offset) 5
      (disp.signExtend 64) = 0x119070)
    (rip : t.RIP = Extracted.textAddress+BitVec.ofNat 64 offset) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress+BitVec.ofNat 64 offset+(5 : BitVec 64) ∧
      (Operand.reg 0 : Operand 64).read u = ((Operand.reg 7 : Operand 8).read t).setWidth 64 ∧
      AgreesExcept (components s) t u := by
  obtain ⟨u, run, ready, sp, ip, ax, agrees⟩ := ScalarFrame.choice_step pre
    (frameOffset := 408) (by decide) (by decide)
    (readyToStep state.machine state.bindingsSupported) state.loaded state.allocated state.rsp
    offset disp hsize hbytes target rip
  have narrow : AgreesExcept [.reg 0, .flags, .rip,
      .mem (stackPtr s - 416) 8, .mem (stackPtr s - 417) 1] t u := by
    apply agrees.narrow
    intro c hc hn
    simp only [ScalarFrame.choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact sp | exact (hn (by simp)).elim
  have writes : WritesWithin [.reg 0, .flags, .rip,
      .mem (stackPtr s - 416) 8, .mem (stackPtr s - 417) 1]
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 2592] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨ScalarFrame.workRegion s 2592, by simp,
      ScalarFrame.work_contains pre (by decide) (by decide) ha⟩
  refine ⟨6, u, run, state.after_effect pre (by decide) ready narrow writes
    (by simp), ip, ax, ?_⟩
  apply agrees.widen
  · intro c hc hm
    simp only [ScalarFrame.choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try simp [Component.isMem] at hm
    all_goals simp [components]
  · intro a c hc ha
    simp only [ScalarFrame.choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals obtain ⟨i, hi, rfl⟩ := ha
    · refine ⟨.mem (stackPtr s - 417) 9, by simp [components], 1+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rw [← BitVec.add_assoc (-(417 : BitVec 64))]
      rfl
    · exact ⟨.mem (stackPtr s - 417) 9, by simp [components], i, by omega, rfl⟩

theorem xor_arguments [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (rip : t.RIP = 0x110034) :
    ∃ u, Advances boundary 2 t u ∧ Frame s u ∧ u.RIP = 0x11003b ∧
      (Operand.reg 7 : Operand 64).read u =
        ((Operand.reg 0 : Operand 8).read t ^^^
          (Operand.mem (stackPtr s-332) : Operand 8).read t).setWidth 64 ∧
      AgreesExcept (components s) t u := by
  have address : stackPtr t+76=stackPtr s-332 := input_stack_address state.rsp (by decide)
  have readable : MemReadable t (stackPtr t+76) 1 := by
    rw [address]
    exact P256.Proofs.Program.readable_of_grow (P256.Proofs.Program.stack_sub_readable pre.stack
      (offset := 332) (len := 1) (by decide) (by decide)) state.allocated
  obtain ⟨v,run1,ready1,e1⟩ := (xor_al_rsp4c_effect_step 0x110034).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10034 [0x32,0x44,0x24,0x4c]
      (by decide) (by decide +kernel)) ⟨rip,readable⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10038 (by decide)))
  change (xorR8M8LegacyEffect 0x110034 0 (.sib 4 none 0 (.d8 76)) t).Holds t v at e1
  have frame1 : AgreesExcept [.reg 0,.flags,.rip] t v := e1.agrees
  have state1 := state.after_registers ready1 frame1 (by simp [Component.Covers]) (by simp)
  have low : (Operand.reg 0 : Operand 8).read v =
      (Operand.reg 0 : Operand 8).read t ^^^
        (Operand.mem (stackPtr s-332) : Operand 8).read t := by
    have h := congrArg (fun x : BitVec 64 => x.setWidth 8) e1.writes
    change (Operand.reg 0 : Operand 8).read v = (mergeGPR 8
      ((Operand.reg 0 : Operand 8).read t ^^^ (Operand.mem (stackPtr t+76) : Operand 8).read t)
      ((Operand.reg 0 : Operand 64).read t)).setWidth 8 at h
    rw [Parity.byte_merge_low,address] at h
    exact h
  obtain ⟨u,run2,ready2,e2⟩ := (movzx_r32_r8_effect_step 0x110038 0xf8 rfl (by decide)).advances
    (readyToStep state1.machine state1.bindingsSupported)
    (programText_slice (programLoaded_codeIn state1.loaded) 0x10038 [0x0f,0xb6,0xf8]
      (by decide) (by decide +kernel)) e1.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1003b (by decide)))
  change (movzxR32R8Effect 0x110038 3 7 0 v).Holds v u at e2
  have frame2 : AgreesExcept [.reg 7,.rip] v u := e2.agrees
  refine ⟨u,run1.trans run2,state1.after_registers ready2 frame2
    (by simp [Component.Covers]) (by simp),e2.rip,?_,
    (frame1.trans frame2).mono (by simp [components])⟩
  exact e2.writes.trans (congrArg (fun x : BitVec 8 => x.setWidth 64) low)

theorem invert_arguments [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (rip : t.RIP = 0x110040) :
    ∃ u, Advances boundary 3 t u ∧ Frame s u ∧ u.RIP = 0x110047 ∧
      (Operand.reg 7 : Operand 64).read u =
        ((~~~((Operand.reg 0 : Operand 8).read t)) &&& 1).setWidth 64 ∧
      AgreesExcept (components s) t u := by
  obtain ⟨v,run1,ready1,e1⟩ := (not_al_effect_step 0x110040).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10040 [0xf6,0xd0]
      (by decide) (by decide +kernel)) rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10042 (by decide)))
  change (notAlEffect 0x110040 t).Holds t v at e1
  have frame1 : AgreesExcept [.reg 0,.rip] t v := e1.agrees
  have state1 := state.after_registers ready1 frame1 (by simp [Component.Covers]) (by simp)
  have low1 : (Operand.reg 0 : Operand 8).read v = ~~~((Operand.reg 0 : Operand 8).read t) := by
    have h := congrArg (fun x : BitVec 64 => x.setWidth 8) e1.writes
    change (Operand.reg 0 : Operand 8).read v = (mergeGPR 8
      (~~~((Operand.reg 0 : Operand 8).read t)) ((Operand.reg 0 : Operand 64).read t)).setWidth 8 at h
    rw [Parity.byte_merge_low] at h
    exact h
  obtain ⟨w,run2,ready2,e2⟩ := (P256.Proofs.Common.Instructions.ByteOps.ByteOps.and_al_imm8_effect_step 0x110042 1).advances
    (readyToStep state1.machine state1.bindingsSupported)
    (programText_slice (programLoaded_codeIn state1.loaded) 0x10042 [0x24,1]
      (by decide) (by decide +kernel)) e1.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10044 (by decide)))
  change (P256.Proofs.Common.Instructions.ByteOps.ByteOps.andAlImm8Effect 0x110042 1 v).Holds v w at e2
  have frame2 : AgreesExcept [.reg 0,.flags,.rip] v w := e2.agrees
  have state2 := state1.after_registers ready2 frame2 (by simp [Component.Covers]) (by simp)
  have low2 : (Operand.reg 0 : Operand 8).read w = (~~~((Operand.reg 0 : Operand 8).read t)) &&& 1 := by
    have h := congrArg (fun x : BitVec 64 => x.setWidth 8) e2.writes
    change (Operand.reg 0 : Operand 8).read w = (mergeGPR 8
      ((Operand.reg 0 : Operand 8).read v &&& 1) ((Operand.reg 0 : Operand 64).read v)).setWidth 8 at h
    rw [Parity.byte_merge_low,low1] at h
    exact h
  obtain ⟨u,run3,ready3,e3⟩ := (movzx_r32_r8_effect_step 0x110044 0xf8 rfl (by decide)).advances
    (readyToStep state2.machine state2.bindingsSupported)
    (programText_slice (programLoaded_codeIn state2.loaded) 0x10044 [0x0f,0xb6,0xf8]
      (by decide) (by decide +kernel)) e2.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10047 (by decide)))
  change (movzxR32R8Effect 0x110044 3 7 0 w).Holds w u at e3
  have frame3 : AgreesExcept [.reg 7,.rip] w u := e3.agrees
  refine ⟨u,(run1.trans run2).trans run3,state2.after_registers ready3 frame3
    (by simp [Component.Covers]) (by simp),e3.rip,?_,
    ((frame1.trans frame2).trans frame3).mono (by simp [components])⟩
  exact e3.writes.trans (congrArg (fun x : BitVec 8 => x.setWidth 64) low2)

private theorem low_of_full {s : RamState} {r : BitVec 5} {x : BitVec 64}
    (h : (Operand.reg r : Operand 64).read s = x) :
    (Operand.reg r : Operand 8).read s = x.setWidth 8 := congrArg (fun x : BitVec 64 => x.setWidth 8) h

theorem selection_bit [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (beta : Nat) (sign : Bool) (rip : t.RIP=0x11002f)
    (parity : (Operand.reg 7 : Operand 64).read t=BitVec.ofNat 64 (beta%2))
    (savedSign : (Operand.mem (stackPtr s-332) : Operand 8).read t=BitVec.ofNat 8 sign.toNat) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP=0x11004c ∧
      (Operand.reg 0 : Operand 8).read u=(if beta%2 == sign.toNat then 1 else 0) ∧
      AgreesExcept (components s) t u := by
  obtain ⟨n1,t1,r1,st1,ip1,v1,f1⟩ := choice_call pre state 0x1002f 0x903c
    (by decide) (by decide +kernel) (by decide +kernel) rip
  have v1low := low_of_full v1
  have hd := low_of_full parity
  obtain ⟨t2,r2,st2,ip2,v2,f2⟩ := xor_arguments pre st1 ip1
  have saved1 : (Operand.mem (stackPtr s-332) : Operand 8).read t1=BitVec.ofNat 8 sign.toNat :=
    (read_preserved f1 (offset := 332) (n := 8) (by decide) (by decide)).trans savedSign
  obtain ⟨n3,t3,r3,st3,ip3,v3,f3⟩ := choice_call pre st2 0x1003b 0x9030
    (by decide) (by decide +kernel) (by decide +kernel) ip2
  have v2low := low_of_full v2
  have v3low := low_of_full v3
  obtain ⟨t4,r4,st4,ip4,v4,f4⟩ := invert_arguments pre st3 ip3
  obtain ⟨n5,t5,r5,st5,ip5,v5,f5⟩ := choice_call pre st4 0x10047 0x9024
    (by decide) (by decide +kernel) (by decide +kernel) ip4
  have v4low := low_of_full v4
  have v5low := low_of_full v5
  refine ⟨n1+2+n3+3+n5,t5,(((r1.trans r2).trans r3).trans r4).trans r5,st5,ip5,?_,
    ((((f1.trans f2).trans f3).trans f4).trans f5).mono (by simp)⟩
  rw [v5low,v4low,v3low,v2low,v1low,hd,saved1]
  have cases : beta%2=0 ∨ beta%2=1 := by omega
  rcases cases with h | h <;> cases sign <;> simp [h]


end P256.Proofs.Sec1.Decompress.Select.Sign
