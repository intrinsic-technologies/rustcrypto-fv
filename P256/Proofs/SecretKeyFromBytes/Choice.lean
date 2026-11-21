import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mov_m8_r8_effect_step)

namespace P256.Proofs.SecretKeyFromBytes

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def choiceBytes : List UInt8 :=
  [0x48, 0x83, 0xec, 0x01, 0x40, 0x88, 0x3c, 0x24,
   0x0f, 0xb6, 0x04, 0x24, 0x48, 0x83, 0xc4, 0x01, 0xc3]

def choiceStoreEffect (s : RamState) : Effect :=
  storeEffect 0x119074 4 stackPtr (fun t => (Operand.reg 7 : Operand 8).read t) s

structure ChoicePre (s : RamState) : Prop where
  rip : s.RIP = 0x119070
  write : MemWritable s (stackPtr s - 1) 1
  returnRead : MemReadable s (stackPtr s) 8
  returnLow : (stackTop s).toNat < 2^32
  codeApart : RangeApart (stackPtr s - 1) 1 0x119070 17

structure ChoiceResult (s t : RamState) : Prop where
  rip : t.RIP = (returnBoundary s).rip
  rsp : stackPtr t = (returnBoundary s).rsp
  rax : (Operand.reg 0 : Operand 64).read t = ((Operand.reg 7 : Operand 8).read s).setWidth 64
  agrees : AgreesExcept [.reg 0, .reg 4, .flags, .rip, .mem (stackPtr s - 1) 1] s t

private theorem choice_code_sub {s : RamState}
    (h : CodeIn (codeRange 0x119070 choiceBytes) s) :
    CodeIn (codeRange 0x119070 [0x48, 0x83, 0xec, 1]) s :=
  h.mono (codeRange_mem_of_take (by decide +kernel))

private theorem choice_code_store {s : RamState}
    (h : CodeIn (codeRange 0x119070 choiceBytes) s) :
    CodeIn (codeRange 0x119074 [0x40, 0x88, 0x3c, 0x24]) s :=
  CodeIn.mono (codeRange_mem_of_drop (p := 0x119070) (all := choiceBytes) 4 (by decide +kernel)) h

private theorem choice_code_load {s : RamState}
    (h : CodeIn (codeRange 0x119070 choiceBytes) s) :
    CodeIn (codeRange 0x119078 [0x0f, 0xb6, 0x04, 0x24]) s :=
  CodeIn.mono (codeRange_mem_of_drop (p := 0x119070) (all := choiceBytes) 8 (by decide +kernel)) h

private theorem choice_code_add {s : RamState}
    (h : CodeIn (codeRange 0x119070 choiceBytes) s) :
    CodeIn (codeRange 0x11907c [0x48, 0x83, 0xc4, 1]) s :=
  CodeIn.mono (codeRange_mem_of_drop (p := 0x119070) (all := choiceBytes) 12 (by decide +kernel)) h

private theorem choice_code_ret {s : RamState}
    (h : CodeIn (codeRange 0x119070 choiceBytes) s) :
    CodeIn (codeRange 0x119080 [0xc3]) s :=
  CodeIn.mono (codeRange_mem_of_drop (p := 0x119070) (all := choiceBytes) 16 (by decide +kernel)) h

private theorem choice_sub_step [Bindings] :
    StepEffect (fun s => s.RIP = 0x119070)
      (codeRange 0x119070 [0x48, 0x83, 0xec, 1])
      (subR64Imm8Effect 0x119070 4 1) :=
  sub_r64_imm8_effect_step 0x119070 0x48 0xec 1 (by constructor <;> rfl) rfl rfl

private theorem choice_add_step [Bindings] :
    StepEffect (fun s => s.RIP = 0x11907c)
      (codeRange 0x11907c [0x48, 0x83, 0xc4, 1])
      (addR64Imm8Effect 0x11907c 4 1) :=
  add_r64_imm8_effect_step 0x11907c 0x48 0xc4 1 (by constructor <;> rfl) rfl rfl

private theorem choice_load_step [Bindings] :
    StepEffect (LoadPre 0x119078 stackPtr 1)
      (codeRange 0x119078 [0x0f, 0xb6, 0x04, 0x24])
      (fun s => {
        rip := 0x11907c
        writes := [⟨(Operand.reg 0 : Operand 64),
          ((Operand.mem (stackPtr s) : Operand 8).read s).setWidth 64⟩] }) := by
  have h := movzx_r32_m8_effect_step 0x119078 0 (.sib 4 none 0 .none)
    (by constructor; exact nofun; intro; decide +kernel) rfl rfl
  have ha : (fun s : RamState => (AddrMode.sib 4 none 0 .none).addr s (0 : BitVec 64)) = stackPtr := by
    funext s
    change stackPtr s + 0 = stackPtr s
    exact BitVec.add_zero _
  have ha' (s : RamState) (p : BitVec 64) : (AddrMode.sib 4 none 0 .none).addr s p = stackPtr s :=
    congrFun ha s
  have hb : (0x0f :: 0xb6 :: (AddrMode.sib 4 none 0 .none).modrm 0 ::
      (AddrMode.sib 4 none 0 .none).tail) = [0x0f, 0xb6, 0x04, 0x24] := by decide +kernel
  have hl : 0x119078 + BitVec.ofNat 64 (3 + (AddrMode.sib 4 none 0 .none).tail.length) =
      (0x11907c : BitVec 64) := by decide +kernel
  have hr : gprNumber 0 0 0 = 0 := by decide +kernel
  simpa only [StepEffect, movzxR32M8Effect, ha', hb, hl, hr] using h

end P256.Proofs.SecretKeyFromBytes

namespace P256.Proofs.SecretKeyFromBytes

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem choice_return_apart {s : RamState} (h : ChoicePre s) :
    RangeApart (stackPtr s - 1) 1 (stackPtr s) 8 := by
  have hw := h.write.low
  have hr := h.returnRead.low
  have he : (stackPtr s - 1).toNat + 1 = (stackPtr s).toNat := by
    have hs := (stackPtr s).isLt
    rw [BitVec.toNat_sub] at hw ⊢
    change (18446744073709551616 - 1 + (stackPtr s).toNat) % 18446744073709551616 + 1 ≤ 4294967296 at hw
    change (18446744073709551616 - 1 + (stackPtr s).toNat) % 18446744073709551616 + 1 = (stackPtr s).toNat
    omega
  apply RangeApart.of_toNat (by omega) (by omega)
  exact .inl (by omega)

private theorem choice_mem_read {s t : RamState} {cs : List Component}
    (h : AgreesExcept cs s t) {a : BitVec 64} {n : Nat}
    (ha : ∀ i < n / 8, ∀ c ∈ cs, ¬ c.Covers (a + BitVec.ofNat 64 i)) :
    (Operand.mem a : Operand n).read t = (Operand.mem a : Operand n).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[a + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[a + BitVec.ofNat 64 i]?).getD 0
  rw [h.byte (ha i hi)]

private theorem choice_readable {s t : RamState} {cs : List Component}
    (h : AgreesExcept cs s t) {a : BitVec 64} {n : Nat} (hr : MemReadable s a n) :
    MemReadable t a n :=
  ⟨hr.low, fun i hi => h.grow _ (hr.mem i hi)⟩

private theorem choice_agrees_trans {s t u : RamState} {cs : List Component}
    (h : AgreesExcept cs s t) (h' : AgreesExcept cs t u) : AgreesExcept cs s u :=
  (h.trans h').mono fun _ hx => (List.mem_append.mp hx).elim id id

private theorem choice_correct_of_store [Bindings]
    (hStore : StepEffect (StorePre 0x119074 4 stackPtr 1)
      (codeRange 0x119074 [0x40, 0x88, 0x3c, 0x24]) choiceStoreEffect)
    {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s)
    (hCode : CodeIn (codeRange 0x119070 choiceBytes) s)
    (hPre : ChoicePre s)
    (hBoundary : ∀ p ∈ [0x119074, 0x119078, 0x11907c, 0x119080, stackTop s],
      p ≠ boundary.rip) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ ChoiceResult s t := by
  obtain ⟨s1, hs1, hr1, he1⟩ := choice_sub_step s hReady (choice_code_sub hCode) hPre.rip
  have hsp1 : stackPtr s1 = stackPtr s - 1 := he1.writes
  have hip1 : s1.RIP = 0x119074 := he1.rip
  have hm1 : s1.external = s.external :=
    he1.agrees.external (by simp [subR64Imm8Effect_components, Component.Covers])
  have hc1 := hCode.of_external_eq hm1
  have hw1 : MemWritable s1 (stackPtr s1) 1 := by
    rw [hsp1]
    exact hPre.write.of_external_eq hm1
  have ha1 : RangeApart (stackPtr s1) 1 0x119074 4 := by
    rw [hsp1]
    intro i hi j hj
    have hj' : 4 + j < 17 := by omega
    have ha := hPre.codeApart i hi (4 + j) hj'
    have he : (0x119074 : BitVec 64) + BitVec.ofNat 64 j =
        0x119070 + BitVec.ofNat 64 (4 + j) := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    rwa [he]
  obtain ⟨s2, hs2, hr2, he2⟩ := hStore s1 hr1 (choice_code_store hc1) ⟨hip1, hw1, ha1⟩
  have hip2 : s2.RIP = 0x119078 := he2.rip
  have hsp2 : stackPtr s2 = stackPtr s1 := he2.agrees.read (n := 64) (r := 4) (by simp [choiceStoreEffect, storeEffect, Effect.components])
  have hag1 : AgreesExcept [.reg 0, .reg 4, .flags, .rip, .mem (stackPtr s - 1) 1] s s1 :=
    he1.agrees.mono (by simp [subR64Imm8Effect_components])
  have hag2 : AgreesExcept [.reg 0, .reg 4, .flags, .rip, .mem (stackPtr s - 1) 1] s1 s2 := by
    apply he2.agrees.mono
    simp [choiceStoreEffect, storeEffect, Effect.components, hsp1]
  have hag12 := choice_agrees_trans hag1 hag2
  have hc2 : CodeIn (codeRange 0x119070 choiceBytes) s2 := by
    apply CodeIn.of_agreesExcept hag12 ?_ hCode
    intro x hx c hc
    obtain ⟨j, hj, hxj⟩ := exists_of_mem_codeRange hx
    simp only [choiceBytes, List.length_cons, List.length_nil] at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact id
    rintro ⟨i, hi, he⟩
    exact hPre.codeApart i hi j hj (he.symm.trans hxj)
  have hw2 := choice_readable he2.agrees hw1.readable
  have hread2 : MemReadable s2 (stackPtr s2) 1 := hsp2 ▸ hw2
  obtain ⟨s3, hs3, hr3, he3⟩ := choice_load_step s2 hr2 (choice_code_load hc2) ⟨hip2, hread2⟩
  have hip3 : s3.RIP = 0x11907c := he3.rip
  have hsp3 : stackPtr s3 = stackPtr s2 := he3.agrees.read (n := 64) (r := 4) (by simp [Effect.components])
  have hm3 : s3.external = s2.external := he3.agrees.external (by simp [Effect.components, Component.Covers])
  have hc3 := hc2.of_external_eq hm3
  obtain ⟨s4, hs4, hr4, he4⟩ := choice_add_step s3 hr3 (choice_code_add hc3) hip3
  have hip4 : s4.RIP = 0x119080 := he4.rip
  have hsp4 : stackPtr s4 = stackPtr s := by
    have hw : stackPtr s4 = stackPtr s3 + 1 := he4.writes
    rw [hw, hsp3, hsp2, hsp1, BitVec.sub_add_cancel]
  have hag3 : AgreesExcept [.reg 0, .reg 4, .flags, .rip, .mem (stackPtr s - 1) 1] s2 s3 :=
    he3.agrees.mono (by simp [Effect.components])
  have hag4 : AgreesExcept [.reg 0, .reg 4, .flags, .rip, .mem (stackPtr s - 1) 1] s3 s4 :=
    he4.agrees.mono (by simp [addR64Imm8Effect_components])
  have hag14 := choice_agrees_trans (choice_agrees_trans hag12 hag3) hag4
  have htop4 : stackTop s4 = stackTop s := by
    unfold stackTop
    rw [hsp4]
    apply choice_mem_read hag14
    intro i hi c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact id
    rintro ⟨j, hj, he⟩
    exact choice_return_apart hPre j hj i hi he.symm
  have hread4 : MemReadable s4 (stackPtr s4) 8 := by
    rw [hsp4]
    exact choice_readable hag14 hPre.returnRead
  have hc4 := hc3.of_external_eq (he4.agrees.external (by simp [addR64Imm8Effect_components, Component.Covers]))
  obtain ⟨s5, hs5, hr5, he5⟩ := ret_effect_step 0x119080 s4 hr4 (choice_code_ret hc4)
    ⟨⟨hip4, hread4⟩, htop4 ▸ hPre.returnLow⟩
  have hip5 : s5.RIP = stackTop s := he5.rip.trans htop4
  have ha1 := Advances.of_step (boundary := boundary) hs1 (Or.inl (by
    rw [hip1]
    exact hBoundary _ (by simp)))
  have ha2 := Advances.of_step (boundary := boundary) hs2 (Or.inl (by
    rw [hip2]
    exact hBoundary _ (by simp)))
  have ha3 := Advances.of_step (boundary := boundary) hs3 (Or.inl (by
    rw [hip3]
    exact hBoundary _ (by simp)))
  have ha4 := Advances.of_step (boundary := boundary) hs4 (Or.inl (by
    rw [hip4]
    exact hBoundary _ (by simp)))
  have ha5 := Advances.of_step (boundary := boundary) hs5 (Or.inl (by
    rw [hip5]
    exact hBoundary _ (by simp)))
  refine ⟨s5, (((ha1.trans ha2).trans ha3).trans ha4).trans ha5, hr5, ?_⟩
  refine ⟨hip5, ?_, ?_, ?_⟩
  · have hw : stackPtr s5 = stackPtr s4 + 8 := he5.writes
    exact hw.trans (congrArg (· + 8) hsp4)
  · have he3ax : (Operand.reg 0 : Operand 64).read s3 =
        ((Operand.mem (stackPtr s2) : Operand 8).read s2).setWidth 64 := he3.writes
    have he2m : (Operand.mem (stackPtr s1) : Operand 8).read s2 =
        (Operand.reg 7 : Operand 8).read s1 := he2.writes
    rw [he5.agrees.read (by simp [retEffect_components]), he4.agrees.read (by simp [addR64Imm8Effect_components]), he3ax,
      hsp2, he2m, he1.agrees.read (by simp [subR64Imm8Effect_components])]
  · apply choice_agrees_trans hag14
    apply he5.agrees.mono
    simp [retEffect_components]

private theorem choice_store_step [Bindings] :
    StepEffect (StorePre 0x119074 4 stackPtr 1)
      (codeRange 0x119074 [0x40, 0x88, 0x3c, 0x24]) choiceStoreEffect := by
  have h := mov_m8_r8_effect_step 0x119074 0x40 (by simp [RexPrefix]) 7
    (.sib 4 none 0 .none) (by constructor; exact nofun; intro; decide +kernel) rfl rfl
  have ha (s : RamState) (p : BitVec 64) :
      (AddrMode.sib 4 none 0 .none).addr s p = stackPtr s := by
    change stackPtr s + 0 = stackPtr s
    exact BitVec.add_zero _
  change StepEffect (StorePre 0x119074 4
      (fun s => (AddrMode.sib 4 none 0 .none).addr s 0x119078) 1)
    (codeRange 0x119074 [0x40, 0x88, 0x3c, 0x24])
    (storeEffect 0x119074 4
      (fun s => (AddrMode.sib 4 none 0 .none).addr s 0x119078)
      (fun s => (Operand.reg 7 : Operand 8).read s)) at h
  simpa only [StepEffect, ha, choiceStoreEffect] using h

theorem choice_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s)
    (hCode : CodeIn (codeRange 0x119070 choiceBytes) s)
    (hPre : ChoicePre s)
    (hBoundary : ∀ p ∈ [0x119074, 0x119078, 0x11907c, 0x119080, stackTop s],
      p ≠ boundary.rip) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ ChoiceResult s t :=
  choice_correct_of_store choice_store_step hReady hCode hPre hBoundary

theorem choice_code_loaded {s : RamState} (h : ProgramLoaded s) :
    CodeIn (codeRange 0x119070 choiceBytes) s :=
  P256.Proofs.Program.programText_slice (P256.Proofs.Program.programLoaded_codeIn h)
    0x19070 choiceBytes (by decide +kernel) (by decide +kernel)

end P256.Proofs.SecretKeyFromBytes
