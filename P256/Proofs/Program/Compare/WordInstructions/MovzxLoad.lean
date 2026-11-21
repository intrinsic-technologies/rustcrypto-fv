import P256.Proofs.Common.Curve.LinearCombination.NafReverse.Load
namespace P256.Proofs.Program.Compare.WordInstructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

abbrev movzxR32M16Effect :=
  P256.Proofs.Common.Curve.LinearCombination.NafReverse.movzxR32M16Effect

attribute [x86_compose] movzxR32M16Effect

theorem movzx_r32_m16_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x0f :: 0xb7 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s
      (am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))) 2) :
    Machine.step s = some (.next (afterStep s (4 + am.tail.length) fun t =>
      writeResult (dataAccess t "load")
        (.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 32)
        (movzxSpec 32 ((Operand.mem (am.addr s
          (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))) : Operand 16).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length))))) := by
  have hlen : (rex :: 0x0f :: 0xb7 :: am.modrm reg :: am.tail : List UInt8).length =
      4 + am.tail.length := by simp only [List.length_cons]; omega
  have hlow' : s.RIP.toNat +
      (rex :: 0x0f :: 0xb7 :: am.modrm reg :: am.tail : List UInt8).length ≤ 2^32 := by
    rw [hlen]
    exact hlow
  have hrew : (rexContext s.DS rex.toBitVec).rex_w = 0 := by
    simp only [RexNoWPrefix, List.mem_cons, List.not_mem_nil, or_false] at hrex
    rcases hrex with hrex | hrex | hrex | hrex | hrex | hrex | hrex | hrex <;>
      simp only [rexContext, hrex] <;> rfl
  have hdecode := P256.Proofs.Common.Curve.LinearCombination.NafReverse.movzx_0FB7_memory_run
    s h (rexContext s.DS rex.toBitVec) rfl rfl hrew rfl rfl reg am hv
    (AddrContext.rex _ _ am hx hb) _ 2 (by decide) rfl rfl
    (fun j _ => by rw [show 2 + 2 + j = j + 1 + 1 + 1 + 1 by omega]; rfl)
    (by simp only [List.length_cons]; omega) hcode hlow' (by rw [hlen]; exact hread)
  rw [hlen] at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (4 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0xb7 _ hrex.rexPrefix ⟨by decide, by decide⟩
    hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem movzx_r32_m16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (rex :: 0x0f :: 0xb7 :: am.modrm reg :: am.tail))
      (movzxR32M16Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    subst hp
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  subst hp
  refine ⟨_, movzx_r32_m16_rex_step s h rex hrex reg am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec]
  exact BitVec.setWidth_setWidth (by decide)

theorem tail_word_left_step [Bindings] :
    StepEffect
      (LoadPre 0x11cdd0 (fun s => (AddrMode.sib 0 (some 11) 0 .none).addr s 0x11cdd5) 2)
      (codeRange 0x11cdd0 [0x46, 0x0f, 0xb7, 0x04, 0x18])
      (movzxR32M16Effect 0x11cdd0 5 8 (.sib 0 (some 11) 0 .none)) :=
  movzx_r32_m16_rex_effect_step 0x11cdd0 0x46 (by unfold RexNoWPrefix; decide +kernel) 0
    (.sib 0 (some 11) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem tail_word_right_step [Bindings] :
    StepEffect
      (LoadPre 0x11cdd5 (fun s => (AddrMode.sib 2 (some 11) 0 .none).addr s 0x11cdda) 2)
      (codeRange 0x11cdd5 [0x42, 0x0f, 0xb7, 0x3c, 0x1a])
      (movzxR32M16Effect 0x11cdd5 5 7 (.sib 2 (some 11) 0 .none)) :=
  movzx_r32_m16_rex_effect_step 0x11cdd5 0x42 (by unfold RexNoWPrefix; decide +kernel) 7
    (.sib 2 (some 11) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end P256.Proofs.Program.Compare.WordInstructions
