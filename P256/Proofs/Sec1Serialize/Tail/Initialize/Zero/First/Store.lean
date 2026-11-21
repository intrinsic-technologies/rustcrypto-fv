import P256.Proofs.Sec1Serialize.Tail.Initialize.Zero.First.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem zeroing_read_bytes {u : RamState} {addr : BitVec 64} {n : Nat}
    (h : memLoad u.external addr n = 0) (hr : MemReadable u addr (n / 8)) :
    ∀ i, i < n / 8 → u.external[addr + BitVec.ofNat 64 i]? = some 0 := by
  intro i hi
  have hb := storedByte_memLoad u.external addr (n := n) i hi
  rw [h] at hb
  have hs := hr.mem i hi
  cases he : u.external[addr + BitVec.ofNat 64 i]? with
  | none => simp [he] at hs
  | some b =>
    have heq : b = 0 := by
      simpa [storedByte, memByte, PhysicalMemory.read, he] using hb.symm
    simp [heq]

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {infinity : Bool}

theorem Zeroing.zero64 (pre : CalleePre s boundary 0x110d70 72 65 328)
    (pc offset : Nat) (h : Zeroing s t boundary bytes infinity (offset - 8)) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (ho : offset ≤ 184) (hl : 127 ≤ offset) (halign : offset % 8 = 0)
    (ha : ∀ v : RamState, storeAddrAt (Extracted.textAddress + BitVec.ofNat 64 pc) am
      (7 + am.tail.length) v = v.regValue .rsp + (312 - BitVec.ofNat 64 offset))
    (hn : pc + (7 + am.tail.length) < 118431)
    (hcode : Extracted.textBytes.toListFrom pc (7 + am.tail.length) =
      0x48 :: 0xc7 :: am.modrm 0 :: (am.tail ++ immBytes 32 0))
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 pc) :
    ∃ u, Zeroing s u boundary bytes infinity offset ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (pc + (7 + am.tail.length)) := by
  let p := Extracted.textAddress + BitVec.ofNat 64 pc
  have haddr : storeAddrAt p am (7 + am.tail.length) t =
      stackPtr s - BitVec.ofNat 64 offset := by
    rw [ha t]
    change stackPtr t + (312 - BitVec.ofNat 64 offset) = _
    rw [h.state.rsp]
    rw [BitVec.sub_eq_add_neg (312 : BitVec 64), ← BitVec.add_assoc, BitVec.sub_add_cancel]
    exact (BitVec.sub_eq_add_neg _ _).symm
  have code : CodeIn
      (codeRange p (0x48 :: 0xc7 :: am.modrm 0 :: (am.tail ++ immBytes 32 0))) t := by
    apply programText_slice (programLoaded_codeIn h.state.loaded) pc
    · simp only [List.length_cons, List.length_append, immBytes_length]
      omega
    · simpa only [List.length_cons, List.length_append, immBytes_length,
        show am.tail.length + 4 + 1 + 1 + 1 = 7 + am.tail.length by omega] using hcode
  have write : MemWritable t (storeAddrAt p am (7 + am.tail.length) t) 8 := by
    rw [haddr]
    exact writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by omega) halign) h.state.allocated
  have apart : RangeApart (storeAddrAt p am (7 + am.tail.length) t) 8 p (7 + am.tail.length) := by
    rw [haddr]
    have ha' : stackPtr t + BitVec.ofNat 64 (312 - offset) =
        stackPtr s - BitVec.ofNat 64 offset := by
      rw [scalar_stack_address (frameOffset := 312) h.state.rsp (by decide) (by omega)]
      congr 2
      omega
    rw [← ha']
    exact stack_code pre h.state (frameOffset := 312) (offset := 312 - offset)
      (codeOffset := pc) (by decide) (by omega) (by omega)
  obtain ⟨u, step, ready, effect⟩ := mov_m64_imm32_effect_step p 0x48
    (by simp [RexWPrefix]) am hv hx.symm hb.symm 0 t
    (readyToStep h.state.machine h.state.bindingsSupported) code ⟨rip, write, apart⟩
  have components : (movM64Imm32Effect p am 0 t).components =
      [.mem (stackPtr s - BitVec.ofNat 64 offset) 8, .rip] := by
    simp only [movM64Imm32Effect, storeEffect_components, haddr]
  have hip : (movM64Imm32Effect p am 0 t).rip =
      Extracted.textAddress + BitVec.ofNat 64 (pc + (7 + am.tail.length)) := by
    simp only [movM64Imm32Effect, storeEffect, p, BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨u, h.of_store pre ho (by omega) (by decide) step ready effect components ?_ ?_,
    effect.rip.trans hip⟩
  · rw [hip]
    exact inProgram_of_textOffset _ hn
  · have hz := effect.writes
    change memLoad u.external (storeAddrAt p am (7 + am.tail.length) t) 64 = 0 at hz
    rw [haddr] at hz
    apply zeroing_read_bytes hz
    exact readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega))
      (fun a ha => effect.agrees.grow a (h.state.allocated a ha))

theorem Zeroing.zero8 (pre : CalleePre s boundary 0x110d70 72 65 328)
    (pc offset : Nat) (h : Zeroing s t boundary bytes infinity (offset - 1)) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (ho : offset ≤ 184) (hl : 120 ≤ offset)
    (ha : ∀ v : RamState, storeAddrAt (Extracted.textAddress + BitVec.ofNat 64 pc) am
      (3 + am.tail.length) v = v.regValue .rsp + (312 - BitVec.ofNat 64 offset))
    (hn : pc + (3 + am.tail.length) < 118431)
    (hcode : Extracted.textBytes.toListFrom pc (3 + am.tail.length) =
      0xc6 :: am.modrm 0 :: (am.tail ++ immBytes 8 0))
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 pc) :
    ∃ u, Zeroing s u boundary bytes infinity offset ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (pc + (3 + am.tail.length)) := by
  let p := Extracted.textAddress + BitVec.ofNat 64 pc
  have haddr : storeAddrAt p am (3 + am.tail.length) t =
      stackPtr s - BitVec.ofNat 64 offset := by
    rw [ha t]
    change stackPtr t + (312 - BitVec.ofNat 64 offset) = _
    rw [h.state.rsp]
    rw [BitVec.sub_eq_add_neg (312 : BitVec 64), ← BitVec.add_assoc, BitVec.sub_add_cancel]
    exact (BitVec.sub_eq_add_neg _ _).symm
  have code : CodeIn (codeRange p (0xc6 :: am.modrm 0 :: (am.tail ++ immBytes 8 0))) t := by
    apply programText_slice (programLoaded_codeIn h.state.loaded) pc
    · simp only [List.length_cons, List.length_append, immBytes_length]
      omega
    · simpa only [List.length_cons, List.length_append, immBytes_length,
        show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega] using hcode
  have write : MemWritable t (storeAddrAt p am (3 + am.tail.length) t) 1 := by
    rw [haddr]
    exact writable_of_grow (stack_sub_writable pre.stack
      (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (len := 1)
      (by omega) (by omega) (by decide) (by omega)) h.state.allocated
  have apart : RangeApart (storeAddrAt p am (3 + am.tail.length) t) 1 p (3 + am.tail.length) := by
    rw [haddr]
    have ha' : stackPtr t + BitVec.ofNat 64 (312 - offset) =
        stackPtr s - BitVec.ofNat 64 offset := by
      rw [scalar_stack_address (frameOffset := 312) h.state.rsp (by decide) (by omega)]
      congr 2
      omega
    rw [← ha']
    exact stack_code pre h.state (frameOffset := 312) (offset := 312 - offset)
      (codeOffset := pc) (by decide) (by omega) (by omega)
  obtain ⟨u, step, ready, effect⟩ := mov_m8_imm8_effect_step p am hv hx hb 0 t
    (readyToStep h.state.machine h.state.bindingsSupported) code ⟨rip, write, apart⟩
  have components : (movM8Imm8Effect p am 0 t).components =
      [.mem (stackPtr s - BitVec.ofNat 64 offset) 1, .rip] := by
    simp only [movM8Imm8Effect, storeEffect_components, haddr]
  have hip : (movM8Imm8Effect p am 0 t).rip =
      Extracted.textAddress + BitVec.ofNat 64 (pc + (3 + am.tail.length)) := by
    simp only [movM8Imm8Effect, storeEffect, p, BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨u, h.of_store pre ho (by omega) (by decide) step ready effect components ?_ ?_,
    effect.rip.trans hip⟩
  · rw [hip]
    exact inProgram_of_textOffset _ hn
  · have hz := effect.writes
    change memLoad u.external (storeAddrAt p am (3 + am.tail.length) t) 8 = 0 at hz
    rw [haddr] at hz
    apply zeroing_read_bytes hz
    exact readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega))
      (fun a ha => effect.agrees.grow a (h.state.allocated a ha))

end P256.Proofs.Sec1Serialize
