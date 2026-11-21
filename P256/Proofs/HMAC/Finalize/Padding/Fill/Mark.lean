import P256.Proofs.HMAC.Finalize.Padding.Fill.Setup
import P256.Proofs.HMAC.Finalize.Copy
import P256.Proofs.SHA256.LengthEncoding

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Padding

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common

 theorem mark [Bindings] (outer : Bool)
    {initial s : RamState} {boundary : ReturnBoundary} {message : ByteArray}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : Buffered initial s message) (rip : s.RIP = paddingStart outer) :
    ∃ fuel t, Advances boundary fuel s t ∧ Marked initial t message outer ∧
      t.RIP = fillCall outer ∧ MemoryWriteFrame s t #v[scratchRegion initial] := by
  have rem : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have base (k : Nat) : rspOf s + BitVec.ofNat 64 (72 + k) =
      stackPtr initial - 256#64 + BitVec.ofNat 64 k := by
    change stackPtr s + _ = _
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, stack_address state.rsp (by decide : 72 ≤ 328)]
  have position : FillSetup.position s = BitVec.ofNat 64 (message.size % 64) := by
    unfold FillSetup.position
    rw [show rspOf s + 135 = stackPtr initial - 256#64 + 63 from base 63, memLoad_8]
    change ((s.external[stackPtr initial - 256#64 + 63]?).getD 0).toBitVec.setWidth 64 = _
    rw [state.state.position]
    simp only [Option.getD_some, UInt8.toBitVec_ofNat']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  have count : memLoad s.external (rspOf s + 168) 64 = BitVec.ofNat 64 (message.size / 64) := by
    have bytes := Bytes.of_memLoad (n := 64)
      (ScalarFrame.stack_readable (stackPre pre) state.toFrameState (by decide) (offset := 168) (len := 8) (by decide)).mem
    have count := state.state.count
    rw [← show rspOf s + 168 = stackPtr initial - 256#64 + 96 from base 96] at count
    exact Except.ok.inj (bytes.loadBytes64.symm.trans count)
  have markerAddress : rspOf s + FillSetup.position s + 72 =
      stackPtr initial - 256#64 + BitVec.ofNat 64 (message.size % 64) := by
    rw [position]
    have commute : rspOf s + BitVec.ofNat 64 (message.size % 64) + 72 =
        rspOf s + 72 + BitVec.ofNat 64 (message.size % 64) := by
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (message.size % 64)) 72#64]
    rw [commute]
    exact congrArg (· + BitVec.ofNat 64 (message.size % 64)) (stack_address state.rsp (by decide : 72 ≤ 328))
  have localAddress : rspOf s + FillSetup.position s + 72 =
      stackPtr s + BitVec.ofNat 64 (72 + message.size % 64) := by
    rw [markerAddress]
    exact (base _).symm
  have setupPre : FillSetup.Pre outer s := by
    refine ⟨rip, ScalarFrame.stack_readable (stackPre pre) state.toFrameState (by decide) (by decide),
      ScalarFrame.stack_readable (stackPre pre) state.toFrameState (by decide) (by decide), ?_, ?_⟩
    · rw [localAddress]
      have w := ScalarFrame.stack_writable (frameOffset := 328) (stackPre pre) state.toFrameState (by decide)
        (offset := 72 + message.size % 64) (len := 1) (by omega) (by decide)
      exact ⟨w.low, w.mem, w.tables⟩
    · rw [localAddress]
      cases outer
      · exact ScalarFrame.stack_code (frameOffset := 328) (stackPre pre) state.toFrameState (by decide) (by omega) (codeOffset := 0xfb7) (by decide)
      · exact ScalarFrame.stack_code (frameOffset := 328) (stackPre pre) state.toFrameState (by decide) (by omega) (codeOffset := 0x1255) (by decide)
  obtain ⟨fuel, t, run, ready, _, effect⟩ := FillSetup.run outer boundary pre.outerBoundary
    s (readyToStep state.machine state.bindingsSupported) (FillSetup.code outer state.loaded) setupPre
  have markerAddressBits : rspOf s + FillSetup.position s + 72#64 =
      stackPtr initial - 256#64 + BitVec.ofNat 64 (message.size % 64) := markerAddress
  have writes : WritesWithin (FillSetup.effect outer s).components #v[scratchRegion initial] := by
    intro c hc a covered
    simp only [FillSetup.effect, Effect.components, List.map_cons, List.map_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc
    rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | rfl
    all_goals try exact covered.elim
    obtain ⟨i, hi, rfl⟩ := covered
    have iz : i = 0 := by omega
    subst i
    simp only [BitVec.ofNat_eq_ofNat, markerAddressBits, BitVec.add_zero]
    exact ⟨_, by simp, scratch_contains pre (offset := 256) (len := 64)
      (by decide) (by decide) ⟨message.size % 64, rem, rfl⟩⟩
  have frame := state.toFrameState.after_effect (stackPre pre) (by decide) ready effect.agrees
    (by
      intro c hc a ha
      obtain ⟨region, member, contains⟩ := writes c hc a ha
      have eq : region = scratchRegion initial := by simpa using member
      subst region
      refine ⟨workRegion initial 672, by simp, ?_⟩
      change (stackPtr initial).toNat - 672 ≤ a.toNat ∧
        a.toNat < (stackPtr initial).toNat - 672 + 520 at contains
      exact ⟨contains.1, by change a.toNat < (stackPtr initial).toNat - 672 + (672 - 48); omega⟩)
    (by cases outer <;> simp [FillSetup.effect, Effect.components,
      FillSetup.hashReg, FillSetup.posReg, FillSetup.countReg, FillSetup.zeroReg])
  have bytes (i : Nat) (hi : i < 104) (ne : i ≠ message.size % 64) :
      t.external[stackPtr initial - 256#64 + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - 256#64 + BitVec.ofNat 64 i]? := by
    apply effect.agrees.byte
    intro c hc covered
    simp only [FillSetup.effect, Effect.components, List.map_cons, List.map_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc
    rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | rfl
    all_goals try exact covered.elim
    obtain ⟨j, hj, eq⟩ := covered
    have jz : j = 0 := by omega
    subst j
    simp only [BitVec.ofNat_eq_ofNat, markerAddressBits, BitVec.add_zero] at eq
    have same := (BitVec.add_right_inj _).mp eq
    have natSame := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat] at natSame
    exact ne (by omega)
  have fields := effect.writes
  change (Operand.reg (FillSetup.hashReg outer) : Operand 64).read t = rspOf s + 136 ∧
    (Operand.reg (FillSetup.posReg outer) : Operand 64).read t = FillSetup.position s ∧
    (Operand.reg (FillSetup.countReg outer) : Operand 64).read t = memLoad s.external (rspOf s + 168) 64 ∧
    (Operand.reg (FillSetup.zeroReg outer) : Operand 64).read t = FillSetup.position s ^^^ 63 ∧
    memLoad t.external (rspOf s + FillSetup.position s + 72) 8 = 128 ∧
    t.regValue .rdi = rspOf s + FillSetup.position s + 73 ∧
    t.regValue .rsi = 0 ∧ t.regValue .rdx = FillSetup.position s ^^^ 63 at fields
  rcases fields with ⟨hashReg, posReg, countReg, zeroReg, marker, destination, zero, length⟩
  have hashAddress : rspOf s + 136 = stackPtr initial - 192#64 :=
    stack_address state.rsp (by decide : 136 ≤ 328)
  have hashBase : stackPtr initial - 256#64 + 64#64 = stackPtr initial - 192#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  refine ⟨fuel, t, run, ⟨frame,
    (effect.agrees.read (n := 64) (r := 3) (by cases outer <;> simp [FillSetup.effect, Effect.components,
      FillSetup.hashReg, FillSetup.posReg, FillSetup.countReg, FillSetup.zeroReg])).trans state.outputPointer,
    ?_, ?_, ?_, ?_, ?_, zero, ?_, ?_, ?_, ?_⟩, effect.rip, effect.agrees.memoryWriteFrame writes⟩
  · have h := posReg.trans position
    cases outer <;> exact h
  · have h := countReg.trans count
    cases outer <;> exact h
  · have h := hashReg.trans hashAddress
    cases outer <;> exact h
  · rw [position, SHA256.tail_zero_count _ rem] at zeroReg
    cases outer <;> exact zeroReg
  · rw [destination]
    rw [show (73 : BitVec 64) = 72 + 1 by decide +kernel, ← BitVec.add_assoc, markerAddress]
    rw [BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  · rw [length, position]
    exact SHA256.tail_zero_count _ rem
  · exact hasBytes_copy state.state.buffer (fun i hi => bytes i (by omega) (by omega))
  · rw [markerAddress, memLoad_8] at marker
    change ((t.external[stackPtr initial - 256#64 + BitVec.ofNat 64 (message.size % 64)]?).getD 0).toBitVec = 128 at marker
    cases byte : t.external[stackPtr initial - 256#64 + BitVec.ofNat 64 (message.size % 64)]? with
    | none => rw [byte] at marker; contradiction
    | some v =>
      simp only [byte, Option.getD_some] at marker
      exact congrArg some (UInt8.eq_of_toBitVec_eq marker)
  · have hash := state.state.hash
    simp only [BitVec.ofNat_eq_ofNat, hashBase] at hash
    apply hash.copy
    intro i hi
    have b := bytes (64 + i) (by omega) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, hashBase] using b

end P256.Proofs.HMAC.Finalize.Padding
