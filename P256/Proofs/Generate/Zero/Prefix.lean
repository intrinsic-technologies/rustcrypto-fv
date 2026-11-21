import P256.Proofs.HMAC.Key.Frame
import P256.Proofs.Generate.Zero.Frame
import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Correct

set_option autoImplicit false

namespace P256.Proofs.Generate.Zero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

theorem prefix_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {offset x y : Nat} {disp : BitVec 32}
    (pre : CalleePre s boundary (Extracted.textAddress + BitVec.ofNat 64 offset) 32 32 32)
    (code : PrefixCode offset disp)
    (left : Nat256At s (s.regValue .rdi) x)
    (right : Nat256At s (s.regValue .rsi) y) :
    ∃ t, PrefixResult s t boundary offset x y := by
  obtain ⟨a, runA, readyA, loadedA, ripA, rspA, agreesA, _⟩ :=
    push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary (readyToStep pre.machine pre.bindingsSupported)
      pre.loaded (fun _ h => h) 0 0 offset (by rw [BitVec.sub_zero]) pre.rip
      (by decide) (by decide) (by have bound := code.bound; change offset + 1 < 118431; omega)
      code.push
  have pcAdd (i j : Nat) :
      Extracted.textAddress + BitVec.ofNat 64 i + BitVec.ofNat 64 j =
        Extracted.textAddress + BitVec.ofNat 64 (i+j) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  obtain ⟨n, b, runB, readyB, _, effectB⟩ := arguments boundary
    (Extracted.textAddress + BitVec.ofNat 64 (offset+1))
    (fun i hi => by
      rw [pcAdd]
      apply boundary_ne_program pre.outerBoundary (inProgram_of_textOffset _ ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      have bound := code.bound
      omega)
    a readyA
    (programText_slice (programLoaded_codeIn loadedA) (offset+1) argumentBytes
      (by have bound := code.bound; change offset + 1 + 13 ≤ 118431; omega) code.arguments)
    ripA
  have ab : AgreesExcept (prefixClobbers s) s b :=
    (agreesA.trans effectB.agrees).mono (by
      simp [prefixClobbers, argumentEffect, Effect.components])
  have spB : stackPtr b = stackPtr s - 8 :=
    (effectB.agrees.read (n := 64) (r := 4) (by simp [argumentEffect, Effect.components])).trans rspA
  have siA : a.regValue .rsi = s.regValue .rsi := agreesA.read (n := 64) (r := 6) (by simp)
  have diB : b.regValue .rdi = s.regValue .rdi := ab.read (n := 64) (r := 7)
    (by simp [prefixClobbers])
  have dxB : b.regValue .rdx = s.regValue .rsi := effectB.writes.1.trans siA
  have siB : b.regValue .rsi = 4 := effectB.writes.2.1
  have cxB : b.regValue .rcx = 4 := effectB.writes.2.2
  have ripB : b.RIP = Extracted.textAddress + BitVec.ofNat 64 (offset+14) := by
    have h := effectB.rip
    change b.RIP = Extracted.textAddress + BitVec.ofNat 64 (offset+1) + BitVec.ofNat 64 13 at h
    rw [pcAdd] at h
    simpa only [Nat.add_assoc] using h
  have pushB : pushAddr b = stackPtr s - 16 := by
    rw [pushAddr, spB, BitVec.sub_sub]
    rfl
  have callPre : PushPre (Extracted.textAddress + BitVec.ofNat 64 (offset+14)) 5 b := by
    refine ⟨ripB, ?_, ?_⟩
    · rw [pushB]
      exact writable_of_grow
        (stack_sub_writable8 pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (offset := 16)
          (by decide) (by decide)) ab.grow
    · rw [pushB]
      exact P256.Proofs.HMAC.Key.stack_code_apart pre (offset := 16)
        (by decide) (by decide) (by have bound := code.bound; omega)
  obtain ⟨c, runC, readyC, effectC⟩ :=
    (call_rel32_effect_step _ disp (by rw [code.target]; decide)).advances readyB
      (programText_slice (programLoaded_codeIn (prefix_loaded pre ab)) (offset+14)
        (encodeCallRel32 disp) (by have bound := code.bound; change offset+14+5 ≤ 118431; omega)
        code.call) callPre
      (by
        rw [code.target]
        exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x19270 (by decide)))
  have ac : AgreesExcept (prefixClobbers s) s c :=
    (ab.trans effectC.agrees).mono (by
      simp [prefixClobbers, pushEffect_components, pushB])
  have diC : c.regValue .rdi = s.regValue .rdi :=
    (effectC.agrees.read (n := 64) (r := 7) (by simp)).trans diB
  have dxC : c.regValue .rdx = s.regValue .rsi :=
    (effectC.agrees.read (n := 64) (r := 2) (by simp)).trans dxB
  have spC : stackPtr c = stackPtr s - 16 := effectC.writes.1.trans pushB
  have cp : P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Pre c boundary := by
    refine ⟨readyC, prefix_loaded pre ac, ?_,
      (effectC.agrees.read (n := 64) (r := 6) (by simp)).trans siB,
      (effectC.agrees.read (n := 64) (r := 1) (by simp)).trans cxB, ?_, ?_, ?_,
      pre.outerBoundary, ?_⟩
    · exact effectC.rip.trans code.target
    · rw [diC]
      exact readable_of_grow
        (memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _)) ac.grow
    · rw [dxC]
      exact readable_of_grow
        (memoryRegion_memReadable pre.inputBounded pre.inputAllocated (Nat.le_refl _) (Nat.le_refl _)) ac.grow
    · rw [spC]
      exact readable_of_grow (stack_sub_readable pre.stack
        (offset := 16) (len := 8) (by decide) (by decide)) ac.grow
    · change InProgram (stackTop c)
      rw [(callEffect_stack effectC).1]
      change InProgram (Extracted.textAddress + BitVec.ofNat 64 (offset+14) + BitVec.ofNat 64 5)
      rw [pcAdd]
      exact inProgram_of_textOffset _ (by have bound := code.bound; omega)
  have leftC : Nat256At c (c.regValue .rdi) x := by
    rw [diC]
    exact prefix_input pre ac pre.outputBounded (pre.separation 1 2 (by decide)) left
  have rightC : Nat256At c (c.regValue .rdx) y := by
    rw [dxC]
    exact prefix_input pre ac pre.inputBounded (pre.separation 0 2 (by decide)) right
  obtain ⟨t, result, value⟩ := P256.Proofs.SecretKeyFromBytes.Scalar.Equal.equal_correct cp
  simp only [SecretKeyFromBytes.Scalar.Equal.prefixEqual_nat256 leftC rightC, decide_eq_true_eq] at value
  obtain ⟨m, runD⟩ := result.execution
  refine ⟨t, ⟨⟨1+n+1+m, ((runA.trans runB).trans runC).trans runD⟩,
    result.ready, result.loaded cp.loaded, ?_, ?_, ?_, value⟩⟩
  · exact (ac.trans result.agrees).mono (by
      simp [prefixClobbers, P256.Proofs.SecretKeyFromBytes.Scalar.Equal.clobbers])
  · rw [result.rip]
    change stackTop c = _
    rw [(callEffect_stack effectC).1]
    change Extracted.textAddress + BitVec.ofNat 64 (offset+14) + BitVec.ofNat 64 5 = _
    rw [pcAdd]
  · exact result.rsp.trans ((callEffect_stack effectC).2.trans spB)

end P256.Proofs.Generate.Zero
