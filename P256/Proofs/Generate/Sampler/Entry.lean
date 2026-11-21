import P256.Proofs.Generate.Sampler.Prologue
import P256.Proofs.Generate.Sampler.Setup
import P256.Proofs.Generate.Sampler.Memory
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SignatureFromDer.Parser.ReadSlice

structure LoopReady [Bindings] (s t : RamState) (input : ByteArray) (offset : Nat)
    (pc : BitVec 64 := 0x100c94) (lookAhead : Nat := 0) : Prop
    extends State s t where
  rip : t.RIP = pc
  descriptor : t.regValue .r14 = s.regValue .rsi
  source : t.regValue .rbp = Sampler.source s + BitVec.ofNat 64 (offset+lookAhead)
  remaining : t.regValue .r13 = BitVec.ofNat 64 (input.size-offset)
  decoded : t.regValue .r15 = stackPtr s - 184
  buffer : t.regValue .r12 = stackPtr s - 224
  output : memLoad t.external (stackPtr s - 192) 64 = s.regValue .rdi

theorem entry_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : Pre s boundary input) :
    ∃ t, (∃ fuel, Advances boundary fuel s t) ∧ LoopReady s t input 0 := by
  obtain ⟨a, runA, frameA, ripA, memoryA, agreesA⟩ := frame_entry pre.toCalleePre
  have stateA := State.of_scalarFrame frameA
  have rsiA : a.regValue .rsi = s.regValue .rsi :=
    agreesA.read (n := 64) (r := 6) (by simp [saveFrame])
  have rdiA : a.regValue .rdi = s.regValue .rdi :=
    agreesA.read (n := 64) (r := 7) (by simp [saveFrame])
  have preserved : ∀ (addr : BitVec 64), (s.regValue .rsi).toNat ≤ addr.toNat →
      addr.toNat + 8 ≤ (s.regValue .rsi).toNat + 16 →
      memLoad a.external addr 64 = memLoad s.external addr 64 := by
    intro addr lower upper
    apply frame_memLoad frameA.frame ?_ pre.inputBounded lower upper
    intro region hr
    have which : region = registerRegion s .rdi 104 ∨ region = Stack.region s 3624 := by
      simpa using hr
    rcases which with rfl | rfl
    · exact pre.separation 0 1 (by decide)
    · exact pre.separation 0 2 (by decide)
  have lengthOffset : (s.regValue .rsi + 8).toNat = (s.regValue .rsi).toNat + 8 := by
    have bound : (s.regValue .rsi).toNat + 16 < 2^32 := pre.inputBounded
    rw [BitVec.toNat_add]
    change ((s.regValue .rsi).toNat + 8) % 2^64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have inputRead : MemReadable a (a.regValue .rsi) 16 := by
    rw [rsiA]
    exact readable_of_grow (memoryRegion_memReadable pre.inputBounded pre.inputAllocated
      (by exact Nat.le_refl _) (by exact Nat.le_refl _)) frameA.allocated
  have hp : SetupPre a := ⟨ripA,inputRead,stateA.stack_writable pre (by decide),
    stateA.stack_code pre (offset := 72) (len := 8) (codeOffset := 0xbe1)
      (codeLen := 25) (by decide) (by decide), by
      change RangeApart _ _ (a.regValue .rsi) _
      rw [rsiA]
      exact stateA.stack_descriptor pre (by decide)⟩
  obtain ⟨fuelB, b, runB, readyB, _, effectB⟩ := (setup boundary pre.outerBoundary) a
    (readyToStep frameA.machine frameA.bindingsSupported) (setup_loaded frameA.loaded) hp
  have stateB := stateA.after pre readyB effectB.agrees (by
    intro c hc address covered
    simp only [setupEffect,Effect.components,List.map_cons,List.map_nil,
      List.mem_cons,List.not_mem_nil,or_false,List.mem_append,List.append_nil,
      Write.component,Operand.component] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    exact ⟨ScalarFrame.workRegion s 3624,by simp [bodyWrites],
      stateA.work_writes pre (by decide) covered⟩)
    (effectB.agrees.read (n := 64) (r := 4) (by simp [setupEffect,Effect.components]))
  have values := effectB.writes
  simp only [setupEffect] at values
  have outputB : memLoad b.external (stackPtr s - 192) 64 = s.regValue .rdi := by
    have h := values.2.1
    change memLoad b.external (stackPtr a + 72) 64 = a.regValue .rdi at h
    have addr : stackPtr a + 72 = stackPtr s - 192 :=
      ScalarFrame.scalar_stack_address (frameOffset := 264) (offset := 72)
        frameA.rsp (by decide) (by decide)
    rw [addr,rdiA] at h
    exact h
  obtain ⟨t,runT,readyT,effectT⟩ := (jmp_rel32_effect_step 0x100bfa 149 (by decide +kernel)).advances
    readyB (programText_slice (programLoaded_codeIn stateB.loaded) 0xbfa
      [0xe9,0x95,0x0,0x0,0x0] (by decide) rfl) effectB.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xc94 (by decide)))
  have stateT := stateB.after_registers pre readyT effectT.agrees
    (by simp [jmpEffect,Effect.components,Component.Covers])
    (by simp [jmpEffect,Effect.components])
  refine ⟨t,⟨_,(runA.trans runB).trans runT⟩,
    { toState := stateT, rip := effectT.rip, descriptor := ?_, source := ?_,
      remaining := ?_, decoded := ?_, buffer := ?_, output := ?_ }⟩
  · exact (effectT.agrees.read (n := 64) (r := 14) (by simp [jmpEffect,Effect.components])).trans
      (values.1.trans rsiA)
  · apply (effectT.agrees.read (n := 64) (r := 5)
      (by simp [jmpEffect,Effect.components])).trans
    change b.regValue .rbp = source s + 0#64
    rw [BitVec.add_zero]
    have h := values.2.2.1
    change b.regValue .rbp = memLoad a.external (a.regValue .rsi) 64 at h
    rw [rsiA,preserved _ (by exact Nat.le_refl _) (by omega)] at h
    exact h
  · apply (effectT.agrees.read (n := 64) (r := 13)
      (by simp [jmpEffect,Effect.components])).trans
    have h := values.2.2.2.1
    change b.regValue .r13 = memLoad a.external (a.regValue .rsi + 8) 64 at h
    rw [rsiA,preserved _ (by rw [lengthOffset]; omega) (by rw [lengthOffset]; omega),pre.length] at h
    change b.regValue .r13 = BitVec.ofNat 64 input.size
    exact h
  · exact (effectT.agrees.read (n := 64) (r := 15)
      (by simp [jmpEffect,Effect.components])).trans
      (values.2.2.2.2.1.trans (ScalarFrame.scalar_stack_address (frameOffset := 264)
        (offset := 80) frameA.rsp (by decide) (by decide)))
  · exact (effectT.agrees.read (n := 64) (r := 12)
      (by simp [jmpEffect,Effect.components])).trans
      (values.2.2.2.2.2.trans (ScalarFrame.scalar_stack_address (frameOffset := 264)
        (offset := 40) frameA.rsp (by decide) (by decide)))
  · rw [effectT.agrees.external (by simp [jmpEffect,Effect.components,Component.Covers])]
    exact outputB

end P256.Proofs.Generate.Sampler
