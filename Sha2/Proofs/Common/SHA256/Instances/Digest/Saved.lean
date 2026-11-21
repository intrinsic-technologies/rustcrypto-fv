import Sha2.Proofs.Common.SHA256.Instances.Digest.Registers
import Sha2.Proofs.Common.SHA256.Instances.Digest.Serialize

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Digest

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem saved_memory {v : Wrapper.Variant} [Bindings] {initial p h u absorbedState c q t z a w : RamState} {data : ByteArray}
    (call : OneShot.ValidCall (routine v) initial data)
    (prsp : stackPtr p = stackPtr initial - 312)
    (args : (Blocks.Digest.Header.effect (Segment.header.pc v) p).Holds p h)
    (init : Initialize.Post (Initialization.digest.layout v) (rspOf h + 168) h u)
    (input : Absorb.Direct.Finished (absorb v) initial u absorbedState (regions initial v) ⟨initial.regValue .rdi, data⟩)
    (setup : (Blocks.Digest.CloneSetup.effect (Segment.cloneSetup.pc v) absorbedState).Holds absorbedState c)
    (copy : (repMovsqEffect (Segment.clone.pc v) c).Holds c q)
    (normalize : (Blocks.Digest.Normalize.effect (Segment.normalize.pc v) q).Holds q t)
    (finish : Finalize.Finalized (Finalization.digest.layout v) initial t z (regions initial v) data)
    (load : (Serialize.effect (Segment.loadSwap.pc v) (.loadSwap .at64 (v == .sha224)) z).Holds z a)
    (store : (Serialize.effect (Segment.store.pc v) (.store .rbx (v == .sha224)) a).Holds a w)
    (output : (.reg 3 : Operand 64).read a = initial.regValue .rdx) :
    ∀ x : BitVec 64, (stackPtr initial).toNat - 40 ≤ x.toNat →
      x.toNat < (stackPtr initial).toNat + 8 → w.external[x]? = p.external[x]? := by
  intro x high upper
  have bounds : 784 ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2^32 :=
    stack_valid_bounds call.stack
  have rspH : rspOf h = stackPtr initial - 312 :=
    (args.agrees.read (n := 64) (r := 4) (by
      simp [Blocks.Digest.Header.effect, Effect.components])).trans prsp
  have rspV : rspOf absorbedState = stackPtr initial - 312 := input.rsp
  have below (offset len : Nat) (bound : offset + len ≤ 272)
      (covered : (Component.mem (stackPtr initial - 312 + BitVec.ofNat 64 offset) len).Covers x) :
      False := by
    have low := stack_frame_below_saved call.stack (frame := 312) (allocation := 272)
      (by (try dsimp only [routine]); decide +kernel) bound (by (try dsimp only [routine]); decide +kernel) covered
    omega
  have belowRegion (offset len : Nat) (bound : offset + len ≤ 272)
      (member : (⟨(stackPtr initial - 312 + BitVec.ofNat 64 offset).toNat, len⟩ :
        MemoryRegion).Contains x.toNat) : False := by
    change (stackPtr initial - BitVec.ofNat 64 312 + BitVec.ofNat 64 offset).toNat ≤ x.toNat ∧
      x.toNat < (stackPtr initial - BitVec.ofNat 64 312 + BitVec.ofNat 64 offset).toNat + len at member
    rw [stack_frame_toNat call.stack (frame := 312) (offset := offset) (by (try dsimp only [routine]); decide +kernel) (by omega)] at member
    omega
  have belowCall (member : (⟨(stackPtr initial - 312 - 344).toNat, 344⟩ :
      MemoryRegion).Contains x.toNat) : False := by
    have address : (stackPtr initial - 312 - 344).toNat = (stackPtr initial).toNat - 656 :=
      stack_frame_below_toNat call.stack (frame := 312) (below := 344) (by (try dsimp only [routine]); decide +kernel)
    change _ ≤ x.toNat ∧ x.toNat < _ at member
    rw [address] at member
    dsimp only at member
    omega
  have headerMemory : h.external = p.external := args.agrees.external (by
    simp [Blocks.Digest.Header.effect, Effect.components, Component.Covers])
  have initMemory : u.external[x]? = h.external[x]? := by
    apply init.frame.memory
    intro comp hc covered
    change comp ∈ [.reg 0, .reg 0, .reg 0, .reg 0,
      .mem ((rspOf h + 168) + 64) 32, .mem ((rspOf h + 168) + 96) 8,
      .mem ((rspOf h + 168) + 63) 1, .rip] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals rw [rspH, BitVec.add_assoc] at covered
    · exact below 232 32 (by (try dsimp only [routine]); decide +kernel) covered
    · exact below 264 8 (by (try dsimp only [routine]); decide +kernel) covered
    · exact below 231 1 (by (try dsimp only [routine]); decide +kernel) covered
  have inputMemory : absorbedState.external[x]? = u.external[x]? := by
    apply input.memory
    intro region hr contains
    change region ∈ #v[⟨(stackPtr initial - 312 + 168).toNat, 104⟩,
      ⟨(stackPtr initial - 312 - 344).toNat, 344⟩] at hr
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact belowRegion 168 104 (by (try dsimp only [routine]); decide +kernel) contains
    · exact belowCall contains
  have setupMemory : c.external = absorbedState.external := setup.agrees.external (by
    simp [Blocks.Digest.CloneSetup.effect, Effect.components, Component.Covers])
  have values : rdi.read c = rspOf absorbedState ∧ rsi.read c = rspOf absorbedState + 168 ∧ rcx.read c = 13 := setup.writes
  have count : (rcx.read c).toNat = 13 := by rw [values.2.2]; decide +kernel
  have copyMemory : q.external[x]? = c.external[x]? := by
    apply copy.agrees.memory
    intro comp hc covered
    rw [repMovsqEffect_components, count, values.1] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    rw [rspV] at covered
    exact below 0 104 (by (try dsimp only [routine]); decide +kernel) (by simpa using covered)
  have normalizeMemory : t.external = q.external := normalize.agrees.external (by
    simp [Blocks.Digest.Normalize.effect, Effect.components, Component.Covers])
  have finalMemory : z.external[x]? = t.external[x]? := by
    apply finish.frame.memory
    intro region hr contains
    change region ∈ #v[⟨(stackPtr initial - 312 + 0).toNat, 64⟩,
      ⟨(stackPtr initial - 312 + 0 + 64).toNat, 32⟩,
      ⟨(stackPtr initial - 312 + 104).toNat, 64⟩,
      ⟨(stackPtr initial - 312 - 344).toNat, 344⟩] at hr
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact belowRegion 0 64 (by (try dsimp only [routine]); decide +kernel) contains
    · have zero : stackPtr initial - 312 + 0 = stackPtr initial - 312 := BitVec.add_zero _
      rw [zero] at contains
      exact belowRegion 64 32 (by (try dsimp only [routine]); decide +kernel) contains
    · exact belowRegion 104 64 (by (try dsimp only [routine]); decide +kernel) contains
    · exact belowCall contains
  have loadMemory : a.external = z.external := load.agrees.external (by
    cases v <;> simp [Serialize.effect, Effect.components, Component.Covers])
  have outputApart : ¬ (OneShot.outputRegion (routine v) initial).Contains x.toNat := by
    intro contains
    have sep : (OneShot.outputRegion (routine v) initial).Disjoint (Stack.region initial 784) :=
      (List.pairwise_cons.mp call.separation.1).1 _ (List.mem_singleton_self _)
    apply sep x.toNat contains
    change (stackPtr initial).toNat - 784 ≤ x.toNat ∧ x.toNat <
      (stackPtr initial).toNat - 784 + ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 784))
    constructor <;> omega
  have outputBelow (offset : Nat) (bound : offset + 4 ≤ v.outputBytes)
      (covered : (Component.mem ((.reg 3 : Operand 64).read a + BitVec.ofNat 64 offset) 4).Covers x) :
      False := by
    obtain ⟨i, hi, rfl⟩ := covered
    apply outputApart
    rw [output, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add call.outputInMemory.2.1 (Nat.le_refl _) (Nat.le_refl _)
      (by change offset+i < v.outputBytes; omega)
  have storeMemory : w.external[x]? = a.external[x]? := by
    apply store.agrees.memory
    intro comp hc covered
    cases v <;> simp only [Serialize.effect, Effect.components,
      show (Wrapper.Variant.sha224 == .sha224) = true from by decide,
      show (Wrapper.Variant.sha256 == .sha224) = false from by decide,
      Bool.false_eq_true, ite_false, ite_true, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      Serialize.OutputRegister.value, List.mem_cons, List.not_mem_nil, or_false] at hc
    all_goals rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc
    all_goals try (subst comp)
    all_goals try exact covered.elim
    all_goals try (rcases hc with rfl | rfl)
    all_goals try exact covered.elim
    all_goals first
      | exact outputBelow 0 (by (try dsimp only [routine]); decide +kernel) covered
      | exact outputBelow 4 (by (try dsimp only [routine]); decide +kernel) covered
      | exact outputBelow 8 (by (try dsimp only [routine]); decide +kernel) covered
      | exact outputBelow 12 (by (try dsimp only [routine]); decide +kernel) covered
      | exact outputBelow 16 (by (try dsimp only [routine]); decide +kernel) covered
      | exact outputBelow 20 (by (try dsimp only [routine]); decide +kernel) covered
      | exact outputBelow 24 (by (try dsimp only [routine]); decide +kernel) covered
      | exact outputBelow 28 (by (try dsimp only [routine]); decide +kernel) covered
  rw [storeMemory, loadMemory, finalMemory, normalizeMemory, copyMemory,
    setupMemory, inputMemory, initMemory, headerMemory]

end Sha2.Proofs.Common.SHA256.Instances.Digest
