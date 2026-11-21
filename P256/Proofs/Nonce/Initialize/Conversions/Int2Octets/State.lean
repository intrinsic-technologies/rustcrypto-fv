import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Interface
import P256.Proofs.Program.SaveRegisters
import P256.Proofs.Program.Stack
import P256.Proofs.Program.State
import P256.Proofs.Common.Machine.CallReturn

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Program (savedRegisters)

theorem stackRegion_contains_sub {s : RamState} {reserve offset len : Nat}
    (hReserve : Stack.NoUnderflow s reserve) (hOffset : offset ≤ reserve)
    (hLen : len ≤ offset) {address : BitVec 64}
    (hCover : (Component.mem (stackPtr s - BitVec.ofNat 64 offset) len).Covers address) :
    (Stack.region s reserve).Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hCover
  have hsp := (stackPtr s).isLt
  change reserve ≤ (stackPtr s).toNat at hReserve
  have ho : offset < 2^64 := by omega
  have hsub : (BitVec.ofNat 64 offset) ≤ stackPtr s := by
    simpa only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho] using
      Nat.le_trans hOffset hReserve
  have hi64 : i < 2^64 := by omega
  have hsum : (stackPtr s).toNat - offset + i < 2^64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_sub_of_le hsub, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64,
    Nat.mod_eq_of_lt hsum]
  change (stackPtr s).toNat - reserve ≤ (stackPtr s).toNat - offset + i ∧
    (stackPtr s).toNat - offset + i < (stackPtr s).toNat - reserve +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - reserve))
  omega

theorem saved_word_eq {initial s t : RamState}
    (memory : ∀ a, (Component.mem (stackPtr initial - 48) 56).Covers a →
      t.external[a]? = s.external[a]?)
    (offset : Nat) (bound : offset + 8 ≤ 56) :
    memLoad t.external (stackPtr initial - 48 + BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial - 48 + BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  have covered : (Component.mem (stackPtr initial - 48) 56).Covers
      (stackPtr initial - 48 + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) :=
    ⟨offset + i, by omega, by rw [BitVec.add_assoc, BitVec.ofNat_add]⟩
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [memory _ covered]

theorem stack_pre [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) : CalleePre s boundary 0x106f40 0 0 128 := by
  refine ⟨pre.bindingsSupported, pre.machine, pre.directionFlag, pre.loaded, pre.rip,
    ?_, ?_, ?_, ?_, pre.stack, ?_, ?_, pre.outerBoundary, pre.returnInProgram⟩
  · have h := pre.orderBounded
    simp only [MemoryRegion.Bounded, registerRegion] at h ⊢
    omega
  · intro a h
    simp only [registerRegion, MemoryRegion.Contains, Nat.add_zero] at h
    omega
  · have h := pre.inputBounded
    simp only [MemoryRegion.Bounded, registerRegion] at h ⊢
    omega
  · intro a h
    simp only [registerRegion, MemoryRegion.Contains, Nat.add_zero] at h
    omega
  · intro i j hij a hi hj
    have cases : i = 0 ∨ i = 1 := by have h := j.isLt; omega
    rcases cases with rfl | rfl
    · change (s.regValue .rsi).toNat ≤ a ∧ a < (s.regValue .rsi).toNat + 0 at hi
      omega
    · change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + 0 at hi
      omega
  · intro region hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro a h
      simp only [registerRegion, MemoryRegion.Contains, Nat.add_zero] at h
      omega
    · exact pre.avoids _ (by simp)

structure Stage [bindings : Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop where
  execution : ∃ fuel, Advances boundary fuel initial s
  bindingsSupported : MachineRamUnitStrideDecodable bindings s
  machine : SupportedIntegerMachineState bindings.processor s
  loaded : ProgramLoaded s
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome
  frame : MemoryWriteFrame initial s #v[registerRegion initial .rdx 32, Stack.region initial 128]
  rsp : stackPtr s = stackPtr initial - 72
  saved : ∀ entry ∈ savedRegisters,
    memLoad s.external (stackPtr initial - BitVec.ofNat 64 entry.2) 64 =
      initial.regValue entry.1
  returnAddress : memLoad s.external (stackPtr initial) 64 =
    memLoad initial.external (stackPtr initial) 64
  directionFlag : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS
  mxcsr : s.MXCSR = initial.MXCSR
  fp87 : s.FP87_Control = initial.FP87_Control

structure EntryRegisters (initial s : RamState) : Prop where
  input : s.regValue .rdi = initial.regValue .rdi
  order : s.regValue .rsi = initial.regValue .rsi
  output : s.regValue .rdx = initial.regValue .rdx
  length : s.regValue .rcx = 32

structure LoopRegisters (initial s : RamState) (i : Nat) : Prop where
  input : s.regValue .r13 = initial.regValue .rdi
  output : s.regValue .r14 = initial.regValue .rdx
  zero : s.regValue .r12 = 0
  count : s.regValue .r15 = 4
  index : s.regValue .rbp = BitVec.ofNat 64 i
  remaining : s.regValue .rbx = BitVec.ofNat 64 (32 - 8 * i)
  length : s.regValue .rdx = BitVec.ofNat 64 (32 - 8 * i)

theorem Stage.of_agrees [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {components : List Component} {fuel : Nat}
    (stage : Stage initial s boundary) (pre : Pre initial boundary)
    (run : Advances boundary fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t)
    (writes : WritesWithin components
      #v[registerRegion initial .rdx 32, Stack.region initial 128])
    (saved : ∀ c ∈ components, ∀ a,
      (Component.mem (stackPtr initial - 48) 56).Covers a → ¬ c.Covers a)
    (rsp : .reg 4 ∉ components)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) : Stage initial t boundary := by
  have memory := agrees.memoryWriteFrame writes
  have kept := fun a ha => agrees.memory a (fun c hc => saved c hc a ha)
  obtain ⟨n, hn⟩ := stage.execution
  refine ⟨⟨n + fuel, hn.trans run⟩,
    bindingsSupported_of_ready_agrees stage.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees stage.machine ready agrees, ?_,
    fun a ha => agrees.grow a (stage.allocated a ha),
    memoryWriteFrame_trans stage.frame memory,
    (agrees.read (n := 64) (r := 4) rsp).trans stage.rsp, ?_, ?_,
    agrees.directionFlagClear (by component_not_mem) stage.directionFlag,
    (agrees.mxcsr (by component_not_mem)).trans stage.mxcsr,
    (agrees.fcw (by component_not_mem)).trans stage.fp87⟩
  · intro a b fetch
    rw [memory a]
    · exact stage.loaded a b fetch
    · intro region hr ha
      have hr' : region ∈ [registerRegion initial .rdx 32, Stack.region initial 128] := by
        simpa using hr
      exact pre.avoids region hr' a ha (.inl ⟨b, fetch⟩)
  · intro entry he
    have eqn := stage.saved entry he
    simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply Eq.trans _ eqn
    · simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd, BitVec.add_zero] using
          saved_word_eq (initial := initial) kept 40 (by decide)
    · simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd, BitVec.add_zero] using
          saved_word_eq (initial := initial) kept 32 (by decide)
    · simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd, BitVec.add_zero] using
          saved_word_eq (initial := initial) kept 24 (by decide)
    · simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd, BitVec.add_zero] using
          saved_word_eq (initial := initial) kept 16 (by decide)
    · simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd, BitVec.add_zero] using
          saved_word_eq (initial := initial) kept 8 (by decide)
    · simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd, BitVec.add_zero] using
          saved_word_eq (initial := initial) kept 0 (by decide)
  · apply Eq.trans _ stage.returnAddress
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
      BitVec.reduceAdd, BitVec.add_zero] using
        saved_word_eq (initial := initial) kept 48 (by decide)

theorem Stage.input_integer [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {value : Nat} (stage : Stage initial s boundary) (pre : Pre initial boundary)
    (integer : Nat256At initial (initial.regValue .rdi) value) :
    Nat256At s (initial.regValue .rdi) value := by
  refine ⟨integer.1, ?_⟩
  intro i hi
  rw [stage.frame]
  · exact integer.2 i hi
  · intro region hr ha
    have input := memoryRegion_contains_add pre.inputBounded
      (Nat.le_refl _) (Nat.le_refl _) hi
    have hr' : region = registerRegion initial .rdx 32 ∨ region = Stack.region initial 128 := by
      simpa using hr
    rcases hr' with rfl | rfl
    · exact pre.separation ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) _ input ha
    · exact pre.separation ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide) _ input ha

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets
