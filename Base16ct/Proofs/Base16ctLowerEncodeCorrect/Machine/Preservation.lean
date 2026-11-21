import Base16ct.Proofs.Base16ctLowerEncodeCorrect.Machine.Interface

namespace Base16ct.Proofs.LowerEncode

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem read_mem_of_agreesExcept {s t : RamState} {cs : List Component}
    (he : AgreesExcept cs s t) (a : BitVec 64) (n : Nat)
    (h : ∀ i < n / 8, ∀ c ∈ cs, ¬ c.Covers (a + BitVec.ofNat 64 i)) :
    (Operand.mem a : Operand n).read t = (Operand.mem a : Operand n).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[a + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[a + BitVec.ofNat 64 i]?).getD 0
  rw [he.byte (h i hi)]

def PreservesCalleeSaved (cs : List Component) : Prop :=
  ∀ r ∈ ([5, 12, 13, 14, 15] : List (BitVec 5)), .reg r ∉ cs

theorem calleeSaved_of_agreesExcept {s t : RamState} {cs : List Component}
    (he : AgreesExcept cs s t) (h : PreservesCalleeSaved cs) :
    (∀ r ∈ [Syntax.Reg.rbp, .r12, .r13, .r14, .r15], t.regValue r = s.regValue r) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact he.read (n := 64) (h 5 (by simp))
  · exact he.read (n := 64) (h 12 (by simp))
  · exact he.read (n := 64) (h 13 (by simp))
  · exact he.read (n := 64) (h 14 (by simp))
  · exact he.read (n := 64) (h 15 (by simp))

theorem MachineInvariant.of_agreesExcept [bindings : Bindings]
    {initial s t : RamState} {capacity : Nat} {cs : List Component}
    (h : MachineInvariant initial capacity s) (he : AgreesExcept cs s t)
    (hr : ReadyToStep t) (hsaved : PreservesCalleeSaved cs)
    (hw : WritesWithin cs (writableRegions initial capacity))
    (hcode : ∀ c ∈ cs, ∀ a b, (a, b) ∈ Extracted.programImage → ¬ c.Covers a)
    (hreturn : ∀ i < 8, ∀ c ∈ cs, ¬ c.Covers (stackPtr initial + BitVec.ofNat 64 i))
    (hd : Component.df ∉ cs := by simp) :
    MachineInvariant initial capacity t := by
  refine ⟨hr, ?_, SupportedSSE.of_agreesExcept he h.sse,
    he.directionFlagClear hd h.df, ?_, fun a ha => he.grow a (h.grows a ha),
    memoryWriteFrame_trans h.memoryFrame (he.memoryWriteFrame hw), ?_⟩
  · exact CodeIn.of_agreesExcept he (fun x hx c hc => hcode c hc x.1 x.2 hx) h.code
  · intro r hr
    exact (calleeSaved_of_agreesExcept he hsaved r hr).trans (h.calleeSaved r hr)
  · exact (read_mem_of_agreesExcept he _ 64 hreturn).trans h.outerReturn

theorem MachineInvariant.initial [bindings : Bindings] {initial : RamState}
    {input : List UInt8} {capacity written : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctLowerEncode initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity)) :
    MachineInvariant initial written initial := by
  have hr : EntryReady Extracted.programImage initial :=
    EntryReady.of_sections hMachine hBindings.smrr hBindings.memoryType
      hBindings.leadingZeroCount hCall.programLoaded (by decide +kernel)
  exact ⟨hr.ready, hr.code, hr.sse, hCall.directionFlagUnset, fun _ _ => rfl,
    fun _ h => h, memoryWriteFrame_refl _ _, rfl⟩

theorem MachineInvariant.of_agreesExcept_noMem [bindings : Bindings]
    {initial s t : RamState} {capacity : Nat} {cs : List Component}
    (h : MachineInvariant initial capacity s) (he : AgreesExcept cs s t)
    (hr : ReadyToStep t) (hsaved : PreservesCalleeSaved cs)
    (hn : ∀ c ∈ cs, c.isMem = false) (hd : Component.df ∉ cs := by simp) :
    MachineInvariant initial capacity t := by
  have hcover : ∀ c ∈ cs, ∀ a, ¬ c.Covers a := by
    intro c hc a
    have hm := hn c hc
    cases c <;> simp_all [Component.Covers, Component.isMem]
  exact h.of_agreesExcept he hr hsaved
    (fun c hc a ha => False.elim (hcover c hc a ha))
    (fun c hc a _ _ => hcover c hc a)
    (fun _ _ c hc => hcover c hc _) hd

theorem MachineInvariant.supported [bindings : Bindings]
    {initial s : RamState} {capacity : Nat} (h : MachineInvariant initial capacity s) :
    SupportedIntegerMachineState bindings.processor s :=
  ⟨h.ready.cpu, h.sse, h.ready.memory, h.ready.ready⟩

end Base16ct.Proofs.LowerEncode
