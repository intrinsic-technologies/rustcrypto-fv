import P256.Proofs.Verifying.Combination.PointNegativeFinish.Steps
import P256.Proofs.Verifying.Combination.Output.MultiReturn
import P256.Proofs.Verifying.Combination.Loop.MultiDigitState
import P256.Proofs.Sec1Serialize.Tail.Selection.Memory
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.NegativeFinish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open X86 X86.Machine X86.UserProcess X86Proofs

def components (t : RamState) : List Component :=
  [.reg 0, .reg 1, .mem (stackPtr t + 264#64) 32, .mem (stackPtr t + 328#64) 32, .rip]

theorem effect_frame {t w : RamState} (h : (effect t).Holds t w) :
    AgreesExcept (components t) t w := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [components, Component.isMem]
  · intro a c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals obtain ⟨i, hi, rfl⟩ := ha
    · refine ⟨.mem (stackPtr t + 264#64) 32, by simp [components], 24+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.add_assoc]
      congr 1
      rw [← BitVec.add_assoc]
      rfl
    · refine ⟨.mem (stackPtr t + 264#64) 32, by simp [components], 16+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.add_assoc]
      congr 1
      rw [← BitVec.add_assoc]
      rfl
    · refine ⟨.mem (stackPtr t + 264#64) 32, by simp [components], 8+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.add_assoc]
      congr 1
      rw [← BitVec.add_assoc]
      rfl
    · exact ⟨.mem (stackPtr t + 264#64) 32, by simp [components], i, by omega, rfl⟩
    · refine ⟨.mem (stackPtr t + 328#64) 32, by simp [components], 24+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.add_assoc]
      congr 1
      rw [← BitVec.add_assoc]
      rfl
    · refine ⟨.mem (stackPtr t + 328#64) 32, by simp [components], 16+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.add_assoc]
      congr 1
      rw [← BitVec.add_assoc]
      rfl
    · refine ⟨.mem (stackPtr t + 328#64) 32, by simp [components], 8+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.add_assoc]
      congr 1
      rw [← BitVec.add_assoc]
      rfl
    · exact ⟨.mem (stackPtr t + 328#64) 32, by simp [components], i, by omega, rfl⟩

theorem after_effect [Bindings] {s t w : RamState} {boundary : ReturnBoundary}
    (pre : Return.Pre s boundary) (state : State s t) (ready : ReadyToStep w)
    (agrees : AgreesExcept (components t) t w) : State s w := by
  apply state.after_effect pre (by decide) ready agrees ?_ (by simp [components])
  intro c hc a ha
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · have addr := scalar_stack_address state.rsp (offset := 264) (by decide) (by decide)
    rw [addr] at ha
    exact ⟨workRegion s 1432, by simp, work_contains pre (by decide) (by decide) ha⟩
  · have addr := scalar_stack_address state.rsp (offset := 328) (by decide) (by decide)
    rw [addr] at ha
    exact ⟨workRegion s 1432, by simp, work_contains pre (by decide) (by decide) ha⟩

theorem kept [Bindings] {s t w : RamState} {boundary : ReturnBoundary} {off len i : Nat}
    (pre : Return.Pre s boundary) (state : State s t)
    (agrees : AgreesExcept (components t) t w)
    (ho : off ≤ 408) (hl : len ≤ off+8)
    (hx : off+32 ≤ 144 ∨ 144+len ≤ off)
    (hz : off+32 ≤ 80 ∨ 80+len ≤ off) (hi : i<len) :
    w.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
      t.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc ha
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · rw [scalar_stack_address state.rsp (offset := 264) (by decide) (by decide)] at ha
    obtain ⟨j, hj, he⟩ := ha
    exact stack_sub_apart pre.stack (by decide) (by omega) (by decide) hl hx j hj i hi he.symm
  · rw [scalar_stack_address state.rsp (offset := 328) (by decide) (by decide)] at ha
    obtain ⟨j, hj, he⟩ := ha
    exact stack_sub_apart pre.stack (by decide) (by omega) (by decide) hl hz j hj i hi he.symm

theorem copied_bytes [Bindings] {s t w : RamState} {boundary : ReturnBoundary}
    {source destination : Nat} (pre : Return.Pre s boundary) (state : State s t)
    (frame : State s w) (hs : source ≤ 408) (hd : destination ≤ 408)
    (hsl : 32 ≤ source) (hdl : 32 ≤ destination)
    (words : ∀ k < 4,
      memLoad w.external (stackPtr s-BitVec.ofNat 64 destination+BitVec.ofNat 64 (8*k)) 64 =
        memLoad t.external (stackPtr s-BitVec.ofNat 64 source+BitVec.ofNat 64 (8*k)) 64) :
    ∀ i < 32, w.external[stackPtr s-BitVec.ofNat 64 destination+BitVec.ofNat 64 i]? =
      t.external[stackPtr s-BitVec.ofNat 64 source+BitVec.ofNat 64 i]? := by
  intro i hi
  have hb := memByte_of_memLoad_eq (words (i/8) (by omega)) (i%8) (by omega)
  have hi' : 8*(i/8)+i%8=i := by omega
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, hi'] at hb
  have src := (readable_of_grow (stack_sub_readable pre.stack
    (offset := source) (len := 32) (by omega) (by omega)) state.allocated).mem i hi
  have dst := (readable_of_grow (stack_sub_readable pre.stack
    (offset := destination) (len := 32) (by omega) (by omega)) frame.allocated).mem i hi
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp dst
  obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.mp src
  change (w.external[_]?).getD 0 = (t.external[_]?).getD 0 at hb
  rw [ha, hb'] at hb
  simpa only [ha, hb', Option.getD_some, Option.some.injEq] using hb

end P256.Proofs.Verifying.Combination.Loop.Multi.NegativeFinish
