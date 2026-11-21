import P256.Proofs.Field.Interface
import P256.Proofs.Program.Stack

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem schoolbook_pre [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary} {entryPC : BitVec 64} {rightReg : Syntax.Reg}
    (pre : CalleePre s boundary entryPC 32 32 280)
    (rightBounded : (registerRegion s rightReg 32).Bounded)
    (rightAllocated : (registerRegion s rightReg 32).Allocated s.external)
    (rightStack : (registerRegion s rightReg 32).Disjoint (Stack.region s 280))
    (hb : MachineRamUnitStrideDecodable bindings t)
    (hm : SupportedIntegerMachineState bindings.processor t)
    (df : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS) (loaded : ProgramLoaded t)
    (rip : t.RIP = 0x11c960) (rsp : stackPtr t = stackPtr s - 144)
    (left : t.regValue .rsi = s.regValue .rsi)
    (right : t.regValue .rcx = s.regValue rightReg)
    (destination : t.regValue .rdi = stackPtr s - 72)
    (leftLength : t.regValue .rdx = 4) (rightLength : t.regValue .r8 = 4)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (ret : InProgram (returnBoundary t).rip) : SchoolbookPre t boundary := by
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr t).toNat = (stackPtr s).toNat - 144 := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dst : (t.regValue .rdi).toNat = (stackPtr s).toNat - 72 := by
    rw [destination]
    exact stack_sub_toNat pre.stack (by decide)
  have stackStart : (Stack.region t 136).start = (stackPtr s).toNat - 280 := by
    change (stackPtr t).toNat - 136 = _
    rw [sp]
    omega
  have stackEnd : (Stack.region t 136).start + (Stack.region t 136).size =
      (stackPtr s).toNat - 136 := by
    rw [stack_region_end]
    change (stackPtr t).toNat + 8 = _
    rw [sp]
    omega
  have sub (region : MemoryRegion)
      (lo : (stackPtr s).toNat - 280 ≤ region.start)
      (hi : region.start + region.size ≤ (stackPtr s).toNat + 8) :
      ∀ a, region.Contains a → (Stack.region s 280).Contains a := by
    intro a ha
    change region.start ≤ a ∧ a < region.start + region.size at ha
    change (stackPtr s).toNat - 280 ≤ a ∧
      a < (Stack.region s 280).start + (Stack.region s 280).size
    rw [stack_region_end]
    constructor <;> omega
  have stackSub := sub (Stack.region t 136) (by rw [stackStart]; exact Nat.le_refl _)
    (by rw [stackEnd]; omega)
  have outputSub := sub (registerRegion t .rdi 64)
    (by change _ ≤ (t.regValue .rdi).toNat; rw [dst]; omega)
    (by change (t.regValue .rdi).toNat + 64 ≤ _; rw [dst]; omega)
  have allocated (region : MemoryRegion) (h : region.Allocated s.external) :
      region.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (grow a (Option.isSome_iff_exists.mpr (h a ha)))
  have stackAllocated (region : MemoryRegion)
      (h : ∀ a, region.Contains a → (Stack.region s 280).Contains a) :
      region.Allocated t.external :=
    allocated region (fun a ha => pre.stack.2.1 a (h a.toNat ha))
  have leftEq : registerRegion t .rsi 32 = registerRegion s .rsi 32 := by
    simp only [registerRegion, left]
  have rightEq : registerRegion t .rcx 32 = registerRegion s rightReg 32 := by
    simp only [registerRegion, right]
  have leftStack := pre.separation (0 : Fin 3) (2 : Fin 3) (by decide)
  refine ⟨⟨hb, hm, df, loaded, rip, leftEq ▸ pre.inputBounded,
    leftEq ▸ allocated _ pre.inputAllocated, ?_, stackAllocated _ outputSub,
    ?_, ?_, ?_, pre.outerBoundary, ret⟩, rightEq ▸ rightBounded,
    rightEq ▸ allocated _ rightAllocated, ?_, ?_, leftLength, rightLength⟩
  · change (t.regValue .rdi).toNat + 64 < 2^32
    rw [dst]
    omega
  · refine ⟨?_, stackAllocated _ stackSub, ?_, ?_⟩
    · change (Stack.region t 136).start + (Stack.region t 136).size < 2^32
      rw [stackEnd]
      omega
    · change 136 ≤ (stackPtr t).toNat
      rw [sp]
      omega
    · change (stackPtr t).toNat % 16 = 8
      rw [sp]
      have := pre.stack.2.2.2
      change (stackPtr s).toNat % 16 = 8 at this
      omega
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have pairs : (i.val = 0 ∧ j.val = 1) ∨ (i.val = 0 ∧ j.val = 2) ∨
        (i.val = 1 ∧ j.val = 2) := by change i.val < j.val at hij; omega
    rcases pairs with ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩
    all_goals have ei : i = ⟨_, hi ▸ i.isLt⟩ := Fin.ext hi
    all_goals have ej : j = ⟨_, hj ▸ j.isLt⟩ := Fin.ext hj
    all_goals rw [ei, ej]
    · intro a ha hb
      exact leftStack a (leftEq ▸ ha) (outputSub a hb)
    · intro a ha hb
      exact leftStack a (leftEq ▸ ha) (stackSub a hb)
    · intro a ha hb
      change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + 64 at ha
      change (Stack.region t 136).start ≤ a ∧
        a < (Stack.region t 136).start + (Stack.region t 136).size at hb
      rw [dst] at ha
      rw [stackEnd] at hb
      omega
  · intro region hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pre.avoids _ (by simp) a (outputSub a.toNat ha)
    · exact pre.avoids _ (by simp) a (stackSub a.toNat ha)
  · intro a ha hb
    exact rightStack a (rightEq ▸ ha) (outputSub a hb)
  · intro a ha hb
    exact rightStack a (rightEq ▸ ha) (stackSub a hb)

end P256.Proofs.Field.Montgomery
