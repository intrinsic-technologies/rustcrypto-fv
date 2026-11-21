import Md5.Proofs.Streaming.LoopControl
import Md5.Proofs.Streaming.Compare

namespace Md5.Proofs.Streaming

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

inductive StackCounterKind where
  | resetSecond
  | finalizeResetSecond
  | resetDiscardSecond
  deriving DecidableEq

namespace StackCounterKind

def loopKind : StackCounterKind → LoopKind.Kind
  | .resetSecond => .resetSecond
  | .finalizeResetSecond => .finalizeResetSecond
  | .resetDiscardSecond => .resetDiscardSecond

def jumpKind : StackCounterKind → CounterJumpKind
  | .resetSecond => .resetSecond
  | .finalizeResetSecond => .finalizeResetSecond
  | .resetDiscardSecond => .resetDiscardSecond

def pc (kind : StackCounterKind) (full : Bool) : BitVec 64 :=
  match kind with
  | .resetSecond => if full then 0x100a6f else 0x1009b6
  | .finalizeResetSecond => if full then 0x1010ff else 0x101046
  | .resetDiscardSecond => if full then 0x1015df else 0x101529

def index : StackCounterKind → BitVec 5
  | .resetSecond | .finalizeResetSecond => 5
  | .resetDiscardSecond => 12

def offset : StackCounterKind → BitVec 64
  | .resetSecond | .finalizeResetSecond => 192
  | .resetDiscardSecond => 8

def cmpSize : StackCounterKind → BitVec 64
  | .resetSecond | .finalizeResetSecond => 8
  | .resetDiscardSecond => 5

def cmpEA : StackCounterKind → AddrMode
  | .resetSecond | .finalizeResetSecond => .sib 4 none 0 (.d32 192)
  | .resetDiscardSecond => .sib 4 none 0 (.d8 8)

def displacement (kind : StackCounterKind) (full : Bool) : BitVec 32 :=
  match kind with
  | .resetSecond | .finalizeResetSecond => if full then 0xffffff47 else 0xc9
  | .resetDiscardSecond => if full then 0xffffff4a else 0xc6

end StackCounterKind

private theorem stack_counter_post [Bindings] (kind : StackCounterKind) (full : Bool)
    {boundary : ReturnBoundary} (hOutside : ¬ InProgram boundary.rip)
    {s : RamState} {finish index : Nat} (hReady : ReadyToStep s)
    (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = kind.pc full)
    (hIndex : (Operand.reg kind.index : Operand 64).read s = BitVec.ofNat 64 index)
    (hCount : stackWord s kind.offset = BitVec.ofNat 64 finish)
    (hi : index < finish) (hb : finish < 2^64)
    (hRead : MemReadable s (stackPtr s + kind.offset) 8) :
    ∃ t, LoopCounterPost kind.loopKind boundary finish index s t := by
  have hkindIndex : LoopKind.indexRegister kind.loopKind = kind.index := by cases kind <;> rfl
  let pc : BitVec 64 := kind.pc full
  let cc : BitVec 4 := if full then 5 else 4
  let disp : BitVec 32 := kind.displacement full
  have hInc : StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc (encodeIncR64 (kind.index.setWidth 4))) (incR64Effect pc kind.index) :=
    by
      cases kind
      · exact inc_r64_effect_step pc 0x48 0xc5 (by simp [RexWPrefix]) (by decide) (by decide)
      · exact inc_r64_effect_step pc 0x48 0xc5 (by simp [RexWPrefix]) (by decide) (by decide)
      · exact inc_r64_effect_step pc 0x49 0xc4 (by simp [RexWPrefix]) (by decide) (by decide)
  have hIncCode : CodeIn (codeRange pc (encodeIncR64 (kind.index.setWidth 4))) s := by
    cases kind <;> cases full
    · exact program_text_slice hCode 0x9b6 3 (by decide +kernel)
    · exact program_text_slice hCode 0xa6f 3 (by decide +kernel)
    · exact program_text_slice hCode 0x1046 3 (by decide +kernel)
    · exact program_text_slice hCode 0x10ff 3 (by decide +kernel)
    · exact program_text_slice hCode 0x1529 3 (by decide +kernel)
    · exact program_text_slice hCode 0x15df 3 (by decide +kernel)
  obtain ⟨u, hIncRun, hIncReady, hIncEffect⟩ := hInc.advances hReady hIncCode hRip (by
    cases kind <;> cases full
    · exact text_address_ne_return hOutside 0x9b9 (by decide +kernel)
    · exact text_address_ne_return hOutside 0xa72 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x1049 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x1102 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x152c (by decide +kernel)
    · exact text_address_ne_return hOutside 0x15e2 (by decide +kernel))
  have hIncCode' := hIncEffect.codeIn (incR64Effect_avoids _ _ _ _) hCode
  have hRsp : stackPtr u = stackPtr s := hIncEffect.agrees.read (n := 64) (r := 4) (by cases kind <;> simp [StackCounterKind.index])
  have hMemory : u.external = s.external :=
    hIncEffect.agrees.external (by simp [Component.Covers])
  have hIncrement : (Operand.reg kind.index : Operand 64).read u = BitVec.ofNat 64 (index + 1) := by
    have hv : (Operand.reg kind.index : Operand 64).read u = (Operand.reg kind.index : Operand 64).read s + 1 :=
      hIncEffect.writes
    rw [hv, hIndex, BitVec.ofNat_add]
    rfl
  have hCmp : StepEffect (LoadPre (pc + 3) (fun t ↦ stackPtr t + kind.offset) 8)
      (codeRange (pc + 3) (if kind = .resetDiscardSecond then [0x4c, 0x39, 0x64, 0x24, 8] else [0x48, 0x39, 0xac, 0x24, 0xc0, 0, 0, 0]))
      (cmpM64R64Effect (pc + 3) kind.index kind.cmpEA) :=
    by
      cases kind
      · exact cmp_m64_r64_effect_step (pc + 3) 0x48 (by simp [RexWPrefix]) 5
          (.sib 4 none 0 (.d32 192)) (by decide) rfl rfl
      · exact cmp_m64_r64_effect_step (pc + 3) 0x48 (by simp [RexWPrefix]) 5
          (.sib 4 none 0 (.d32 192)) (by decide) rfl rfl
      · exact cmp_m64_r64_effect_step (pc + 3) 0x4c (by simp [RexWPrefix]) 4
          (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl
  have hCmpCode : CodeIn
      (codeRange (pc + 3) (if kind = .resetDiscardSecond then [0x4c, 0x39, 0x64, 0x24, 8] else [0x48, 0x39, 0xac, 0x24, 0xc0, 0, 0, 0])) u := by
    cases kind <;> cases full
    · exact program_text_slice hIncCode' 0x9b9 8 (by decide +kernel)
    · exact program_text_slice hIncCode' 0xa72 8 (by decide +kernel)
    · exact program_text_slice hIncCode' 0x1049 8 (by decide +kernel)
    · exact program_text_slice hIncCode' 0x1102 8 (by decide +kernel)
    · exact program_text_slice hIncCode' 0x152c 5 (by decide +kernel)
    · exact program_text_slice hIncCode' 0x15e2 5 (by decide +kernel)
  have hCmpPre : LoadPre (pc + 3) (fun t ↦ stackPtr t + kind.offset) 8 u :=
    ⟨hIncEffect.rip, by rw [hRsp]; exact hRead.of_external_eq hMemory⟩
  obtain ⟨v, hCmpRun, hCmpReady, hCmpEffect⟩ := hCmp.advances hIncReady hCmpCode hCmpPre (by
    cases kind <;> cases full
    · exact text_address_ne_return hOutside 0x9c1 (by decide +kernel)
    · exact text_address_ne_return hOutside 0xa7a (by decide +kernel)
    · exact text_address_ne_return hOutside 0x1051 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x110a (by decide +kernel)
    · exact text_address_ne_return hOutside 0x1531 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x15e7 (by decide +kernel))
  have hCmpCode' := hCmpEffect.codeIn (cmpM64R64Effect_avoids _ _ _ _ _) hIncCode'
  have hEq : ((BitVec.ofNat 64 finish) == BitVec.ofNat 64 (index + 1)) =
      decide (finish = index + 1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro hh
      have hn := congrArg BitVec.toNat hh
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb,
        Nat.mod_eq_of_lt (show index + 1 < 2^64 by omega)] using hn
    · intro hh
      rw [hh]
  have hZero : (StatusFlags.ofRFLAGS v.RFLAGS).ZF = decide (finish = index + 1) := by
    have hz := hCmpEffect.flag .ZF
    rw [cmpM64R64Effect_zf] at hz
    have hea : kind.cmpEA.addr u (pc + 3 + BitVec.ofNat 64 (movLoadLen kind.cmpEA)) = stackPtr u + kind.offset := by
      cases kind <;> rfl
    rw [hea] at hz
    change (StatusFlags.ofRFLAGS v.RFLAGS).ZF =
      ((Operand.mem (stackPtr u + kind.offset) : Operand 64).read u ==
        (Operand.reg kind.index : Operand 64).read u) at hz
    rw [hIncrement, hRsp] at hz
    change (StatusFlags.ofRFLAGS v.RFLAGS).ZF =
      (memLoad u.external (stackPtr s + kind.offset) 64 == BitVec.ofNat 64 (index + 1)) at hz
    rw [hMemory] at hz
    change (StatusFlags.ofRFLAGS v.RFLAGS).ZF =
      (stackWord s kind.offset == BitVec.ofNat 64 (index + 1)) at hz
    rw [hCount, hEq] at hz
    exact hz
  have hNext : (jccEffect (pc + 3 + kind.cmpSize) 6 cc (disp.signExtend 64) v).rip =
      if index + 1 < finish then LoopKind.entry kind.loopKind else if full then kind.jumpKind.entry else LoopKind.finalPC kind.loopKind := by
    by_cases hend : index + 1 < finish
    · have hne : finish ≠ index + 1 := by omega
      cases kind <;> cases full <;> simp [pc, cc, disp, jccEffect, branchEffect, condHolds,
        StackCounterKind.pc, StackCounterKind.displacement, StackCounterKind.cmpSize,
        StackCounterKind.loopKind, LoopKind.entry, hZero, hne, hend, branchTarget]
    · have heq : finish = index + 1 := by omega
      cases kind <;> cases full <;> simp [pc, cc, disp, jccEffect, branchEffect, condHolds,
        StackCounterKind.pc, StackCounterKind.displacement, StackCounterKind.cmpSize,
        StackCounterKind.loopKind, StackCounterKind.jumpKind, LoopKind.finalPC,
        CounterJumpKind.entry, hZero, heq, branchTarget]
  have hBranchBoundary : (jccEffect (pc + 3 + kind.cmpSize) 6 cc (disp.signExtend 64) v).rip ≠
      boundary.rip := by
    rw [hNext]
    split
    · cases kind
      · exact text_address_ne_return hOutside 0x9c7 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x1057 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x1537 (by decide +kernel)
    · split
      · cases kind
        · exact text_address_ne_return hOutside 0xa80 (by decide +kernel)
        · exact text_address_ne_return hOutside 0x1110 (by decide +kernel)
        · exact text_address_ne_return hOutside 0x15ed (by decide +kernel)
      · cases kind
        · exact text_address_ne_return hOutside 0xa90 (by decide +kernel)
        · exact text_address_ne_return hOutside 0x1120 (by decide +kernel)
        · exact text_address_ne_return hOutside 0x15fd (by decide +kernel)
  have hBranchCode : CodeIn
      (codeRange (pc + 3 + kind.cmpSize) (0x0f :: jccOpcode32 cc :: immBytes 32 disp)) v := by
    cases kind <;> cases full
    · simp only [pc, cc, disp, StackCounterKind.pc, StackCounterKind.cmpSize,
        StackCounterKind.displacement, Bool.false_eq_true, ite_false, BitVec.reduceAdd]
      rw [show (0x0f :: jccOpcode32 4 :: immBytes 32 0xc9) =
        [0xf, 0x84, 0xc9, 0x0, 0x0, 0x0] by decide +kernel]
      exact program_text_slice hCmpCode' 0x9c1 6 (by decide +kernel)
    · simp only [pc, cc, disp, StackCounterKind.pc, StackCounterKind.cmpSize,
        StackCounterKind.displacement, ite_true, BitVec.reduceAdd]
      rw [show (0x0f :: jccOpcode32 5 :: immBytes 32 0xffffff47) =
        [0xf, 0x85, 0x47, 0xff, 0xff, 0xff] by decide +kernel]
      exact program_text_slice hCmpCode' 0xa7a 6 (by decide +kernel)
    · simp only [pc, cc, disp, StackCounterKind.pc, StackCounterKind.cmpSize,
        StackCounterKind.displacement, Bool.false_eq_true, ite_false, BitVec.reduceAdd]
      rw [show (0x0f :: jccOpcode32 4 :: immBytes 32 0xc9) =
        [0xf, 0x84, 0xc9, 0x0, 0x0, 0x0] by decide +kernel]
      exact program_text_slice hCmpCode' 0x1051 6 (by decide +kernel)
    · simp only [pc, cc, disp, StackCounterKind.pc, StackCounterKind.cmpSize,
        StackCounterKind.displacement, ite_true, BitVec.reduceAdd]
      rw [show (0x0f :: jccOpcode32 5 :: immBytes 32 0xffffff47) =
        [0xf, 0x85, 0x47, 0xff, 0xff, 0xff] by decide +kernel]
      exact program_text_slice hCmpCode' 0x110a 6 (by decide +kernel)
    · simp only [pc, cc, disp, StackCounterKind.pc, StackCounterKind.cmpSize,
        StackCounterKind.displacement, Bool.false_eq_true, ite_false, BitVec.reduceAdd]
      rw [show (0x0f :: jccOpcode32 4 :: immBytes 32 0xc6) =
        [0xf, 0x84, 0xc6, 0x0, 0x0, 0x0] by decide +kernel]
      exact program_text_slice hCmpCode' 0x1531 6 (by decide +kernel)
    · simp only [pc, cc, disp, StackCounterKind.pc, StackCounterKind.cmpSize,
        StackCounterKind.displacement, ite_true, BitVec.reduceAdd]
      rw [show (0x0f :: jccOpcode32 5 :: immBytes 32 0xffffff4a) =
        [0xf, 0x85, 0x4a, 0xff, 0xff, 0xff] by decide +kernel]
      exact program_text_slice hCmpCode' 0x15e7 6 (by decide +kernel)
  obtain ⟨t, hBranchRun, hBranchReady, hBranchEffect⟩ :=
    (jcc_rel32_effect_step (pc + 3 + kind.cmpSize) cc disp).advances hCmpReady hBranchCode
      ⟨by
        exact hCmpEffect.rip.trans (by
          simp only [cmpM64R64Effect]
          cases kind <;> cases full <;> decide +kernel),
        fun _ ↦ by cases kind <;> cases full <;> decide +kernel⟩ hBranchBoundary
  have hBranchAgrees : AgreesExcept [.rip] v t := hBranchEffect.agrees
  have hAllAgrees : AgreesExcept [.reg kind.index, .flags, .rip] s t := by
    apply ((hIncEffect.agrees.trans hCmpEffect.agrees).trans hBranchAgrees).mono
    simp [incR64Effect, cmpM64R64Effect, Effect.components]
  have hIndex' : (Operand.reg kind.index : Operand 64).read t = BitVec.ofNat 64 (index + 1) :=
    (hBranchAgrees.read (n := 64) (r := kind.index) (by cases kind <;> simp [StackCounterKind.index])).trans
      ((hCmpEffect.agrees.read (n := 64) (r := kind.index) (by
        rw [cmpM64R64Effect_components]; simp)).trans hIncrement)
  have hCode' := hAllAgrees.codeIn (by simp [Component.Covers]) hCode
  have hRun := (hIncRun.trans hCmpRun).trans hBranchRun
  have hRip' := hBranchEffect.rip.trans hNext
  by_cases hend : index + 1 < finish
  · refine ⟨t, ⟨⟨3, hRun⟩, hBranchReady, hCode', ?_, ?_, ?_⟩⟩
    · simpa only [hend, ite_true] using hRip'
    · simpa only [hkindIndex] using hIndex'
    · simpa only [hkindIndex] using hAllAgrees
  · cases full with
    | false =>
      refine ⟨t, ⟨⟨3, hRun⟩, hBranchReady, hCode', ?_, ?_, ?_⟩⟩
      · simpa only [hend, ite_false, Bool.false_eq_true] using hRip'
      · simpa only [hkindIndex] using hIndex'
      · simpa only [hkindIndex] using hAllAgrees
    | true =>
      have hJumpRip : t.RIP = kind.jumpKind.entry := by
        simpa only [hend, ite_false, ite_true, CounterJumpKind.entry] using hRip'
      obtain ⟨fuel, w, hJumpRun, hJumpReady, hJumpCode, hJumpEffect⟩ :=
        counter_finish_jump kind.jumpKind boundary hOutside t hBranchReady hCode' hJumpRip
      refine ⟨w, ⟨⟨3 + fuel, hRun.trans hJumpRun⟩, hJumpReady, hJumpCode, ?_, ?_, ?_⟩⟩
      · cases kind <;> simpa only [hend, ite_false, LoopKind.finalPC, CounterJumpKind.target,
          StackCounterKind.jumpKind, StackCounterKind.loopKind]
          using hJumpEffect.rip
      · rw [hkindIndex]
        exact (hJumpEffect.agrees.read (n := 64) (r := kind.index) (by simp [Effect.components])).trans
          hIndex'
      · apply (hAllAgrees.trans hJumpEffect.agrees).mono
        simp [Effect.components, hkindIndex]

theorem stack_loop_counter [Bindings] (kind : LoopKind.Kind)
    (hk : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    {boundary : ReturnBoundary} (hOutside : ¬ InProgram boundary.rip)
    {s : RamState} {finish index : Nat} (hReady : ReadyToStep s)
    (hCode : CodeIn Extracted.programImage s) (hRip : s.RIP ∈ kind.exits)
    (hIndex : (Operand.reg (LoopKind.indexRegister kind) : Operand 64).read s =
      BitVec.ofNat 64 index)
    (hCount : LoopKind.count kind s = BitVec.ofNat 64 finish)
    (hi : index < finish) (hb : finish < 2^64)
    (hRead : MemReadable s (stackPtr s + LoopKind.countOffset kind) 8) :
    ∃ t, LoopCounterPost kind boundary finish index s t := by
  rcases hk with rfl | rfl | rfl
  · simp only [Buffered.UpdateKind.exits, List.mem_cons, List.not_mem_nil, or_false] at hRip
    rcases hRip with hRip | hRip
    · exact stack_counter_post .resetSecond false hOutside hReady hCode hRip hIndex hCount hi hb hRead
    · exact stack_counter_post .resetSecond true hOutside hReady hCode hRip hIndex hCount hi hb hRead
  · simp only [Buffered.UpdateKind.exits, List.mem_cons, List.not_mem_nil, or_false] at hRip
    rcases hRip with hRip | hRip
    · exact stack_counter_post .finalizeResetSecond false hOutside hReady hCode hRip hIndex hCount hi hb hRead
    · exact stack_counter_post .finalizeResetSecond true hOutside hReady hCode hRip hIndex hCount hi hb hRead
  · simp only [Buffered.UpdateKind.exits, List.mem_cons, List.not_mem_nil, or_false] at hRip
    rcases hRip with hRip | hRip
    · exact stack_counter_post .resetDiscardSecond false hOutside hReady hCode hRip hIndex hCount hi hb hRead
    · exact stack_counter_post .resetDiscardSecond true hOutside hReady hCode hRip hIndex hCount hi hb hRead

theorem resetSecond_loop_counter [Bindings]
    {boundary : ReturnBoundary} (hOutside : ¬ InProgram boundary.rip)
    {s : RamState} {finish index : Nat} (hReady : ReadyToStep s)
    (hCode : CodeIn Extracted.programImage s) (hRip : s.RIP ∈ Buffered.UpdateKind.resetSecond.exits)
    (hIndex : (Operand.reg (LoopKind.indexRegister .resetSecond) : Operand 64).read s =
      BitVec.ofNat 64 index)
    (hCount : LoopKind.count .resetSecond s = BitVec.ofNat 64 finish)
    (hi : index < finish) (hb : finish < 2^64)
    (hRead : MemReadable s (stackPtr s + 192) 8) :
    ∃ t, LoopCounterPost .resetSecond boundary finish index s t := by
  simp only [Buffered.UpdateKind.exits, List.mem_cons, List.not_mem_nil, or_false] at hRip
  rcases hRip with hRip | hRip
  · exact stack_counter_post .resetSecond false hOutside hReady hCode hRip hIndex hCount hi hb hRead
  · exact stack_counter_post .resetSecond true hOutside hReady hCode hRip hIndex hCount hi hb hRead

end Md5.Proofs.Streaming
