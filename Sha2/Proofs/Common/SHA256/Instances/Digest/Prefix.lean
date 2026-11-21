import Sha2.Proofs.Common.SHA256.Instances.Digest.Initialize
import Sha2.Proofs.Common.SHA256.Instances.Digest.Absorb
import Sha2.Proofs.Common.SHA256.Absorb.DirectCorrectness

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Digest

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem prepared {v : Wrapper.Variant} [Bindings] {initial p h u : RamState} {data : ByteArray}
    (call : OneShot.ValidCall (routine v) initial data)
    (push : (Prologue.effect (Segment.prologue.pc v) .five272 initial).Holds initial p)
    (prsp : stackPtr p = stackPtr initial - 312)
    (args : (Blocks.Digest.Header.effect (Segment.header.pc v) p).Holds p h)
    (init : Initialize.Post (Initialization.digest.layout v) (rspOf h + 168) h u)
    (state : ExecutionState initial u (regions initial v)) :
    Absorb.Direct.Prepared (absorb v) ((absorb v).sp initial) ⟨initial.regValue .rdi, data⟩ u := by
  have hrsp : stackPtr h = stackPtr initial - 312 :=
    (args.agrees.read (n := 64) (r := 4) (by
      simp [Blocks.Digest.Header.effect, Effect.components])).trans prsp
  have hrsp' : rspOf h = (absorb v).sp initial := hrsp
  have writes : h.regValue .rbx = p.regValue .rdx ∧
      h.regValue .r14 = p.regValue .rsi ∧ h.regValue .rsi = p.regValue .rdi := args.writes
  have reginit (r : BitVec 5) (ne : r ≠ 0) :
      (.reg r : Operand 64).read u = (.reg r : Operand 64).read h := by
    apply init.frame.read
    change Component.reg r ∉ [.reg 0, .reg 0, .reg 0, .reg 0,
      .mem ((rspOf h + 168) + 64) 32, .mem ((rspOf h + 168) + 96) 8,
      .mem ((rspOf h + 168) + 63) 1, .rip]
    simpa using ne
  have input : (⟨initial.regValue .rdi, data⟩ : Input).region = OneShot.inputRegion initial data := rfl
  have initPC : (Initialization.digest.layout v).finish = (absorb v).pc .select := by
    cases v <;> decide +kernel
  refine ⟨init.rip.trans initPC, init.rsp.trans hrsp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change HasherAt u ((absorb v).sp initial + 168) ByteArray.empty v.initialHash
    rw [← hrsp']
    exact init.hasher
  · exact (reginit 6 (by (try dsimp only [routine]); decide +kernel)).trans (writes.2.2.trans
      (push.agrees.read (n := 64) (r := 7) (by
        simp [Prologue.effect, Prologue.registers, Epilogue.Layout.six, Effect.components,
          List.zipIdx_cons, List.zipIdx_nil, Write.component, Operand.component])))
  · have orig : p.regValue .rsi = initial.regValue .rsi :=
      push.agrees.read (n := 64) (r := 6) (by
        simp [Prologue.effect, Prologue.registers, Epilogue.Layout.six, Effect.components,
          List.zipIdx_cons, List.zipIdx_nil, Write.component, Operand.component])
    exact (reginit 14 (by (try dsimp only [routine]); decide +kernel)).trans (writes.2.1.trans (orig.trans (by
      rw [← call.lengthArgumentMatchesData, BitVec.ofNat_toNat, BitVec.setWidth_eq])))
  · rw [input]
    apply Common.Memory.hasBytes_of_frame call.inputInMemory.2.2 call.inputInMemory.2.1 state.frame
    intro region member
    have mem : region ∈ [OneShot.outputRegion (routine v) initial,
        Stack.region initial (routine v).minStackBytes] := by
      have stackSize : (routine v).minStackBytes = 784 := rfl
      simpa [regions, stackSize] using member
    exact (call.separation.2 region mem).1 _ (List.mem_singleton_self _)
  · rw [input]
    exact call.inputInMemory.2.1
  · change data.size < 2^61
    have bound : (initial.regValue .rdi).toNat + data.size < 2^32 := call.inputInMemory.2.1
    omega

theorem absorbed {v : Wrapper.Variant} [bindings : Bindings] {initial : RamState} {data : ByteArray}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : OneShot.ValidCall (routine v) initial data) :
    ∃ p h u t,
      (Prologue.effect (Segment.prologue.pc v) .five272 initial).Holds initial p ∧
      stackPtr p = stackPtr initial - 312 ∧
      (Blocks.Digest.Header.effect (Segment.header.pc v) p).Holds p h ∧
      Initialize.Post (Initialization.digest.layout v) (rspOf h + 168) h u ∧
      Absorb.Direct.Finished (absorb v) initial u t (regions initial v) ⟨initial.regValue .rdi, data⟩ := by
  obtain ⟨p, stateP, push, rspP, ripP⟩ := prologue (v := v) machine call
  obtain ⟨h, stateH, args⟩ := header (v := v) machine call stateP ripP
  have rspH : stackPtr h = stackPtr initial - 312 :=
    (args.agrees.read (n := 64) (r := 4) (by
      simp [Blocks.Digest.Header.effect, Effect.components])).trans rspP
  have headerPC : (Blocks.Digest.Header.effect (Segment.header.pc v) p).rip =
      (Initialization.digest.layout v).start := by
    cases v <;> rfl
  obtain ⟨u, stateU, init⟩ := initialized (v := v) machine call stateH rspH
    (args.rip.trans headerPC)
  have prep := prepared (v := v) call push rspP args init stateU
  have avoid : (Stack.region initial 784).Avoids (fun a => InProgram a ∨ InPageTables a) :=
    (call.separation.2 _ (by exact List.mem_cons_of_mem _ (List.mem_singleton_self _))).2
  have within : ∀ region ∈ Absorb.Direct.footprint (absorb v) ((absorb v).sp initial),
      ∀ a, region.Contains a → ∃ outer ∈ regions initial v, outer.Contains a := by
    intro region member a ha
    change region ∈ #v[⟨(stackPtr initial - 312 + 168).toNat, 104⟩,
      ⟨(stackPtr initial - 312 - 344).toNat, 344⟩] at member
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
    refine ⟨Stack.region initial 784, by simp [regions], ?_⟩
    rcases member with rfl | rfl
    · exact stack_frame_region_subset call.stack (frame := 312) (offset := 168)
        (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel) ha
    · have sub : stackPtr initial - 312 - 344 = stackPtr initial - BitVec.ofNat 64 656 := by
        rw [BitVec.sub_sub]; rfl
      rw [sub] at ha
      exact stack_sub_region_subset call.stack (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel) ha
  obtain ⟨t, result⟩ := Absorb.Direct.correct (absorb v) (absorb_wellFormed v) (absorb_flow v)
    (absorb_codeFacts v) (absorb_blockContracts (v := v) _
      (valid_return_boundary machine call.stack call.returnAddress).2.2)
    stride machine call.stack avoid call.returnAddress stateU prep
    ((call.separation.2 _ (by exact List.mem_cons_of_mem _ (List.mem_singleton_self _))).1 _
      (List.mem_singleton_self _)) within
  exact ⟨p, h, u, t, push, rspP, args, init, result⟩

end Sha2.Proofs.Common.SHA256.Instances.Digest
