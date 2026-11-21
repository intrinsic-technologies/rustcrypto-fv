import Sha2.Proofs.Common.SHA256.Instances.Absorb.TableShape
import Sha2.Proofs.Common.SHA256.Instances.Absorb.LoadPre
import Sha2.Proofs.Common.SHA256.Blocks.Absorb

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb

set_option maxHeartbeats 400000 in
theorem noClone_load [bindings : Bindings] {l : Table.Layout}
    (shape : NoCloneShape l) (boundary : ReturnBoundary)
    (stride : UnitStringStride bindings) (outside : ¬ InProgram boundary.rip) (sp : BitVec 64) :
    AdvanceTriple boundary (Table.LoadPre l sp)
      ((l.load ++ l.cloneIn).flatMap Blocks.Site.code) (Table.LoadPost l sp) := by
  rcases shape with ⟨noIn, noOut, data⟩
  unfold noCloneData at data
  split at data
  · rename_i count pc0 index source length pointers lengths pc1 tail address hcount hload
    have facts := of_decide_eq_true data
    rcases facts with ⟨hi, headCode, exitCode, hs, hl, ht, hstored, hptrBound,
      hlenBound, hrestore, hbufBound, distinct, clobbers, hbuffer, rfl, pc1Eq,
      entryEq, code0, code1, rfl, rfl, rfl, small, large⟩
    clear data headCode exitCode small large noOut
    intro s ready loaded pre
    have pre1 : Blocks.Pre l.head
        (.loadPair index source length (.d32 l.pointerSlot) (.d32 l.lengthSlot)) s := by
      apply loadPair_pre_of_table pre hi
      · simp [AddrMode.Valid]
      · simp [AddrMode.Valid]
      · simp_all [AddrMode.Valid, regLow, List.pairwise_cons]
      · exact d32_value_ofNat _ hptrBound
      · exact d32_value_ofNat _ hlenBound
      · simp_all [List.pairwise_cons]
    have runPair : Blocks.Contract boundary l.head
        (.loadPair index source length (.d32 l.pointerSlot) (.d32 l.lengthSlot)) :=
      Blocks.run boundary _ _ stride outside (codeLocation_inProgram code0) trivial
    have codePair : CodeIn (codeRange l.head
        (Blocks.bytes (.loadPair index source length (.d32 l.pointerSlot) (.d32 l.lengthSlot)))) s := by
      apply loaded.mono
      intro x hx
      simp only [hload, noIn, List.append_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      exact List.mem_append_left _ hx
    obtain ⟨fuel, u, run, readyU, codeU, step⟩ := runPair s ready codePair pre1
    have memory : u.external = s.external := step.agrees.external (by
      simp [Blocks.effect, Effect.components, Component.Covers])
    have widen := Blocks.widened_eq
    have distinct5 := distinct.map (S := fun a b : BitVec 5 => a ≠ b)
      (fun r => r.setWidth 5) (fun a b hab he => hab ((widen a b).mp he))
    simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at distinct5
    have rsp : stackPtr u = sp := by
      apply Eq.trans (step.agrees.read (n := 64) (r := 4) ?_) pre.rsp
      simp_all [Blocks.effect, Effect.components, Write.component, Operand.component,
        List.pairwise_cons, ne_comm]
    have pre2 : Blocks.Pre pc1
        (.loadTail tail (.sib 4 none 0 (.d8 (l.chunk.bufferOffset + 63)))) u := by
      refine ⟨?_, by simp [AddrMode.Valid], ?_⟩
      · rw [pc1Eq]
        exact step.rip
      · have disp : (Disp.d8 (l.chunk.bufferOffset + 63)).value =
            BitVec.ofNat 64 (l.chunk.bufferOffset + 63) := by
          change (Disp.d8 (BitVec.ofNat 8 l.chunk.bufferOffset + BitVec.ofNat 8 63)).value = _
          rw [← BitVec.ofNat_add]
          exact d8_value_ofNat _ hbufBound
        have read := (Common.Memory.memReadable_sub pre.active.toMemReadable 63 1 (by decide)).of_external_eq memory
        change MemReadable u (stackPtr u + (Disp.d8 (l.chunk.bufferOffset + 63)).value) 1
        rw [rsp, disp]
        simpa only [Layout.buffer, BitVec.ofNat_add, BitVec.add_assoc] using read
    have runTail : Blocks.Contract boundary pc1
        (.loadTail tail (.sib 4 none 0 (.d8 (l.chunk.bufferOffset + 63)))) :=
      Blocks.run boundary _ _ stride outside (codeLocation_inProgram code1) trivial
    have loadedU : CodeIn ((l.load ++ l.cloneIn).flatMap Blocks.Site.code) u := by
      apply step.codeIn _ loaded
      apply Effect.Avoids.of_noMem
      simp [Blocks.effect, Effect.components, Component.Covers]
    have codeTail : CodeIn (codeRange pc1 (Blocks.bytes
        (.loadTail tail (.sib 4 none 0 (.d8 (l.chunk.bufferOffset + 63)))))) u := by
      apply loadedU.mono
      intro x hx
      simp only [hload, noIn, List.append_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      exact List.mem_append_right _ hx
    obtain ⟨fuel2, t, run2, readyT, codeT, step2⟩ := runTail u readyU codeTail pre2
    have memory2 : t.external = u.external := step2.agrees.external (by
      simp [Blocks.effect, Effect.components, Component.Covers])
    have memoryT := memory2.trans memory
    have loadedT : CodeIn ((l.load ++ l.cloneIn).flatMap Blocks.Site.code) t := by
      apply step2.codeIn _ loadedU
      apply Effect.Avoids.of_noMem
      simp [Blocks.effect, Effect.components, Component.Covers]
    refine ⟨fuel + fuel2, t, run.trans run2, readyT, loadedT, ?_⟩
    clear runPair runTail codePair codeTail pre1 pre2 loadedU codeU codeT code0 code1 hload
    have total := step.agrees.trans step2.agrees
    have agrees : AgreesExcept (l.chunk.clobbered.map Component.reg ++
        (l.chunk.bufferSource.toList.map fun r => Component.reg (r.setWidth 5)) ++
        [.mem (l.chunk.buffer sp) 104, .flags, .rip]) s t := by
      apply total.mono
      intro c hc
      simp only [Blocks.effect, Effect.components, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, List.map_cons, List.map_nil, Write.component,
        Operand.component, or_assoc] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [List.mem_map, List.mem_append]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, agrees, ?_, ?_⟩
    · exact step2.rip.trans entryEq.symm
    · exact (step2.agrees.read (n := 64) (r := 4) (by
        simp_all [Blocks.effect, Effect.components, Write.component, Operand.component,
          List.pairwise_cons, ne_comm])).trans rsp
    · rw [hs]
      have preserved : Blocks.readReg t source = Blocks.readReg u source :=
        step2.agrees.read (by simp_all [Blocks.effect, Effect.components,
          Write.component, Operand.component, ne_comm])
      apply preserved.trans
      have written : Blocks.readReg u source = memLoad s.external
          (memLoad s.external (rspOf s + (Disp.d32 l.pointerSlot).value) 64 +
            (Blocks.readReg s index <<< 3)) 64 := step.writes.2.1
      have stack : rspOf s = sp := pre.rsp
      simpa only [stack, d32_value_ofNat _ hptrBound, hi] using written
    · rw [hl]
      have preserved : Blocks.readReg t length = Blocks.readReg u length :=
        step2.agrees.read (by simp_all [Blocks.effect, Effect.components,
          Write.component, Operand.component, ne_comm])
      apply preserved.trans
      have written : Blocks.readReg u length = memLoad s.external
          (memLoad s.external (rspOf s + (Disp.d32 l.lengthSlot).value) 64 +
            (Blocks.readReg s index <<< 3)) 64 := step.writes.2.2
      have stack : rspOf s = sp := pre.rsp
      simpa only [stack, d32_value_ofNat _ hlenBound, hi] using written
    · rw [ht]
      have written : Blocks.readReg t tail = (memLoad u.external
          (stackPtr u + (Disp.d8 (l.chunk.bufferOffset + 63)).value) 8).setWidth 64 := step2.writes
      have disp : (Disp.d8 (l.chunk.bufferOffset + 63)).value =
          BitVec.ofNat 64 (l.chunk.bufferOffset + 63) := by
        change (Disp.d8 (BitVec.ofNat 8 l.chunk.bufferOffset + BitVec.ofNat 8 63)).value = _
        rw [← BitVec.ofNat_add]
        exact d8_value_ofNat _ hbufBound
      rw [rsp, memory, disp] at written
      simpa only [Table.Layout.stored, hstored, BitVec.ofNat_add,
        BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using written
    · intro i _
      simp only [Table.Layout.stored, Layout.buffer, hstored]
      exact congrArg (fun m => m[sp + BitVec.ofNat 64 l.chunk.bufferOffset + BitVec.ofNat 64 i]?) memoryT
    · intro r hr
      have opt : l.chunk.bufferSource = some r := by simpa only [Option.mem_def] using hr
      have different : r ≠ source ∧ r ≠ length ∧ r ≠ tail ∧ r ≠ 0 := by
        simpa only [opt, noCloneBufferSource, decide_eq_true_eq] using hbuffer
      have wide0 : r.setWidth 5 ≠ (0 : BitVec 5) := fun eq => different.2.2.2 ((widen r 0).mp eq)
      have wideS : r.setWidth 5 ≠ source.setWidth 5 := fun eq => different.1 ((widen r source).mp eq)
      have wideL : r.setWidth 5 ≠ length.setWidth 5 := fun eq => different.2.1 ((widen r length).mp eq)
      have wideT : r.setWidth 5 ≠ tail.setWidth 5 := fun eq => different.2.2.1 ((widen r tail).mp eq)
      exact (total.read (by simp_all [Blocks.effect, Effect.components,
        Write.component, Operand.component])).trans (pre.bufferRegister noIn r hr)
    · rw [hcount]
      exact total.read (by simp_all [Blocks.effect, Effect.components,
        Write.component, Operand.component, ne_comm])
    · rw [hi]
      exact total.read (by simp_all [Blocks.effect, Effect.components,
        Write.component, Operand.component, ne_comm])
    · intro address _
      exact congrArg (fun m => m[address]?) memoryT
    · intro r hr hsource
      exact agrees.read (by simp_all [ne_comm])
  · contradiction

end Sha2.Proofs.Common.SHA256.Instances.Absorption
