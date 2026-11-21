import P256.Proofs.Verifying.Combination.Table.Call
import P256.Proofs.Verifying.Combination.Table.Memory
import P256.Proofs.Verifying.Combination.Table.Result
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Site
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Projective.Add
import P256.Proofs.Projective.Double

set_option autoImplicit false

open P256.Proofs.Program (CalleePre CalleeResult StackCallLayout inProgram_of_textOffset)
open P256.Proofs.Projective.Multiply.Machine.Loop (CallSite call_return_program)

namespace P256.Proofs.Verifying.Combination.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Projective

structure PointCallResult [Bindings] (s t u : RamState) (cursor point : BitVec 64)
    (boundary : ReturnBoundary) (ret : BitVec 64) (cells : Cells) : Prop extends Memory s u cursor point cells where
  execution : ∃ fuel, Advances boundary fuel t u
  rip : u.RIP = ret
  registers : ∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r

theorem finish_point_call [Bindings] {s t v u : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {cells : Cells} {value : Projective}
    {target : RamState → BitVec 64} {ret : BitVec 64} {reserve : Nat}
    (pre : TablePre s boundary cursor point) (state : Memory s t cursor point cells)
    (slot : Slot) (run : Advances boundary 1 t v) (ready : ReadyToStep v)
    (effect : (callEffect target ret t).Holds t v)
    (output : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 (offset slot))
    (result : CalleeResult v u boundary 96 reserve)
    (capacity : 1104 + reserve ≤ 2120)
    (valueAt : ProjectiveAt u (v.regValue .rdi) value) :
    PointCallResult s t u cursor point boundary ret (writeCell cells slot value) := by
  have sv := state.toFrameState.after_call pre ready effect
  have bounds := offset_bounds slot
  have stackBounds := P256.Proofs.Program.stack_bounds pre.stack
  have retV : (returnBoundary v).rip = ret := (callEffect_stack effect).1
  have work := stack_result_work_frame pre sv result output
    (by omega) bounds.1 (by omega)
  have cu : MemoryWriteFrame v u #v[registerRegion s .rdi 768, Stack.region s 2120] := by
    intro a ha
    apply work a
    intro region hr hin
    have he : region = workRegion s := by simpa using hr
    subst region
    apply ha (Stack.region s 2120) (by simp)
    change (stackPtr s).toNat - 2120 ≤ a.toNat ∧
      a.toNat < (stackPtr s).toNat - 2120 + 2088 at hin
    change (stackPtr s).toNat - 2120 ≤ a.toNat ∧
      a.toNat < (Stack.region s 2120).start + (Stack.region s 2120).size
    rw [P256.Proofs.Program.stack_region_end]
    constructor <;> omega
  have cv : MemoryWriteFrame t v #v[registerRegion s .rdi 768, Stack.region s 2120] := by
    intro a ha
    apply effect.agrees.memoryWriteFrame (call_writes pre state.toFrameState) a
    intro region hr hin
    have hr' : region = Stack.region s 2120 := by simpa using hr
    exact ha _ (by simp [hr']) hin
  refine ⟨state.update
    (sv.after_stack_result pre result output (by omega) bounds.1 (by omega))
    (output ▸ valueAt) ?_ (cursor_read_of_frame pre (memoryWriteFrame_trans cv cu)),
    ?_, result.rip.trans retV, ?_⟩
  · intro off len ho hl apart i hi
    exact (stack_result_byte pre sv result output (by omega) ho hl apart hi).trans
      (call_byte state.toFrameState effect ho hl hi)
  · obtain ⟨fuel, run'⟩ := result.execution
    exact ⟨1 + fuel, run.trans run'⟩
  · intro r hr
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)

theorem call_site [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point target : BitVec 64}
    (pre : TablePre s boundary cursor point) (state : FrameState s t cursor)
    (site : CallSite target) (targetProg : InProgram target)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.offset) :
    ∃ v, Advances boundary 1 t v ∧ ReadyToStep v ∧
      (callEffect (fun _ => target) site.returnRip t).Holds t v := by
  have low := P256.Proofs.Program.inProgram_low targetProg
  have step := direct_call pre state site.offset site.disp (Nat.le_of_lt site.bounded)
    site.bytes (by rw [site.target_eq]; exact low) (by rw [site.target_eq]; exact targetProg) rip
  simpa only [site.target_eq, CallSite.returnRip] using step

def addLayout : StackCallLayout 2120 96 96 920 :=
  ⟨1104, 320, 224, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem add_cells [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {cells : Cells} {left right : Projective}
    (pre : TablePre s boundary cursor point) (state : Memory s t cursor point cells)
    (site : CallSite 0x1051f0)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.offset)
    (dst : t.regValue .rdi = stackPtr s - 224)
    (src : t.regValue .rsi = stackPtr s - 320)
    (leftAt : ProjectiveAt t (stackPtr s - 224) left)
    (rightAt : ProjectiveAt t (stackPtr s - 320) right) :
    ∃ u, PointCallResult s t u cursor point boundary site.returnRip
      (writeCell cells 9 (left.add right)) := by
  obtain ⟨v, run, ready, effect⟩ := call_site pre state.toFrameState site
    (inProgram_of_textOffset 0x51f0 (by decide)) rip
  have sv := state.toFrameState.after_call pre ready effect
  have dstV : v.regValue .rdi = stackPtr s - 224 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans dst
  have srcV : v.regValue .rsi = stackPtr s - 320 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans src
  have cp := CalleePre.of_stack pre.toCalleePre addLayout sv.bindingsSupported sv.machine sv.directionFlag
    sv.loaded sv.allocated effect.rip sv.rsp srcV dstV (call_return_program site effect)
  have leftV : ProjectiveAt v (v.regValue .rdi) left := by
    rw [dstV]
    exact leftAt.of_bytes_eq (fun i hi => call_byte state.toFrameState effect (by decide) (by decide) hi)
  have rightV : ProjectiveAt v (v.regValue .rsi) right := by
    rw [srcV]
    exact rightAt.of_bytes_eq (fun i hi => call_byte state.toFrameState effect (by decide) (by decide) hi)
  obtain ⟨u, result, value⟩ := projective_add_correct cp leftV rightV
  exact ⟨u, finish_point_call pre state 9 run ready effect dstV result (by decide) value⟩

def doubleSite : CallSite 0x105d80 :=
  ⟨0xb040, 0xffffad3b, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem double_cells [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {cells : Cells} {value : Projective}
    (pre : TablePre s boundary cursor point) (state : Memory s t cursor point cells)
    (rip : t.RIP = 0x10b040) (dst : t.regValue .rdi = stackPtr s - 128)
    (input : ProjectiveAt t (stackPtr s - 128) value) :
    ∃ u, PointCallResult s t u cursor point boundary 0x10b045
      (writeCell cells 10 value.double) := by
  obtain ⟨v, run, ready, effect⟩ := call_site pre state.toFrameState doubleSite
    (inProgram_of_textOffset 0x5d80 (by decide)) rip
  have sv := state.toFrameState.after_call pre ready effect
  have dstV : v.regValue .rdi = stackPtr s - 128 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans dst
  have cp : CalleePre v boundary 0x105d80 0 96 1016 .rdi :=
    CalleePre.of_stack pre.toCalleePre
      (⟨1104, 128, 128, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩ : StackCallLayout 2120 0 96 1016)
      sv.bindingsSupported sv.machine sv.directionFlag sv.loaded sv.allocated
      effect.rip sv.rsp dstV dstV (call_return_program doubleSite effect)
  have inputV : ProjectiveAt v (v.regValue .rdi) value := by
    rw [dstV]
    exact input.of_bytes_eq (fun i hi => call_byte state.toFrameState effect (by decide) (by decide) hi)
  obtain ⟨u, result, value'⟩ := projective_double_correct cp inputV
  exact ⟨u, finish_point_call pre state 10 run ready effect dstV result (by decide) value'⟩

end P256.Proofs.Verifying.Combination.Table
