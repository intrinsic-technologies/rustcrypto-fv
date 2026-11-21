import Sha2.Proofs.Common.SHA256.Absorb.TraversalProof.Load

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Table

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

variable [Bindings] {l : Layout} {initial s : RamState} {n reserve index : Nat}
    {regions : Vector MemoryRegion n} {inputs : Array Input}

theorem iteration (ctx : Context l initial regions reserve)
    (state : ExecutionState initial s regions)
    (loop : LoopState l (l.chunk.sp initial) inputs index s)
    (data : InputData l (l.chunk.sp initial) inputs s)
    (separation : Separation l initial s reserve inputs)
    (count : CountAt l (l.chunk.sp initial) s)
    (copyIndex : ∀ call ∈ [l.chunk.smallCall, l.chunk.fillCall, l.chunk.tailCall], ∀ r,
      call.encoding = .register r → r ≠ l.index) :
    ∃ t, ExecutionState initial t regions ∧
      InputData l (l.chunk.sp initial) inputs t ∧ Separation l initial t reserve inputs ∧
      CountAt l (l.chunk.sp initial) t ∧
      MemoryWriteFrame s t (footprint l (l.chunk.sp initial)) ∧
      (∀ r : BitVec 5, r.toNat < 16 → r ∉ l.clobbered →
        (.reg r : Operand 64).read t = (.reg r : Operand 64).read s) ∧
      (LoopState l (l.chunk.sp initial) inputs (index + 1) t ∨
        (t.RIP = l.exit ∧ stackPtr t = l.chunk.sp initial ∧
          HasherAt t (l.stored (l.chunk.sp initial)) (message inputs) l.chunk.initialHash ∧
          l.count.read (l.chunk.sp initial) t = BitVec.ofNat 64 inputs.size)) := by
  obtain ⟨a, stateA, load, prepared⟩ := load_iteration ctx state loop data separation
  have memoryA : MemoryWriteFrame s a (footprint l (l.chunk.sp initial)) :=
    singleton_frame (by simp [footprint]) load.memory
  have dataA := data.of_frame ctx.wf ctx.stack state separation memoryA
  have separationA := separation.of_frame ctx.wf ctx.stack state memoryA
  have countA := count.of_frame ctx.wf ctx.stack memoryA
  obtain ⟨b, chunk⟩ := ctx.chunkCorrect ctx.wf.chunk ctx.flow ctx.chunkCode ctx.targets
    ctx.chunkBlocks ctx.stride ctx.machine ctx.stack ctx.avoids ctx.returnAddress stateA prepared
    (separation.inputApart ⟨index, loop.remaining⟩) ctx.chunk_within
  have memoryB := chunk_frame chunk.frame.memory
  have dataB := dataA.of_frame ctx.wf ctx.stack stateA separationA memoryB
  have separationB := separationA.of_frame ctx.wf ctx.stack stateA memoryB
  have countB := countA.of_frame ctx.wf ctx.stack memoryB
  have indexB : Blocks.readReg b l.index = BitVec.ofNat 64 index :=
    (chunk.frame.registers (l.index.setWidth 5) (by
      simp only [BitVec.toNat_setWidth]
      have bound := l.index.isLt
      omega) ctx.wf.indexPreserved).trans (load.index.trans loop.indexRegister)
  have countValue : l.count.read (l.chunk.sp initial) b = BitVec.ofNat 64 inputs.size :=
    (count_of_chunk ctx.wf ctx.stack countA chunk).trans (load.count.trans loop.count)
  let large : Bool := decide (64 - (Wrapper.prefixMessage inputs index).size % 64 ≤
    (inputs[index]'loop.remaining).bytes.size)
  have pre : NextPre l (l.chunk.sp initial) large b := {
    rip := by
      rw [chunk.rip]
      dsimp only [large]
      split <;> split <;> simp_all only [decide_eq_true_eq] <;> omega
    rsp := chunk.rsp
    countBound := by
      rw [countValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := data.sizeBound; omega)]
      exact data.sizeBound
    countRead := countB.readable
    workingPointer := by
      intro isLarge
      apply chunk.bufferRestored
      simpa only [large, decide_eq_true_eq] using isLarge
    remaining := by
      rw [indexB, countValue, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := data.sizeBound; have := loop.remaining; omega),
        Nat.mod_eq_of_lt (by have := data.sizeBound; omega)]
      exact loop.remaining
    active := ctx.readable chunk.state ctx.wf.chunk.bufferFits
    stored := ctx.writable chunk.state ctx.wf.storedFits (by decide)
    direction := chunk.state.directionFlag
    bufferRegister := by
      intro r hr
      exact (chunk.frame.registers (r.setWidth 5) (by
        simp only [BitVec.toNat_setWidth]
        have bound := r.isLt
        omega) (ctx.flow.bufferSaved r hr).1).trans (load.bufferRegister r hr)
    separate := clone_separate ctx.wf ctx.stack
    codeApart := by
      intro site member
      exact local_codeApart (site := site) ctx.wf ctx.stack
        (fun a ha hp => ctx.avoids a ha (.inl hp)) ctx.code chunk.state.loaded
        ctx.wf.storedFits (next_site_member member)
  }
  have code : CodeIn (((if large then l.nextLarge else l.nextSmall) ++ l.cloneOut).flatMap
      Blocks.Site.code) b :=
    ctx.code.sequence ((if large then l.nextLarge else l.nextSmall) ++ l.cloneOut)
      (fun _ member => next_site_member member) chunk.state.loaded
  obtain ⟨fuel, t, run, ready, _, post⟩ := ctx.blocks.advance _ large b
    (supportedMachine_readyToStep chunk.state.machine) code pre
  have memoryNext : MemoryWriteFrame b t (footprint l (l.chunk.sp initial)) :=
    singleton_frame (by simp [footprint]) post.memory
  have stateT := ctx.after_block chunk.state run ready post.agrees (by simp) memoryNext
  have hasher : HasherAt t (l.stored (l.chunk.sp initial))
      (Wrapper.prefixMessage inputs (index + 1)) l.chunk.initialHash := by
    rw [Wrapper.prefixMessage_succ inputs index loop.remaining]
    exact chunk.hasher.of_bytes post.copied
  have nextIndex : Blocks.readReg t l.index = BitVec.ofNat 64 (index + 1) := by
    rw [post.index, indexB, BitVec.ofNat_add]
    rfl
  have nextCount : l.count.read (l.chunk.sp initial) t = BitVec.ofNat 64 inputs.size := post.count.trans countValue
  have last : Blocks.readReg b l.index + 1 = l.count.read (l.chunk.sp initial) b ↔ index + 1 = inputs.size := by
    rw [indexB, countValue]
    constructor
    · intro same
      have numeric := congrArg BitVec.toNat same
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat] at numeric
      have bound := data.sizeBound
      have remaining := loop.remaining
      omega
    · intro same
      rw [← same, BitVec.ofNat_add]
      rfl
  refine ⟨t, stateT, dataB.of_frame ctx.wf ctx.stack chunk.state separationB memoryNext,
    separationB.of_frame ctx.wf ctx.stack chunk.state memoryNext, countB.of_frame ctx.wf ctx.stack memoryNext,
    memoryWriteFrame_trans memoryA (memoryWriteFrame_trans memoryB memoryNext), ?_, ?_⟩
  · intro r small kept
    have chunkKept : r ∉ l.chunk.clobbered := fun member => kept (ctx.wf.chunkClobbers r member)
    have indexKept : r ≠ l.index.setWidth 5 := fun same => kept (same ▸ ctx.wf.indexClobber)
    exact (post.registers r chunkKept indexKept).trans
      ((chunk.frame.registers r small chunkKept).trans (load.registers r chunkKept (by
        intro source member same
        exact kept (same ▸ ctx.wf.bufferSourceClobbers source member))))
  · by_cases done : index + 1 = inputs.size
    · right
      refine ⟨?_, post.rsp, ?_, nextCount⟩
      · rw [post.rip, ite_eq_left (last.mpr done)]
      · simpa only [done, Wrapper.prefixMessage_size] using hasher
    · left
      refine ⟨?_, post.rsp, hasher, nextIndex, nextCount,
        by have remaining := loop.remaining; omega, ?_, post.workingPointer, post.storedPointer, ?_⟩
      · rw [post.rip, ite_eq_right (fun same => done (last.mp same))]
      · intro _ r member
        have different : r.setWidth 5 ≠ l.index.setWidth 5 := by
          intro same
          apply ctx.wf.bufferSourceIndex r member
          apply BitVec.eq_of_toNat_eq
          have numeric := congrArg BitVec.toNat same
          simp only [BitVec.toNat_setWidth] at numeric
          have first := r.isLt
          have second := l.index.isLt
          omega
        exact (post.registers (r.setWidth 5) (ctx.flow.bufferSaved r member).1 different).trans
          (pre.bufferRegister r member)
      · intro call member r encoding
        have target := ctx.targets.copies call member
        rw [encoding] at target
        have different : r.setWidth 5 ≠ l.index.setWidth 5 := by
          intro same
          apply copyIndex call member r encoding
          apply BitVec.eq_of_toNat_eq
          have numeric := congrArg BitVec.toNat same
          simp only [BitVec.toNat_setWidth] at numeric
          have first := r.isLt
          have second := l.index.isLt
          omega
        exact (post.registers (r.setWidth 5) target.2 different).trans
          ((chunk.frame.registers (r.setWidth 5) (by
            simp only [BitVec.toNat_setWidth]
            have bound := r.isLt
            omega) target.2).trans (prepared.copyRegister call member r encoding))

end Sha2.Proofs.Common.SHA256.Absorb.Table
