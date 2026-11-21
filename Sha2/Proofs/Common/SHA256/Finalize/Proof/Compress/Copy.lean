import Sha2.Proofs.Common.SHA256.Finalize.Proof.Compress.Memory
import Sha2.Proofs.Wrapper.Hash.Finalize.Compress.Lower

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize.Compress

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem first [Bindings] {L : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {chunk : ByteArray} {hash : Array UInt32}
    (ctx : Context L initial regions reserve) (input : HashAt L initial before s regions hash)
    (rip : s.RIP = L.firstHead)
    (bytes : (⟨(L.buffer (L.sp initial)).toNat,64⟩ : MemoryRegion).HasBytes s.external chunk) :
    ∃ t, HashAt L initial before t regions hash ∧ t.RIP = L.firstLower ∧
      (⟨(L.buffer (L.sp initial)).toNat,64⟩ : MemoryRegion).HasBytes t.external chunk ∧
      memLoad t.external (L.scratch (L.sp initial)+56) 64 =
        memLoad t.external (L.buffer (L.sp initial)+56) 64 ∧
      AgreesExcept [.reg 0,.mem (L.sp initial+BitVec.ofNat 64 (L.variant.scratch+56)) 8,.rip] s t := by
  have pre : FirstHead.Pre L.firstHead L.variant s := by
    refine ⟨rip, ?_, ?_, ?_⟩
    all_goals rw [show rspOf s = L.sp initial from input.rsp]
    · exact ctx.readable input.state (by have := ctx.wf.bufferFits; omega)
    · exact ctx.writable input.state (by have := ctx.wf.scratchFits; omega) (by decide)
    · exact ctx.codeApart (by have := ctx.wf.scratchFits; omega) (ctx.code.inside .firstHead)
  obtain ⟨_,t,run,ready,_,effect⟩ := ctx.blocks.firstHead s
    (supportedMachine_readyToStep input.state.machine) (ctx.code.loaded .firstHead s input.state.loaded) pre
  have frame : AgreesExcept [.reg 0,.mem (L.sp initial+BitVec.ofNat 64 (L.variant.scratch+56)) 8,.rip] s t := by
    simpa only [FirstHead.effect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      show rspOf s = L.sp initial from input.rsp] using effect.agrees
  have writes : ∀ c ∈ [Component.reg (0#5),.mem (L.sp initial+BitVec.ofNat 64 (L.variant.scratch+56)) 8,.rip],
      ∀ a, c.Covers a → (Component.mem (L.scratch (L.sp initial)) 64).Covers a := by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · exact scratch_cover (by decide) ha
    · exact ha.elim
  have state := preserve ctx input run ready frame (fun c hc a ha => .inr (writes c hc a ha))
    (by intro r h0 h1; simp only [BitVec.ofNat_eq_ofNat] at h0; simp [h0]) (by simp)
  have kept := scratch_keeps_buffer frame writes
  refine ⟨t,state,effect.rip.trans ctx.flow.firstHead,⟨bytes.1,?_⟩,?_,frame⟩
  · intro i
    have h := kept i.val (by have size : chunk.size = 64 := bytes.1; omega)
    simpa only [Layout.buffer,Layout.scratch,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using h.trans (by
      simpa only [Layout.buffer,Layout.scratch,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using bytes.2 i)
  · have word := effect.writes.2
    change memLoad t.external (rspOf s + BitVec.ofNat 64 (L.variant.scratch+56)) 64 =
      memLoad s.external (rspOf s + BitVec.ofNat 64 (L.variant.buffer.value+56)) 64 at word
    have normalized : memLoad t.external (L.scratch (L.sp initial)+56) 64 =
        memLoad s.external (L.buffer (L.sp initial)+56) 64 := by
      simpa only [Layout.scratch,Layout.buffer,show rspOf s = L.sp initial from input.rsp,
        BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using word
    apply normalized.trans
    symm
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    simpa only [PhysicalMemory.read,BitVec.add_assoc,← BitVec.ofNat_add,BitVec.ofNat_eq_ofNat] using
      kept (56+i) (by omega)

theorem lower_frame {L : Layout} {sp p : BitVec 64} {s t : RamState}
    (rsp : stackPtr s = sp) (effect : (Lower.effect p L.variant s).Holds s t) :
    AgreesExcept [.reg 0,.reg 1,.mem (L.scratch sp) 56,.rip] s t := by
  apply Common.Encoding.Serialize.agrees_of_footprint effect.agrees
  · intro c hc hm
    simp only [Lower.effect,Effect.components,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
      Write.component,Operand.component,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem]
  · intro c hc a ha
    simp only [Lower.effect,Effect.components,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
      Write.component,Operand.component,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨.mem (L.scratch sp) 56,by simp,?_⟩
    all_goals obtain ⟨i,hi,rfl⟩ := ha
    all_goals change rspOf s = sp at rsp
    · exact ⟨48+i,by omega,by simp only [Layout.scratch,rsp,BitVec.ofNat_add,BitVec.add_assoc]⟩
    · exact ⟨40+i,by omega,by simp only [Layout.scratch,rsp,BitVec.ofNat_add,BitVec.add_assoc]⟩
    · exact ⟨32+i,by omega,by simp only [Layout.scratch,rsp,BitVec.ofNat_add,BitVec.add_assoc]⟩
    · exact ⟨24+i,by omega,by simp only [Layout.scratch,rsp,BitVec.ofNat_add,BitVec.add_assoc]⟩
    · exact ⟨16+i,by omega,by simp only [Layout.scratch,rsp,BitVec.ofNat_add,BitVec.add_assoc]⟩
    · exact ⟨8+i,by omega,by simp only [Layout.scratch,rsp,BitVec.ofNat_add,BitVec.add_assoc]⟩
    · exact ⟨i,by omega,by simp only [Layout.scratch,rsp,Nat.add_zero]⟩

theorem lower_words {L : Layout} {sp p : BitVec 64} {s t : RamState}
    (rsp : stackPtr s = sp) (effect : (Lower.effect p L.variant s).Holds s t) :
    ∀ j < 7, memLoad t.external (L.scratch sp+BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (L.buffer sp+BitVec.ofNat 64 (8*j)) 64 := by
  have stores := effect.writes
  simp only [Lower.effect,List.map_cons,List.map_nil,List.cons_append,List.nil_append,Write.AllHold] at stores
  obtain ⟨_,_,w48,w40,w32,w24,w16,w8,w0⟩ := stores
  intro j hj
  rcases (by omega : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals change rspOf s = sp at rsp
  all_goals simp only [Layout.scratch,Layout.buffer,BitVec.add_assoc,Nat.reduceMul,BitVec.add_zero]
  · simpa only [Operand.read,rsp,Nat.add_zero] using w0
  · simpa only [Operand.read,rsp,BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w8
  · simpa only [Operand.read,rsp,BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w16
  · simpa only [Operand.read,rsp,BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w24
  · simpa only [Operand.read,rsp,BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w32
  · simpa only [Operand.read,rsp,BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w40
  · simpa only [Operand.read,rsp,BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w48

theorem lower [Bindings] (last : Bool) {L : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {chunk : ByteArray} {hash : Array UInt32}
    (ctx : Context L initial regions reserve) (input : HashAt L initial before s regions hash)
    (rip : s.RIP = if last then L.lastLower else L.firstLower)
    (bytes : (⟨(L.buffer (L.sp initial)).toNat,64⟩ : MemoryRegion).HasBytes s.external chunk)
    (high : memLoad s.external (L.scratch (L.sp initial)+56) 64 =
      memLoad s.external (L.buffer (L.sp initial)+56) 64) :
    ∃ t, HashAt L initial before t regions hash ∧ t.RIP = (if last then L.lastSetup else L.firstSetup) ∧
      (⟨(L.scratch (L.sp initial)).toNat,64⟩ : MemoryRegion).HasBytes t.external chunk ∧
      AgreesExcept [.reg 0,.reg 1,.mem (L.scratch (L.sp initial)) 56,.rip] s t := by
  let p := if last then L.lastLower else L.firstLower
  have inside : BlockInProgram p (Lower.bytes L.variant).length := by
    cases last
    · exact ctx.code.inside .firstLower
    · exact ctx.code.inside .lastLower
  have pre : Lower.Pre p L.variant s := by
    refine ⟨rip,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · have apart : OffsetsApart (BitVec.ofNat 64 L.variant.buffer.value) 56
          (BitVec.ofNat 64 L.variant.scratch) 56 := by
        cases L.variant <;> unfold OffsetsApart <;> decide +kernel
      intro i hi j hj eq
      exact apart.ne (rspOf s) hi hj (by decide) eq
    all_goals rw [show rspOf s = L.sp initial from input.rsp]
    all_goals first
      | exact ctx.readable input.state (by have := ctx.wf.bufferFits; omega)
      | exact ctx.writable input.state (by have := ctx.wf.scratchFits; omega) (by decide)
      | exact ctx.codeApart (by have := ctx.wf.scratchFits; omega) inside
  obtain ⟨_,t,run,ready,_,effect⟩ := ctx.blocks.lower p inside s
    (supportedMachine_readyToStep input.state.machine) (by
      cases last
      · exact ctx.code.loaded .firstLower s input.state.loaded
      · exact ctx.code.loaded .lastLower s input.state.loaded) pre
  have frame := lower_frame input.rsp effect
  have writes : Writes L (L.sp initial) [.reg 0,.reg 1,.mem (L.scratch (L.sp initial)) 56,.rip] := by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨i,hi,he⟩ := ha
    exact .inr ⟨i,by omega,he⟩
  have state := preserve ctx input run ready frame writes
    (by intro r h0 h1; simp only [BitVec.ofNat_eq_ofNat] at h0 h1; simp [h0,h1]) (by simp)
  have top : memLoad t.external (L.scratch (L.sp initial)+56) 64 =
      memLoad s.external (L.buffer (L.sp initial)+56) 64 := by
    rw [← high]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    apply frame.byte
    intro c hc ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨j,hj,he⟩ := ha
    have apart : OffsetsApart (0#64) 56 (56#64) 8 := by unfold OffsetsApart; decide +kernel
    apply apart.ne (L.scratch (L.sp initial)) hj hi (by decide)
    simpa only [BitVec.add_zero,PhysicalMemory.read,BitVec.ofNat_eq_ofNat] using he.symm
  have words : ∀ j < 8, memLoad t.external (L.scratch (L.sp initial)+BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (L.buffer (L.sp initial)+BitVec.ofNat 64 (8*j)) 64 := by
    intro j hj
    by_cases low : j < 7
    · exact lower_words input.rsp effect j low
    · have eq : j=7 := by omega
      subst j
      exact top
  have copied := Sha2.Proofs.Wrapper.Hash.Finalize.Compress.block_bytes_of_words
    (ctx.readable input.state (by have := ctx.wf.bufferFits; omega))
    (ctx.readable state.state ctx.wf.scratchFits) words
  refine ⟨t,state,?_,⟨bytes.1,?_⟩,frame⟩
  · have h := effect.rip
    cases last
    · exact h.trans ctx.flow.firstLower
    · exact h.trans ctx.flow.lastLower
  · intro i
    have h := copied i.val (by have size : chunk.size = 64 := bytes.1; omega)
    simpa only [Layout.buffer,Layout.scratch,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using h.trans (by
      simpa only [Layout.buffer,Layout.scratch,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using bytes.2 i)

end Sha2.Proofs.Common.SHA256.Finalize.Compress
