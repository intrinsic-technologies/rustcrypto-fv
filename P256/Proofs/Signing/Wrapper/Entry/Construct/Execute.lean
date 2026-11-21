import P256.Proofs.Signing.Wrapper.Entry.Construct.Memory
import P256.Proofs.Signing.Wrapper.Entry.Construct.Arguments
import P256.Proofs.Signing.Wrapper.Entry.Construct.Clear
import P256.Proofs.Signing.Wrapper.Entry.Construct.ClearCopy
import P256.Proofs.Signing.Wrapper.Entry.Construct.RepArguments
import P256.Proofs.Signing.Wrapper.Entry.Construct.FinalStore

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Construct

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem arguments [Bindings] {initial s : RamState} {secret message : ByteArray}
    (ctx : Context initial secret message) (state : State initial s 520)
    (rip : s.RIP=0x10263e) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ State initial t 520 ∧
      (Arguments.effect s).Holds s t := by
  obtain ⟨slices,call⟩ := ctx.call
  have outside := outer_boundary call ctx.machine ctx.bindingsSupported
  obtain ⟨fuel,t,run,ready,_,effect⟩ := Arguments.run _ outside s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x263e _
      (by decide) (by decide +kernel))
    ⟨rip,fun off h => readable ctx state h,
      fun off h => writable ctx state h (by decide),
      fun off co cl h hc => code_apart ctx state h hc⟩
  refine ⟨fuel,t,run,after ctx state run ready effect.agrees ?_ ?_ ?_,effect⟩
  · intro c hc a ha
    simp only [Arguments.effect,Effect.components,Write.component,Operand.component,
      List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact ha.elim
  · simp [Arguments.effect,Effect.components,Write.component,Operand.component]
  · simp [Arguments.effect,Effect.components,Write.component,Operand.component]

theorem clear [Bindings] {initial s : RamState} {secret message : ByteArray}
    (ctx : Context initial secret message) (state : State initial s 520)
    (rip : s.RIP=0x102677) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ State initial t 520 ∧
      (Clear.effect s).Holds s t := by
  obtain ⟨slices,call⟩ := ctx.call
  have outside := outer_boundary call ctx.machine ctx.bindingsSupported
  obtain ⟨fuel,t,run,ready,_,effect⟩ := Clear.run _ outside s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x2677 _
      (by decide) (by decide +kernel))
    ⟨rip,fun off h => readable ctx state h,
      fun off h => writable ctx state h (by decide),
      fun off co cl h hc => code_apart ctx state h hc⟩
  refine ⟨fuel,t,run,after ctx state run ready effect.agrees ?_ ?_ ?_,effect⟩
  · intro c hc a ha
    simp only [Clear.effect,Effect.components,Write.component,Operand.component,
      List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨workRegion initial,by simp,work ctx state (by decide) ha⟩
  · simp [Clear.effect,Effect.components,Write.component,Operand.component]
  · simp [Clear.effect,Effect.components,Write.component,Operand.component]

theorem clearcopy [Bindings] {initial s : RamState} {secret message : ByteArray}
    (ctx : Context initial secret message) (state : State initial s 520)
    (rip : s.RIP=0x1026ac) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ State initial t 520 ∧
      (ClearCopy.effect s).Holds s t := by
  obtain ⟨slices,call⟩ := ctx.call
  have outside := outer_boundary call ctx.machine ctx.bindingsSupported
  obtain ⟨fuel,t,run,ready,_,effect⟩ := ClearCopy.run _ outside s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x26ac _
      (by decide) (by decide +kernel))
    ⟨rip,fun off h => readable ctx state h,
      fun off h => writable ctx state h (by decide),
      fun off co cl h hc => code_apart ctx state h hc⟩
  refine ⟨fuel,t,run,after ctx state run ready effect.agrees ?_ ?_ ?_,effect⟩
  · intro c hc a ha
    simp only [ClearCopy.effect,Effect.components,Write.component,Operand.component,
      List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨workRegion initial,by simp,work ctx state (by decide) ha⟩
  · simp [ClearCopy.effect,Effect.components,Write.component,Operand.component]
  · simp [ClearCopy.effect,Effect.components,Write.component,Operand.component]

theorem reparguments [Bindings] {initial s : RamState} {secret message : ByteArray}
    (ctx : Context initial secret message) (state : State initial s 520)
    (rip : s.RIP=0x1026df) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ State initial t 520 ∧
      (RepArguments.effect s).Holds s t := by
  obtain ⟨slices,call⟩ := ctx.call
  have outside := outer_boundary call ctx.machine ctx.bindingsSupported
  obtain ⟨fuel,t,run,ready,_,effect⟩ := RepArguments.run _ outside s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x26df _
      (by decide) (by decide +kernel))
    ⟨rip,fun off h => readable ctx state h,
      fun off h => writable ctx state h (by decide),
      fun off co cl h hc => code_apart ctx state h hc⟩
  refine ⟨fuel,t,run,after ctx state run ready effect.agrees ?_ ?_ ?_,effect⟩
  · intro c hc a ha
    simp only [RepArguments.effect,Effect.components,Write.component,Operand.component,
      List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
  · simp [RepArguments.effect,Effect.components,Write.component,Operand.component]
  · simp [RepArguments.effect,Effect.components,Write.component,Operand.component]

theorem finalstore [Bindings] {initial s : RamState} {secret message : ByteArray}
    (ctx : Context initial secret message) (state : State initial s 520)
    (rip : s.RIP=0x1026f4) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ State initial t 520 ∧
      (FinalStore.effect s).Holds s t := by
  obtain ⟨slices,call⟩ := ctx.call
  have outside := outer_boundary call ctx.machine ctx.bindingsSupported
  obtain ⟨fuel,t,run,ready,_,effect⟩ := FinalStore.run _ outside s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x26f4 _
      (by decide) (by decide +kernel))
    ⟨rip,fun off h => readable ctx state h,
      fun off h => writable ctx state h (by decide),
      fun off co cl h hc => code_apart ctx state h hc⟩
  refine ⟨fuel,t,run,after ctx state run ready effect.agrees ?_ ?_ ?_,effect⟩
  · intro c hc a ha
    simp only [FinalStore.effect,Effect.components,Write.component,Operand.component,
      List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨workRegion initial,by simp,work ctx state (by decide) ha⟩
  · simp [FinalStore.effect,Effect.components,Write.component,Operand.component]
  · simp [FinalStore.effect,Effect.components,Write.component,Operand.component]

end P256.Proofs.Signing.Wrapper.Entry.Construct
