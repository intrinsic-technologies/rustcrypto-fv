import AesGcm.Proofs.Machine.Fixslice16.Operations
import AesGcm.Proofs.Machine.Fixslice.Memory
import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Core.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def tagMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp) (args[5].get 64)
  memStore mem (sp - 8) ((if use256 then 0x102b67 else 0x102707) : BitVec 64)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem tag_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 16)
    (hr : Readable mem (args[4].get 64 + 88) 32) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102b3e else .l1026de), args, mem⟩ = .call callee continuation ∧
      callee.label = (if use256 then .l101c20 else .l101800) ∧
      continuation.target = (if use256 then .l102b67 else .l102707) ∧
      continuation.guard = some ⟨64, (if use256 then 0x102b67 else 0x102707)⟩ ∧
      callee.store = tagMemory use256 args mem ∧
      (callee.arguments[0]'(by change 0 < 53; decide)).get 64 = args[0].get 64 ∧
      (callee.arguments[1]'(by change 1 < 53; decide)).get 64 = memLoad mem ((args[4].get 64) + 104) 64 ∧
      (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = (args[4].get 64) + 120 ∧
      (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = memLoad mem ((args[4].get 64) + 88) 64 ∧
      (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = (args[4].get 64) - 8 ∧
      (callee.arguments[5]'(by change 5 < 53; decide)).get 64 = args[5].get 64 ∧
      (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = memLoad mem ((args[4].get 64) + 96) 64 ∧
      (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = memLoad mem ((args[4].get 64) + 88) 64 + 1 ∧
      (callee.arguments[8]'(by change 8 < 53; decide)).get 64 = memLoad mem ((args[4].get 64) + 112) 64 ∧
      (callee.arguments[9]'(by change 9 < 53; decide)).get 64 = args[13].get 64 ∧
      (callee.arguments[10]'(by change 10 < 53; decide)).get 64 = args[10].get 64 ∧
      (callee.arguments[11]'(by change 11 < 53; decide)).get 64 = args[11].get 64 ∧
      (callee.arguments[12]'(by change 12 < 53; decide)).get 64 = args[12].get 64 ∧
      (callee.arguments[13]'(by change 13 < 53; decide)).get 64 = args[13].get 64 ∧
      (callee.arguments[14]'(by change 14 < 53; decide)).get 64 = args[14].get 64 ∧
      (callee.arguments[15]'(by change 15 < 53; decide)).get 64 = args[15].get 64 ∧
      callee.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      callee.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      callee.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      callee.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x102b3e else 0x1026de) 41 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1026de x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l102b3e x hx))).apart
  have hstackLow := hstack.readable.low
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
  all_goals
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l1026de, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l102b3e, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards call
      rfl
    all_goals first | rfl | (intro hTypes; runtime_typed) | runtime_finish [tagMemory]

def copyTailInMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp + 80) (args[13].get 64)
  memStore mem (sp - 8) ((if use256 then 0x102b02 else 0x1026a2) : BitVec 64)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem copyTailIn_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 96) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102ae3 else .l102683), args, mem⟩ = .call callee continuation ∧
      callee.label = .l103f00 ∧
      continuation.target = (if use256 then .l102b02 else .l1026a2) ∧
      continuation.guard = some ⟨64, (if use256 then 0x102b02 else 0x1026a2)⟩ ∧
      callee.store = copyTailInMemory use256 args mem ∧
      (callee.arguments[0]'(by change 0 < 53; decide)).get 64 = args[0].get 64 ∧
      (callee.arguments[1]'(by change 1 < 53; decide)).get 64 = args[1].get 64 ∧
      (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = args[14].get 64 ∧
      (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = 0x103f00 ∧
      (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = (args[4].get 64) - 8 ∧
      (callee.arguments[5]'(by change 5 < 53; decide)).get 64 = args[5].get 64 ∧
      (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = args[15].get 64 ∧
      (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = (args[4].get 64) + 136 ∧
      (callee.arguments[8]'(by change 8 < 53; decide)).get 64 = args[8].get 64 ∧
      (callee.arguments[9]'(by change 9 < 53; decide)).get 64 = args[9].get 64 ∧
      (callee.arguments[10]'(by change 10 < 53; decide)).get 64 = args[10].get 64 ∧
      (callee.arguments[11]'(by change 11 < 53; decide)).get 64 = args[11].get 64 ∧
      (callee.arguments[12]'(by change 12 < 53; decide)).get 64 = args[12].get 64 ∧
      (callee.arguments[13]'(by change 13 < 53; decide)).get 64 = (args[4].get 64) + 136 ∧
      (callee.arguments[14]'(by change 14 < 53; decide)).get 64 = args[14].get 64 ∧
      (callee.arguments[15]'(by change 15 < 53; decide)).get 64 = args[15].get 64 ∧
      callee.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      callee.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      callee.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      callee.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x102ae3 else 0x102683) 31 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l102683 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l102ae3 x hx))).apart
  have hstackLow := hstack.readable.low
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
  all_goals
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l102683, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l102ae3, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards call
      rfl
    all_goals first | rfl | (intro hTypes; runtime_typed) | runtime_finish [copyTailInMemory]

def cryptTailMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp + 16) (sp + 56)
  let mem := memStore mem (sp + 24) (args[13].get 64)
  let mem := memStore mem (sp + 32) (args[13].get 64)
  let mem := memStore mem (sp + 40) (1#64)
  memStore mem (sp - 8) ((if use256 then 0x102b2e else 0x1026ce) : BitVec 64)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem cryptTail_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 56) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102b02 else .l1026a2), args, mem⟩ = .call callee continuation ∧
      callee.label = (if use256 then .l1084e0 else .l107050) ∧
      continuation.target = (if use256 then .l102b2e else .l1026ce) ∧
      continuation.guard = some ⟨64, (if use256 then 0x102b2e else 0x1026ce)⟩ ∧
      callee.store = cryptTailMemory use256 args mem ∧
      (callee.arguments[0]'(by change 0 < 53; decide)).get 64 = (args[4].get 64) + 56 ∧
      (callee.arguments[1]'(by change 1 < 53; decide)).get 64 = args[1].get 64 ∧
      (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = args[2].get 64 ∧
      (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = args[3].get 64 ∧
      (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = (args[4].get 64) - 8 ∧
      (callee.arguments[5]'(by change 5 < 53; decide)).get 64 = args[5].get 64 ∧
      (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = (args[4].get 64) + 16 ∧
      (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = (args[4].get 64) + 48 ∧
      (callee.arguments[8]'(by change 8 < 53; decide)).get 64 = args[8].get 64 ∧
      (callee.arguments[9]'(by change 9 < 53; decide)).get 64 = args[9].get 64 ∧
      (callee.arguments[10]'(by change 10 < 53; decide)).get 64 = args[10].get 64 ∧
      (callee.arguments[11]'(by change 11 < 53; decide)).get 64 = args[11].get 64 ∧
      (callee.arguments[12]'(by change 12 < 53; decide)).get 64 = args[12].get 64 ∧
      (callee.arguments[13]'(by change 13 < 53; decide)).get 64 = args[13].get 64 ∧
      (callee.arguments[14]'(by change 14 < 53; decide)).get 64 = args[14].get 64 ∧
      (callee.arguments[15]'(by change 15 < 53; decide)).get 64 = args[15].get 64 ∧
      callee.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      callee.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      callee.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      callee.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x102b02 else 0x1026a2) 44 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1026a2 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l102b02 x hx))).apart
  have hstackLow := hstack.readable.low
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
  all_goals
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l1026a2, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l102b02, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards call
      rfl
    all_goals first | rfl | (intro hTypes; runtime_typed) | runtime_finish [cryptTailMemory]

def copyTailOutMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  memStore mem (sp - 8) ((if use256 then 0x102b3e else 0x1026de) : BitVec 64)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem copyTailOut_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 8)
    (hr : Readable mem (args[4].get 64 + 80) 8)
    (hcallee : args[3].get 64 = 0x103f00) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102b2e else .l1026ce), args, mem⟩ = .call callee continuation ∧
      callee.label = .l103f00 ∧
      continuation.target = (if use256 then .l102b3e else .l1026de) ∧
      continuation.guard = some ⟨64, (if use256 then 0x102b3e else 0x1026de)⟩ ∧
      callee.store = copyTailOutMemory use256 args mem ∧
      (callee.arguments[0]'(by change 0 < 53; decide)).get 64 = args[0].get 64 ∧
      (callee.arguments[1]'(by change 1 < 53; decide)).get 64 = args[1].get 64 ∧
      (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = args[14].get 64 ∧
      (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = args[3].get 64 ∧
      (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = (args[4].get 64) - 8 ∧
      (callee.arguments[5]'(by change 5 < 53; decide)).get 64 = args[5].get 64 ∧
      (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = args[13].get 64 ∧
      (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = args[12].get 64 ∧
      (callee.arguments[8]'(by change 8 < 53; decide)).get 64 = args[8].get 64 ∧
      (callee.arguments[9]'(by change 9 < 53; decide)).get 64 = args[9].get 64 ∧
      (callee.arguments[10]'(by change 10 < 53; decide)).get 64 = args[10].get 64 ∧
      (callee.arguments[11]'(by change 11 < 53; decide)).get 64 = args[11].get 64 ∧
      (callee.arguments[12]'(by change 12 < 53; decide)).get 64 = args[12].get 64 ∧
      (callee.arguments[13]'(by change 13 < 53; decide)).get 64 = memLoad mem ((args[4].get 64) + 80) 64 ∧
      (callee.arguments[14]'(by change 14 < 53; decide)).get 64 = args[14].get 64 ∧
      (callee.arguments[15]'(by change 15 < 53; decide)).get 64 = args[15].get 64 ∧
      callee.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      callee.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      callee.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      callee.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x102b2e else 0x1026ce) 16 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1026ce x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l102b2e x hx))).apart
  have hstackLow := hstack.readable.low
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
  all_goals
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l1026ce, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l102b2e, args, mem⟩ = _
      cfg_eval [hcallee]
      refine_norm [hcallee]
      runtime_guards call
      rfl
    all_goals first | rfl | (intro hTypes; runtime_typed) | runtime_finish [copyTailOutMemory, hcallee]

def cryptFullMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp + 16) (args[1].get 64)
  let mem := memStore mem (sp + 24) (args[15].get 64)
  let mem := memStore mem (sp + 32) (args[13].get 64)
  let mem := memStore mem (sp + 40) (args[5].get 64 >>> 4)
  memStore mem (sp - 8) ((if use256 then 0x102aa2 else 0x102642) : BitVec 64)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem cryptFull_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 56) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102a59 else .l1025f9), args, mem⟩ = .call callee continuation ∧
      callee.label = (if use256 then .l1084e0 else .l107050) ∧
      continuation.target = (if use256 then .l102aa2 else .l102642) ∧
      continuation.guard = some ⟨64, (if use256 then 0x102aa2 else 0x102642)⟩ ∧
      callee.store = cryptFullMemory use256 args mem ∧
      (callee.arguments[0]'(by change 0 < 53; decide)).get 64 = args[5].get 64 >>> 4 ∧
      (callee.arguments[1]'(by change 1 < 53; decide)).get 64 = args[1].get 64 ∧
      (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = args[2].get 64 ∧
      (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = args[15].get 64 + (0xffffffff0 &&& args[5].get 64) ∧
      (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = (args[4].get 64) - 8 ∧
      (callee.arguments[5]'(by change 5 < 53; decide)).get 64 = args[5].get 64 ∧
      (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = (args[4].get 64) + 16 ∧
      (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = (args[4].get 64) + 48 ∧
      (callee.arguments[8]'(by change 8 < 53; decide)).get 64 = args[8].get 64 ∧
      (callee.arguments[9]'(by change 9 < 53; decide)).get 64 = args[9].get 64 ∧
      (callee.arguments[10]'(by change 10 < 53; decide)).get 64 = args[10].get 64 ∧
      (callee.arguments[11]'(by change 11 < 53; decide)).get 64 = args[11].get 64 ∧
      (callee.arguments[12]'(by change 12 < 53; decide)).get 64 = (0xffffffff0 &&& args[5].get 64) + args[13].get 64 ∧
      (callee.arguments[13]'(by change 13 < 53; decide)).get 64 = args[13].get 64 ∧
      (callee.arguments[14]'(by change 14 < 53; decide)).get 64 = ((args[5].get 64).setWidth 32 &&& 15).setWidth 64 ∧
      (callee.arguments[15]'(by change 15 < 53; decide)).get 64 = args[15].get 64 ∧
      callee.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      callee.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      callee.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      callee.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x102a59 else 0x1025f9) 73 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1025f9 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l102a59 x hx))).apart
  have hstackLow := hstack.readable.low
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
  all_goals
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l1025f9, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l102a59, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards call
      rfl
    all_goals first | rfl | (intro hTypes; runtime_typed) | runtime_finish [cryptFullMemory]

def zeroTailMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  memStore mem (sp - 8) ((if use256 then 0x102ae3 else 0x102683) : BitVec 64)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem zeroTail_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 8)
    (hslotRead : Readable mem 0x201228 8)
    (hslot : memLoad mem 0x201228 64 = 0x103eb0) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102abe else .l10265e), args, mem⟩ = .call callee continuation ∧
      callee.label = .l103eb0 ∧
      continuation.target = (if use256 then .l102ae3 else .l102683) ∧
      continuation.guard = some ⟨64, (if use256 then 0x102ae3 else 0x102683)⟩ ∧
      callee.store = zeroTailMemory use256 args mem ∧
      (callee.arguments[0]'(by change 0 < 53; decide)).get 64 = 16 - args[14].get 64 ∧
      (callee.arguments[1]'(by change 1 < 53; decide)).get 64 = args[1].get 64 ∧
      (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = (if args[14].get 64 < 16 then 16 - args[14].get 64 else 0) ∧
      (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = args[3].get 64 ∧
      (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = (args[4].get 64) - 8 ∧
      (callee.arguments[5]'(by change 5 < 53; decide)).get 64 = args[5].get 64 ∧
      (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = 0 ∧
      (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = (args[4].get 64) + args[14].get 64 + 136 ∧
      (callee.arguments[8]'(by change 8 < 53; decide)).get 64 = args[8].get 64 ∧
      (callee.arguments[9]'(by change 9 < 53; decide)).get 64 = args[9].get 64 ∧
      (callee.arguments[10]'(by change 10 < 53; decide)).get 64 = args[10].get 64 ∧
      (callee.arguments[11]'(by change 11 < 53; decide)).get 64 = args[11].get 64 ∧
      (callee.arguments[12]'(by change 12 < 53; decide)).get 64 = args[12].get 64 ∧
      (callee.arguments[13]'(by change 13 < 53; decide)).get 64 = args[13].get 64 ∧
      (callee.arguments[14]'(by change 14 < 53; decide)).get 64 = args[14].get 64 ∧
      (callee.arguments[15]'(by change 15 < 53; decide)).get 64 = args[15].get 64 ∧
      callee.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      callee.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      callee.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      callee.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x102abe else 0x10265e) 37 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l10265e x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l102abe x hx))).apart
  have hstackLow := hstack.readable.low
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
  all_goals
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l10265e, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l102abe, args, mem⟩ = _
      cfg_eval [hslot]
      refine_norm [hslot]
      runtime_guards call
      rfl
    all_goals first | rfl | (intro hTypes; runtime_typed) | runtime_finish [zeroTailMemory, hslot]

def maskMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let original := mem
  let mem := memStore mem (sp + 88) (args[3].get 64)
  let mem := memStore mem (sp + 104) (args[1].get 64)
  let mem := memStore mem (sp + 112) (args[8].get 64)
  let mem := memStore mem (sp + 128) (0#64)
  let mem := memStore mem (sp + 120) (0#64)
  let mem := memStore mem (sp + 96) (args[6].get 64)
  let mem := memStore mem (sp + 16) (memLoad original (args[2].get 64) 32)
  let mem := memStore mem (sp + 20) (memLoad original (args[2].get 64 + 4) 32)
  let mem := memStore mem (sp + 24) (memLoad original (args[2].get 64 + 8) 32)
  let mem := memStore mem (sp + 28) (0x1000000#32)
  memStore mem (sp - 8) ((if use256 then 0x102a22 else 0x1025c2) : BitVec 64)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem mask_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 144)
    (hr : Readable mem (args[2].get 64) 12)
    (hroom : 8 ≤ (args[4].get 64).toNat)
    (hApart : (args[4].get 64 - 8).toNat + 144 ≤ (args[2].get 64).toNat ∨
      (args[2].get 64).toNat + 12 ≤ (args[4].get 64 - 8).toNat) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1029c0 else .l102560), args, mem⟩ = .call callee continuation ∧
      callee.label = (if use256 then .l106960 else .l105100) ∧
      continuation.target = (if use256 then .l102a22 else .l1025c2) ∧
      continuation.guard = some ⟨64, (if use256 then 0x102a22 else 0x1025c2)⟩ ∧
      callee.store = maskMemory use256 args mem ∧
      (callee.arguments[0]'(by change 0 < 53; decide)).get 64 = args[0].get 64 ∧
      (callee.arguments[1]'(by change 1 < 53; decide)).get 64 = args[1].get 64 ∧
      (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = (args[4].get 64) + 16 ∧
      (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = (memLoad mem (args[2].get 64 + 8) 32).setWidth 64 ∧
      (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = (args[4].get 64) - 8 ∧
      (callee.arguments[5]'(by change 5 < 53; decide)).get 64 = args[6].get 64 + 32 ∧
      (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = args[6].get 64 + 32 ∧
      (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = (args[4].get 64) + 120 ∧
      (callee.arguments[8]'(by change 8 < 53; decide)).get 64 = args[8].get 64 ∧
      (callee.arguments[9]'(by change 9 < 53; decide)).get 64 = args[9].get 64 ∧
      (callee.arguments[10]'(by change 10 < 53; decide)).get 64 = args[10].get 64 ∧
      (callee.arguments[11]'(by change 11 < 53; decide)).get 64 = args[11].get 64 ∧
      (callee.arguments[12]'(by change 12 < 53; decide)).get 64 = args[12].get 64 ∧
      (callee.arguments[13]'(by change 13 < 53; decide)).get 64 = (memLoad mem (args[2].get 64) 32).setWidth 64 ∧
      (callee.arguments[14]'(by change 14 < 53; decide)).get 64 = args[9].get 64 ∧
      (callee.arguments[15]'(by change 15 < 53; decide)).get 64 = (memLoad mem (args[2].get 64 + 4) 32).setWidth 64 ∧
      callee.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      callee.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      callee.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      callee.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  revert hstack hr hroom hApart
  refine args_cases (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 ↦ ?_) args
  clear args
  intro hstack hr hroom hApart
  let args : Values Value Reg.count := #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52]
  change Writable code mem (a4.get 64 - 8) 144 at hstack
  change Readable mem (a2.get 64) 12 at hr
  change 8 ≤ (a4.get 64).toNat at hroom
  change (a4.get 64 - 8).toNat + 144 ≤ (a2.get 64).toNat ∨
    (a2.get 64).toNat + 12 ≤ (a4.get 64 - 8).toNat at hApart
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x1029c0 else 0x102560) 98 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l102560 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1029c0 x hx))).apart
  have hstackLow := hstack.readable.low
  have hnonceLow := hr.low
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
  all_goals
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l102560, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l1029c0, args, mem⟩ = _
      cfg_eval []
      runtime_guards call
      rfl
    all_goals first
      | (intro hTypes; runtime_typed)
      | (simp only [maskMemory, Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero, List.getElem_cons_succ, Bool.false_eq_true, ↓reduceIte] <;>
         runtime_finish [])
  all_goals repeat first | (solve | runtime_finish []) | congr 1

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem maskMemory_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hroom : 8 ≤ (args[4].get 64).toNat)
    (hbound : (args[4].get 64).toNat + 136 ≤ 2^64) :
    RamWriteFrame mem (maskMemory use256 args mem) [span (args[4].get 64 - 8) 144] := by
  simp only [maskMemory]
  runtime_finish [span]

theorem cryptFullMemory_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hroom : 8 ≤ (args[4].get 64).toNat)
    (hbound : (args[4].get 64).toNat + 48 ≤ 2^64) :
    RamWriteFrame mem (cryptFullMemory use256 args mem) [span (args[4].get 64 - 8) 56] := by
  simp only [cryptFullMemory]
  runtime_finish [span]

theorem cryptTailMemory_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hroom : 8 ≤ (args[4].get 64).toNat)
    (hbound : (args[4].get 64).toNat + 48 ≤ 2^64) :
    RamWriteFrame mem (cryptTailMemory use256 args mem) [span (args[4].get 64 - 8) 56] := by
  simp only [cryptTailMemory]
  runtime_finish [span]

theorem tagMemory_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hroom : 8 ≤ (args[4].get 64).toNat)
    (hbound : (args[4].get 64).toNat + 8 ≤ 2^64) :
    RamWriteFrame mem (tagMemory use256 args mem) [span (args[4].get 64 - 8) 16] := by
  simp only [tagMemory]
  runtime_finish [span]

theorem copyTailInMemory_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hroom : 8 ≤ (args[4].get 64).toNat)
    (hbound : (args[4].get 64).toNat + 88 ≤ 2^64) :
    RamWriteFrame mem (copyTailInMemory use256 args mem) [span (args[4].get 64 - 8) 96] := by
  simp only [copyTailInMemory]
  runtime_finish [span]

theorem copyTailOutMemory_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hroom : 8 ≤ (args[4].get 64).toNat) :
    RamWriteFrame mem (copyTailOutMemory use256 args mem) [span (args[4].get 64 - 8) 8] := by
  simp only [copyTailOutMemory]
  runtime_finish [span]

theorem zeroTailMemory_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hroom : 8 ≤ (args[4].get 64).toNat) :
    RamWriteFrame mem (zeroTailMemory use256 args mem) [span (args[4].get 64 - 8) 8] := by
  simp only [zeroTailMemory]
  runtime_finish [span]

theorem maskMemory_loads (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) :
    memLoad (maskMemory use256 args mem) (args[4].get 64 - 8) 64 =
      (if use256 then 0x102a22 else 0x1025c2) ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 88) 64 = args[3].get 64 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 96) 64 = args[6].get 64 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 104) 64 = args[1].get 64 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 112) 64 = args[8].get 64 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 16) 32 =
      memLoad mem (args[2].get 64) 32 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 20) 32 =
      memLoad mem (args[2].get 64 + 4) 32 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 24) 32 =
      memLoad mem (args[2].get 64 + 8) 32 ∧
    memLoad (maskMemory use256 args mem) (args[4].get 64 + 28) 32 = 0x1000000 := by
  repeat' apply And.intro
  all_goals
    simp only [maskMemory]
    repeat first
      | rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
      | (rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          apply RangeApart.of_diff
          bv_omega)])
  all_goals rfl

set_option maxRecDepth 2048 in
theorem maskMemory_block (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (nonce : Vector UInt8 12)
    (hnonce : (span (args[2].get 64) 12).HasBytes mem ⟨nonce.toArray⟩) :
    Fixslice.memoryBlock (maskMemory use256 args mem) (args[4].get 64 + 16) =
      Fixslice16.fromStandard (nonce ++ #v[(0 : UInt8), 0, 0, 1]) := by
  obtain ⟨-, -, -, -, -, w0, w1, w2, w3⟩ := maskMemory_loads use256 args mem
  have words (k : Fin 3) :
      memLoad (maskMemory use256 args mem)
        (args[4].get 64 + 16 + BitVec.ofNat 64 (4 * k.val)) 32 =
      memLoad mem (args[2].get 64 + BitVec.ofNat 64 (4 * k.val)) 32 := by
    rcases k with ⟨k, hk⟩
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using w0
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using w1
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using w2
  have nonceByte (i : Fin 12) : memByte mem (args[2].get 64 + BitVec.ofNat 64 i.val) = nonce[i] := by
    have h := hnonce.2 ⟨i.val, by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt⟩
    change mem[BitVec.ofNat 64 ((args[2].get 64).toNat + i.val)]? = some nonce[i] at h
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    simp only [memByte, PhysicalMemory.read, h, Option.getD_some]
  have copied (i : Fin 12) :
      memByte (maskMemory use256 args mem) (args[4].get 64 + 16 + BitVec.ofNat 64 i.val) =
      nonce[i] := by
    have h := congrArg (fun w : BitVec 32 ↦ storedByte w (i.val % 4))
      (words ⟨i.val / 4, by omega⟩)
    rw [storedByte_memLoad _ _ _ (by omega), storedByte_memLoad _ _ _ (by omega)] at h
    have heq : 4 * (i.val / 4) + i.val % 4 = i.val := by omega
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add, heq] at h
    simpa only [BitVec.add_assoc] using h.trans (nonceByte i)
  have last (i : Fin 4) :
      memByte (maskMemory use256 args mem)
        (args[4].get 64 + 16 + BitVec.ofNat 64 (12 + i.val)) =
      (#v[0, 0, 0, 1] : Vector UInt8 4)[i] := by
    have h := congrArg (fun w : BitVec 32 ↦ storedByte w i.val) w3
    rw [storedByte_memLoad _ _ _ (by omega)] at h
    have hs : storedByte (0x1000000#32) i.val = (#v[0, 0, 0, 1] : Vector UInt8 4)[i] := by
      rcases i with ⟨i, hi⟩
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hcases with rfl | rfl | rfl | rfl
      · change storedByte (0x1000000#32) 0 = (0 : UInt8)
        decide +kernel
      · change storedByte (0x1000000#32) 1 = (0 : UInt8)
        decide +kernel
      · change storedByte (0x1000000#32) 2 = (0 : UInt8)
        decide +kernel
      · change storedByte (0x1000000#32) 3 = (1 : UInt8)
        decide +kernel
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      ← BitVec.add_assoc (16#64), BitVec.reduceAdd] using h.trans hs
  funext i
  apply congrArg UInt8.toBitVec
  change memByte (maskMemory use256 args mem) (args[4].get 64 + 16 + BitVec.ofNat 64 i.val) =
    (Vector.append nonce (#v[0, 0, 0, 1] : Vector UInt8 4))[i.val]
  by_cases hi : i.val < 12
  · exact (copied ⟨i.val, hi⟩).trans
      (Vector.getElem_append_left (xs := nonce) (ys := (#v[0, 0, 0, 1] : Vector UInt8 4)) hi).symm
  · have h := last ⟨i.val - 12, by omega⟩
    have hidx : 12 + (i.val - 12) = i.val := by omega
    simp only [hidx] at h
    exact h.trans
      (Vector.getElem_append_right (xs := nonce) (ys := (#v[0, 0, 0, 1] : Vector UInt8 4))
        i.isLt (by omega)).symm

end AesGcm.Proofs.Machine.Core.Encrypt
