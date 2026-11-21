import AesGcm.Proofs.AES16.KeySchedule.Adjust.Schedule128
import AesGcm.Proofs.AES16.KeySchedule.Adjust.Schedule256
import AesGcm.Proofs.AES16.KeySchedule.Adjust.Memory
import AesGcm.Proofs.Machine.LIR.Fn104370.Frame
import AesGcm.Proofs.Machine.LIR.Fn1057c0.Frame

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option hygiene false in
local macro "adjust_proof " callee:ident evaluation:ident entry:num label:ident continuation:ident
    ret:num len:num cover:ident bytes:ident schedule:ident : tactic => do
  let calleeSimp ← `(Lean.Parser.Tactic.simpLemma| $callee:ident)
  `(tactic| (
    have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n $entry $len := by
      have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x ($cover x hx))
      have hl : ($bytes:ident).length = $len := by decide +kernel
      rw [hl] at hx
      exact hx.apart
    runtime_context [hsp, hdst, hslot]
    refine ⟨$callee code args mem,
      {target := $continuation, kept := #v[], arity := rfl, guard := some ⟨64, $ret⟩},
      ?exec, ?fields⟩
    case exec =>
      change LIR.program.runBlock (dialect code) ⟨$label, args, mem⟩ = _
      rw [$evaluation:ident]
      simp (config := { zeta := false }) only [$calleeSimp]
      extract_lets
      runtime_guards call
      runtime_guards call
      rfl
    case fields =>
      refine ⟨rfl, rfl, rfl, ?rsp, ?dst, ?src, rfl, ?dst2,
        rfl, rfl, rfl, rfl, ?typed, ?ret, ?frame, ?schedule⟩
      case schedule => exact $schedule code args mem sp planes hsp hwords
      all_goals simp (config := { zeta := false }) only [$calleeSimp]
      all_goals extract_lets
      case typed =>
        simp only [adjust_call_rsp]
        runtime_typed
      case frame =>
        simp only [span]
        runtime_local_frame
      all_goals runtime_local_memory_norm [hsp, hdst, adjust_call_rsp]
  ))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem adjust128_memcpy_call (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (sp dst : BitVec 64) (planes : Fin ((variant false).Nr + 1) → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp) (_hTypes : GPRsTyped args)
    (hstack : Writable code mem (sp - 8) (if false then 320 else 208))
    (_hroom : 8 ≤ sp.toNat)
    (hdst : memLoad mem (sp + (if false then 304 else 192)) 64 = dst)
    (hslotRead : Readable mem 0x201208 8)
    (hslot : memLoad mem 0x201208 64 = 0x103f00)
    (hslotApart : RangeApart (sp - 8) (if false then 320 else 208) 0x201208 8)
    (hwords : ∀ (r : Fin ((variant false).Nr + 1)) (p : Fin 8),
      memLoad mem (sp + (if false then 12 else 8) +
        BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if false then .l10593a else .l10446f), args, mem⟩ = .call callee continuation ∧
      callee.label = .l103f00 ∧
      continuation.target = (if false then .l10693d else .l1050df) ∧
      continuation.guard = some ⟨64, if false then 0x10693d else 0x1050df⟩ ∧
      (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 ∧
      (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = dst ∧
      (callee.arguments[6]'(by change 6 < 53; decide)).get 64 =
        sp + (if false then 12 else 8) ∧
      (callee.arguments[2]'(by change 2 < 53; decide)).get 64 =
        (if false then 240 else 176) ∧
      (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = dst ∧
      callee.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      callee.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      callee.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      callee.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      GPRsTyped callee.arguments ∧
      memLoad callee.store (sp - 8) 64 = (if false then 0x10693d else 0x1050df) ∧
      RamWriteFrame mem callee.store
        [span (sp - 8) 8, span (sp + (if false then 12 else 8))
          (if false then 276 else 184)] ∧
      (∀ (r : Fin ((variant false).Nr + 1)) (p : Fin 8),
        memLoad callee.store (sp + (if false then 12 else 8) +
          BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 =
          adjustKey (variant false) r.val (planes r) p) := by
  have hstackRead := hstack.readable
  have hstackLow := hstackRead.low
  have hslotSep := adjust_rangeApart_bounds
    (by decide : 0 < (if false then 320 else 208)) (by decide : 0 < 8) hslotApart
  simp only [BitVec.reduceToNat] at hslotSep
  simp only [Bool.false_eq_true, ↓reduceIte] at hstack hstackRead hstackLow hdst
  simp only [Bool.false_eq_true, ↓reduceIte] at hslotSep hwords ⊢
  adjust_proof adjust128_callee adjust128_eval 0x10446f LIR.Label.l10446f LIR.Label.l1050df 0x1050df
    3184 LIR.code_l10446f LIR.bytes_l10446f adjust128_schedule

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem adjust256_memcpy_call (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (sp dst : BitVec 64) (planes : Fin ((variant true).Nr + 1) → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp) (_hTypes : GPRsTyped args)
    (hstack : Writable code mem (sp - 8) (if true then 320 else 208))
    (_hroom : 8 ≤ sp.toNat)
    (hdst : memLoad mem (sp + (if true then 304 else 192)) 64 = dst)
    (hslotRead : Readable mem 0x201208 8)
    (hslot : memLoad mem 0x201208 64 = 0x103f00)
    (hslotApart : RangeApart (sp - 8) (if true then 320 else 208) 0x201208 8)
    (hwords : ∀ (r : Fin ((variant true).Nr + 1)) (p : Fin 8),
      memLoad mem (sp + (if true then 12 else 8) +
        BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if true then .l10593a else .l10446f), args, mem⟩ = .call callee continuation ∧
      callee.label = .l103f00 ∧
      continuation.target = (if true then .l10693d else .l1050df) ∧
      continuation.guard = some ⟨64, if true then 0x10693d else 0x1050df⟩ ∧
      (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 ∧
      (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = dst ∧
      (callee.arguments[6]'(by change 6 < 53; decide)).get 64 =
        sp + (if true then 12 else 8) ∧
      (callee.arguments[2]'(by change 2 < 53; decide)).get 64 =
        (if true then 240 else 176) ∧
      (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = dst ∧
      callee.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      callee.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      callee.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      callee.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      GPRsTyped callee.arguments ∧
      memLoad callee.store (sp - 8) 64 = (if true then 0x10693d else 0x1050df) ∧
      RamWriteFrame mem callee.store
        [span (sp - 8) 8, span (sp + (if true then 12 else 8))
          (if true then 276 else 184)] ∧
      (∀ (r : Fin ((variant true).Nr + 1)) (p : Fin 8),
        memLoad callee.store (sp + (if true then 12 else 8) +
          BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 =
          adjustKey (variant true) r.val (planes r) p) := by
  have hstackRead := hstack.readable
  have hstackLow := hstackRead.low
  have hslotSep := adjust_rangeApart_bounds
    (by decide : 0 < (if true then 320 else 208)) (by decide : 0 < 8) hslotApart
  simp only [BitVec.reduceToNat] at hslotSep
  simp only [↓reduceIte] at hstack hstackRead hstackLow hdst
  simp only [↓reduceIte] at hslotSep hwords ⊢
  adjust_proof adjust256_callee adjust256_eval 0x10593a LIR.Label.l10593a LIR.Label.l10693d 0x10693d
    4099 LIR.code_l10593a LIR.bytes_l10593a adjust256_schedule

theorem adjust_memcpy_call (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (sp dst : BitVec 64) (planes : Fin ((variant use256).Nr + 1) → Fixslice16.Planes16)
    (hsp : args[4].get 64 = sp) (hTypes : GPRsTyped args)
    (hstack : Writable code mem (sp - 8) (if use256 then 320 else 208))
    (hroom : 8 ≤ sp.toNat)
    (hdst : memLoad mem (sp + (if use256 then 304 else 192)) 64 = dst)
    (hslotRead : Readable mem 0x201208 8)
    (hslot : memLoad mem 0x201208 64 = 0x103f00)
    (hslotApart : RangeApart (sp - 8) (if use256 then 320 else 208) 0x201208 8)
    (hwords : ∀ (r : Fin ((variant use256).Nr + 1)) (p : Fin 8),
      memLoad mem (sp + (if use256 then 12 else 8) +
        BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = planes r p) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l10593a else .l10446f), args, mem⟩ = .call callee continuation ∧
      callee.label = .l103f00 ∧
      continuation.target = (if use256 then .l10693d else .l1050df) ∧
      continuation.guard = some ⟨64, if use256 then 0x10693d else 0x1050df⟩ ∧
      (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 ∧
      (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = dst ∧
      (callee.arguments[6]'(by change 6 < 53; decide)).get 64 =
        sp + (if use256 then 12 else 8) ∧
      (callee.arguments[2]'(by change 2 < 53; decide)).get 64 =
        (if use256 then 240 else 176) ∧
      (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = dst ∧
      callee.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      callee.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      callee.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      callee.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      GPRsTyped callee.arguments ∧
      memLoad callee.store (sp - 8) 64 = (if use256 then 0x10693d else 0x1050df) ∧
      RamWriteFrame mem callee.store
        [span (sp - 8) 8, span (sp + (if use256 then 12 else 8))
          (if use256 then 276 else 184)] ∧
      (∀ (r : Fin ((variant use256).Nr + 1)) (p : Fin 8),
        memLoad callee.store (sp + (if use256 then 12 else 8) +
          BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 =
          adjustKey (variant use256) r.val (planes r) p) := by
  cases use256
  · exact adjust128_memcpy_call code hcode args mem sp dst planes hsp hTypes hstack hroom
      hdst hslotRead hslot hslotApart hwords
  · exact adjust256_memcpy_call code hcode args mem sp dst planes hsp hTypes hstack hroom
      hdst hslotRead hslot hslotApart hwords

end AesGcm.Proofs.Machine.AES16.KeySchedule
