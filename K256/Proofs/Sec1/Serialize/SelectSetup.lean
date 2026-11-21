import K256.Proofs.Sec1.Serialize.Select
import K256.Proofs.Common.Refine.Lemma.Region

set_option autoImplicit false

namespace K256.Proofs.Sec1.Serialize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

private theorem zeroFillStore {code : CodeMap} {sp offset : BitVec 64} {m t : Ram}
    {w off len : Nat}
    (hcode : ∀ x ∈ fnCode, x ∈ code)
    (stack : Writable code m (sp + 80) 65)
    (frame : RamWriteFrame m t [⟨(sp + 80).toNat, 65⟩])
    (inside : (offset - 80).toNat + w / 8 ≤ 65)
    (instruction : off + len ≤ bytes_l121831.length) :
    StoreOk code t (sp + offset) (w / 8) (0x121831 + BitVec.ofNat 64 off) len ∧
    RamWriteFrame m (memStore t (sp + offset) (0 : BitVec w)) [⟨(sp + 80).toNat, 65⟩] := by
  have access := (stack.of_frame frame).of_offsets (x := sp) (c := offset) (d := 80) rfl rfl inside
  refine ⟨ParseSignature.storeOk_of_codeRange access
    (fun x hx => hcode x (code_l121831 x hx)) instruction, frame.memStore _ ?_⟩
  refine ⟨_, List.mem_cons_self .., ?_⟩
  have addr := toNat_of_offsets (x := sp) (c := offset) (d := 80) rfl rfl stack.readable.low inside
  have low := stack.readable.low
  change (sp + 80).toNat ≤ (sp + offset).toNat ∧
    (sp + offset).toNat + w / 8 ≤ (sp + 80).toNat + 65 ∧
    (sp + offset).toNat + w / 8 ≤ 2 ^ 64
  rw [addr]
  omega

theorem selectionSetupBlock {code : CodeMap} {sp : BitVec 64}
    {a : Vector Value Reg.count} {m : Ram}
    (hcode : ∀ x ∈ fnCode, x ∈ code)
    (stack : Writable code m (sp + 80) 65) (rsp : a[4] = ⟨64, sp⟩) :
    ∃ (b : Vector Value Reg.count) (t : Ram),
      program.runBlock (dialect code) ⟨.l121831, a, m⟩ = .jump ⟨.l121890, b, t⟩ ∧
      b[2] = ⟨64, 0⟩ ∧ SelectionKeeps a b ∧
      RamWriteFrame m t [⟨(sp + 80).toNat, 65⟩] := by
  obtain ⟨h144, f144⟩ := zeroFillStore (offset := 144) (w := 8) (off := 0) (len := 8)
    hcode stack (RamWriteFrame.refl _ _) (by decide) (by decide)
  obtain ⟨h136, f136⟩ := zeroFillStore (offset := 136) (w := 64) (off := 8) (len := 12)
    hcode stack f144 (by decide) (by decide)
  obtain ⟨h128, f128⟩ := zeroFillStore (offset := 128) (w := 64) (off := 20) (len := 12)
    hcode stack f136 (by decide) (by decide)
  obtain ⟨h120, f120⟩ := zeroFillStore (offset := 120) (w := 64) (off := 32) (len := 9)
    hcode stack f128 (by decide) (by decide)
  obtain ⟨h112, f112⟩ := zeroFillStore (offset := 112) (w := 64) (off := 41) (len := 9)
    hcode stack f120 (by decide) (by decide)
  obtain ⟨h104, f104⟩ := zeroFillStore (offset := 104) (w := 64) (off := 50) (len := 9)
    hcode stack f112 (by decide) (by decide)
  obtain ⟨h96, f96⟩ := zeroFillStore (offset := 96) (w := 64) (off := 59) (len := 9)
    hcode stack f104 (by decide) (by decide)
  obtain ⟨h88, f88⟩ := zeroFillStore (offset := 88) (w := 64) (off := 68) (len := 9)
    hcode stack f96 (by decide) (by decide)
  obtain ⟨h80, f80⟩ := zeroFillStore (offset := 80) (w := 64) (off := 77) (len := 9)
    hcode stack f88 (by decide) (by decide)
  simp only [Nat.reduceDiv, BitVec.reduceAdd] at h144 h136 h128 h120 h112 h104 h96 h88 h80
  simp only [← BitVec.ofNat_eq_ofNat] at h144 h136 h128 h120 h112 h104 h96 h88 h80
  have rsp' : a[4].get 64 = sp := by rw [rsp, Value.get_mk]
  refine ⟨?_, ?_, ?eval, ?post⟩
  case eval =>
    cfg_eval
    rw [rsp', ite_eq_left h144, ite_eq_left h136, ite_eq_left h128, ite_eq_left h120,
      ite_eq_left h112, ite_eq_left h104, ite_eq_left h96, ite_eq_left h88, ite_eq_left h80]
  case post =>
    refine ⟨rfl, ?_, f80⟩
    intro ⟨r, _⟩ hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> rfl


theorem selectionFromSetup {code : CodeMap} {sp : BitVec 64} {a : Vector Value Reg.count}
    {m : Ram} {calls : List (StackFrame Value Label signature Reg.count)} {bytes : ByteArray}
    (hcode : ∀ x ∈ fnCode, x ∈ code)
    (stack : Writable code m (sp + 7) 273) (rsp : a[4] = ⟨64, sp⟩)
    (selector : a[0].get 8 = 0)
    (source : (⟨(sp + 215).toNat, 65⟩ : MemoryRegion).HasBytes m bytes) :
    ∃ (b : Vector Value Reg.count) (t : Ram),
      (program.sem (dialect code)).Reaches
        ⟨⟨.l121831, a, m⟩, calls⟩ ⟨⟨.l1218bb, b, t⟩, calls⟩ ∧
      b[2] = ⟨64, 65⟩ ∧ SelectionKeeps a b ∧
      RamWriteFrame m t (selectionWrites sp) ∧
      (⟨(sp + 80).toNat, 65⟩ : MemoryRegion).HasBytes t bytes := by
  have target : Writable code m (sp + 80) 65 :=
    stack.of_offsets (x := sp) (c := 80) (d := 7) rfl rfl (by decide)
  obtain ⟨mid, s, setup, index, keepSetup, setupFrame⟩ :=
    selectionSetupBlock hcode target rsp
  have rsp' : mid[4] = ⟨64, sp⟩ := (keepSetup 4 (by decide)).trans rsp
  have selector' : mid[0].get 8 = 0 :=
    (congrArg (Value.get 8) (keepSetup 0 (by decide))).trans selector
  obtain ⟨b, t, loop, doneIdx, keepLoop, loopFrame, copied⟩ :=
    selectionLoop (calls := calls) hcode (stack.of_frame setupFrame) rsp' index selector'
  have step : (program.sem (dialect code)).Step
      ⟨⟨.l121831, a, m⟩, calls⟩ ⟨⟨.l121890, mid, s⟩, calls⟩ := by
    change program.step (dialect code) ⟨⟨.l121831, a, m⟩, calls⟩ = _
    simp only [Program.step, setup, Transfer.next]
  have setupFrame' : RamWriteFrame m s (selectionWrites sp) :=
    ⟨fun x hx => setupFrame.outside x
      ⟨hx.1, fun r hr => hx.2 r (List.mem_cons_of_mem _ hr)⟩, setupFrame.present⟩
  have frame := setupFrame'.trans loopFrame fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨b, t, .step step loop, doneIdx, fun r hr => (keepLoop r hr).trans (keepSetup r hr),
    frame, source.1, ?_⟩
  intro i
  have hsize : bytes.size = 65 := source.1
  have hi : i.val < 65 := hsize ▸ i.isLt
  have shifted (k : Nat) :
      BitVec.ofNat 64 ((sp + BitVec.ofNat 64 k).toNat + i.val) =
        sp + BitVec.ofNat 64 (k + i.val) := by
    rw [ofNat_toNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
  have shiftedSrc : BitVec.ofNat 64 ((sp + 215).toNat + i.val) =
      sp + BitVec.ofNat 64 (215 + i.val) := shifted 215
  have shiftedDst : BitVec.ofNat 64 ((sp + 80).toNat + i.val) =
      sp + BitVec.ofNat 64 (80 + i.val) := shifted 80
  have srcNat : (sp + 215).toNat = (sp + 7).toNat + 208 :=
    toNat_of_offsets (x := sp) (c := 215) (d := 7) (n := 65)
      rfl rfl stack.readable.low (by decide)
  have dstNat : (sp + 80).toNat = (sp + 7).toNat + 73 :=
    toNat_of_offsets (x := sp) (c := 80) (d := 7) (n := 65)
      rfl rfl stack.readable.low (by decide)
  have byteNat : (sp + BitVec.ofNat 64 (215 + i.val)).toNat = (sp + 215).toNat + i.val := by
    rw [← shiftedSrc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    rw [srcNat]
    have := stack.readable.low
    omega
  have outside : Outside [⟨(sp + 80).toNat, 65⟩] (sp + BitVec.ofNat 64 (215 + i.val)) 1 := by
    refine ⟨?_, fun r hr => ?_⟩
    · rw [byteNat, srcNat]
      have := stack.readable.low
      omega
    · obtain rfl := List.mem_singleton.mp hr
      right
      change (sp + 80).toNat + 65 ≤ (sp + BitVec.ofNat 64 (215 + i.val)).toNat
      rw [byteNat, srcNat, dstNat]
      omega
  have contents := (copied i.val hi).trans (setupFrame.memLoad_eq outside)
  have byte := memByte_of_memLoad_eq contents 0 (by decide)
  simp only [BitVec.add_zero] at byte
  have sourceByte := source.2 i
  change m[BitVec.ofNat 64 ((sp + 215).toNat + i.val)]? = some bytes[i.val] at sourceByte
  rw [shiftedSrc] at sourceByte
  have allocated := (target.readable.of_frame frame).present i.val hi
  rw [← ofNat_toNat_add, shiftedDst] at allocated
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp allocated
  change t[BitVec.ofNat 64 ((sp + 80).toNat + i.val)]? = some bytes[i.val]
  rw [shiftedDst, hv]
  simp only [memByte, PhysicalMemory.read, hv, sourceByte, Option.getD_some] at byte
  rw [byte]

end K256.Proofs.Sec1.Serialize
