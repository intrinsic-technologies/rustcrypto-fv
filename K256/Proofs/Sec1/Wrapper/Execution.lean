import K256.Proofs.Sec1.Parser.Memory
import K256.Proofs.Sec1.Wrapper.Contracts
import K256.Proofs.Sec1.Wrapper.Calls
import K256.Proofs.Sec1.Wrapper.Branches
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Sec1.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Sec1.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters

private theorem serializeSuccess {s : RamState} {bytes : ByteArray} {args : Vector Value 53} {mem : Ram}
    {point : Curve.Point} (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    (model : Secp256k1.decodePublicKey bytes = some point)
    (frame : CallerFrame s [stack s] args mem) (status : args[3] = ⟨64, 0⟩)
    (pointAt : Parser.PublicKeyAt mem (s.regValue .rsp - 104) point)
    (serialize : SerializerCall s) (copy : CopyCall s) :
    ∃ out, Run .l101df8 args mem out ∧ Post s bytes out := by
  let sp := s.regValue .rsp
  have write := stackWritable (offset := 256) (len := 8) call (by decide) (by decide) (by decide)
  have serInc := fun x hx => Common.fnCode_subset_programImage x (code_l101df8 x hx)
  have serGuard : StoreOk Extracted.programImage mem (sp - 256) 8 0x101e07 5 :=
    ParseSignature.storeOk_of_codeRange (off := 15) (write.of_frame frame.writes) serInc (by decide)
  have step := serialize_call_setup frame.rsp serGuard
  obtain ⟨ser, serRun, serRet, fs, bs, tag, hb⟩ := serialize args mem point frame status pointAt
  have rsp : Value.get 64 ser.values[4] = sp - 248 := by rw [fs.rsp]; rfl
  have addr : sp - 248 + 15 = sp - 233 := by bv_omega
  have rd : LoadOk ser.store (sp - 233) 1 := by
    have hr := ((stackWritable (offset := 233) (len := 1) call (by decide) (by decide)
      (by decide)).readable.of_frame fs.writes)
    exact ⟨hr.low, hr.present⟩
  have branch := serializerDispatch (code := Extracted.programImage) rsp (addr ▸ rd) (addr ▸ tag)
  let next := (((ser.values.set 0 ⟨64, mergeGPR 8 1 (Value.get 64 ser.values[0])⟩).set 1 ⟨64, 4⟩).set 2
    ⟨64, mergeGPR 8 3 (Value.get 64 ser.values[2])⟩).set 19 (.ofBool false)
  have fn : CallerFrame s [stack s] next ser.store := by
    apply fs.of_registers
    intro ⟨i, hi⟩ h
    change next[i] = ser.values[i]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [next, Vector.getElem_set] <;> rfl
  have nxtTag : Value.get 64 next[1] = 4 := by
    have eq : next[1] = ⟨64,4⟩ := by simp [next]
    rw [eq]; rfl
  have nxtBx : next[3] = ⟨64,0⟩ := by simpa [next, Vector.getElem_set] using bs
  have cpInc := fun x hx => Common.fnCode_subset_programImage x (code_l101e4c x hx)
  have cpGuard : StoreOk Extracted.programImage ser.store (sp - 256) 8 0x101e5c 6 :=
    ParseSignature.storeOk_of_codeRange (off := 16) (write.of_frame fs.writes) cpInc (by decide)
  have loaded := (Parser.inputs_of_stackFrame call fs.writes).2
  obtain ⟨lengthRead, lengthValue⟩ := memcpy_length_load loaded 4
  obtain ⟨targetRead, targetValue⟩ := memcpy_target_load loaded
  have cpStep := memcpy_call_setup 4 fn.rsp fn.dst nxtTag cpGuard lengthRead lengthValue targetRead targetValue
  obtain ⟨cp, cpRun, cpRet, fc, bc, hc⟩ := copy next ser.store _ fn nxtBx hb
  obtain ⟨out, ending, returned, eax, hmem⟩ :=
    finish (regions := #v[outputRegion publicKeyFromSec1Bytes s, stack s]) (status := 0) call fc (by rw [bc]; rfl)
  refine ⟨out, ?_, ?_⟩
  · apply ParseSignature.exec_call step serRun (by rw [serRet]; rfl)
    apply Program.Exec.next (next := ⟨⟨.l101e4c, next, ser.store⟩, []⟩)
    · exact congrArg (Transfer.next _ []) branch
    apply ParseSignature.exec_call cpStep cpRun (by rw [cpRet]; rfl)
    exact ending
  · unfold Post
    rw [model]
    exact ⟨returned, eax, hmem ▸ hc⟩

theorem execution {s : RamState} {bytes : ByteArray} (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    (parse : ParserCall s bytes) (serialize : SerializerCall s) (copy : CopyCall s) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨lifted.locationOf .l101dd0 s, []⟩ out ∧
      Post s bytes out := by
  let sp := s.regValue .rsp
  obtain ⟨p, run, ret, f, parsed⟩ := parse
  have rsp : Value.get 64 p.values[4] = sp - 248 := by rw [f.rsp]; rfl
  have addr : sp - 248 + 136 = sp - 112 := by bv_omega
  have rd : LoadOk p.store (sp - 112) 8 := by
    have hr := ((stackWritable (offset := 112) (len := 8) call (by decide) (by decide)
      (by decide)).readable.of_frame f.writes)
    exact ⟨hr.low, hr.present⟩
  have branch := parserDispatch (code := Extracted.programImage) rsp (addr ▸ rd)
  dsimp only at branch parsed
  rw [addr] at branch
  let tag := memLoad p.store (sp - 112) 64
  let next := (p.values.set 3 ⟨64, tag⟩).set 19 (.ofBool (tag == 1))
  have fn : CallerFrame s [stack s] next p.store := by
    apply f.of_registers
    intro ⟨i, hi⟩ h
    change next[i] = p.values[i]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [next, Vector.getElem_set] <;> rfl
  have bx : next[3] = ⟨64, tag⟩ := by simp [next]
  suffices cont : ∃ out, Run (if tag = 1 then .l101e62 else .l101df8) next p.store out ∧
      Post s bytes out by
    obtain ⟨out, after, post⟩ := cont
    refine ⟨out, ?_, post⟩
    apply ParseSignature.exec_call (entryBlock call) run (by rw [ret]; rfl)
    exact .next (congrArg (Transfer.next _ []) branch) after
  cases model : Secp256k1.decodePublicKey bytes with
  | none =>
    rw [model] at parsed
    have ht : tag = 1 := parsed
    rw [ite_eq_left ht]
    obtain ⟨out, he, returned, eax, _⟩ :=
      finish (regions := #v[stack s]) (status := 1) call fn (by rw [bx, ht]; rfl)
    refine ⟨out, he, ?_⟩
    unfold Post
    rw [model]
    exact ⟨returned, eax⟩
  | some point =>
    rw [model] at parsed
    have ht : tag = 0 := parsed.1
    rw [ite_eq_right (show tag ≠ 1 by rw [ht]; decide)]
    exact serializeSuccess call model fn (bx.trans (congrArg (fun x => (⟨64,x⟩ : Value)) ht))
      parsed.2 serialize copy

end K256.Proofs.Sec1.Wrapper
