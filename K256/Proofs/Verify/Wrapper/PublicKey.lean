import K256.Proofs.Verify.Transfer.PublicKey
import K256.Proofs.Verify.Choice
import K256.Proofs.Verify.Wrapper.Entry
import K256.Proofs.Verify.Wrapper.Child
import K256.Proofs.Sec1.Serialize.Layout

namespace K256.Proofs.Verify.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Standards.SECG.ECC

abbrev parserRegisters (s : RamState) : Vector Value 53 :=
  parserArgs (lifted.locationOf .l102fc0 s).arguments (stackPtr s) (s.regValue .rdi) (s.regValue .rsi)
    (s.regValue .rdx) (s.regValue .rcx)

abbrev parserActivation (s : RamState) :=
  childActivation s (parserMemory s) (parserRegisters s) 1544 0x102fe9

private theorem parserOperands (a : Vector Value 53) (sp key msg len sig : BitVec 64) :
    let regs := parserArgs a sp key msg len sig
    regs[6].get 64 = key ∧ regs[7].get 64 = sp - 528 ∧ regs[2].get 64 = 65 := by
  dsimp only
  simp only [parserArgs, Vector.getElem_set, ↓reduceIte]
  exact ⟨rfl, rfl, rfl⟩

private theorem parserChild {s : RamState} {key message sig : ByteArray}
    (call : ValidCall verifyingKeyVerify s [key,message,sig]) :
    ChildRegisters s (parserRegisters s) := by
  have df := call.directionFlagUnset
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  case refine_3 =>
    rintro ⟨i,hi⟩ hm
    change (parserRegisters s)[i].width = 64
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [parserRegisters,parserArgs,Vector.getElem_set,↓reduceIte,Lifted.locationOf,Vector.getElem_ofFn] <;> rfl
  all_goals simp only [parserRegisters,parserArgs,Vector.getElem_set,↓reduceIte,
    Lifted.locationOf,Vector.getElem_ofFn] <;> first | rfl | exact Reg.read_df_iff.mpr df

private theorem parseKeyAt {s : RamState} {key msg sig : ByteArray} {p : Curve.Point}
    (call : ValidCall verifyingKeyVerify s [key,msg,sig]) (decoded : Secp256k1.decodePublicKey key = some p)
    (fr : Activation) (a : Vector Value 53) (mem : Memory s fr.original)
    (atoms : Atom.All Extracted.programImage a fr.original (Fn106390.frameAt .l106390 fr))
    (si : fr.rsi = s.regValue .rdi) (di : fr.rdi = stackPtr s - 528) (len : fr.rdx = 65)
    (top : fr.rsp.toNat = (stackPtr s).toNat - 544) (bot : fr.low.toNat = (stackPtr s).toNat - 2088) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l106390, a, fr.original⟩, []⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn106390.doneAt fr) ∧
      Memory s out.store ∧ ParseSignature.ArgumentWidths out.values ∧ memLoad out.store (stackPtr s - 528) 64 = 0 ∧
      Ecdh.Decode.AffinePointAt out.store (stackPtr s - 528 + 8) p := by
  let src := registerRegion s .rdi 65
  have keyMem : ValidInput s src key := call.inputsInMemory.1
  obtain ⟨bytes, _, _, image⟩ := inputMemory call mem.frame
  have readable := Readable.of_hasBytes bytes keyMem.2.1
  have inputSize : key.size = 65 := bytes.1
  have rd : Readable fr.original fr.rsi 65 := by
    rw [si]
    rw [inputSize] at readable
    change Readable _ (BitVec.ofNat 64 (s.regValue .rdi).toNat) 65 at readable
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using readable
  have depth : 13000 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
  have dst : fr.rdi.toNat = (stackPtr s).toNat - 528 := by
    rw [di]
    exact Common.stackOffset (off := 528) call.stackAvailable (by decide)
  have sep : MemorySeparation [stack s] [src, registerRegion s .rsi msg.size, registerRegion s .rcx 64] :=
    call.separation
  have pos : 0 < (stack s).size := by
    change 0 < (stackPtr s).toNat + 8 - ((stackPtr s).toNat - 13000)
    omega
  have apart := apart_of_disjoint ((sep.2 _ List.mem_cons_self).2 _ List.mem_cons_self) pos (show 0 < 65 by decide)
  change (stackPtr s).toNat - 13000 + ((stackPtr s).toNat+8-((stackPtr s).toNat-13000)) ≤ (s.regValue .rdi).toNat ∨
    (s.regValue .rdi).toNat + 65 ≤ (stackPtr s).toNat - 13000 at apart
  have srcApart : Outside [ParseSignature.callStack fr] fr.rsi 65 := by
    refine ⟨by have := rd.low; omega, ?_⟩
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    change fr.rsi.toNat + 65 ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rsi.toNat
    rw [si]
    omega
  have window := Common.stackWritable (off := 13000) (len := 13000) call (by decide) (by decide) (by decide)
  have text := Sec1.Serialize.writable_text_apart window (by decide)
  have bottom := Common.stackOffset (off := 13000) call.stackAvailable (by decide)
  change (stackPtr s - 13000).toNat = (stackPtr s).toNat - 13000 at bottom
  change (stackPtr s - 13000).toNat + 13000 ≤ 0x100000 ∨ 0x12a9bf ≤ (stackPtr s - 13000).toNat at text
  have written := (Common.stackWritable (off := 528) (len := 96) call (by decide) (by decide) (by decide)).of_frame mem.frame
  obtain ⟨out, run, tag, done_, frame, widths, flag, affine⟩ :=
    Verify.Transfer.publicKeyExecution fr a atoms len rd srcApart (di ▸ written) (by omega)
      image (by omega) inputSize (by rw [si]; exact bytes) decoded
  refine ⟨out, run, tag, done_, mem.advance call frame ?_, widths, di ▸ flag, di ▸ affine⟩
  intro reg hr
  rcases List.mem_cons.mp hr with h | h
  · subst reg
    change _ ≤ fr.low.toNat ∧ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ _
    omega
  · obtain rfl := List.mem_singleton.mp h
    change (stackPtr s).toNat - 13000 ≤ fr.rdi.toNat ∧ fr.rdi.toNat + 96 ≤ (stackPtr s).toNat - 32
    omega


private theorem parserLayout (fr : Activation) :
    Fn106390.frameInfo.entryAtoms fr = Fn106390.frameAt .l106390 fr := rfl

private theorem parserCallSlots : Fn106390.frameInfo.CallSlotsIn Sec1.LIR.rodataSection := by decide +kernel

private theorem parserCallSpan : Fn106390.frameInfo.CallSlotSpanIn Sec1.LIR.rodataSection := by decide +kernel

private theorem parserAtoms {s : RamState} {key msg sig : ByteArray} {a : Vector Value 53} {m : Ram}
    (call : ValidCall verifyingKeyVerify s [key,msg,sig]) (mem : Memory s m) (regs : ChildRegisters s a)
    (ret : memLoad m (stackPtr s - 544) 64 = 0x102fe9) :
    Atom.All Extracted.programImage a m (Fn106390.frameAt .l106390 (childActivation s m a 1544 0x102fe9)) := by
  rw [← parserLayout]
  exact childEntry call mem regs Fn106390.frameInfo (room := 1544) (by decide) (by decide) (by decide)
    parserCallSlots parserCallSpan (by decide) ret

private theorem activationOperands (s : RamState) :
    (parserActivation s).rsi = s.regValue .rdi ∧
    (parserActivation s).rdi = stackPtr s - 528 ∧ (parserActivation s).rdx = 65 := by
  simp only [parserActivation, childActivation, parserRegisters]
  generalize (lifted.locationOf .l102fc0 s).arguments = a
  exact parserOperands a _ _ _ _ _

private theorem parseKey {s : RamState} {key msg sig : ByteArray} {p : Curve.Point}
    (call : ValidCall verifyingKeyVerify s [key,msg,sig]) (decoded : Secp256k1.decodePublicKey key = some p) :
    let fr := parserActivation s
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l106390, parserRegisters s, parserMemory s⟩, []⟩ out ∧
      out.tag = some ⟨64,0x102fe9⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn106390.doneAt fr) ∧
      Memory s out.store ∧ ParseSignature.ArgumentWidths out.values ∧ memLoad out.store (stackPtr s - 528) 64 = 0 ∧
      Ecdh.Decode.AffinePointAt out.store (stackPtr s - 528 + 8) p := by
  let fr := parserActivation s
  obtain ⟨mem, ret⟩ := parserMemory_state call
  have atoms := parserAtoms call mem (parserChild call) ret
  have vals := activationOperands s
  have top : fr.rsp.toNat = (stackPtr s).toNat - 544 :=
    Common.stackOffset (off := 544) call.stackAvailable (by decide)
  have bot : fr.low.toNat = (stackPtr s).toNat - 2088 :=
    Common.stackOffset (off := 2088) call.stackAvailable (by decide)
  have result := parseKeyAt (s := s) (key := key) (msg := msg) (sig := sig) (p := p)
    call decoded fr (parserRegisters s) mem atoms vals.1 vals.2.1 vals.2.2 top bot
  exact result

theorem keyPrefix {s : RamState} {key msg sig : ByteArray} {p : Curve.Point}
    (call : ValidCall verifyingKeyVerify s [key,msg,sig]) (decoded : Secp256k1.decodePublicKey key = some p) :
    ∃ a m, (program.sem (dialect Extracted.programImage)).Reaches ⟨lifted.locationOf .l102fc0 s, []⟩
        ⟨⟨.l102fe9, a, m⟩, []⟩ ∧
      Atom.All Extracted.programImage a m (Fn106390.doneAt (parserActivation s)) ∧
      Memory s m ∧ ParseSignature.ArgumentWidths a ∧ memLoad m (stackPtr s - 528) 64 = 0 ∧
      Ecdh.Decode.AffinePointAt m (stackPtr s - 528 + 8) p := by
  obtain ⟨out, run, tag, post⟩ := parseKey call decoded
  have reach := Verify.reachesOfCall (resume := .l102fe9) (entry call) run tag
  exact ⟨out.values, out.store, reach, post⟩

end K256.Proofs.Verify.Wrapper
