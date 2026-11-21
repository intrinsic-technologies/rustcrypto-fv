import K256.Proofs.Sec1.Wrapper.Entry
import K256.Proofs.Sec1.Wrapper.Finish
import K256.Proofs.Sec1.Parser.Affine
import K256.Proofs.Sec1.Post

namespace K256.Proofs.Sec1.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine Sec1.LIR Standards.SECG.ECC Standards.SECG.DomainParameters

abbrev stack (s : RamState) := Stack.region s publicKeyFromSec1Bytes.minStackBytes

abbrev Run (label : Label) (args : Vector Value 53) (mem : Ram) (out : Output Value Ram 53) :=
  program.Exec (dialect Extracted.programImage) ⟨⟨label, args, mem⟩, []⟩ out

def ParserCall (s : RamState) (bytes : ByteArray) : Prop :=
  let sp := s.regValue .rsp
  ∃ out, Run .l106390 (parserArgs s) (parserMemory s) out ∧
    out.tag = some ⟨64, 0x101dea⟩ ∧ CallerFrame s [stack s] out.values out.store ∧
    match Secp256k1.decodePublicKey bytes with
    | none => memLoad out.store (sp - 112) 64 = 1
    | some point => memLoad out.store (sp - 112) 64 = 0 ∧ Parser.PublicKeyAt out.store (sp - 104) point

def SerializerCall (s : RamState) : Prop :=
  let sp := s.regValue .rsp
  ∀ (args : Vector Value 53) (mem : Ram) (point : Curve.Point),
    CallerFrame s [stack s] args mem → args[3] = ⟨64, 0⟩ → Parser.PublicKeyAt mem (sp - 104) point →
    let child := (((args.set 2 ⟨64, 0⟩).set 4 ⟨64, sp - 256⟩).set 6 ⟨64, sp - 104⟩).set 7 ⟨64, sp - 233⟩
    ∃ out, Run .l1215e0 child (memStore mem (sp - 256) (0x101e0c : BitVec 64)) out ∧
      out.tag = some ⟨64, 0x101e0c⟩ ∧ CallerFrame s [stack s] out.values out.store ∧
      out.values[3] = ⟨64, 0⟩ ∧ memLoad out.store (sp - 233) 8 = 4 ∧
      (⟨(sp - 233).toNat, 65⟩ : MemoryRegion).HasBytes out.store (Points.encodePoint Secp256k1.domain false point)

def CopyCall (s : RamState) : Prop :=
  let sp := s.regValue .rsp
  let dst := s.regValue .rdi
  ∀ (args : Vector Value 53) (mem : Ram) (encoded : ByteArray),
    CallerFrame s [stack s] args mem → args[3] = ⟨64, 0⟩ →
    (⟨(sp - 233).toNat, 65⟩ : MemoryRegion).HasBytes mem encoded →
    let child := (((args.set 2 ⟨64, 65⟩).set 4 ⟨64, sp - 256⟩).set 6 ⟨64, sp - 233⟩).set 7 ⟨64, dst⟩
    ∃ out, Run .l12a820 child (memStore mem (sp - 256) (0x101e62 : BitVec 64)) out ∧
      out.tag = some ⟨64, 0x101e62⟩ ∧
      CallerFrame s [outputRegion publicKeyFromSec1Bytes s, stack s] out.values out.store ∧
      out.values[3] = ⟨64, 0⟩ ∧ (outputRegion publicKeyFromSec1Bytes s).HasBytes out.store encoded

end K256.Proofs.Sec1.Wrapper
