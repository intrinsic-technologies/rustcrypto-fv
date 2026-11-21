import Sha2.Proofs.Common.SHA512.Compression.Safety.Basic
import Sha2.Proofs.Common.SHA512.Compression.Safety.Effects
import Sha2.Proofs.Common.SHA512.Compression.Safety.Memory
import Sha2.Proofs.Common.SHA512.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA512.Compression.Safety.Steps
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part00
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part01
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part02
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part03
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part04
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part05
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part06
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part07
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part08
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part09
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part10
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part11
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part12
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part13
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part14
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part15
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part16
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part17
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part18
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part19
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part20
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part21
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part22
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part23
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part24
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part25
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part26
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part27
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part28
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part29
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part30
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part31
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part32
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part33
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part34
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part35
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part36
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part37
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part38
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part39
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part40
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part41
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part42
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part43
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part44
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part45
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part46
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part47
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part48
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part49
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part50
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part51
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part52
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part53
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part54
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part55
import Sha2.Proofs.Common.SHA512.Compression.Safety.Part56

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Safety

open Sha2.Spec Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem certificate_part00 [Bindings] {initial : RamState} {hash : Array UInt64}
    {block : ByteArray} (pre : BlockPre initial hash block) :
    Certificate initial Decoded.part00 before00 after00 positions00 :=
  part00 pre

theorem certificate_part01 [Bindings] {initial : RamState} {hash : Array UInt64}
    {block : ByteArray} (pre : BlockPre initial hash block) :
    Certificate initial Decoded.part01 before01 after01 positions01 :=
  part01 pre

theorem certificate_part02 [Bindings] {initial : RamState} {hash : Array UInt64}
    {block : ByteArray} (pre : BlockPre initial hash block) :
    Certificate initial Decoded.part02 before02 after02 positions02 :=
  part02 pre

theorem certificate_part03 [Bindings] {initial : RamState} {hash : Array UInt64}
    {block : ByteArray} (pre : BlockPre initial hash block)
    (loaded : ProgramLoaded initial) :
    Certificate initial Decoded.part03 before03 after03 positions03 :=
  part03 pre loaded



theorem certificate_part06And [Bindings] {initial : RamState} {hash : Array UInt64}
    {block : ByteArray} (pre : BlockPre initial hash block) :
    Certificate initial Decoded.part06And before06And after06And positions06And := by
  unfold Decoded.part06And before06And after06And positions06And
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 57348 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      simp only [CheckedInstruction.load, CheckedInstruction.ofStep]
      change model.RIP = 1105916 ∧ MemReadable initial ((AddrMode.sib 4 none 0 (.d32 176)).addr model (1105916 + BitVec.ofNat 64 (3 + (AddrMode.sib 4 none 0 (.d32 176)).tail.length))) 8
      refine ⟨state.rip, ?_⟩
      simp only [AddrMode.addr, AddrMode.reg64, Operand.read]
      have rspEq : model.GPR[↑(gprIndex (4 : BitVec 5))] = stackPtr initial := by
        simpa [Operand.read] using state.rsp
      change MemReadable initial (model.GPR[↑(gprIndex (4 : BitVec 5))] + BitVec.ofNat 64 176) 8
      rw [rspEq]
      exact frame_readable pre.stack 176 8 (by decide)
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  exact .nil _


set_option maxRecDepth 4096 in
 theorem certificate [Bindings] {initial : RamState} {hash : Array UInt64} {block : ByteArray}
    (pre : BlockPre initial hash block) (loaded : ProgramLoaded initial) :
    Certificate initial Decoded.instructions before00 after56 (List.tail positions) := by
  have c06a : Certificate initial Decoded.part06And after06 after06And positions06And := by
    simpa only [before06And] using (certificate_part06And pre)
  exact ((part00 pre)).append (((part01 pre)).append (((part02 pre)).append (((part03 pre loaded)).append (((part04 pre)).append (((part05 pre loaded)).append (((part06 pre loaded)).append (c06a.append (((part07 pre)).append (((part08 pre loaded)).append (((part09 pre loaded)).append (((part10 pre)).append (((part11 pre loaded)).append (((part12 pre loaded)).append (((part13 pre loaded)).append (((part14 pre loaded)).append (((part15 pre loaded)).append (((part16 pre loaded)).append (((part17 pre loaded)).append (((part18 pre loaded)).append (((part19 pre loaded)).append (((part20 pre loaded)).append (((part21 pre)).append (((part22 pre loaded)).append (((part23 pre loaded)).append (((part24 pre loaded)).append (((part25 pre loaded)).append (((part26 pre loaded)).append (((part27 pre loaded)).append (((part28 pre loaded)).append (((part29 pre loaded)).append (((part30 pre loaded)).append (((part31 pre loaded)).append (((part32 pre loaded)).append (((part33 pre loaded)).append (((part34 pre loaded)).append (((part35 pre loaded)).append (((part36 pre loaded)).append (((part37 pre loaded)).append (((part38 pre loaded)).append (((part39 pre loaded)).append (((part40 pre loaded)).append (((part41 pre loaded)).append (((part42 pre loaded)).append (((part43 pre loaded)).append (((part44 pre loaded)).append (((part45 pre loaded)).append (((part46 pre loaded)).append (((part47 pre loaded)).append (((part48 pre loaded)).append (((part49 pre loaded)).append (((part50 pre loaded)).append (((part51 pre loaded)).append (((part52 pre loaded)).append (((part53 pre loaded)).append (((part54 pre)).append (((part55 pre)).append ((part56 pre))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Sha2.Proofs.Common.SHA512.Compression.Safety
