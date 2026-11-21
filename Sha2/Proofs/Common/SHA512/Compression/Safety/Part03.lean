import Sha2.Proofs.Wrapper.Call
import Sha2.Proofs.Common.SHA512.Compression.Safety.Steps
import Sha2.Proofs.Common.SHA512.Compression.Safety.Memory
import Sha2.Proofs.Common.SHA512.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part03
set_option autoImplicit false
namespace Sha2.Proofs.Common.SHA512.Compression.Safety
open Sha2.Spec Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions.MemoryAlu
set_option maxRecDepth 4096 in
 theorem part03 [Bindings] {initial : RamState} {hash : Array UInt64} {block : ByteArray}
 (pre : BlockPre initial hash block) (loaded : ProgramLoaded initial) :
 Certificate initial Decoded.part03 before03 after03 positions03 := by
 unfold Decoded.part03 before03 after03 positions03
 apply Certificate.cons
 · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (by simpa [positionOf] using text_inside 57129 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
   · intro model state
     change model.RIP = 1105698 ∧ MemReadable initial 0x200000 8
     have h : MemReadable initial 0x200000 8 := by
       refine ⟨by decide, ?_⟩
       intro i hi
       have byte := Sha2.Proofs.Wrapper.rodata_loaded loaded (offset := i) (by omega)
       exact Option.isSome_iff_exists.mpr ⟨_, by simpa [BitVec.ofNat_add, ← BitVec.add_assoc, Sha2.Spec.Program.Extracted.rodataAddress] using byte⟩
     exact ⟨state.rip, h⟩
   · intro model state
     refine ⟨(addSpec ((Operand.reg 1 : Operand 64).read model)
       ((Operand.mem ((AddrMode.rip 0xf20d7).addr model (0x10df22 + BitVec.ofNat 64 7)) : Operand 64).read model)).1, ?_, ?_⟩
     · have hr : (rexR (72#8)).toNat = 0 := by decide
       simp [CheckedInstruction.load, CheckedInstruction.ofStep, addR64M64Effect, gprNumber, AddrMode.tail, hr]
     · intro r hr
       have eq : r = 6 := List.mem_singleton.mp hr
       subst r
       exact Or.inr ⟨by decide, by simp [after02]⟩
 apply Certificate.cons
 · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (by simpa [positionOf] using text_inside 57132 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
   · intro model state; exact state.rip
   · intro model state; refine ⟨_, rfl, ?_⟩; intro r hr; have eq : r = 6 := List.mem_singleton.mp hr; subst r; exact Or.inr ⟨by decide, by simp [positionOf]⟩
 apply Certificate.cons
 · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (by simpa [positionOf] using text_inside 57135 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
   · intro model state; exact state.rip
   · intro model state; refine ⟨_, rfl, ?_⟩; intro r hr; have eq : r = 6 := List.mem_singleton.mp hr; subst r; exact Or.inr ⟨by decide, by simp [positionOf]⟩
 exact .nil _
end Sha2.Proofs.Common.SHA512.Compression.Safety
