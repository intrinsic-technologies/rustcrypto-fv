import Md5.Proofs.Buffered.Stack
import Md5.Proofs.Buffered.Update.Calls
import Md5.Proofs.Block.Entry
import Md5.Proofs.Buffered.FinalizeReset.CompressCall

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem memcpy_r15 [bindings : Bindings] (hstride : UnitStringStride bindings)
    {boundary : ReturnBoundary} {p : BitVec 64} {s : RamState}
    (hsite : p = 0x1009ab ∨ p = 0x100a0a ∨ p = 0x100a6c ∨
      p = 0x10103b ∨ p = 0x10109a ∨ p = 0x1010fc ∨
      p = 0x10151e ∨ p = 0x101576 ∨ p = 0x1015dc)
    (hout : ¬ InProgram boundary.rip)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = p) (hr15 : (Operand.reg 15 : Operand 64).read s = 0x1024b0)
    (hslot : Memory.MemWritable s (pushAddr s) 8) (hpre : MemcpySitePre (p + 3) s) :
    ∃ t, MemcpySiteResult boundary (p + 3) s t := by
  have hbytes : CodeIn (codeRange p [0x41, 0xff, 0xd7]) s := by
    rcases hsite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact program_text_slice hcode 0x9ab 3 (by decide +kernel)
    · exact program_text_slice hcode 0xa0a 3 (by decide +kernel)
    · exact program_text_slice hcode 0xa6c 3 (by decide +kernel)
    · exact program_text_slice hcode 0x103b 3 (by decide +kernel)
    · exact program_text_slice hcode 0x109a 3 (by decide +kernel)
    · exact program_text_slice hcode 0x10fc 3 (by decide +kernel)
    · exact program_text_slice hcode 0x151e 3 (by decide +kernel)
    · exact program_text_slice hcode 0x1576 3 (by decide +kernel)
    · exact program_text_slice hcode 0x15dc 3 (by decide +kernel)
  have hret : p + 3 ≠ boundary.rip := by
    rcases hsite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact text_address_ne_return hout 0x9ae (by decide +kernel)
    · exact text_address_ne_return hout 0xa0d (by decide +kernel)
    · exact text_address_ne_return hout 0xa6f (by decide +kernel)
    · exact text_address_ne_return hout 0x103e (by decide +kernel)
    · exact text_address_ne_return hout 0x109d (by decide +kernel)
    · exact text_address_ne_return hout 0x10ff (by decide +kernel)
    · exact text_address_ne_return hout 0x1521 (by decide +kernel)
    · exact text_address_ne_return hout 0x1579 (by decide +kernel)
    · exact text_address_ne_return hout 0x15df (by decide +kernel)
  have hstep := Stack.call_r64_rex_effect_step p 0x41 0xd7
    (by unfold RexPrefix; decide) (by decide) (by decide)
  change StepEffect (Stack.CallPre p (fun u ↦ (Operand.reg 15 : Operand 64).read u))
    (codeRange p [0x41, 0xff, 0xd7])
    (callEffect (fun u ↦ (Operand.reg 15 : Operand 64).read u) (p + 3)) at hstep
  exact memcpy_call hstride
    (outside_text_range_of_not_inProgram hout 0x1024b0 0x1024df (by decide) (by decide +kernel))
    hstep hready hcode hbytes
    ⟨⟨hrip, hslot⟩, by dsimp only; rw [hr15]; decide⟩ hpre hr15 hret


theorem compress_call [Bindings] {boundary : ReturnBoundary} {p : BitVec 64}
    {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray} {s : RamState}
    (hsite : p = 0x100a1f ∨ p = 0x100a42 ∨ p = 0x1010af ∨ p = 0x1010d2 ∨
      p = 0x10158d ∨ p = 0x1015b0) (hout : ¬ InProgram boundary.rip)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = p) (hp : FinalizeReset.CompressCall.Pre buffer input s) :
    ∃ t, FinalizeReset.CompressCall.Post boundary (p + 5) buffer input s t := by
  rcases hsite with rfl | rfl | rfl | rfl | rfl | rfl
  · have hb : CodeIn (codeRange 0x100a1f [0xe8, 0x7c, 0x11, 0x00, 0x00]) s :=
      program_text_slice hcode 0xa1f 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Stack.call_rel32_effect_step 0x100a1f 0x117c (by decide)) hready hcode hb
      ⟨hrip, hp.pushWritable⟩ hp rfl (by decide) (by unfold OutsideCompression; decide) hout
      (text_address_ne_return hout 0xa24 (by decide +kernel))
  · have hb : CodeIn (codeRange 0x100a42 [0xe8, 0x59, 0x11, 0x00, 0x00]) s :=
      program_text_slice hcode 0xa42 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Stack.call_rel32_effect_step 0x100a42 0x1159 (by decide)) hready hcode hb
      ⟨hrip, hp.pushWritable⟩ hp rfl (by decide) (by unfold OutsideCompression; decide) hout
      (text_address_ne_return hout 0xa47 (by decide +kernel))
  · have hb : CodeIn (codeRange 0x1010af [0xe8, 0xec, 0xa, 0x00, 0x00]) s :=
      program_text_slice hcode 0x10af 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Stack.call_rel32_effect_step 0x1010af 0xaec (by decide)) hready hcode hb
      ⟨hrip, hp.pushWritable⟩ hp rfl (by decide) (by unfold OutsideCompression; decide) hout
      (text_address_ne_return hout 0x10b4 (by decide +kernel))
  · have hb : CodeIn (codeRange 0x1010d2 [0xe8, 0xc9, 0xa, 0x00, 0x00]) s :=
      program_text_slice hcode 0x10d2 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Stack.call_rel32_effect_step 0x1010d2 0xac9 (by decide)) hready hcode hb
      ⟨hrip, hp.pushWritable⟩ hp rfl (by decide) (by unfold OutsideCompression; decide) hout
      (text_address_ne_return hout 0x10d7 (by decide +kernel))
  · have hb : CodeIn (codeRange 0x10158d [0xe8, 0xe, 0x6, 0x00, 0x00]) s :=
      program_text_slice hcode 0x158d 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Stack.call_rel32_effect_step 0x10158d 0x60e (by decide)) hready hcode hb
      ⟨hrip, hp.pushWritable⟩ hp rfl (by decide) (by unfold OutsideCompression; decide) hout
      (text_address_ne_return hout 0x1592 (by decide +kernel))
  · have hb : CodeIn (codeRange 0x1015b0 [0xe8, 0xeb, 0x5, 0x00, 0x00]) s :=
      program_text_slice hcode 0x15b0 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Stack.call_rel32_effect_step 0x1015b0 0x5eb (by decide)) hready hcode hb
      ⟨hrip, hp.pushWritable⟩ hp rfl (by decide) (by unfold OutsideCompression; decide) hout
      (text_address_ne_return hout 0x15b5 (by decide +kernel))

end Md5.Proofs.Buffered.ResetSecond
