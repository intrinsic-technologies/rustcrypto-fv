import Md5.Proofs.Buffered.Stack
import Md5.Proofs.Buffered.Update.Calls
import Md5.Proofs.Buffered.Update.Rodata
import Md5.Proofs.Buffered.FinalizeReset.CompressCall

namespace Md5.Proofs.NewEntries.Reset.FirstUpdate

open Md5.Proofs.Buffered Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

theorem memcpy_rip [bindings : Bindings] (hstride : Prelude.UnitStringStride bindings)
    {boundary : ReturnBoundary} {p : BitVec 64} {s : RamState}
    (hsite : p = 0x1013de ∨ p = 0x101437 ∨ p = 0x1014a0)
    (hout : ¬ InProgram boundary.rip)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = p) (hslot : Memory.MemWritable s (pushAddr s) 8)
    (hp : MemcpySitePre (p + 6) s) :
    ∃ t, MemcpySiteResult boundary (p + 6) s t := by
  have hb := outside_text_range_of_not_inProgram hout 0x1024b0 0x1024df
    (by decide) (by decide +kernel)
  rcases hsite with rfl | rfl | rfl
  · have htarget : callMemPtr 0x1013de (.rip 0xfec1c) s = 0x1024b0 := memcpy_pointer hcode
    have hbytes : CodeIn (codeRange 0x1013de [0xff, 0x15, 0x1c, 0xec, 0x0f, 0x00]) s :=
      program_text_slice hcode 0x13de 6 (by decide +kernel)
    exact memcpy_call hstride hb (Stack.call_m64_rip_effect_step 0x1013de 0xfec1c)
      hready hcode hbytes
      ⟨⟨⟨hrip, hslot⟩, by rw [htarget]; decide⟩, memcpy_pointer_readable hcode⟩
      hp htarget (text_address_ne_return hout 0x13e4 (by decide +kernel))
  · have htarget : callMemPtr 0x101437 (.rip 0xfebc3) s = 0x1024b0 := memcpy_pointer hcode
    have hbytes : CodeIn (codeRange 0x101437 [0xff, 0x15, 0xc3, 0xeb, 0x0f, 0x00]) s :=
      program_text_slice hcode 0x1437 6 (by decide +kernel)
    exact memcpy_call hstride hb (Stack.call_m64_rip_effect_step 0x101437 0xfebc3)
      hready hcode hbytes
      ⟨⟨⟨hrip, hslot⟩, by rw [htarget]; decide⟩, memcpy_pointer_readable hcode⟩
      hp htarget (text_address_ne_return hout 0x143d (by decide +kernel))
  · have htarget : callMemPtr 0x1014a0 (.rip 0xfeb5a) s = 0x1024b0 := memcpy_pointer hcode
    have hbytes : CodeIn (codeRange 0x1014a0 [0xff, 0x15, 0x5a, 0xeb, 0x0f, 0x00]) s :=
      program_text_slice hcode 0x14a0 6 (by decide +kernel)
    exact memcpy_call hstride hb (Stack.call_m64_rip_effect_step 0x1014a0 0xfeb5a)
      hready hcode hbytes
      ⟨⟨⟨hrip, hslot⟩, by rw [htarget]; decide⟩, memcpy_pointer_readable hcode⟩
      hp htarget (text_address_ne_return hout 0x14a6 (by decide +kernel))

theorem compress_call [Bindings] {boundary : ReturnBoundary} {p : BitVec 64}
    {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray} {s : RamState}
    (hsite : p = 0x101451 ∨ p = 0x101474) (hout : ¬ InProgram boundary.rip)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = p) (hp : FinalizeReset.CompressCall.Pre buffer input s) :
    ∃ t, FinalizeReset.CompressCall.Post boundary (p + 5) buffer input s t := by
  rcases hsite with rfl | rfl
  · have hbytes : CodeIn (codeRange 0x101451 [0xe8, 0x4a, 0x07, 0x00, 0x00]) s :=
      program_text_slice hcode 0x1451 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Stack.call_rel32_effect_step 0x101451 0x74a (by decide)) hready hcode hbytes
      ⟨hrip, hp.pushWritable⟩ hp rfl (by decide) (by unfold OutsideCompression; decide) hout
      (text_address_ne_return hout 0x1456 (by decide +kernel))
  · have hbytes : CodeIn (codeRange 0x101474 [0xe8, 0x27, 0x07, 0x00, 0x00]) s :=
      program_text_slice hcode 0x1474 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Stack.call_rel32_effect_step 0x101474 0x727 (by decide)) hready hcode hbytes
      ⟨hrip, hp.pushWritable⟩ hp rfl (by decide) (by unfold OutsideCompression; decide) hout
      (text_address_ne_return hout 0x1479 (by decide +kernel))

end Md5.Proofs.NewEntries.Reset.FirstUpdate
