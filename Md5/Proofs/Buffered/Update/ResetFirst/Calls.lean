import Md5.Proofs.Buffered.Stack
import Md5.Proofs.Buffered.Update.Calls
import Md5.Proofs.Buffered.Update.Rodata
import Md5.Proofs.Buffered.FinalizeReset.CompressCall

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

theorem memcpy_rip [bindings : Bindings] (hstride : Prelude.UnitStringStride bindings)
    {boundary : ReturnBoundary} {p : BitVec 64} {s : RamState}
    (hsite : p = 0x10069e ∨ p = 0x1006fe ∨ p = 0x100765)
    (hout : ¬ InProgram boundary.rip)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = p) (hslot : Memory.MemWritable s (pushAddr s) 8)
    (hp : MemcpySitePre (p + 6) s) :
    ∃ t, MemcpySiteResult boundary (p + 6) s t := by
  have hb := outside_text_range_of_not_inProgram hout 0x1024b0 0x1024df
    (by decide) (by decide +kernel)
  rcases hsite with rfl | rfl | rfl
  · have htarget : callMemPtr 0x10069e (.rip 0xff95c) s = 0x1024b0 := memcpy_pointer hcode
    have hbytes : CodeIn (codeRange 0x10069e [0xff, 0x15, 0x5c, 0xf9, 0x0f, 0x00]) s :=
      program_text_slice hcode 0x69e 6 (by decide +kernel)
    exact memcpy_call hstride hb (Stack.call_m64_rip_effect_step 0x10069e 0xff95c)
      hready hcode hbytes
      ⟨⟨⟨hrip, hslot⟩, by rw [htarget]; decide⟩, memcpy_pointer_readable hcode⟩
      hp htarget (text_address_ne_return hout 0x6a4 (by decide +kernel))
  · have htarget : callMemPtr 0x1006fe (.rip 0xff8fc) s = 0x1024b0 := memcpy_pointer hcode
    have hbytes : CodeIn (codeRange 0x1006fe [0xff, 0x15, 0xfc, 0xf8, 0x0f, 0x00]) s :=
      program_text_slice hcode 0x6fe 6 (by decide +kernel)
    exact memcpy_call hstride hb (Stack.call_m64_rip_effect_step 0x1006fe 0xff8fc)
      hready hcode hbytes
      ⟨⟨⟨hrip, hslot⟩, by rw [htarget]; decide⟩, memcpy_pointer_readable hcode⟩
      hp htarget (text_address_ne_return hout 0x704 (by decide +kernel))
  · have htarget : callMemPtr 0x100765 (.rip 0xff895) s = 0x1024b0 := memcpy_pointer hcode
    have hbytes : CodeIn (codeRange 0x100765 [0xff, 0x15, 0x95, 0xf8, 0x0f, 0x00]) s :=
      program_text_slice hcode 0x765 6 (by decide +kernel)
    exact memcpy_call hstride hb (Stack.call_m64_rip_effect_step 0x100765 0xff895)
      hready hcode hbytes
      ⟨⟨⟨hrip, hslot⟩, by rw [htarget]; decide⟩, memcpy_pointer_readable hcode⟩
      hp htarget (text_address_ne_return hout 0x76b (by decide +kernel))

theorem compress_call [Bindings] {boundary : ReturnBoundary} {p : BitVec 64}
    {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray} {s : RamState}
    (hsite : p = 0x100718 ∨ p = 0x10073b) (hout : ¬ InProgram boundary.rip)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = p) (hp : FinalizeReset.CompressCall.Pre buffer input s) :
    ∃ t, FinalizeReset.CompressCall.Post boundary (p + 5) buffer input s t := by
  rcases hsite with rfl | rfl
  · have hbytes : CodeIn (codeRange 0x100718 [0xe8, 0x83, 0x14, 0x00, 0x00]) s :=
      program_text_slice hcode 0x718 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Stack.call_rel32_effect_step 0x100718 0x1483 (by decide)) hready hcode hbytes
      ⟨hrip, hp.pushWritable⟩ hp rfl (by decide) (by unfold OutsideCompression; decide) hout
      (text_address_ne_return hout 0x71d (by decide +kernel))
  · have hbytes : CodeIn (codeRange 0x10073b [0xe8, 0x60, 0x14, 0x00, 0x00]) s :=
      program_text_slice hcode 0x73b 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Stack.call_rel32_effect_step 0x10073b 0x1460 (by decide)) hready hcode hbytes
      ⟨hrip, hp.pushWritable⟩ hp rfl (by decide) (by unfold OutsideCompression; decide) hout
      (text_address_ne_return hout 0x740 (by decide +kernel))

end Md5.Proofs.Buffered.ResetFirst
