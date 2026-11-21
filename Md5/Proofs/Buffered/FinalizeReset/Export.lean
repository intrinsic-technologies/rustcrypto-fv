import Md5.Proofs.Buffered.FinalizeReset.Export.Bytes
import Md5.Proofs.Buffered.FinalizeReset.Export.Execution

namespace Md5.Proofs.Buffered.FinalizeReset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

structure ExportPre [Bindings] (boundary : ReturnBoundary) (digest : Vector UInt8 16)
    (s : RamState) (variant : Variant := .saved) : Prop extends Export.RunPre s variant where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  boundaryOutside : ¬ InProgram boundary.rip
  digest : (⟨(stackPtr s + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes
    s.external ⟨digest.toArray⟩

structure ExportPost [Bindings] (boundary : ReturnBoundary) (digest : Vector UInt8 16)
    (s t : RamState) (variant : Variant := .saved) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = variant.exit
  absorbed : Absorbed (context s) ByteArray.empty t
  digest : (outputRegion s).HasBytes t.external ⟨digest.toArray⟩
  agrees : AgreesExcept (changes s) s t

theorem ExportPost.rsp {variant : Variant} [Bindings] {boundary : ReturnBoundary} {digest : Vector UInt8 16}
    {s t : RamState} (h : ExportPost boundary digest s t variant) : stackPtr t = stackPtr s :=
  h.agrees.read (n := 64) (r := 4) (by simp [changes])

theorem ExportPost.rbp {variant : Variant} [Bindings] {boundary : ReturnBoundary} {digest : Vector UInt8 16}
    {s t : RamState} (h : ExportPost boundary digest s t variant) :
    (Operand.reg 5 : Operand 64).read t = (Operand.reg 5 : Operand 64).read s :=
  h.agrees.read (by simp [changes])

theorem ExportPost.r12 {variant : Variant} [Bindings] {boundary : ReturnBoundary} {digest : Vector UInt8 16}
    {s t : RamState} (h : ExportPost boundary digest s t variant) :
    (Operand.reg 12 : Operand 64).read t = (Operand.reg 12 : Operand 64).read s :=
  h.agrees.read (by simp [changes])

theorem export_digest {variant : Variant} [Bindings] {boundary : ReturnBoundary}
    {digest : Vector UInt8 16} {s : RamState} (h : ExportPre boundary digest s variant) :
    ∃ t, ExportPost boundary digest s t variant := by
  have hCode : CodeIn (codeRange (variant.address 0x10091c) (Export.bytes variant)) s := by
    cases variant with
    | saved => exact program_text_slice h.code 0x91c 109 (by decide +kernel)
    | direct => exact program_text_slice h.code 0xfcc 77 (by decide +kernel)
  obtain ⟨fuel, t, hAdvance, hReady, _, hEffect⟩ :=
    Export.execution boundary h.boundaryOutside s h.ready hCode h.toRunPre
  exact ⟨t, ⟨⟨fuel, hAdvance⟩, hReady,
    hEffect.codeIn (Export.effect_avoids h.toStorage) h.code,
    (by cases variant <;> exact hEffect.rip),
    Export.effect_absorbed h.toStorage hEffect,
    Export.effect_digest h.toStorage hEffect h.digest, Export.effect_agrees hEffect⟩⟩

end Md5.Proofs.Buffered.FinalizeReset
