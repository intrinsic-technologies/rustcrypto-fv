import Md5.Proofs.Buffered.Update.ResetFirst.Batch.Blocks
import Md5.Proofs.Buffered.Update.ResetFirst.Batch.Tail

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem batch_run_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {offset count : Nat} {buffer : Standards.RFC.MD5.Buffer}
    (h : UpdatePre kind boundary message input s)
    (hb : UpdateBatchReady kind boundary input s offset buffer count u) :
    ∃ t, UpdateBatchDone kind boundary input s offset buffer count t := by
  obtain ⟨v, hv⟩ := batch_blocks_run_of_kind hk h hb
  exact batch_tail_run_of_kind hk h hv

theorem batch_run [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {offset count : Nat} {buffer : Standards.RFC.MD5.Buffer}
    (h : UpdatePre .resetFirst boundary message input s)
    (hb : BatchReady boundary input s offset buffer count u) :
    ∃ t, BatchDone boundary input s offset buffer count t := by
  exact batch_run_of_kind (kind := .resetFirst) (Or.inl rfl) h hb

end Md5.Proofs.Buffered.ResetFirst
