import Md5.Proofs.Buffered.Update.Slices.Full.Blocks
import Md5.Proofs.Buffered.Update.Slices.Tail

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem batch {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {offset count : Nat} {buffer : Standards.RFC.MD5.Buffer}
    (h : UpdatePre (kind variant) boundary message input s)
    (hp : BatchReady variant boundary input s offset buffer count u) :
    ∃ t, BatchDone variant boundary input s offset buffer count t := by
  obtain ⟨v, hv⟩ := blocks h hp
  exact tail h hv

end Md5.Proofs.Buffered.Update.Slices
