import Md5.Proofs.Buffered.Update.Slices.Control
import Md5.Proofs.Buffered.Update.Batch

namespace Md5.Proofs.Buffered.Update.Slices

open X86.Machine

abbrev BatchReady (variant : Bool) [Bindings] := UpdateBatchReady (kind variant)

abbrev BlocksDone (variant : Bool) [Bindings] := UpdateBlocksDone (kind variant)

abbrev BatchDone (variant : Bool) [Bindings] := UpdateBatchDone (kind variant)

theorem kind_batchSizeRegister (variant : Bool) :
    (kind variant).batchSizeRegister = 5 := by cases variant <;> rfl

theorem kind_batchEntry (variant : Bool) :
    (kind variant).batchEntry = pc variant 0x1003c5 := by cases variant <;> rfl

theorem kind_tailEntry (variant : Bool) :
    (kind variant).tailEntry = pc variant 0x1003dd := by cases variant <;> rfl

end Md5.Proofs.Buffered.Update.Slices
