import Md5.Proofs.Buffered.Update.Batch

namespace Md5.Proofs.Buffered.ResetFirst

open X86 X86.Machine X86.UserProcess X86Proofs

abbrev BatchReady [Bindings] := UpdateBatchReady .resetFirst

abbrev BatchDone [Bindings] := UpdateBatchDone .resetFirst

end Md5.Proofs.Buffered.ResetFirst
