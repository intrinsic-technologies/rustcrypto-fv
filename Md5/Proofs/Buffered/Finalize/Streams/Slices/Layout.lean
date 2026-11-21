import Md5.Proofs.Buffered.Finalize.Contracts

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

abbrev streamKind (update : Bool) : Kind :=
  if update then .updateFinalizeInto else .slices

def relocated (update : Bool) (address : Nat) : Nat :=
  address + if update then 0x15b0 else 0

end Md5.Proofs.Buffered.Finalize.Streams.Slices
