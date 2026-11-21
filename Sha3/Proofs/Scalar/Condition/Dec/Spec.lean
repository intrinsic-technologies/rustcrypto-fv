import X86Proofs.Core.Flags

namespace X86Proofs

def decSpec {n : Nat} (f : StatusFlags) (x : BitVec n) : BitVec n × StatusFlags :=
  let r := x - 1
  (r, { OF := decide (r.toInt ≠ x.toInt - 1), CF := f.CF,
        SF := r.msb, ZF := r == 0, PF := evenParity (r.extractLsb' 0 8),
        AF := x.extractLsb' 0 4 == 0 })

end X86Proofs
