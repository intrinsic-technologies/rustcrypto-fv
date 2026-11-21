import X86

namespace X86Proofs

def movzxSpec {m : Nat} (n : Nat) (x : BitVec m) : BitVec n := x.setWidth n

end X86Proofs
