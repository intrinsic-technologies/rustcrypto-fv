import K256.Proofs.Verify.Hash.Compression.Values
import K256.Proofs.Verify.Hash.Compression.Mathematics.BitVecModel

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash.Compression.Values

def hashState (values : Values) : BitVecState :=
  ⟨(values.regs 3).setWidth 32, (values.regs 14).setWidth 32,
    (values.regs 0).setWidth 32, (values.regs 9).setWidth 32,
    (values.regs 8).setWidth 32, (values.regs 10).setWidth 32,
    (values.regs 2).setWidth 32, (values.regs 1).setWidth 32⟩

end K256.Proofs.Verify.Hash.Compression.Values
