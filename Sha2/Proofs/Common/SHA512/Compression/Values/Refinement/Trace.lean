import Sha2.Proofs.Common.SHA512.Compression.Values.Refinement.Part56
import Sha2.Proofs.Common.SHA512.Compression.Values.Refinement.Part20Remainder
import Sha2.Proofs.Common.SHA512.Compression.Decoded

set_option autoImplicit false
namespace Sha2.Proofs.Common.SHA512.Compression.Values.Refinement
open X86 X86.Machine X86.UserProcess X86Proofs
set_option maxRecDepth 4096 in
theorem part20 [Bindings] (initial : RamState) :
    TraceRefinement initial Decoded.part20 Program.part20
      Safety.before20 Safety.after20 Safety.positions20 := by
  have firstPart := part20_prefix10 initial
  simp only [List.drop_zero] at firstPart
  simpa only [List.take_append_drop] using firstPart.append (part20_remainder initial)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem trace [Bindings] (initial : RamState) :
    TraceRefinement initial Decoded.instructions Program.operations
      Safety.before00 Safety.after56 Safety.positions.tail := by
  simp only [Program.operations, Program.part20Prefix10, Program.part20Remainder,
    List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [← List.append_assoc (Program.part20.take 10) (Program.part20.drop 10),
    List.take_append_drop]
  exact (part00 initial).append ((part01 initial).append ((part02 initial).append ((part03 initial).append ((part04 initial).append ((part05 initial).append ((part06 initial).append ((part06And initial).append ((part07 initial).append ((part08 initial).append ((part09 initial).append ((part10 initial).append ((part11 initial).append ((part12 initial).append ((part13 initial).append ((part14 initial).append ((part15 initial).append ((part16 initial).append ((part17 initial).append ((part18 initial).append ((part19 initial).append ((part20 initial).append ((part21 initial).append ((part22 initial).append ((part23 initial).append ((part24 initial).append ((part25 initial).append ((part26 initial).append ((part27 initial).append ((part28 initial).append ((part29 initial).append ((part30 initial).append ((part31 initial).append ((part32 initial).append ((part33 initial).append ((part34 initial).append ((part35 initial).append ((part36 initial).append ((part37 initial).append ((part38 initial).append ((part39 initial).append ((part40 initial).append ((part41 initial).append ((part42 initial).append ((part43 initial).append ((part44 initial).append ((part45 initial).append ((part46 initial).append ((part47 initial).append ((part48 initial).append ((part49 initial).append ((part50 initial).append ((part51 initial).append ((part52 initial).append ((part53 initial).append ((part54 initial).append ((part55 initial).append ((part56 initial))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Sha2.Proofs.Common.SHA512.Compression.Values.Refinement
