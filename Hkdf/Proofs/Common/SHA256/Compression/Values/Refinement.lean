import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part00
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part01
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part02
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part03
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part04
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part05
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part06
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part07
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part08
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part09
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part10
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part11
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part12
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part13
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part14
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part15
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part16
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part17
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part18
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part19
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part20
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part21
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part22
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part23
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part24
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part25
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part26
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part27
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part28
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part29
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part30
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part31
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part32
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part33
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part34
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part35
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part36
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part37
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part38
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part39
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part40
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part41
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part42
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part43
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part44
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part45
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part46
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part47
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part48
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part49
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part50
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part51
import Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement.Part52
import Hkdf.Proofs.Common.SHA256.Compression.Decoded

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement

open X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem trace [Bindings] (initial : RamState) :
    TraceRefinement initial Decoded.instructions Program.operations
      Safety.before00 Safety.after52 Safety.positions.tail := by
  exact (part00 initial).append ((part01 initial).append ((part02 initial).append ((part03 initial).append ((part04 initial).append ((part05 initial).append ((part06 initial).append ((part07 initial).append ((part08 initial).append ((part09 initial).append ((part10 initial).append ((part11 initial).append ((part12 initial).append ((part13 initial).append ((part14 initial).append ((part15 initial).append ((part16 initial).append ((part17 initial).append ((part18 initial).append ((part19 initial).append ((part20 initial).append ((part21 initial).append ((part22 initial).append ((part23 initial).append ((part24 initial).append ((part25 initial).append ((part26 initial).append ((part27 initial).append ((part28 initial).append ((part29 initial).append ((part30 initial).append ((part31 initial).append ((part32 initial).append ((part33 initial).append ((part34 initial).append ((part35 initial).append ((part36 initial).append ((part37 initial).append ((part38 initial).append ((part39 initial).append ((part40 initial).append ((part41 initial).append ((part42 initial).append ((part43 initial).append ((part44 initial).append ((part45 initial).append ((part46 initial).append ((part47 initial).append ((part48 initial).append ((part49 initial).append ((part50 initial).append ((part51 initial).append (part52 initial))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hkdf.Proofs.Common.SHA256.Compression.Values.Refinement
