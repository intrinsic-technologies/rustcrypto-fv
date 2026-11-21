import P256.Proofs.SHA256.Compression.Values.Refinement.Part00
import P256.Proofs.SHA256.Compression.Values.Refinement.Part01
import P256.Proofs.SHA256.Compression.Values.Refinement.Part02
import P256.Proofs.SHA256.Compression.Values.Refinement.Part03
import P256.Proofs.SHA256.Compression.Values.Refinement.Part04
import P256.Proofs.SHA256.Compression.Values.Refinement.Part05
import P256.Proofs.SHA256.Compression.Values.Refinement.Part06
import P256.Proofs.SHA256.Compression.Values.Refinement.Part07
import P256.Proofs.SHA256.Compression.Values.Refinement.Part08
import P256.Proofs.SHA256.Compression.Values.Refinement.Part09
import P256.Proofs.SHA256.Compression.Values.Refinement.Part10
import P256.Proofs.SHA256.Compression.Values.Refinement.Part11
import P256.Proofs.SHA256.Compression.Values.Refinement.Part12
import P256.Proofs.SHA256.Compression.Values.Refinement.Part13
import P256.Proofs.SHA256.Compression.Values.Refinement.Part14
import P256.Proofs.SHA256.Compression.Values.Refinement.Part15
import P256.Proofs.SHA256.Compression.Values.Refinement.Part16
import P256.Proofs.SHA256.Compression.Values.Refinement.Part17
import P256.Proofs.SHA256.Compression.Values.Refinement.Part18
import P256.Proofs.SHA256.Compression.Values.Refinement.Part19
import P256.Proofs.SHA256.Compression.Values.Refinement.Part20
import P256.Proofs.SHA256.Compression.Values.Refinement.Part21
import P256.Proofs.SHA256.Compression.Values.Refinement.Part22
import P256.Proofs.SHA256.Compression.Values.Refinement.Part23
import P256.Proofs.SHA256.Compression.Values.Refinement.Part24
import P256.Proofs.SHA256.Compression.Values.Refinement.Part25
import P256.Proofs.SHA256.Compression.Values.Refinement.Part26
import P256.Proofs.SHA256.Compression.Values.Refinement.Part27
import P256.Proofs.SHA256.Compression.Values.Refinement.Part28
import P256.Proofs.SHA256.Compression.Values.Refinement.Part29
import P256.Proofs.SHA256.Compression.Values.Refinement.Part30
import P256.Proofs.SHA256.Compression.Values.Refinement.Part31
import P256.Proofs.SHA256.Compression.Values.Refinement.Part32
import P256.Proofs.SHA256.Compression.Values.Refinement.Part33
import P256.Proofs.SHA256.Compression.Values.Refinement.Part34
import P256.Proofs.SHA256.Compression.Values.Refinement.Part35
import P256.Proofs.SHA256.Compression.Values.Refinement.Part36
import P256.Proofs.SHA256.Compression.Values.Refinement.Part37
import P256.Proofs.SHA256.Compression.Values.Refinement.Part38
import P256.Proofs.SHA256.Compression.Values.Refinement.Part39
import P256.Proofs.SHA256.Compression.Values.Refinement.Part40
import P256.Proofs.SHA256.Compression.Values.Refinement.Part41
import P256.Proofs.SHA256.Compression.Values.Refinement.Part42
import P256.Proofs.SHA256.Compression.Values.Refinement.Part43
import P256.Proofs.SHA256.Compression.Values.Refinement.Part44
import P256.Proofs.SHA256.Compression.Values.Refinement.Part45
import P256.Proofs.SHA256.Compression.Values.Refinement.Part46
import P256.Proofs.SHA256.Compression.Values.Refinement.Part47
import P256.Proofs.SHA256.Compression.Values.Refinement.Part48
import P256.Proofs.SHA256.Compression.Values.Refinement.Part49
import P256.Proofs.SHA256.Compression.Values.Refinement.Part50
import P256.Proofs.SHA256.Compression.Values.Refinement.Part51
import P256.Proofs.SHA256.Compression.Values.Refinement.Part52
import P256.Proofs.SHA256.Compression.Decoded

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Values.Refinement

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem trace [Bindings] (initial : RamState) :
    TraceRefinement initial Decoded.instructions Program.operations
      Safety.before00 Safety.after52 Safety.positions.tail := by
  exact (part00 initial).append ((part01 initial).append ((part02 initial).append ((part03 initial).append ((part04 initial).append ((part05 initial).append ((part06 initial).append ((part07 initial).append ((part08 initial).append ((part09 initial).append ((part10 initial).append ((part11 initial).append ((part12 initial).append ((part13 initial).append ((part14 initial).append ((part15 initial).append ((part16 initial).append ((part17 initial).append ((part18 initial).append ((part19 initial).append ((part20 initial).append ((part21 initial).append ((part22 initial).append ((part23 initial).append ((part24 initial).append ((part25 initial).append ((part26 initial).append ((part27 initial).append ((part28 initial).append ((part29 initial).append ((part30 initial).append ((part31 initial).append ((part32 initial).append ((part33 initial).append ((part34 initial).append ((part35 initial).append ((part36 initial).append ((part37 initial).append ((part38 initial).append ((part39 initial).append ((part40 initial).append ((part41 initial).append ((part42 initial).append ((part43 initial).append ((part44 initial).append ((part45 initial).append ((part46 initial).append ((part47 initial).append ((part48 initial).append ((part49 initial).append ((part50 initial).append ((part51 initial).append (part52 initial))))))))))))))))))))))))))))))))))))))))))))))))))))

end P256.Proofs.SHA256.Compression.Values.Refinement
