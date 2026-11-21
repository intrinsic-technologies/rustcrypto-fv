import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part00
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part01
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part02
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part03
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part04
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part05
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part06
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part07
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part08
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part09
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part10
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part11
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part12
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part13
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part14
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part15
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part16
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part17
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part18
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part19
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part20
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part21
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part22
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part23
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part24
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part25
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part26
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part27
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part28
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part29
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part30
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part31
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part32
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part33
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part34
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part35
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part36
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part37
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part38
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part39
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part40
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part41
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part42
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part43
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part44
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part45
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part46
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part47
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part48
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part49
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part50
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part51
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Part52
import Hkdf.Proofs.Common.SHA256.Compression.Decoded

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Safety

open X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem certificate [Bindings] {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (pre : BlockPre initial hash block) :
    Certificate initial Decoded.instructions before00 after52 positions.tail := by
  exact (part00 pre).append ((part01 pre).append ((part02 pre).append ((part03 pre).append ((part04 pre).append ((part05 pre).append ((part06 pre).append ((part07 pre).append ((part08 pre).append ((part09 pre).append ((part10 pre).append ((part11 pre).append ((part12 pre).append ((part13 pre).append ((part14 pre).append ((part15 pre).append ((part16 pre).append ((part17 pre).append ((part18 pre).append ((part19 pre).append ((part20 pre).append ((part21 pre).append ((part22 pre).append ((part23 pre).append ((part24 pre).append ((part25 pre).append ((part26 pre).append ((part27 pre).append ((part28 pre).append ((part29 pre).append ((part30 pre).append ((part31 pre).append ((part32 pre).append ((part33 pre).append ((part34 pre).append ((part35 pre).append ((part36 pre).append ((part37 pre).append ((part38 pre).append ((part39 pre).append ((part40 pre).append ((part41 pre).append ((part42 pre).append ((part43 pre).append ((part44 pre).append ((part45 pre).append ((part46 pre).append ((part47 pre).append ((part48 pre).append ((part49 pre).append ((part50 pre).append ((part51 pre).append (part52 pre))))))))))))))))))))))))))))))))))))))))))))))))))))

end Hkdf.Proofs.Common.SHA256.Compression.Safety
