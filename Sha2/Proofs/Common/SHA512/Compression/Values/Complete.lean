import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part00
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part02
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part03
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part04
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part05
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part06
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part06And
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part07
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part08
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part09
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part10
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part11
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part12
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part13
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part14
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part15
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part16
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part17
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part18
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part19
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part20Prefix10
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part20Remainder
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part21
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part22
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part23
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part24
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part25
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part26
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part27
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part28
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part29
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part30
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part31
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part32
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part33
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part34
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part35
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part36
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part37
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part38
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part39
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part40
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part41
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part42
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part43
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part44
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part45
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part46
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part47
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part48
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part49
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part50
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part51
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part52
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part53
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part54
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part55
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part56

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values

set_option maxRecDepth 4096 in
theorem run_partitioned (context : ValueContext) (s : Values) :
    run context Program.operations s =
      (run context Program.part56 (run context Program.part55 (run context Program.part54 (run context Program.part53 (run context Program.part52 (run context Program.part51 (run context Program.part50 (run context Program.part49 (run context Program.part48 (run context Program.part47 (run context Program.part46 (run context Program.part45 (run context Program.part44 (run context Program.part43 (run context Program.part42 (run context Program.part41 (run context Program.part40 (run context Program.part39 (run context Program.part38 (run context Program.part37 (run context Program.part36 (run context Program.part35 (run context Program.part34 (run context Program.part33 (run context Program.part32 (run context Program.part31 (run context Program.part30 (run context Program.part29 (run context Program.part28 (run context Program.part27 (run context Program.part26 (run context Program.part25 (run context Program.part24 (run context Program.part23 (run context Program.part22 (run context Program.part21 (run context Program.part20Remainder (run context Program.part20Prefix10 (run context Program.part19 (run context Program.part18 (run context Program.part17 (run context Program.part16 (run context Program.part15 (run context Program.part14 (run context Program.part13 (run context Program.part12 (run context Program.part11 (run context Program.part10 (run context Program.part09 (run context Program.part08 (run context Program.part07 (run context Program.part06And (run context Program.part06 (run context Program.part05 (run context Program.part04 (run context Program.part03 (run context Program.part02 (run context Program.part01 (run context Program.part00 s))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  simp only [Program.operations, List.flatten_cons, List.flatten_nil, List.append_nil, run_append]

end Sha2.Proofs.Common.SHA512.Compression.Values

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
theorem run_correct (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant00 h block s) : invariant57 h block (run context Program.operations s) := by
  have result00 := part00 h block context _ input start
  have result01 := part01 h block context _ input result00
  have result02 := part02 h block context _ input result01
  have result03 := part03 h block context _ input constants result02
  have result04 := part04 h block context _ input result03
  have result05 := part05 h block context _ input constants result04
  have result06 := part06 h block context _ input constants result05
  have result06And := part06And h block context _ input result06
  have result07 := part07 h block context _ input result06And
  have result08 := part08 h block context _ input constants result07
  have result09 := part09 h block context _ input constants result08
  have result10 := part10 h block context _ input result09
  have result11 := part11 h block context _ input constants result10
  have result12 := part12 h block context _ input constants result11
  have result13 := part13 h block context _ input constants result12
  have result14 := part14 h block context _ input constants result13
  have result15 := part15 h block context _ input constants result14
  have result16 := part16 h block context _ input constants result15
  have result17 := part17 h block context _ input constants result16
  have result18 := part18 h block context _ input constants result17
  have result19 := part19 h block context _ input constants result18
  have result20Prefix10 := part20Prefix10 h block context _ input result19
  have result20Remainder := part20Remainder h block context _ input constants result20Prefix10
  have result21 := part21 h block context _ input result20Remainder
  have result22 := part22 h block context _ input constants result21
  have result23 := part23 h block context _ input constants result22
  have result24 := part24 h block context _ input constants result23
  have result25 := part25 h block context _ input constants result24
  have result26 := part26 h block context _ input constants result25
  have result27 := part27 h block context _ input constants result26
  have result28 := part28 h block context _ input constants result27
  have result29 := part29 h block context _ input constants result28
  have result30 := part30 h block context _ input constants result29
  have result31 := part31 h block context _ input constants result30
  have result32 := part32 h block context _ input constants result31
  have result33 := part33 h block context _ input constants result32
  have result34 := part34 h block context _ input constants result33
  have result35 := part35 h block context _ input constants result34
  have result36 := part36 h block context _ input constants result35
  have result37 := part37 h block context _ input constants result36
  have result38 := part38 h block context _ input constants result37
  have result39 := part39 h block context _ input constants result38
  have result40 := part40 h block context _ input constants result39
  have result41 := part41 h block context _ input constants result40
  have result42 := part42 h block context _ input constants result41
  have result43 := part43 h block context _ input constants result42
  have result44 := part44 h block context _ input constants result43
  have result45 := part45 h block context _ input constants result44
  have result46 := part46 h block context _ input constants result45
  have result47 := part47 h block context _ input constants result46
  have result48 := part48 h block context _ input constants result47
  have result49 := part49 h block context _ input constants result48
  have result50 := part50 h block context _ input constants result49
  have result51 := part51 h block context _ input constants result50
  have result52 := part52 h block context _ input constants result51
  have result53 := part53 h block context _ input constants result52
  have result54 := part54 h block context _ input result53
  have result55 := part55 h block context _ input result54
  have result56 := part56 h block context _ input result55
  simpa only [Program.operations, List.flatten_cons, List.flatten_nil, List.append_nil, run_append] using result56

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
