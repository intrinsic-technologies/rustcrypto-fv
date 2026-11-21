import P256.Proofs.SHA256.Interface
import P256.Proofs.SHA256.Compression.Values.Correctness.Part00
import P256.Proofs.SHA256.Compression.Values.Correctness.Part01
import P256.Proofs.SHA256.Compression.Values.Correctness.Part02
import P256.Proofs.SHA256.Compression.Values.Correctness.Part03
import P256.Proofs.SHA256.Compression.Values.Correctness.Part04
import P256.Proofs.SHA256.Compression.Values.Correctness.Part05
import P256.Proofs.SHA256.Compression.Values.Correctness.Part06
import P256.Proofs.SHA256.Compression.Values.Correctness.Part07
import P256.Proofs.SHA256.Compression.Values.Correctness.Part08
import P256.Proofs.SHA256.Compression.Values.Correctness.Part09
import P256.Proofs.SHA256.Compression.Values.Correctness.Part10
import P256.Proofs.SHA256.Compression.Values.Correctness.Part11
import P256.Proofs.SHA256.Compression.Values.Correctness.Part12
import P256.Proofs.SHA256.Compression.Values.Correctness.Part13
import P256.Proofs.SHA256.Compression.Values.Correctness.Part14
import P256.Proofs.SHA256.Compression.Values.Correctness.Part15
import P256.Proofs.SHA256.Compression.Values.Correctness.Part16
import P256.Proofs.SHA256.Compression.Values.Correctness.Part17
import P256.Proofs.SHA256.Compression.Values.Correctness.Part18
import P256.Proofs.SHA256.Compression.Values.Correctness.Part19
import P256.Proofs.SHA256.Compression.Values.Correctness.Part20
import P256.Proofs.SHA256.Compression.Values.Correctness.Part21
import P256.Proofs.SHA256.Compression.Values.Correctness.Part22
import P256.Proofs.SHA256.Compression.Values.Correctness.Part23
import P256.Proofs.SHA256.Compression.Values.Correctness.Part24
import P256.Proofs.SHA256.Compression.Values.Correctness.Part25
import P256.Proofs.SHA256.Compression.Values.Correctness.Part26
import P256.Proofs.SHA256.Compression.Values.Correctness.Part27
import P256.Proofs.SHA256.Compression.Values.Correctness.Part28
import P256.Proofs.SHA256.Compression.Values.Correctness.Part29
import P256.Proofs.SHA256.Compression.Values.Correctness.Part30
import P256.Proofs.SHA256.Compression.Values.Correctness.Part31
import P256.Proofs.SHA256.Compression.Values.Correctness.Part32
import P256.Proofs.SHA256.Compression.Values.Correctness.Part33
import P256.Proofs.SHA256.Compression.Values.Correctness.Part34
import P256.Proofs.SHA256.Compression.Values.Correctness.Part35
import P256.Proofs.SHA256.Compression.Values.Correctness.Part36
import P256.Proofs.SHA256.Compression.Values.Correctness.Part37
import P256.Proofs.SHA256.Compression.Values.Correctness.Part38
import P256.Proofs.SHA256.Compression.Values.Correctness.Part39
import P256.Proofs.SHA256.Compression.Values.Correctness.Part40
import P256.Proofs.SHA256.Compression.Values.Correctness.Part41
import P256.Proofs.SHA256.Compression.Values.Correctness.Part42
import P256.Proofs.SHA256.Compression.Values.Correctness.Part43
import P256.Proofs.SHA256.Compression.Values.Correctness.Part44
import P256.Proofs.SHA256.Compression.Values.Correctness.Part45
import P256.Proofs.SHA256.Compression.Values.Correctness.Part46
import P256.Proofs.SHA256.Compression.Values.Correctness.Part47
import P256.Proofs.SHA256.Compression.Values.Correctness.Part48
import P256.Proofs.SHA256.Compression.Values.Correctness.Part49
import P256.Proofs.SHA256.Compression.Values.Correctness.Part50
import P256.Proofs.SHA256.Compression.Values.Correctness.Part51
import P256.Proofs.SHA256.Compression.Values.Correctness.Part52
import P256.Proofs.SHA256.Compression.Values.Endpoints

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Values.Correctness

open P256.Proofs.Common.SHA256.Compression

open P256.Proofs.SHA256 Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem run_correct (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant00 h block s) : invariant53 h block (run context Program.operations s) := by
  have result00 := part00 h block context s input start
  have result01 := part01 h block context _ input result00
  have result02 := part02 h block context _ input result01
  have result03 := part03 h block context _ input result02
  have result04 := part04 h block context _ input result03
  have result05 := part05 h block context _ input result04
  have result06 := part06 h block context _ input result05
  have result07 := part07 h block context _ input result06
  have result08 := part08 h block context _ input result07
  have result09 := part09 h block context _ input result08
  have result10 := part10 h block context _ input result09
  have result11 := part11 h block context _ input result10
  have result12 := part12 h block context _ input result11
  have result13 := part13 h block context _ input result12
  have result14 := part14 h block context _ input result13
  have result15 := part15 h block context _ input result14
  have result16 := part16 h block context _ input result15
  have result17 := part17 h block context _ input result16
  have result18 := part18 h block context _ input result17
  have result19 := part19 h block context _ input result18
  have result20 := part20 h block context _ input result19
  have result21 := part21 h block context _ input result20
  have result22 := part22 h block context _ input result21
  have result23 := part23 h block context _ input result22
  have result24 := part24 h block context _ input result23
  have result25 := part25 h block context _ input result24
  have result26 := part26 h block context _ input result25
  have result27 := part27 h block context _ input result26
  have result28 := part28 h block context _ input result27
  have result29 := part29 h block context _ input result28
  have result30 := part30 h block context _ input result29
  have result31 := part31 h block context _ input result30
  have result32 := part32 h block context _ input result31
  have result33 := part33 h block context _ input result32
  have result34 := part34 h block context _ input result33
  have result35 := part35 h block context _ input result34
  have result36 := part36 h block context _ input result35
  have result37 := part37 h block context _ input result36
  have result38 := part38 h block context _ input result37
  have result39 := part39 h block context _ input result38
  have result40 := part40 h block context _ input result39
  have result41 := part41 h block context _ input result40
  have result42 := part42 h block context _ input result41
  have result43 := part43 h block context _ input result42
  have result44 := part44 h block context _ input result43
  have result45 := part45 h block context _ input result44
  have result46 := part46 h block context _ input result45
  have result47 := part47 h block context _ input result46
  have result48 := part48 h block context _ input result47
  have result49 := part49 h block context _ input result48
  have result50 := part50 h block context _ input result49
  have result51 := part51 h block context _ input result50
  have result52 := part52 h block context _ input result51
  simpa only [Program.operations, run_append] using result52

theorem hashState_correct {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (registers : RegistersAt initial hash)
    (bytes : (registerRegion initial .rsi 64).HasBytes initial.external block) :
    hashState (run (contextOfRam initial) Program.operations (ofRam initial)) =
      BitVecState.ofState (P256.Proofs.SHA256.State.ofArray (Reference.compress hash (Standards.NIST.SHA2.bytesToBits block))) := by
  apply compress_of_invariant53
  exact run_correct _ _ _ _ (input_words_of_bytes bytes)
    (invariant00_of_hashState _ (hashState_ofRam registers))

end P256.Proofs.SHA256.Compression.Values.Correctness
