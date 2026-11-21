import Md5.Proofs.Block.Rounds.Machine.First
import Md5.Proofs.Block.Rounds.Machine.Second
import Md5.Proofs.Block.Rounds.Machine.Third
import Md5.Proofs.Block.Rounds.Machine.Fourth

namespace Md5.Proofs.Block.Rounds

open X86 X86.Machine X86.UserProcess

set_option maxRecDepth 4096 in
theorem machine_rounds [Bindings] : RunWords 0x101be0 0x102427 wordProgram := by
  simpa only [wordProgram, List.append_assoc] using segment1_runs.seq (segment2_runs.seq (segment3_runs.seq
    (segment4_runs.seq (segment5_runs.seq (segment6_runs.seq (segment7_runs.seq (segment8_runs.seq
    (segment9_runs.seq (segment10_runs.seq (segment11_runs.seq (segment12_runs.seq
    (segment13_runs.seq (segment14_runs.seq (segment15_runs.seq (segment16_runs.seq
    (segment17_runs.seq (segment18_runs.seq (segment19_runs.seq (segment20_runs.seq
    (segment21_runs.seq (segment22_runs.seq (segment23_runs.seq (segment24_runs.seq
    (segment25_runs.seq (segment26_runs.seq (segment27_runs.seq (segment28_runs.seq
    (segment29_runs.seq (segment30_runs.seq (segment31_runs.seq (segment32_runs.seq
    (segment33_runs.seq (segment34_runs.seq (segment35_runs.seq (segment36_runs.seq
    (segment37_runs.seq (segment38_runs.seq (segment39_runs.seq (segment40_runs.seq
    (segment41_runs.seq (segment42_runs.seq (segment43_runs.seq (segment44_runs.seq
    (segment45_runs.seq (segment46_runs.seq (segment47_runs.seq (segment48_runs.seq
    (segment49_runs.seq (segment50_runs.seq (segment51_runs.seq (segment52_runs.seq
    (segment53_runs.seq (segment54_runs.seq (segment55_runs.seq (segment56_runs.seq
    (segment57_runs.seq (segment58_runs.seq (segment59_runs.seq (segment60_runs.seq
    (segment61_runs.seq (segment62_runs.seq (segment63_runs.seq
    (segment64_runs)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Md5.Proofs.Block.Rounds
