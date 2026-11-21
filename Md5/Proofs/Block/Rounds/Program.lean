import Md5.Proofs.Block.Rounds.Fourth
import Md5.Proofs.Block.Rounds.Schedule

namespace Md5.Proofs.Block.Rounds

open Standards.RFC.MD5

def wordProgram : List WordInstruction :=
  segment1 ++
  segment2 ++
  segment3 ++
  segment4 ++
  segment5 ++
  segment6 ++
  segment7 ++
  segment8 ++
  segment9 ++
  segment10 ++
  segment11 ++
  segment12 ++
  segment13 ++
  segment14 ++
  segment15 ++
  segment16 ++
  segment17 ++
  segment18 ++
  segment19 ++
  segment20 ++
  segment21 ++
  segment22 ++
  segment23 ++
  segment24 ++
  segment25 ++
  segment26 ++
  segment27 ++
  segment28 ++
  segment29 ++
  segment30 ++
  segment31 ++
  segment32 ++
  segment33 ++
  segment34 ++
  segment35 ++
  segment36 ++
  segment37 ++
  segment38 ++
  segment39 ++
  segment40 ++
  segment41 ++
  segment42 ++
  segment43 ++
  segment44 ++
  segment45 ++
  segment46 ++
  segment47 ++
  segment48 ++
  segment49 ++
  segment50 ++
  segment51 ++
  segment52 ++
  segment53 ++
  segment54 ++
  segment55 ++
  segment56 ++
  segment57 ++
  segment58 ++
  segment59 ++
  segment60 ++
  segment61 ++
  segment62 ++
  segment63 ++
  segment64

set_option maxRecDepth 4096 in
theorem wordProgram_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (s : WordState) (h : Invariant0 initial X initial s) :
    Invariant64 initial X (runSchedule initial X) (executeWords wordProgram s) := by
  have h1 := segment1_correct initial X _ _ h
  have h2 := segment2_correct initial X _ _ h1
  have h3 := segment3_correct initial X _ _ h2
  have h4 := segment4_correct initial X _ _ h3
  have h5 := segment5_correct initial X _ _ h4
  have h6 := segment6_correct initial X _ _ h5
  have h7 := segment7_correct initial X _ _ h6
  have h8 := segment8_correct initial X _ _ h7
  have h9 := segment9_correct initial X _ _ h8
  have h10 := segment10_correct initial X _ _ h9
  have h11 := segment11_correct initial X _ _ h10
  have h12 := segment12_correct initial X _ _ h11
  have h13 := segment13_correct initial X _ _ h12
  have h14 := segment14_correct initial X _ _ h13
  have h15 := segment15_correct initial X _ _ h14
  have h16 := segment16_correct initial X _ _ h15
  have h17 := segment17_correct initial X _ _ h16
  have h18 := segment18_correct initial X _ _ h17
  have h19 := segment19_correct initial X _ _ h18
  have h20 := segment20_correct initial X _ _ h19
  have h21 := segment21_correct initial X _ _ h20
  have h22 := segment22_correct initial X _ _ h21
  have h23 := segment23_correct initial X _ _ h22
  have h24 := segment24_correct initial X _ _ h23
  have h25 := segment25_correct initial X _ _ h24
  have h26 := segment26_correct initial X _ _ h25
  have h27 := segment27_correct initial X _ _ h26
  have h28 := segment28_correct initial X _ _ h27
  have h29 := segment29_correct initial X _ _ h28
  have h30 := segment30_correct initial X _ _ h29
  have h31 := segment31_correct initial X _ _ h30
  have h32 := segment32_correct initial X _ _ h31
  have h33 := segment33_correct initial X _ _ h32
  have h34 := segment34_correct initial X _ _ h33
  have h35 := segment35_correct initial X _ _ h34
  have h36 := segment36_correct initial X _ _ h35
  have h37 := segment37_correct initial X _ _ h36
  have h38 := segment38_correct initial X _ _ h37
  have h39 := segment39_correct initial X _ _ h38
  have h40 := segment40_correct initial X _ _ h39
  have h41 := segment41_correct initial X _ _ h40
  have h42 := segment42_correct initial X _ _ h41
  have h43 := segment43_correct initial X _ _ h42
  have h44 := segment44_correct initial X _ _ h43
  have h45 := segment45_correct initial X _ _ h44
  have h46 := segment46_correct initial X _ _ h45
  have h47 := segment47_correct initial X _ _ h46
  have h48 := segment48_correct initial X _ _ h47
  have h49 := segment49_correct initial X _ _ h48
  have h50 := segment50_correct initial X _ _ h49
  have h51 := segment51_correct initial X _ _ h50
  have h52 := segment52_correct initial X _ _ h51
  have h53 := segment53_correct initial X _ _ h52
  have h54 := segment54_correct initial X _ _ h53
  have h55 := segment55_correct initial X _ _ h54
  have h56 := segment56_correct initial X _ _ h55
  have h57 := segment57_correct initial X _ _ h56
  have h58 := segment58_correct initial X _ _ h57
  have h59 := segment59_correct initial X _ _ h58
  have h60 := segment60_correct initial X _ _ h59
  have h61 := segment61_correct initial X _ _ h60
  have h62 := segment62_correct initial X _ _ h61
  have h63 := segment63_correct initial X _ _ h62
  have h64 := segment64_correct initial X _ _ h63
  simpa only [wordProgram, executeWords_append, runSchedule, schedule,
    List.foldl_cons, List.foldl_nil] using h64

def readWordBuffer (s : WordState) : Buffer :=
  ⟨s (.reg 1), s (.reg 8), s (.reg 2), s (.reg 0)⟩

theorem wordProgram_processBlock (initial : Buffer) (X : Vector (BitVec 32) 16)
    (s : WordState) (h : Invariant0 initial X initial s) :
    readWordBuffer (executeWords wordProgram s) = processBlock initial X := by
  obtain ⟨hD, hA, hC, hB⟩ := wordProgram_correct initial X s h
  rw [processBlock_eq_runSchedule]
  simp only [readWordBuffer, feedForward, hD, hA, hC, hB, BitVec.add_comm]

end Md5.Proofs.Block.Rounds
