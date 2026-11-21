import K256.Proofs.Generate.Generator.Multiply.AddExecution.Frame.Segment

namespace K256.Proofs.Generate.Generator.Multiply.AddFrame

open K256.Proofs.Generate.LIR

open Lean Elab Tactic in
elab "add_body_range " lo:num " through " hi:num : tactic => do
  let rec prove (lo hi : Nat) (fuel : Nat) : TacticM Unit := do
    match fuel with
    | 0 => throwError "empty addition block range"
    | fuel + 1 =>
      if hi == lo + 1 then evalTactic (← `(tactic| add_body_segment))
      else
        let mid := (lo + hi) / 2
        let block := mkIdent (`K256.Proofs.Generate.LIR ++ Name.mkSimple s!"b_l10a410_{mid}")
        evalTactic (← `(tactic| apply BodySegment.trans (c := $block)))
        focus <| prove lo mid fuel
        prove mid hi fuel
  prove lo.getNat hi.getNat (hi.getNat - lo.getNat)

set_option maxHeartbeats 3000000 in
private theorem body27 : BodySegment b_l10a410_27 b_l10a410_35 := by
  add_body_range 27 through 35

set_option maxHeartbeats 3000000 in
private theorem body35 : BodySegment b_l10a410_35 b_l10a410_43 := by
  add_body_range 35 through 43

set_option maxHeartbeats 3000000 in
private theorem body43 : BodySegment b_l10a410_43 b_l10a410_51 := by
  add_body_range 43 through 51

set_option maxHeartbeats 3000000 in
private theorem body51 : BodySegment b_l10a410_51 b_l10a410_59 := by
  add_body_range 51 through 59

set_option maxHeartbeats 3000000 in
private theorem body59 : BodySegment b_l10a410_59 b_l10a410_67 := by
  add_body_range 59 through 67

set_option maxHeartbeats 3000000 in
private theorem body67 : BodySegment b_l10a410_67 b_l10a410_75 := by
  add_body_range 67 through 75

set_option maxHeartbeats 3000000 in
private theorem body75 : BodySegment b_l10a410_75 b_l10a410_83 := by
  add_body_range 75 through 83

set_option maxHeartbeats 3000000 in
private theorem body83 : BodySegment b_l10a410_83 b_l10a410_91 := by
  add_body_range 83 through 91

set_option maxHeartbeats 3000000 in
private theorem body91 : BodySegment b_l10a410_91 b_l10a410_99 := by
  add_body_range 91 through 99

set_option maxHeartbeats 3000000 in
private theorem body99 : BodySegment b_l10a410_99 b_l10a410_107 := by
  add_body_range 99 through 107

set_option maxHeartbeats 3000000 in
private theorem body107 : BodySegment b_l10a410_107 b_l10a410_115 := by
  add_body_range 107 through 115

set_option maxHeartbeats 3000000 in
private theorem body115 : BodySegment b_l10a410_115 b_l10a410_123 := by
  add_body_range 115 through 123

set_option maxHeartbeats 3000000 in
private theorem body123 : BodySegment b_l10a410_123 b_l10a410_131 := by
  add_body_range 123 through 131

set_option maxHeartbeats 3000000 in
private theorem body131 : BodySegment b_l10a410_131 b_l10a410_139 := by
  add_body_range 131 through 139

set_option maxHeartbeats 3000000 in
private theorem body139 : BodySegment b_l10a410_139 b_l10a410_147 := by
  add_body_range 139 through 147

set_option maxHeartbeats 3000000 in
private theorem body147 : BodySegment b_l10a410_147 b_l10a410_155 := by
  add_body_range 147 through 155

set_option maxHeartbeats 3000000 in
private theorem body155 : BodySegment b_l10a410_155 b_l10a410_160 := by
  add_body_range 155 through 160

theorem body : BodySegment b_l10a410_27 b_l10a410_160 :=
  body27.trans <|
    body35.trans <|
    body43.trans <|
    body51.trans <|
    body59.trans <|
    body67.trans <|
    body75.trans <|
    body83.trans <|
    body91.trans <|
    body99.trans <|
    body107.trans <|
    body115.trans <|
    body123.trans <|
    body131.trans <|
    body139.trans <|
    body147.trans <|
    body155

end K256.Proofs.Generate.Generator.Multiply.AddFrame
