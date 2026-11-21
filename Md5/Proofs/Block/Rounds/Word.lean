import Md5.Proofs.Block.Rounds.Algebra

namespace Md5.Proofs.Block.Rounds

inductive WordLocation where
  | reg (index : Nat)
  | stack (offset : Nat)
  | input (index : Nat)
  deriving DecidableEq, Repr

abbrev WordState := WordLocation → BitVec 32

inductive WordSource where
  | location (loc : WordLocation)
  | immediate (value : BitVec 32)
  deriving DecidableEq, Repr

def WordSource.read (s : WordState) : WordSource → BitVec 32
  | .location loc => s loc
  | .immediate value => value

inductive WordInstruction where
  | mov (dst : WordLocation) (src : WordSource)
  | add (dst : WordLocation) (src : WordSource)
  | and (dst : WordLocation) (src : WordSource)
  | or (dst : WordLocation) (src : WordSource)
  | xor (dst : WordLocation) (src : WordSource)
  | not (dst : WordLocation)
  | rol (dst : WordLocation) (amount : Nat)
  | lea (dst left right : WordLocation)
  deriving DecidableEq, Repr

def WordState.write (s : WordState) (loc : WordLocation) (value : BitVec 32) : WordState :=
  fun q ↦ if q = loc then value else s q

def WordInstruction.execute (s : WordState) : WordInstruction → WordState
  | .mov dst src => s.write dst (src.read s)
  | .add dst src => s.write dst (s dst + src.read s)
  | .and dst src => s.write dst (s dst &&& src.read s)
  | .or dst src => s.write dst (s dst ||| src.read s)
  | .xor dst src => s.write dst (s dst ^^^ src.read s)
  | .not dst => s.write dst (~~~s dst)
  | .rol dst amount => s.write dst ((s dst).rotateLeft amount)
  | .lea dst left right => s.write dst (s left + s right)

theorem WordInstruction.execute_mov (s : WordState) (dst loc : WordLocation)
    (src : WordSource) :
    WordInstruction.execute s (.mov dst src) loc =
      if loc = dst then src.read s else s loc := rfl

theorem WordInstruction.execute_add (s : WordState) (dst loc : WordLocation)
    (src : WordSource) :
    WordInstruction.execute s (.add dst src) loc =
      if loc = dst then s dst + src.read s else s loc := rfl

theorem WordInstruction.execute_and (s : WordState) (dst loc : WordLocation)
    (src : WordSource) :
    WordInstruction.execute s (.and dst src) loc =
      if loc = dst then s dst &&& src.read s else s loc := rfl

theorem WordInstruction.execute_or (s : WordState) (dst loc : WordLocation)
    (src : WordSource) :
    WordInstruction.execute s (.or dst src) loc =
      if loc = dst then s dst ||| src.read s else s loc := rfl

theorem WordInstruction.execute_xor (s : WordState) (dst loc : WordLocation)
    (src : WordSource) :
    WordInstruction.execute s (.xor dst src) loc =
      if loc = dst then s dst ^^^ src.read s else s loc := rfl

theorem WordInstruction.execute_not (s : WordState) (dst loc : WordLocation)
     :
    WordInstruction.execute s (.not dst) loc =
      if loc = dst then ~~~s dst else s loc := rfl

theorem WordInstruction.execute_rol (s : WordState) (dst loc : WordLocation)
    (amount : Nat) :
    WordInstruction.execute s (.rol dst amount) loc =
      if loc = dst then (s dst).rotateLeft amount else s loc := rfl

theorem WordInstruction.execute_lea (s : WordState) (dst loc : WordLocation)
    (left right : WordLocation) :
    WordInstruction.execute s (.lea dst left right) loc =
      if loc = dst then s left + s right else s loc := rfl

attribute [irreducible] WordInstruction.execute

def executeWords (code : List WordInstruction) (s : WordState) : WordState :=
  code.foldl WordInstruction.execute s

theorem executeWords_append (left right : List WordInstruction) (s : WordState) :
    executeWords (left ++ right) s = executeWords right (executeWords left s) :=
  List.foldl_append

attribute [irreducible] executeWords

theorem executeWords_nil (s : WordState) : executeWords [] s = s := by
  with_unfolding_all rfl

theorem executeWords_cons (instruction : WordInstruction) (code : List WordInstruction)
    (s : WordState) :
    executeWords (instruction :: code) s = executeWords code (instruction.execute s) := by
  with_unfolding_all rfl

end Md5.Proofs.Block.Rounds
