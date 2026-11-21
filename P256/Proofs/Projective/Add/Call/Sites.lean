import P256.Proofs.Projective.Add.Call.Binary
import P256.Proofs.Projective.Add.Call.Unary

set_option autoImplicit false

namespace P256.Proofs.Projective.Add.Call

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure UnaryCallSite (entry : BitVec 64) (reserve : Nat) where
  codeOffset : Nat
  disp : BitVec 32
  codeBound : codeOffset + 5 < 118431
  bytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp
  target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 5 (disp.signExtend 64) = entry
  entryLow : entry.toNat < 2^32
  entryProgram : InProgram entry
  layout : StackCallLayout 920 32 32 reserve
  stack : layout.stackOffset = 640
  outputSaved : 80 ≤ layout.outputOffset

namespace Sites

def call_102f0c : BinaryCallSite 0x113890 280 where
  codeOffset := 0x525c
  disp := 0xe62f
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨640, 592, 560, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_102f6b : BinaryCallSite 0x113890 280 where
  codeOffset := 0x52bb
  disp := 0xe5d0
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨640, 592, 464, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_102fca : BinaryCallSite 0x113890 280 where
  codeOffset := 0x531a
  disp := 0xe571
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨640, 592, 528, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_10302b : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x537b
  disp := 0xe440
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 592, 80, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_10308c : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x53dc
  disp := 0xe3df
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 592, 496, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1030a2 : BinaryCallSite 0x113890 280 where
  codeOffset := 0x53f2
  disp := 0xe499
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨640, 80, 432, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 496
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_103118 : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x5468
  disp := 0xe353
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 592, 496, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_10312b : BinaryCallSite 0x1137e0 24 where
  codeOffset := 0x547b
  disp := 0xe360
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137e0 (by decide)
  layout := ⟨640, 432, 400, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 496
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_10318d : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x54dd
  disp := 0xe2de
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 592, 80, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1031ef : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x553f
  disp := 0xe27c
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 592, 496, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_103205 : BinaryCallSite 0x113890 280 where
  codeOffset := 0x5555
  disp := 0xe336
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨640, 80, 432, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 496
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_10327e : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x55ce
  disp := 0xe1ed
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 624, 496, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 592
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_103291 : BinaryCallSite 0x1137e0 24 where
  codeOffset := 0x55e1
  disp := 0xe1fa
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137e0 (by decide)
  layout := ⟨640, 432, 368, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 496
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1032f2 : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x5642
  disp := 0xe179
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 592, 80, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_103353 : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x56a3
  disp := 0xe118
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 592, 496, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_103369 : BinaryCallSite 0x113890 280 where
  codeOffset := 0x56b9
  disp := 0xe1d2
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨640, 80, 432, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 496
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1033d6 : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x5726
  disp := 0xe095
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 592, 496, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1033e9 : BinaryCallSite 0x1137e0 24 where
  codeOffset := 0x5739
  disp := 0xe0a2
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137e0 (by decide)
  layout := ⟨640, 432, 336, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 496
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_10346a : BinaryCallSite 0x113890 280 where
  codeOffset := 0x57ba
  disp := 0xe0d1
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨640, 624, 496, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 592
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1034b6 : BinaryCallSite 0x1137e0 24 where
  codeOffset := 0x5806
  disp := 0xdfd5
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137e0 (by decide)
  layout := ⟨640, 624, 240, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 496
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1034c6 : UnaryCallSite 0x1137f0 16 where
  codeOffset := 0x5816
  disp := 0xdfd5
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137f0 (by decide)
  layout := ⟨640, 240, 592, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide

def call_103512 : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x5862
  disp := 0xdf59
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 592, 208, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_103591 : BinaryCallSite 0x1137e0 24 where
  codeOffset := 0x58e1
  disp := 0xdefa
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137e0 (by decide)
  layout := ⟨640, 592, 304, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1035a9 : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x58f9
  disp := 0xdec2
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 464, 272, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 208
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1035b9 : UnaryCallSite 0x1137f0 16 where
  codeOffset := 0x5909
  disp := 0xdee2
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137f0 (by decide)
  layout := ⟨640, 528, 592, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide

def call_1035fc : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x594c
  disp := 0xde6f
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 592, 176, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_10364b : BinaryCallSite 0x113890 280 where
  codeOffset := 0x599b
  disp := 0xdef0
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨640, 624, 80, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 336
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1036c1 : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x5a11
  disp := 0xddaa
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 624, 496, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 592
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1036d7 : BinaryCallSite 0x1137e0 24 where
  codeOffset := 0x5a27
  disp := 0xddb4
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137e0 (by decide)
  layout := ⟨640, 80, 144, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 496
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1036e7 : UnaryCallSite 0x1137f0 16 where
  codeOffset := 0x5a37
  disp := 0xddb4
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137f0 (by decide)
  layout := ⟨640, 144, 592, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide

def call_103733 : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x5a83
  disp := 0xdd38
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 592, 112, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_103745 : UnaryCallSite 0x1137f0 16 where
  codeOffset := 0x5a95
  disp := 0xdd56
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137f0 (by decide)
  layout := ⟨640, 560, 592, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide

def call_103785 : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x5ad5
  disp := 0xdce6
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 592, 496, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_10379b : BinaryCallSite 0x1137e0 24 where
  codeOffset := 0x5aeb
  disp := 0xdcf0
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137e0 (by decide)
  layout := ⟨640, 496, 432, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 176
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_10381d : BinaryCallSite 0x113890 280 where
  codeOffset := 0x5b6d
  disp := 0xdd1e
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨640, 592, 80, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_10389f : BinaryCallSite 0x113890 280 where
  codeOffset := 0x5bef
  disp := 0xdc9c
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨640, 592, 496, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1038af : BinaryCallSite 0x1137e0 24 where
  codeOffset := 0x5bff
  disp := 0xdbdc
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137e0 (by decide)
  layout := ⟨640, 80, 624, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 496
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_103923 : BinaryCallSite 0x113890 280 where
  codeOffset := 0x5c73
  disp := 0xdc18
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨640, 272, 496, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_10396c : BinaryCallSite 0x113890 280 where
  codeOffset := 0x5cbc
  disp := 0xdbcf
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨640, 624, 592, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 112
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_10397c : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x5ccc
  disp := 0xdaef
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 496, 624, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 592
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1039bd : BinaryCallSite 0x113890 280 where
  codeOffset := 0x5d0d
  disp := 0xdb7e
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨640, 304, 592, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 368
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1039d5 : BinaryCallSite 0x113890 280 where
  codeOffset := 0x5d25
  disp := 0xdb66
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x13890 (by decide)
  layout := ⟨640, 400, 624, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 432
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def call_1039e8 : BinaryCallSite 0x1137c0 16 where
  codeOffset := 0x5d38
  disp := 0xda83
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x137c0 (by decide)
  layout := ⟨640, 592, 496, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 624
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

end Sites

end P256.Proofs.Projective.Add.Call
