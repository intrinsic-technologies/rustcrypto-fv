import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part00
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part01
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part02
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part03
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part04
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part05
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part06
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part07
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part08
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part09
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part10
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part11
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part12
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part13
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part14
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part15
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part16
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part17
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part18
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part19
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part20
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part21
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part22
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part23
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part24
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part25
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part26
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part27
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part28
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part29
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part30
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part31
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part32
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part33
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part34
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part35
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part36
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part37
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part38
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part39
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part40
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part41
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part42
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part43
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part44
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part45
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part46
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part47
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part48
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part49
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part50
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part51
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part52

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open Hkdf.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine

def instructions [Bindings] : List CheckedInstruction :=
  part00 ++ (part01 ++ (part02 ++ (part03 ++ (part04 ++ (part05 ++ (part06 ++ (part07 ++ (part08 ++ (part09 ++ (part10 ++ (part11 ++ (part12 ++ (part13 ++ (part14 ++ (part15 ++ (part16 ++ (part17 ++ (part18 ++ (part19 ++ (part20 ++ (part21 ++ (part22 ++ (part23 ++ (part24 ++ (part25 ++ (part26 ++ (part27 ++ (part28 ++ (part29 ++ (part30 ++ (part31 ++ (part32 ++ (part33 ++ (part34 ++ (part35 ++ (part36 ++ (part37 ++ (part38 ++ (part39 ++ (part40 ++ (part41 ++ (part42 ++ (part43 ++ (part44 ++ (part45 ++ (part46 ++ (part47 ++ (part48 ++ (part49 ++ (part50 ++ (part51 ++ (part52))))))))))))))))))))))))))))))))))))))))))))))))))))

def instructionsBytes : List UInt8 :=
  part00Bytes ++ (part01Bytes ++ (part02Bytes ++ (part03Bytes ++ (part04Bytes ++ (part05Bytes ++ (part06Bytes ++ (part07Bytes ++ (part08Bytes ++ (part09Bytes ++ (part10Bytes ++ (part11Bytes ++ (part12Bytes ++ (part13Bytes ++ (part14Bytes ++ (part15Bytes ++ (part16Bytes ++ (part17Bytes ++ (part18Bytes ++ (part19Bytes ++ (part20Bytes ++ (part21Bytes ++ (part22Bytes ++ (part23Bytes ++ (part24Bytes ++ (part25Bytes ++ (part26Bytes ++ (part27Bytes ++ (part28Bytes ++ (part29Bytes ++ (part30Bytes ++ (part31Bytes ++ (part32Bytes ++ (part33Bytes ++ (part34Bytes ++ (part35Bytes ++ (part36Bytes ++ (part37Bytes ++ (part38Bytes ++ (part39Bytes ++ (part40Bytes ++ (part41Bytes ++ (part42Bytes ++ (part43Bytes ++ (part44Bytes ++ (part45Bytes ++ (part46Bytes ++ (part47Bytes ++ (part48Bytes ++ (part49Bytes ++ (part50Bytes ++ (part51Bytes ++ (part52Bytes))))))))))))))))))))))))))))))))))))))))))))))))))))

def instructionsLayout : List (BitVec 64 × Nat) :=
  part00Layout ++ (part01Layout ++ (part02Layout ++ (part03Layout ++ (part04Layout ++ (part05Layout ++ (part06Layout ++ (part07Layout ++ (part08Layout ++ (part09Layout ++ (part10Layout ++ (part11Layout ++ (part12Layout ++ (part13Layout ++ (part14Layout ++ (part15Layout ++ (part16Layout ++ (part17Layout ++ (part18Layout ++ (part19Layout ++ (part20Layout ++ (part21Layout ++ (part22Layout ++ (part23Layout ++ (part24Layout ++ (part25Layout ++ (part26Layout ++ (part27Layout ++ (part28Layout ++ (part29Layout ++ (part30Layout ++ (part31Layout ++ (part32Layout ++ (part33Layout ++ (part34Layout ++ (part35Layout ++ (part36Layout ++ (part37Layout ++ (part38Layout ++ (part39Layout ++ (part40Layout ++ (part41Layout ++ (part42Layout ++ (part43Layout ++ (part44Layout ++ (part45Layout ++ (part46Layout ++ (part47Layout ++ (part48Layout ++ (part49Layout ++ (part50Layout ++ (part51Layout ++ (part52Layout))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem instructions_layout [Bindings] : InstructionTrace.layout instructions = instructionsLayout := by
  exact InstructionTrace.layout_append_eq part00_layout (InstructionTrace.layout_append_eq part01_layout (InstructionTrace.layout_append_eq part02_layout (InstructionTrace.layout_append_eq part03_layout (InstructionTrace.layout_append_eq part04_layout (InstructionTrace.layout_append_eq part05_layout (InstructionTrace.layout_append_eq part06_layout (InstructionTrace.layout_append_eq part07_layout (InstructionTrace.layout_append_eq part08_layout (InstructionTrace.layout_append_eq part09_layout (InstructionTrace.layout_append_eq part10_layout (InstructionTrace.layout_append_eq part11_layout (InstructionTrace.layout_append_eq part12_layout (InstructionTrace.layout_append_eq part13_layout (InstructionTrace.layout_append_eq part14_layout (InstructionTrace.layout_append_eq part15_layout (InstructionTrace.layout_append_eq part16_layout (InstructionTrace.layout_append_eq part17_layout (InstructionTrace.layout_append_eq part18_layout (InstructionTrace.layout_append_eq part19_layout (InstructionTrace.layout_append_eq part20_layout (InstructionTrace.layout_append_eq part21_layout (InstructionTrace.layout_append_eq part22_layout (InstructionTrace.layout_append_eq part23_layout (InstructionTrace.layout_append_eq part24_layout (InstructionTrace.layout_append_eq part25_layout (InstructionTrace.layout_append_eq part26_layout (InstructionTrace.layout_append_eq part27_layout (InstructionTrace.layout_append_eq part28_layout (InstructionTrace.layout_append_eq part29_layout (InstructionTrace.layout_append_eq part30_layout (InstructionTrace.layout_append_eq part31_layout (InstructionTrace.layout_append_eq part32_layout (InstructionTrace.layout_append_eq part33_layout (InstructionTrace.layout_append_eq part34_layout (InstructionTrace.layout_append_eq part35_layout (InstructionTrace.layout_append_eq part36_layout (InstructionTrace.layout_append_eq part37_layout (InstructionTrace.layout_append_eq part38_layout (InstructionTrace.layout_append_eq part39_layout (InstructionTrace.layout_append_eq part40_layout (InstructionTrace.layout_append_eq part41_layout (InstructionTrace.layout_append_eq part42_layout (InstructionTrace.layout_append_eq part43_layout (InstructionTrace.layout_append_eq part44_layout (InstructionTrace.layout_append_eq part45_layout (InstructionTrace.layout_append_eq part46_layout (InstructionTrace.layout_append_eq part47_layout (InstructionTrace.layout_append_eq part48_layout (InstructionTrace.layout_append_eq part49_layout (InstructionTrace.layout_append_eq part50_layout (InstructionTrace.layout_append_eq part51_layout (part52_layout))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 8192 in
theorem instructions_ordered [Bindings] : InstructionTrace.ordered 0x109610 instructions = true := by
  rw [InstructionTrace.ordered_eq_layout, instructions_layout]
  decide +kernel

theorem instructions_bytes [Bindings] :
    instructions.flatMap CheckedInstruction.bytes = instructionsBytes := by
  exact InstructionTrace.bytes_append_eq part00_bytes (InstructionTrace.bytes_append_eq part01_bytes (InstructionTrace.bytes_append_eq part02_bytes (InstructionTrace.bytes_append_eq part03_bytes (InstructionTrace.bytes_append_eq part04_bytes (InstructionTrace.bytes_append_eq part05_bytes (InstructionTrace.bytes_append_eq part06_bytes (InstructionTrace.bytes_append_eq part07_bytes (InstructionTrace.bytes_append_eq part08_bytes (InstructionTrace.bytes_append_eq part09_bytes (InstructionTrace.bytes_append_eq part10_bytes (InstructionTrace.bytes_append_eq part11_bytes (InstructionTrace.bytes_append_eq part12_bytes (InstructionTrace.bytes_append_eq part13_bytes (InstructionTrace.bytes_append_eq part14_bytes (InstructionTrace.bytes_append_eq part15_bytes (InstructionTrace.bytes_append_eq part16_bytes (InstructionTrace.bytes_append_eq part17_bytes (InstructionTrace.bytes_append_eq part18_bytes (InstructionTrace.bytes_append_eq part19_bytes (InstructionTrace.bytes_append_eq part20_bytes (InstructionTrace.bytes_append_eq part21_bytes (InstructionTrace.bytes_append_eq part22_bytes (InstructionTrace.bytes_append_eq part23_bytes (InstructionTrace.bytes_append_eq part24_bytes (InstructionTrace.bytes_append_eq part25_bytes (InstructionTrace.bytes_append_eq part26_bytes (InstructionTrace.bytes_append_eq part27_bytes (InstructionTrace.bytes_append_eq part28_bytes (InstructionTrace.bytes_append_eq part29_bytes (InstructionTrace.bytes_append_eq part30_bytes (InstructionTrace.bytes_append_eq part31_bytes (InstructionTrace.bytes_append_eq part32_bytes (InstructionTrace.bytes_append_eq part33_bytes (InstructionTrace.bytes_append_eq part34_bytes (InstructionTrace.bytes_append_eq part35_bytes (InstructionTrace.bytes_append_eq part36_bytes (InstructionTrace.bytes_append_eq part37_bytes (InstructionTrace.bytes_append_eq part38_bytes (InstructionTrace.bytes_append_eq part39_bytes (InstructionTrace.bytes_append_eq part40_bytes (InstructionTrace.bytes_append_eq part41_bytes (InstructionTrace.bytes_append_eq part42_bytes (InstructionTrace.bytes_append_eq part43_bytes (InstructionTrace.bytes_append_eq part44_bytes (InstructionTrace.bytes_append_eq part45_bytes (InstructionTrace.bytes_append_eq part46_bytes (InstructionTrace.bytes_append_eq part47_bytes (InstructionTrace.bytes_append_eq part48_bytes (InstructionTrace.bytes_append_eq part49_bytes (InstructionTrace.bytes_append_eq part50_bytes (InstructionTrace.bytes_append_eq part51_bytes (part52_bytes))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 16384 in
theorem instructionsBytes_length : instructionsBytes.length = 10114 := by
  decide +kernel

theorem instructions_source :
    Extracted.textBytes.toListFrom 0x9610 10114 = instructionsBytes := by
  change Extracted.textBytes.toListFrom 0x9610 (203 + (212 + (211 + (203 + (195 + (179 + (173 + (179 + (180 + (186 + (187 + (200 + (228 + (228 + (238 + (199 + (196 + (193 + (194 + (193 + (187 + (215 + (205 + (210 + (186 + (177 + (185 + (183 + (184 + (185 + (176 + (187 + (208 + (215 + (201 + (215 + (209 + (180 + (180 + (184 + (182 + (189 + (186 + (186 + (181 + (180 + (176 + (192 + (201 + (193 + (171 + (221 + (7))))))))))))))))))))))))))))))))))))))))))))))))))))) = _
  simp only [chunked_toListFrom_append]
  simp only [Nat.reduceAdd, instructionsBytes,
    part00_source,
    part01_source,
    part02_source,
    part03_source,
    part04_source,
    part05_source,
    part06_source,
    part07_source,
    part08_source,
    part09_source,
    part10_source,
    part11_source,
    part12_source,
    part13_source,
    part14_source,
    part15_source,
    part16_source,
    part17_source,
    part18_source,
    part19_source,
    part20_source,
    part21_source,
    part22_source,
    part23_source,
    part24_source,
    part25_source,
    part26_source,
    part27_source,
    part28_source,
    part29_source,
    part30_source,
    part31_source,
    part32_source,
    part33_source,
    part34_source,
    part35_source,
    part36_source,
    part37_source,
    part38_source,
    part39_source,
    part40_source,
    part41_source,
    part42_source,
    part43_source,
    part44_source,
    part45_source,
    part46_source,
    part47_source,
    part48_source,
    part49_source,
    part50_source,
    part51_source,
    part52_source]

theorem instructions_code [Bindings] :
    InstructionTrace.code instructions = codeRange 0x109610 instructionsBytes := by
  rw [InstructionTrace.code_eq_range _ _ instructions_ordered, instructions_bytes]

theorem instructions_code_subset [Bindings] :
    ∀ x ∈ InstructionTrace.code instructions, x ∈ Extracted.programSections.toCodeMap := by
  rw [instructions_code, ← instructions_source]
  intro x hx
  refine List.mem_flatMap.mpr ⟨⟨Extracted.textAddress, Extracted.textBytes⟩,
    by simp [Extracted.programSections], ?_⟩
  apply codeRange_slice_subset Extracted.textAddress Extracted.textBytes.toList 0x9610 10114 x
  rw [chunked_toList_slice _ _ _ (by rw [textBytes_size]; decide +kernel)]
  exact hx

theorem codeIn [Bindings] {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (InstructionTrace.code instructions) s :=
  (programLoaded_codeIn loaded).mono instructions_code_subset

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
