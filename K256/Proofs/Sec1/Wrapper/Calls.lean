import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.Parser.LengthTable
import K256.Proofs.Common.Image
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4

set_option autoImplicit false

namespace K256.Proofs.Sec1.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

def serializeReturn : StackFrame Value Label signature Reg.count :=
  { target := .l101e0c, kept := #v[], arity := rfl, guard := some ⟨64, 0x101e0c⟩ }

def memcpyReturn : StackFrame Value Label signature Reg.count :=
  { target := .l101e62, kept := #v[], arity := rfl, guard := some ⟨64, 0x101e62⟩ }

private theorem rsp_sub_slot (sp : BitVec 64) : sp - 248 - 8 = sp - 256 := by
  rw [BitVec.sub_sub]
  rfl

theorem serialize_call_setup {code : CodeMap} {args : Vector Value 53} {mem : Ram}
    {sp : BitVec 64} (hsp : args[4] = ⟨64, sp - 248⟩)
    (hstore : StoreOk code mem (sp - 256) 8 0x101e07 5) :
    let child := (((args.set 2 ⟨64, 0⟩).set 4 ⟨64, sp - 256⟩).set 6 ⟨64, sp - 104⟩).set
      7 ⟨64, sp - 233⟩
    program.runBlock (dialect code) ⟨.l101df8, args, mem⟩ =
      .call ⟨.l1215e0, child, memStore mem (sp - 256) (0x101e0c : BitVec 64)⟩
        serializeReturn := by
  have rsp : Value.get 64 args[4] = sp - 248 := by rw [hsp]; rfl
  have rsi : sp - 248 + 144 = sp - 104 := by bv_omega
  have rdi : sp - 248 + 15 = sp - 233 := by bv_omega
  dsimp only
  cfg_eval
  simp only [rsp, rsp_sub_slot, rsi, rdi, hstore, ↓reduceIte]
  congr 2
  apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
    fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
  intro i
  finite_cases i <;> simp only [Vector.getElem_set] <;> rfl

theorem memcpy_call_setup {code : CodeMap} {args : Vector Value 53} {mem : Ram}
    {sp dst : BitVec 64} (tag : Fin 6)
    (hsp : args[4] = ⟨64, sp - 248⟩) (hdst : args[14] = ⟨64, dst⟩)
    (htag : Value.get 64 args[1] = BitVec.ofNat 64 tag.val)
    (hstore : StoreOk code mem (sp - 256) 8 0x101e5c 6)
    (hTable : LoadOk mem (wordAddr 0x2022b8 64 tag.val) 8)
    (hLength : memLoad mem (wordAddr 0x2022b8 64 tag.val) 64 = Parser.lengthTable[tag])
    (hGot : LoadOk mem 0x203dd0 8) (hTarget : memLoad mem 0x203dd0 64 = 0x12a820) :
    let child := (((args.set 2 ⟨64, Parser.lengthTable[tag]⟩).set 4 ⟨64, sp - 256⟩).set
      6 ⟨64, sp - 233⟩).set 7 ⟨64, dst⟩
    program.runBlock (dialect code) ⟨.l101e4c, args, mem⟩ =
      .call ⟨.l12a820, child, memStore mem (sp - 256) (0x101e62 : BitVec 64)⟩
        memcpyReturn := by
  have rsp : Value.get 64 args[4] = sp - 248 := by rw [hsp]; rfl
  have r14 : Value.get 64 args[14] = dst := by rw [hdst]; rfl
  have rsi : sp - 248 + 15 = sp - 233 := by bv_omega
  have hAddr : ∀ i : Fin 6, (BitVec.ofNat 64 i.val <<< 3) + 0x2022b8 =
      wordAddr 0x2022b8 64 i.val := by decide +kernel
  dsimp only
  cfg_eval
  simp only [rsp, r14, htag, hAddr tag, hTable, hLength, hGot, hTarget, hstore,
    rsp_sub_slot, rsi, and_self,
    ↓reduceIte]
  congr 2
  apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
    fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
  intro i
  finite_cases i <;> simp only [Vector.getElem_set] <;> rfl

private theorem loaded_rodata_word {mem : Ram}
    (loaded : ∀ x ∈ Extracted.programImage, mem[x.1]? = some x.2)
    (offset : Nat) (value : BitVec 64) (hSize : offset + 8 ≤ 15952)
    (hRead : chunkedRead Extracted.rodataBytes offset 8 = wordBytes value) :
    let addr := Extracted.rodataAddress + BitVec.ofNat 64 offset
    LoadOk mem addr 8 ∧ memLoad mem addr 64 = value := by
  let addr := Extracted.rodataAddress + BitVec.ofNat 64 offset
  let sec : ImageSection := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩
  have hs : sec ∈ Extracted.programSections := by simp [sec, Extracted.programSections]
  have hImage := codeRange_sub_section hs offset 8 hRead (by decide +kernel)
    (by change offset + 8 ≤ Extracted.rodataBytes.size; rwa [Common.rodataBytes_size]) (p := addr) rfl
  have hBytes : Bytes mem addr 8 (storedByte value) := by
    intro i hi
    apply loaded (addr + BitVec.ofNat 64 i, storedByte value i)
    apply hImage
    have h := mem_codeRange addr (wordBytes value) i
      (by simp only [wordBytes, List.length_ofFn]; omega)
    simpa only [wordBytes, List.getElem_ofFn] using h
  have hLow : addr.toNat + 8 ≤ 2 ^ 32 := by
    dsimp only [addr]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    change (0x200000 + offset % 2 ^ 64) % (2 ^ 64) + 8 ≤ 2 ^ 32
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨⟨hLow, fun i hi => ?_⟩, hBytes.memLoad (by decide) (by decide)⟩
  rw [hBytes i hi]
  rfl

theorem memcpy_length_load {mem : Ram}
    (loaded : ∀ x ∈ Extracted.programImage, mem[x.1]? = some x.2) (tag : Fin 6) :
    LoadOk mem (wordAddr 0x2022b8 64 tag.val) 8 ∧
    memLoad mem (wordAddr 0x2022b8 64 tag.val) 64 = Parser.lengthTable[tag] := by
  have contents : ∀ i : Fin 6,
      chunkedRead Extracted.rodataBytes (0x22b8 + 8 * i.val) 8 =
        wordBytes Parser.lengthTable[i] := by decide +kernel
  have hAddr : Extracted.rodataAddress + BitVec.ofNat 64 (0x22b8 + 8 * tag.val) =
      wordAddr 0x2022b8 64 tag.val := by finite_cases tag <;> rfl
  have h := loaded_rodata_word loaded _ _ (by have := tag.isLt; omega) (contents tag)
  exact hAddr ▸ h

theorem memcpy_target_load {mem : Ram}
    (loaded : ∀ x ∈ Extracted.programImage, mem[x.1]? = some x.2) :
    LoadOk mem 0x203dd0 8 ∧ memLoad mem 0x203dd0 64 = 0x12a820 :=
  loaded_rodata_word loaded 0x3dd0 0x12a820 (by decide) (by decide +kernel)

end K256.Proofs.Sec1.Wrapper
