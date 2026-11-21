import P256.Proofs.Program.CallPre
import P256.Proofs.Program.Push
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple
import X86Proofs.Program.Compose

set_option autoImplicit false

namespace P256.Proofs.Program.SavePair

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def savedMemory (s : RamState) : Ram :=
  memStore (memStore s.external (stackPtr s - 8) (s.regValue .r14))
    (stackPtr s - 16) (s.regValue .rbx)

def saveComponents (s : RamState) : List Component :=
  [.reg 4, .flags, .rip, .mem (stackPtr s - 8) 8, .mem (stackPtr s - 16) 8]

structure Code (offset : Nat) (locals : BitVec 8) : Prop where
  size : offset + 7 < 118431
  first : Extracted.textBytes.toListFrom offset (encodePushR64 14).length = encodePushR64 14
  second : Extracted.textBytes.toListFrom (offset + 2) (encodePushR64 3).length = encodePushR64 3
  subtract : Extracted.textBytes.toListFrom (offset + 3)
    ([0x48, 0x83, 0xec] ++ immBytes 8 locals).length = [0x48, 0x83, 0xec] ++ immBytes 8 locals

structure SavedEntry [Bindings] (initial s : RamState) (offset : Nat) (locals : BitVec 8) : Prop where
  execution : Advances (returnBoundary initial) 3 initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 (offset + 7)
  rsp : stackPtr s = stackPtr initial - (16 + locals.signExtend 64)
  memory : s.external = savedMemory initial
  agrees : AgreesExcept (saveComponents initial) initial s

theorem save_correct [bindings : Bindings] {s : RamState} {reserve offset : Nat}
    {locals : BitVec 8} (hs : Stack.Valid s reserve)
    (hav : (Stack.region s reserve).Avoids (fun a => InProgram a ∨ InPageTables a))
    (hout : ¬ InProgram (returnBoundary s).rip) (ready : ReadyToStep s)
    (loaded : ProgramLoaded s) (hip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (space : 16 ≤ reserve) (code : Code offset locals) :
    ∃ t, SavedEntry s t offset locals := by
  obtain ⟨s1, ha1, hr1, hl1, hip1, hsp1, hf1, hm1⟩ :=
    push_exists hs hav hout ready loaded (fun _ h => h)
      14 0 offset (by simp only [BitVec.sub_zero]) hip
      (by omega) (by decide) (by have := code.size; change offset + 2 < 118431; omega) code.first
  obtain ⟨s2, ha2, hr2, hl2, hip2, hsp2, hf2, hm2⟩ :=
    push_exists hs hav hout hr1 hl1 hf1.grow 3 8 (offset + 2) hsp1 hip1
      space (by decide) (by have := code.size; change offset + 2 + 1 < 118431; omega) code.second
  obtain ⟨t, hstep, hrt, het⟩ :=
    sub_r64_imm8_effect_step (Extracted.textAddress + BitVec.ofNat 64 (offset + 3)) 0x48 0xec locals
      (by unfold RexWPrefix; decide +kernel) rfl rfl s2 hr2
      (programText_slice (programLoaded_codeIn hl2) (offset + 3)
        ([0x48,0x83,0xec] ++ immBytes 8 locals)
        (by have := code.size; simp only [List.length_append, List.length_cons, List.length_nil,
          immBytes_length]; omega) code.subtract)
      (by simpa only [show (encodePushR64 3).length = 1 from rfl, Nat.add_assoc] using hip2)
  have hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 (offset + 7) := by
    rw [het.rip]
    change (Extracted.textAddress + BitVec.ofNat 64 (offset + 3)) + 4 = _
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  have ha3 : Advances (returnBoundary s) 1 s2 t :=
    Advances.of_step hstep (.inl (by
      rw [hip]
      exact boundary_ne_program hout (inProgram_of_textOffset (offset + 7) code.size)))
  have hext : t.external = s2.external := het.agrees.external
    (by simp [subR64Imm8Effect_components, Component.Covers])
  refine ⟨t, ⟨(ha1.trans ha2).trans ha3, hrt, ?_, hip, ?_, ?_, ?_⟩⟩
  · intro a b hab
    rw [hext]
    exact hl2 a b hab
  · have hw : stackPtr t = stackPtr s2 - locals.signExtend 64 := het.writes
    rw [hw, hsp2, BitVec.sub_sub]
    rfl
  · have hv : (Operand.reg 3 : Operand 64).read s1 = s.regValue .rbx :=
      hf1.read (by simp)
    rw [hext, hm2, hm1]
    change memStore (memStore s.external (stackPtr s - 8) (s.regValue .r14))
      (stackPtr s - 16) ((Operand.reg 3 : Operand 64).read s1) = _
    rw [hv]
    rfl
  · apply ((hf1.trans hf2).trans het.agrees).mono
    simp only [saveComponents, subR64Imm8Effect_components,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | (rfl | rfl | rfl) <;> simp [gprNumber, rexB, modrmRm]

end P256.Proofs.Program.SavePair
