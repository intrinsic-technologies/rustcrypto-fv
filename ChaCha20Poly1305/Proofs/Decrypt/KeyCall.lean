import ChaCha20Poly1305.Proofs.Decrypt.CallTactic
import ChaCha20Poly1305.Proofs.Decrypt.KeyContract
import ChaCha20Poly1305.Proofs.Decrypt.TagCalls

namespace ChaCha20Poly1305.Proofs.Decrypt.Detached
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash

@[refine_layout] def live (fr : Activation) : List Atom := regs {fr with rdi := fr.r12} ++ [.gpr 5 fr.rbp]

@[refine_layout] def keyStack (sp : BitVec 64) : List MemoryRegion := [slot sp 32 128,slot sp 160 32,slot sp 208 24]
@[refine_layout] def keyAreas (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp+32).toNat+48,4⟩,⟨(sp+32).toNat+64,64⟩,slot sp 160 32] ++ keyStack sp

@[refine_layout] def keyFrame (fr : Activation) := {push fr with rsi:=fr.rsp+208,rdi:=fr.rsp+32}

@[refine_layout] def keyCall (w : Vector UInt32 16) (x : Raw) (dst : BitVec 256) (sp : BitVec 64) : Invoke.Edge where
  site := .l1002e5
  resume := .l100384
  callee := (keyFn w x (sp+160) dst).reserve (keyStack sp)
  before fr := live fr ++ space fr 424 ++ localArea fr ++ [.fact (fr.rsp=sp)] ++ beginWords x fr.rsp ++
    Stream.geometry (short w (fr.rsp+160)) (keyFrame fr)
  after fr := live fr ++ [.gpr 0 0,.mem (fr.rsp+160) 256 dst] ++ fixed x (fr.rsp+32)
  footprint := keyAreas sp

attribute [local irreducible] memLoad memStore

set_option maxHeartbeats 2300000
set_option maxRecDepth 10000
set_option pp.maxSteps 110

theorem keyCallValid (w : Vector UInt32 16) (x : Raw) (dst : BitVec 256) (sp : BitVec 64) :
    (Invoke.layout (keyCall w x dst sp)).BlockSimulation fnCode .site := by
  refine_intro
  subst sp
  refine_uir [Invoke.program]
  refine_lifted [BitVec.add_assoc]
  prepare_call (fun m => ({fr with original:=m,rsp:=fr.rsp-8,ret:=0x100384,rdi:=fr.rsp+32,rsi:=fr.rsp+208},()))
  · refine_close [BitVec.add_assoc]
    all_goals try assumption
  · close_resume [BitVec.add_assoc]
    all_goals simp only [BitVec.add_assoc] at done14 done15 done16 done17 done18 done19 done20 
    all_goals assumption

@[refine_layout] def keyTest (fr : Activation) : Micro.Step where
  entry := .l100384
  exit := .l10038c
  pre := live fr ++ [.gpr 0 0]
  post := live fr
  writes := []

theorem keyTestValid (fr : Activation) : Micro.Valid (keyTest fr) := by
  unfold Micro.Valid
  refine_one [Micro.program,keyTest]
  all_goals first | rfl | assumption | contradiction

end ChaCha20Poly1305.Proofs.Decrypt.Detached
