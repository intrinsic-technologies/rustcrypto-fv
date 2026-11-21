import Sha2.Proofs.Common.SHA256.Absorb.State
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.Memory.Copy
import Sha2.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.CopyCall

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

def Target (site : CallSite) (s : RamState) : Prop :=
  match site.encoding with
  | .relative disp => branchTarget site.pc 5 (disp.signExtend 64) = 0x10dd60
  | .memory am => am.Valid ∧ am.rexX = 0 ∧ am.rexB = 0 ∧
      MemReadable s (am.addr s (site.pc + BitVec.ofNat 64 (callMemLen am))) 8 ∧
      callMemPtr site.pc am s = 0x10dd60
  | .register r => (.reg (r.setWidth 5) : Operand 64).read s = 0x10dd60

structure Pre [Bindings] (site : CallSite) (boundary : ReturnBoundary)
    (count reserve : Nat) (s : RamState) : Prop where
  call : PushPre site.pc site.encoding.bytes.length s
  target : Target site s
  returnInProgram : InProgram (site.pc + BitVec.ofNat 64 site.encoding.bytes.length)
  callee : ∀ u, ReadyToStep u →
    (callEffect (fun _ => 0x10dd60) (site.pc + BitVec.ofNat 64 site.encoding.bytes.length) s).Holds s u →
    CalleePre u boundary 0x10dd60 count count reserve ∧
      u.regValue .rdx = BitVec.ofNat 64 count

def Post [Bindings] (site : CallSite) (boundary : ReturnBoundary)
    (count reserve : Nat) (s t : RamState) : Prop :=
  t.RIP = site.pc + BitVec.ofNat 64 site.encoding.bytes.length ∧ stackPtr t = stackPtr s ∧
    ∃ u, (callEffect (fun _ => 0x10dd60)
      (site.pc + BitVec.ofNat 64 site.encoding.bytes.length) s).Holds s u ∧
      CalleeResult u t boundary count reserve ∧
      (∀ i < count, t.external[u.regValue .rdi + BitVec.ofNat 64 i]? =
        u.external[u.regValue .rsi + BitVec.ofNat 64 i]?)

theorem enter [Bindings] (site : CallSite) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) {s : RamState}
    (ready : ReadyToStep s) (loaded : CodeIn (codeRange site.pc site.encoding.bytes) s)
    (push : PushPre site.pc site.encoding.bytes.length s) (target : Target site s) :
    ∃ u, Advances boundary 1 s u ∧ ReadyToStep u ∧
      (callEffect (fun _ => 0x10dd60)
        (site.pc + BitVec.ofNat 64 site.encoding.bytes.length) s).Holds s u := by
  have hnext : (0x10dd60 : BitVec 64) ≠ boundary.rip :=
    boundary_ne_program outside (inProgram_of_textOffset 0xdd60 (by decide))
  rcases site with ⟨p, encoding⟩
  cases encoding with
  | relative disp =>
    change branchTarget p 5 (disp.signExtend 64) = 0x10dd60 at target
    obtain ⟨u, run, readyU, effect⟩ := (call_rel32_effect_step p disp
      (by rw [target]; decide)).advances (boundary := boundary) ready loaded push
      (by simpa only [callEffect, pushEffect, target] using hnext)
    refine ⟨u, run, readyU, ?_⟩
    simpa only [CallEncoding.bytes, encodeCallRel32, List.length_cons, immBytes_length,
      callEffect, pushEffect, target] using effect
  | memory am =>
    obtain ⟨valid, noX, noB, readable, pointer⟩ := target
    have size : (encodeCallM64 am).length = callMemLen am := by
      simp only [encodeCallM64, List.length_cons, callMemLen]
      omega
    change PushPre p (encodeCallM64 am).length s at push
    rw [size] at push
    obtain ⟨u, run, readyU, effect⟩ := (call_m64_effect_step p am valid noX noB).advances (boundary := boundary)
      ready loaded ⟨⟨push, by rw [pointer]; decide⟩, readable⟩
      (by simpa only [callEffect, pushEffect, pointer] using hnext)
    refine ⟨u, run, readyU, ?_⟩
    simpa only [CallEncoding.bytes, size, callEffect, pushEffect, pointer] using effect
  | register r =>
    change (.reg (r.setWidth 5) : Operand 64).read s = 0x10dd60 at target
    rcases encodeCallR64_spec r with ⟨modrm, bytes, mod, reg, number⟩ |
      ⟨rex, modrm, bytes, rexValid, mod, reg, number⟩
    · change CodeIn (codeRange p (encodeCallR64 r)) s at loaded
      change PushPre p (encodeCallR64 r).length s at push
      rw [bytes] at loaded push
      obtain ⟨u, run, readyU, effect⟩ := (call_r64_effect_step p modrm mod reg).advances (boundary := boundary)
        ready loaded ⟨push, by simpa only [number, target] using
          (show (0x10dd60 : BitVec 64).toNat < 2^32 by decide)⟩
        (by simpa only [callEffect, pushEffect, number, target] using hnext)
      refine ⟨u, run, readyU, ?_⟩
      simpa only [CallEncoding.bytes, bytes, List.length_cons, List.length_nil,
        callEffect, pushEffect, number, target] using effect
    · change CodeIn (codeRange p (encodeCallR64 r)) s at loaded
      change PushPre p (encodeCallR64 r).length s at push
      rw [bytes] at loaded push
      obtain ⟨u, run, readyU, effect⟩ :=
        (call_r64_rex_effect_step p rex modrm rexValid mod reg).advances (boundary := boundary)
          ready loaded ⟨push, by simpa only [number, target] using
          (show (0x10dd60 : BitVec 64).toNat < 2^32 by decide)⟩
          (by simpa only [callEffect, pushEffect, number, target] using hnext)
      refine ⟨u, run, readyU, ?_⟩
      simpa only [CallEncoding.bytes, bytes, List.length_cons, List.length_nil,
        callEffect, pushEffect, number, target] using effect

theorem run [Bindings] (site : CallSite) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip)
    (reload : ∀ t, ProgramLoaded t → CodeIn (codeRange site.pc site.encoding.bytes) t)
    (count reserve : Nat) (bound : count < 2^32) :
    AdvanceTriple boundary (Pre site boundary count reserve)
      (codeRange site.pc site.encoding.bytes) (Post site boundary count reserve) := by
  intro s ready loaded pre
  obtain ⟨u, first, readyU, effect⟩ := enter site boundary outside ready loaded pre.call pre.target
  obtain ⟨callee, length⟩ := pre.callee u readyU effect
  obtain ⟨t, result, copied, _⟩ := Common.Memory.memcpy_correct callee length bound (by
    change InProgram (stackTop u)
    rw [(callEffect_stack effect).1]
    exact pre.returnInProgram)
  obtain ⟨fuel, rest⟩ := result.execution
  refine ⟨1 + fuel, t, first.trans rest, supportedMachine_readyToStep result.machine,
    reload t result.loaded, ?_⟩
  have stack := callEffect_stack effect
  exact ⟨result.rip.trans stack.1, result.rsp.trans stack.2, u, effect, result, copied⟩

theorem Post.hasBytes [Bindings] {site : CallSite} {boundary : ReturnBoundary}
    {count reserve : Nat} {s t : RamState} {chunk : ByteArray}
    (post : Post site boundary count reserve s t)
    (bytes : (registerRegion s .rsi count).HasBytes s.external chunk)
    (apart : RangeApart (s.regValue .rsi) count (pushAddr s) 8) :
    (registerRegion s .rdi count).HasBytes t.external chunk := by
  obtain ⟨_,_,u,effect,_,copied⟩ := post
  have source : u.regValue .rsi = s.regValue .rsi := effect.agrees.read (n := 64) (r := 6)
    (by simp [callEffect,pushEffect_components])
  have output : u.regValue .rdi = s.regValue .rdi := effect.agrees.read (n := 64) (r := 7)
    (by simp [callEffect,pushEffect_components])
  refine ⟨bytes.1,?_⟩
  intro i
  have hi : i.val<count := by have := i.isLt; have size : chunk.size=count := bytes.1; omega
  have copy := copied i.val hi
  rw [source,output] at copy
  have unchanged : u.external[s.regValue .rsi+BitVec.ofNat 64 i.val]? =
      s.external[s.regValue .rsi+BitVec.ofNat 64 i.val]? := by
    apply effect.agrees.byte
    intro c member covered
    simp only [callEffect,pushEffect_components,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact covered.elim
    · obtain ⟨j,hj,same⟩ := covered
      exact apart i.val hi j hj same
    · exact covered.elim
  have original := bytes.2 i
  simpa only [registerRegion,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
    copy.trans (unchanged.trans (by
      simpa only [registerRegion,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using original))

end Sha2.Proofs.Common.SHA256.Absorb.CopyCall
