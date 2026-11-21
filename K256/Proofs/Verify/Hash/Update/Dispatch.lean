import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.Verify.Hash.Update

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Verify.LIR

abbrev returnFrame (label : Label) (ret : BitVec 64) : StackFrame Value Label signature Reg.count :=
  { target := label, kept := #v[], arity := rfl, guard := some ⟨64, ret⟩ }

variable {a : Vector Value Reg.count} {m : Ram} {sp src n : BitVec 64} {code : CodeMap}

def copyArgs (a : Vector Value Reg.count) (sp src n : BitVec 64) : Vector Value Reg.count :=
  let a := (a.set 2 ⟨64, n⟩).set 4 ⟨64, sp - 8⟩
  (a.set 6 ⟨64, src⟩).set 7 ⟨64, sp + 248⟩

def compressArgs (a : Vector Value Reg.count) (sp src n : BitVec 64) : Vector Value Reg.count :=
  let b := n >>> 6
  let r := (n.setWidth 32 &&& 63).setWidth 64
  let a := (a.set 2 ⟨64, b⟩).set 3 ⟨64, b⟩
  let a := (a.set 4 ⟨64, sp - 8⟩).set 6 ⟨64, src⟩
  ((a.set 7 ⟨64, sp + 312⟩).set 12 ⟨64, r⟩).set 15 ⟨64, (0x7fffffffffffffc0 &&& n) + src⟩

local macro "dispatch_regs" : tactic =>
  `(tactic| (congr 2
             apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
               fun eq => Vector.ext fun i hi => eq ⟨i, hi⟩)
             intro i
             finite_cases i <;> (try simp only [copyArgs, compressArgs, Vector.getElem_set]) <;> rfl))

theorem shortCall (rsp : a[4].get 64 = sp) (rbx : a[3].get 64 = n) (r14 : a[14].get 64 = src)
    (push : StoreOk code m (sp - 8) 8 0x10310f 6)
    (got : LoadOk m 0x203dd0 8) (target : memLoad m 0x203dd0 64 = 0x12a820) :
    program.runBlock (dialect code) ⟨.l103101, a, m⟩ =
      .call ⟨.l12a820, copyArgs a sp src n, memStore m (sp - 8) (0x103115 : BitVec 64)⟩
        (returnFrame .l103115 0x103115) := by
  cfg_eval [rsp, rbx, r14, push, got, target]
  dispatch_regs

theorem shortReturn (rsp : a[4].get 64 = sp) (rbx : a[3].get 64 = n)
    (store : StoreOk code m (sp + 311) 1 0x103115 7) :
    program.runBlock (dialect code) ⟨.l103115, a, m⟩ =
      .jump ⟨.l103170, a, memStore m (sp + 311) (n.setWidth 8)⟩ := by
  cfg_eval [rsp, rbx, store]
  dispatch_regs

theorem longCall (rsp : a[4].get 64 = sp) (rbx : a[3].get 64 = n) (r14 : a[14].get 64 = src)
    (store : StoreOk code m (sp + 344) 8 0x103141 8)
    (push : StoreOk code (memStore m (sp + 344) (n >>> 6)) (sp - 8) 8 0x10314f 5) :
    program.runBlock (dialect code) ⟨.l10311e, a, m⟩ =
      .call ⟨.l1218e0, compressArgs a sp src n, memStore (memStore m (sp + 344) (n >>> 6))
        (sp - 8) (0x103154 : BitVec 64)⟩ (returnFrame .l103154 0x103154) := by
  cfg_eval [rsp, rbx, r14, store, push]
  dispatch_regs

theorem longCopy (rsp : a[4].get 64 = sp) (r12 : a[12].get 64 = n) (r15 : a[15].get 64 = src)
    (store : StoreOk code m (sp + 311) 1 0x103154 8)
    (push : StoreOk code (memStore m (sp + 311) (n.setWidth 8)) (sp - 8) 8 0x10316a 6)
    (got : LoadOk (memStore m (sp + 311) (n.setWidth 8)) 0x203dd0 8)
    (target : memLoad (memStore m (sp + 311) (n.setWidth 8)) 0x203dd0 64 = 0x12a820) :
    program.runBlock (dialect code) ⟨.l103154, a, m⟩ =
      .call ⟨.l12a820, copyArgs a sp src n, memStore (memStore m (sp + 311) (n.setWidth 8))
        (sp - 8) (0x103170 : BitVec 64)⟩ (returnFrame .l103170 0x103170) := by
  cfg_eval [rsp, r12, r15, store, push, got, target]
  dispatch_regs

end K256.Proofs.Verify.Hash.Update
