import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Mark.Fill
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Arguments
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Copy
import Hkdf.Proofs.Key.Tail.Bytes
import Hkdf.Proofs.Common.CallFrame.Push

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.SHA256
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def CompressionSite.copyOffset : CompressionSite → Nat
  | .extra => 0xf9a2
  | .inner => 0xf357
  | .outer => 0xf46d

def CompressionSite.blockWrites (site : CompressionSite) (sp : BitVec 64) : Vector MemoryRegion 3 :=
  #v[⟨(sp + 16).toNat,56⟩, ⟨(sp + BitVec.ofNat 64 site.hashOffset).toNat,32⟩, ⟨sp.toNat - 344,344⟩]

def CompressionSite.savedReg (site : CompressionSite) (s : RamState) (r : Syntax.Reg) : BitVec 64 :=
  match site, r with
  | .inner, .r13 => stackPtr s + 16
  | .inner, .r15 => stackPtr s + 144
  | _, _ => s.regValue r

theorem compressBlock [bindings : Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info block : ByteArray} {ptr : BitVec 64} {length : Nat} {hash : Array UInt32}
    {n : Nat} {regions : Vector MemoryRegion n}
    (pre : ExpandPre entry boundary key info ptr length) (frame : Running entry boundary regions s)
    (inStack : Stack.region entry 2264 ∈ regions) (avoid : ∀ r ∈ regions, r.Avoids InProgram)
    (sp : stackPtr s = stackPtr entry - 536) (site : CompressionSite)
    (pc : s.RIP = Extracted.textAddress + BitVec.ofNat 64 site.copyOffset)
    (src : site = .outer → s.regValue .r13 = stackPtr s + 16)
    (bytes : (⟨(stackPtr s + 80).toNat,64⟩ : MemoryRegion).HasBytes s.external block)
    (eighth : slot s 72 = slot s 136)
    (words : HashStateAt s (stackPtr s + BitVec.ofNat 64 site.hashOffset) hash) :
    ∃ t, Running s boundary (site.blockWrites (stackPtr s)) t ∧ t.RIP = site.pc + (5 : BitVec 64) ∧
      stackPtr t = stackPtr s ∧
      (∀ r ∈ ([.rbx,.rbp,.r12,.r13,.r14,.r15] : List Syntax.Reg), t.regValue r = site.savedReg s r) ∧
      t.MXCSR = s.MXCSR ∧ t.FP87_Control = s.FP87_Control ∧
      HashStateAt t (stackPtr s + BitVec.ofNat 64 site.hashOffset)
        (Hkdf.Proofs.NIST.SHA256.compress hash (Hkdf.Proofs.NIST.Encoding.octetsToBits block)) := by
  let start := Extracted.textAddress + BitVec.ofNat 64 site.copyOffset
  have isStart : Copy.IsStart start := by cases site <;> unfold Copy.IsStart <;> decide +kernel
  have rsp : rspOf s = stackPtr s := Operand.read_reg64 s 4
  have stack := pre.call.stack
  have geometry (off : Nat) (le : off ≤ 536) :
      rspOf s + BitVec.ofNat 64 off = stackPtr entry - BitVec.ofNat 64 (536 - off) :=
    rsp ▸ InnerPadding.local_address sp off le
  have copyPre : Copy.Pre start s := by
    refine ⟨pc, ?_, ?_, ?_⟩
    · intro i hi
      rw [geometry _ (by omega)]
      exact stack_readable stack frame.allocated (by omega) (by omega)
    · intro i hi
      rw [geometry _ (by omega)]
      exact stack_writable8 stack pre.call.stackAvoid frame.allocated (by omega) (by omega)
    · intro i hi
      rw [geometry _ (by omega)]
      exact stack_codeApart stack (fun a ha hp => pre.call.stackAvoid a ha (.inl hp))
        (codeOffset := site.copyOffset) (by omega) (by omega) (by cases site <;> decide)
  obtain ⟨nf,u,copy,ru,_,copied⟩ := Copy.run boundary isStart pre.call.outerBoundary s
    (supportedMachine_readyToStep frame.machine) (Copy.code frame.loaded isStart) copyPre
  have regsU (r : Syntax.Reg) (untouched : r ≠ .rax ∧ r ≠ .rcx) : u.regValue r = s.regValue r := by
    apply StreamPadding.reg_agrees copied.agrees
    cases r <;> first | contradiction | (simp [Copy.effect, Effect.components] <;> decide) | exact (untouched.1 rfl).elim | exact (untouched.2 rfl).elim
  have spU : stackPtr u = stackPtr s := regsU .rsp (by decide)
  have dstAddr : rspOf s + 16 = stackPtr entry - BitVec.ofNat 64 520 := geometry 16 (by decide)
  have fits : (rspOf s + 16).toNat + 56 < 2^64 := by
    rw [dstAddr, stack_sub_toNat stack (offset := 520) (by decide)]
    have := (stack_bounds stack).2
    omega
  have copyWithin : WritesWithin (Copy.effect start s).components regions := by
    intro c hc a ha
    have hit := Copy.memory_footprint hc ha
    rw [dstAddr] at hit
    exact ⟨_, inStack, stackRegion_contains_sub stack.2.2.1 (offset := 520) (by decide) (by decide) hit⟩
  have df := show .df ∉ (Copy.effect start s).components by simp [Copy.effect, Effect.components]
  have frameU := frame.of_agrees copy ru copied.agrees copyWithin avoid df
  have copyFrame : MemoryWriteFrame s u (site.blockWrites (stackPtr s)) := by
    apply copied.agrees.memoryWriteFrame
    intro c hc a ha
    obtain ⟨j,hj,rfl⟩ := Copy.memory_footprint hc ha
    refine ⟨⟨(stackPtr s + 16).toNat,56⟩, by simp [CompressionSite.blockWrites], ?_⟩
    change _ ≤ _ ∧ _ < _
    rw [← rsp]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at fits ⊢
    omega
  have blockU : (⟨(rspOf s + 16).toNat,64⟩ : MemoryRegion).HasBytes u.external block := by
    apply Hkdf.Proofs.Key.Tail.copy_qwords_hasBytes (src := rspOf s + 80) bytes
    · have hr := stack_readable stack frameU.allocated (offset := 520) (len := 64) (by decide) (by decide)
      rw [← dstAddr] at hr
      exact hr.mem
    · intro j hj
      by_cases small : j < 7
      · simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          Copy.word copied small
      have eq : j = 7 := by omega
      subst j
      have high : (Component.mem (rspOf s + 72) 8).Agrees s u := by
        intro i hi
        apply copied.agrees.byte
        intro c hc hit
        obtain ⟨k,hk,he⟩ := Copy.memory_footprint hc hit
        bv_omega
      have got : memLoad u.external (rspOf s + 72) 64 = memLoad s.external (rspOf s + 136) 64 :=
        (agrees_memLoad high).trans eighth
      simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using got
  have hashU : HashStateAt u (stackPtr s + BitVec.ofNat 64 site.hashOffset) hash := by
    apply hashState_of_bytes words
    intro i hi
    apply copied.agrees.byte
    intro c hc hit
    obtain ⟨j,hj,he⟩ := Copy.memory_footprint hc hit
    rw [rsp] at he
    cases site <;> simp only [CompressionSite.hashOffset, BitVec.ofNat_eq_ofNat] at he <;> bv_omega
  obtain ⟨na,v,setup,rv,args⟩ := compressionArguments site frameU.loaded ru pre.call.outerBoundary
    (by have := copied.rip; cases site <;> exact this)
  have noMem : ∀ c ∈ (site.setupEffect u).components, ∀ a, ¬ c.Covers a := by
    cases site <;> simp [CompressionSite.setupEffect, Effect.components, Component.Covers]
  have frameV := frameU.of_agrees setup rv args.agrees (fun c hc a ha => (noMem c hc a ha).elim)
    avoid (by cases site <;> simp [CompressionSite.setupEffect, Effect.components])
  have ext := args.agrees.external noMem
  have spV : stackPtr v = stackPtr u := args.agrees.read (n := 64) (r := 4)
    (by cases site <;> simp [CompressionSite.setupEffect, Effect.components])
  have countV : v.regValue .rdx = 1 := by cases site <;> exact args.writes.1
  have destV : v.regValue .rdi = stackPtr s + BitVec.ofNat 64 site.hashOffset := by
    rw [← spU]
    cases site <;> exact args.writes.2.1
  have sourceV : v.regValue .rsi = stackPtr s + 16 := by
    cases site with
    | extra => rw [← spU]; exact args.writes.2.2
    | inner => rw [← spU]; exact args.writes.2.2.1
    | outer => exact args.writes.2.2.trans ((regsU .r13 (by decide)).trans (src rfl))
  have hashV : HashStateAt v (v.regValue .rdi) hash := by
    simpa only [HashStateAt, ext, destV] using hashU
  obtain ⟨t,runT,ripT,spT,abi,writes,hashT⟩ := compress pre frameV ((spV.trans spU).trans sp)
    site args.rip (spV.trans spU ▸ destV) (spV.trans spU ▸ sourceV) countV
    (by rw [spV,spU,ext]; exact blockU) hashV
  have frameAll : MemoryWriteFrame s t (site.blockWrites (stackPtr s)) := by
    apply memoryWriteFrame_trans copyFrame
    intro a ha
    rw [← ext]
    apply writes
    intro r hr hit
    apply ha r _ hit
    rcases (show r = registerRegion v .rdi 32 ∨ r = ⟨(stackPtr v).toNat - 344,344⟩ by simpa using hr) with rfl | rfl
    all_goals simp [registerRegion, destV, spV, spU, CompressionSite.blockWrites]
  obtain ⟨nc, exec⟩ := runT.execution
  refine ⟨t, ⟨⟨_, (copy.trans setup).trans exec⟩, runT.machine, runT.loaded,
    fun a ha => runT.allocated a (args.agrees.grow a (copied.agrees.grow a ha)), runT.directionFlag,
    frameAll⟩, ripT, spT.trans (spV.trans spU), ?_, ?_, ?_, destV ▸ hashT⟩
  · intro r hr
    apply (abi.1 r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases site
    all_goals first
      | exact args.writes.2.2.2.2.trans (congrArg (· + (16 : BitVec 64)) spU)
      | exact args.writes.2.2.2.1.trans (congrArg (· + (144 : BitVec 64)) spU)
      | apply Eq.trans (StreamPadding.reg_agrees args.agrees _ (by simp [CompressionSite.setupEffect, Effect.components] <;> decide)); exact regsU _ (by decide)
  · exact abi.2.2.1.trans ((args.agrees.mxcsr (by cases site <;> simp [CompressionSite.setupEffect, Effect.components])).trans
      (copied.agrees.mxcsr (by simp [Copy.effect, Effect.components])))
  · exact abi.2.2.2.trans ((args.agrees.fcw (by cases site <;> simp [CompressionSite.setupEffect, Effect.components])).trans
      (copied.agrees.fcw (by simp [Copy.effect, Effect.components])))

end Hkdf.Proofs.NewExpand.Expand.Finalize
