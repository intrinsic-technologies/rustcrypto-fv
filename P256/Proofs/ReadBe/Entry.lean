import P256.Proofs.ReadBe.Entry.Capacity
import P256.Proofs.ReadBe.Entry.Store
import P256.Proofs.ReadBe.Entry.Size
import P256.Proofs.ReadBe.Entry.Clamp
import P256.Proofs.ReadBe.Entry.Count
import P256.Proofs.ReadBe.Entry.Start
import P256.Proofs.ReadBe.Entry.Frame

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.ReadBe

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem setup_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x11909e)
    (count : s.regValue .rsi = 32) (limbs : s.regValue .rcx = 4) (bits : s.regValue .r8 = 256)
    (writable : MemWritable s (stackPtr s + 8) 8)
    (apart : ∀ a, Component.Covers (.mem (stackPtr s + 8) 8) a → ¬ InProgram a)
    (outer : ¬ InProgram boundary.rip) :
    ∃ t fuel, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x11914e ∧ stackPtr t = stackPtr s ∧ t.regValue .rbx = 256 ∧
      t.regValue .rbp = 32 ∧ t.regValue .r14 = s.regValue .rdx ∧ t.regValue .r15 = 0 ∧
      t.regValue .r13 = 32 ∧ t.regValue .r12 = s.regValue .rdi + 32 ∧
      t.external = memStore s.external (stackPtr s + 8) (4 : BitVec 64) ∧
      AgreesExcept [.reg 0,.reg 2,.reg 3,.reg 5,.reg 12,.reg 13,.reg 14,.reg 15,
        .flags,.rip,.mem (stackPtr s + 8) 8] s t := by
  obtain ⟨s1, a1, r1, ip1, out1, f1⟩ := Entry.capacity_correct ready loaded rip limbs bits outer
  have m1 := f1.external (by simp [Component.Covers])
  have l1 : ProgramLoaded s1 := by intro a b hb; rw [m1]; exact loaded a b hb
  have sp1 : stackPtr s1 = stackPtr s := f1.read (n := 64) (r := 4) (by simp)
  have c1 : s1.regValue .rcx = 4 := (f1.read (n := 64) (r := 1) (by simp)).trans limbs
  have b1 : s1.regValue .r8 = 256 := (f1.read (n := 64) (r := 8) (by simp)).trans bits
  have w1 : MemWritable s1 (stackPtr s1 + 8) 8 := by rw [sp1]; exact writable.of_external_eq m1
  obtain ⟨s2, a2, r2, l2, ip2, bits2, m2, f2⟩ := Entry.store_correct r1 l1 ip1 c1 b1 w1
    (by rw [sp1]; exact apart) outer
  have sp2 : stackPtr s2 = stackPtr s := (f2.read (n := 64) (r := 4) (by simp)).trans sp1
  have b2 : s2.regValue .r8 = 256 := (f2.read (n := 64) (r := 8) (by simp)).trans b1
  obtain ⟨s3, a3, r3, ip3, size3, f3⟩ := Entry.size_correct r2 l2 ip2 b2 outer
  have m3 := f3.external (by simp [Component.Covers])
  have l3 : ProgramLoaded s3 := by intro a b hb; rw [m3]; exact l2 a b hb
  have c3 : s3.regValue .rsi = 32 :=
    (((f1.trans f2).trans f3).read (n := 64) (r := 6) (by simp)).trans count
  obtain ⟨s4, a4, r4, ip4, size4, f4⟩ := Entry.clamp_correct r3 l3 ip3 c3 size3 outer
  have m4 := (f4.external (by simp [Component.Covers])).trans m3
  have l4 : ProgramLoaded s4 := by intro a b hb; rw [m4]; exact l2 a b hb
  have sp4 : stackPtr s4 = stackPtr s :=
    ((f3.trans f4).read (n := 64) (r := 4) (by simp)).trans sp2
  have memory4 : s4.external = memStore s.external (stackPtr s + 8) (4 : BitVec 64) := by
    rw [m4, m2, m1, sp1]
  have read4 : MemReadable s4 (stackPtr s4 + 8) 8 := by
    rw [sp4]
    exact readable_of_grow writable.readable (((f1.trans f2).trans f3).trans f4).grow
  have value4 : memLoad s4.external (stackPtr s4 + 8) 64 = 4 := by
    rw [sp4, memory4, memLoad_memStore_same _ _ _ (by decide) (by decide)]
  obtain ⟨s5, a5, r5, ip5, limbs5, f5⟩ := Entry.count_correct r4 l4 ip4 size4 read4 value4 outer
  have m5 := f5.external (by simp [Component.Covers])
  have l5 : ProgramLoaded s5 := by intro a b hb; rw [m5]; exact l4 a b hb
  have c5 : s5.regValue .rsi = 32 :=
    ((f4.trans f5).read (n := 64) (r := 6) (by simp)).trans c3
  obtain ⟨t, a6, r6, ip6, size6, source6, offset6, f6⟩ := Entry.start_correct r5 l5 ip5 c5 limbs5 outer
  have m6 := f6.external (by simp [Component.Covers])
  have l6 : ProgramLoaded t := by intro a b hb; rw [m6]; exact l5 a b hb
  have frame := ((((f1.trans f2).trans f3).trans f4).trans f5).trans f6
  refine ⟨t, 31, ((((a1.trans a2).trans a3).trans a4).trans a5).trans a6,
    r6, l6, ip6, frame.read (n := 64) (r := 4) (by simp), ?_, size6, ?_, offset6, ?_, ?_, ?_, ?_⟩
  · exact ((((f3.trans f4).trans f5).trans f6).read (n := 64) (r := 3) (by simp)).trans bits2
  · exact (((((f2.trans f3).trans f4).trans f5).trans f6).read (n := 64) (r := 14) (by simp)).trans out1
  · exact ((f5.trans f6).read (n := 64) (r := 13) (by simp)).trans size4
  · have source5 : s5.regValue .rdi = s.regValue .rdi :=
      ((((f1.trans f2).trans f3).trans f4).trans f5).read (n := 64) (r := 7) (by simp)
    simpa only [source5] using source6
  · rw [m6, m5, memory4]
  · apply frame.mono
    simp only [sp1]
    simp

theorem entry_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : Pre s boundary)
    (bytes : (registerRegion s .rdi 32).HasBytes s.external input) :
    ∃ t fuel, Advances boundary fuel s t ∧ LoopState s t input 0 := by
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, agrees⟩ := Entry.prologue_correct pre
  have count : u.regValue .rsi = 32 :=
    (agrees.read (n := 64) (r := 6) (by simp [Entry.prologueComponents, P256.Proofs.Program.saveFrame])).trans pre.count
  have limbs : u.regValue .rcx = 4 :=
    (agrees.read (n := 64) (r := 1) (by simp [Entry.prologueComponents, P256.Proofs.Program.saveFrame])).trans pre.limbs
  have bits : u.regValue .r8 = 256 :=
    (agrees.read (n := 64) (r := 8) (by simp [Entry.prologueComponents, P256.Proofs.Program.saveFrame])).trans pre.bits
  have output : u.regValue .rdx = s.regValue .rdx :=
    agrees.read (n := 64) (r := 2) (by simp [Entry.prologueComponents, P256.Proofs.Program.saveFrame])
  have source : u.regValue .rdi = s.regValue .rdi :=
    agrees.read (n := 64) (r := 7) (by simp [Entry.prologueComponents, P256.Proofs.Program.saveFrame])
  have slot : stackPtr u + 8 = stackPtr s - 64 := by
    rw [rsp, frameBase]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have writable : MemWritable u (stackPtr u + 8) 8 := by
    rw [slot]
    exact writable_of_grow
      (stack_sub_writable8 pre.stack pre.stack_avoids_tables (offset := 64) (by decide +kernel) (by decide +kernel)) agrees.grow
  have apart : ∀ a, Component.Covers (.mem (stackPtr u + 8) 8) a → ¬ InProgram a := by
    intro a ha hcode
    rw [slot] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact pre.avoids (Stack.region s 128) (by simp) _
      (pre.stack_contains (offset := 64) (by decide +kernel) (by decide +kernel) hi) (.inl hcode)
  obtain ⟨t, fuel, run', ready', loaded', rip', rsp', bits', size', output', offset',
    remaining', source', memory', agrees'⟩ :=
    setup_correct ready loaded rip count limbs bits writable apart pre.outerBoundary
  have finalMemory : t.external = Entry.entryMemory s := by
    rw [memory', memory, slot]
    rfl
  have finalAgrees : AgreesExcept (Entry.entryComponents s) s t := by
    apply (agrees.trans agrees').mono
    intro c hc
    simp only [Entry.prologueComponents, P256.Proofs.Program.saveFrame, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals try simp only [slot]
    all_goals simp [Entry.entryComponents]
  have frame := Entry.frame_correct pre ready' loaded' (rsp'.trans rsp) finalMemory finalAgrees
  refine ⟨t, 7 + fuel, run.trans run', frame, ?_, bits', size', output'.trans output,
    ?_, ?_, ?_, Entry.inputBytes_preserved pre frame bytes, ?_⟩
  · exact rip'
  · exact offset'
  · exact remaining'
  · change t.regValue .r12 = s.regValue .rdi + 32
    simpa only [source] using source'
  · intro j hj
    omega

end P256.Proofs.ReadBe
