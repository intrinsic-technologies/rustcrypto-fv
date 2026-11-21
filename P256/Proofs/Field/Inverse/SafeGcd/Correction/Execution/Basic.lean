import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Layout

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

macro "correction_stack_store" fr:ident mem:ident hc:ident : tactic =>
  `(tactic| first
    | (
      apply CrossPage.StoreOk.of_region (b := ($fr).rsp - 0x38) (len := 0x38)
      · repeat' first | assumption | apply Writable.memStore
      · refine_arith
      · refine_arith
      · apply writable_codeApart (mem := $mem) _ $hc (by decide) (by decide)
        apply Writable.sub (b := ($fr).rsp - 0x38) (len := 0x38)
        · repeat' first | assumption | apply Writable.memStore
        · refine_arith
        · refine_arith)
    | (
      apply StoreOk.of_region (b := ($fr).rsp - 0x38) (len := 0x38)
      · repeat' first | assumption | apply Writable.memStore
      · refine_arith
      · refine_arith
      · apply writable_codeApart (mem := $mem) _ $hc (by decide) (by decide)
        apply Writable.sub (b := ($fr).rsp - 0x38) (len := 0x38)
        · repeat' first | assumption | apply Writable.memStore
        · refine_arith
        · refine_arith))

macro "correction_output_store" fr:ident mem:ident hc:ident : tactic =>
  `(tactic| first
    | (
      apply CrossPage.StoreOk.of_region (b := ($fr).rdi) (len := 32)
      · repeat' first | assumption | apply Writable.memStore
      · refine_arith
      · refine_arith
      · apply writable_codeApart (mem := $mem) _ $hc (by decide) (by decide)
        apply Writable.sub (b := ($fr).rdi) (len := 32)
        · repeat' first | assumption | apply Writable.memStore
        · refine_arith
        · refine_arith)
    | (
      apply StoreOk.of_region (b := ($fr).rdi) (len := 32)
      · repeat' first | assumption | apply Writable.memStore
      · refine_arith
      · refine_arith
      · apply writable_codeApart (mem := $mem) _ $hc (by decide) (by decide)
        apply Writable.sub (b := ($fr).rdi) (len := 32)
        · repeat' first | assumption | apply Writable.memStore
        · refine_arith
        · refine_arith))

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution
