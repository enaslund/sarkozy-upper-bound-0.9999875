module

public import Sarkozy.Cuts.Swapped

/-! Composing two rectangular feature operators through a common label law. -/

@[expose] public section

namespace Sarkozy.Cuts

open Sarkozy.Recentering

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype X] in
theorem recOp_featureComposition (β : FiniteLaw Y) (ν : FiniteLaw Z)
    (A : X → Z → ℝ) (B : Y → Z → ℝ) (f : Y → ℝ) :
    recOp β (fun x y => ν.expect (fun z => A x z * B y z)) f =
      recOp ν A (recAdj β B f) := by
  funext x
  unfold recOp recAdj
  simp only [← FiniteLaw.expect_mul_const, ← FiniteLaw.expect_const_mul]
  rw [expect_comm]
  exact ν.expect_congr fun z => β.expect_congr fun y => mul_assoc _ _ _

theorem nrm_featureComposition (α : FiniteLaw X) (β : FiniteLaw Y) (ν : FiniteLaw Z)
    (A : X → Z → ℝ) (B : Y → Z → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ f, nrm α (recOp ν A f) ≤ a * nrm ν f)
    (hB : ∀ f, nrm β (recOp ν B f) ≤ b * nrm ν f) (f : Y → ℝ) :
    nrm α (recOp β (fun x y => ν.expect (fun z => A x z * B y z)) f) ≤
      (a * b) * nrm β f := by
  rw [recOp_featureComposition]
  exact (hA _).trans ((mul_le_mul_of_nonneg_left
    (nrm_recAdj_le β ν B hb hB f) ha).trans_eq (by ring))

omit [Fintype X] [Fintype Z] in
theorem recOp_kernel_add (β : FiniteLaw Y) (A B : X → Y → ℝ) (f : Y → ℝ) :
    recOp β (fun x y => A x y + B x y) f =
      fun x => recOp β A f x + recOp β B f x := by
  funext x
  simp only [recOp, add_mul, FiniteLaw.expect_add]

omit [Fintype X] [Fintype Z] in
theorem recOp_kernel_smul (β : FiniteLaw Y) (A : X → Y → ℝ) (a : ℝ) (f : Y → ℝ) :
    recOp β (fun x y => a * A x y) f = fun x => a * recOp β A f x := by
  funext x
  simp only [recOp, mul_assoc, FiniteLaw.expect_const_mul]

end Sarkozy.Cuts
