module

public import Sarkozy.SpectralD.RootTailErrors
public import Sarkozy.SpectralD.RootTailCriterion
public import Sarkozy.SpectralD.RootOneBounds
public import Sarkozy.SpectralD.RootOneTests

/-!
# The root spectral bounds at class-one tail primes

The LL20 and LL22 lower bounds have constants 113 and 45. The named
Weil, moving-root, and four-cycle inputs remain hypotheses.
-/

@[expose] public section

namespace Sarkozy.SpectralD.Root

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.SpectralC Sarkozy.SpectralD.Cx
open scoped InnerProductSpace

variable {p : ℕ} [Fact p.Prime]

theorem LL20_tail_one (hW : Target.Weil) (hMR : Target.MovingRoot) (h4 : FourCycleBound p)
    (hp : 2 ^ 512 ≤ p) (hp1 : p % 4 = 1)
    (hne : (injLabellings (ZMod p) LL20.G).Nonempty)
    (v : EuclideanSpace ℝ (LL20.cut.Half → ZMod p)) :
    -(113 * rp p) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp LL20 hne v⟫_ℝ := by
  have hp52 : 2 ^ 52 ≤ p := by omega
  have he := (errors_of_S1 LL20 card_slot.le LL20_hdeg (coarseErr_root_lt_nat hp52)).2.2.1
  have hb := LL20_tail_expansion_bounds
    (weilBound_of_target hW p (ne_two_of_ge hp52)) h4 hp hne he
  exact tail_criterion LL20 rfl hW hMR hp hne LL20_card_half LL20_hdeg LL20_d0_le
    LL20_r_le he hb LL20_rho (LL20_lamH_one hp1) (LL20_plus_one hp1) LL20_deltaE
    (by norm_num) (LL20_tail_finiteTest_one hp1) LL20_tail_finite_cap_one v

theorem LL22_tail_one (hW : Target.Weil) (hMR : Target.MovingRoot) (h4 : FourCycleBound p)
    (hp : 2 ^ 512 ≤ p) (hp1 : p % 4 = 1)
    (hne : (injLabellings (ZMod p) LL22.G).Nonempty)
    (v : EuclideanSpace ℝ (LL22.cut.Half → ZMod p)) :
    -(45 * rp p) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp LL22 hne v⟫_ℝ := by
  have hp52 : 2 ^ 52 ≤ p := by omega
  have he := (errors_of_S1 LL22 card_slot.le LL22_hdeg (coarseErr_root_lt_nat hp52)).2.2.1
  have hb := LL22_tail_expansion_bounds
    (weilBound_of_target hW p (ne_two_of_ge hp52)) h4 hp hne he
  apply tail_criterion LL22 rfl hW hMR hp hne LL22_card_half LL22_hdeg LL22_d0_le
    (fun k => (LL22_r_le k).trans (by norm_num)) he hb
    (fun k => (LL22_rho k).trans (by norm_num)) _ _
    (normLe_mono LL22_deltaE (by norm_num)) (by norm_num)
    (LL22_tail_finiteTest_one hp1) Cx.LL22_tail_finite_cap v
  · intro x
    exact (LL22_lamH_one hp1 x).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (sum_nonneg fun _ _ => sq_nonneg _))
  · intro x
    exact (LL22_plus_one hp1 x).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (sum_nonneg fun _ _ => sq_nonneg _))

end Sarkozy.SpectralD.Root
