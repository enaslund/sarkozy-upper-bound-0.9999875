module

public import Sarkozy.SpectralD.CxCriterion3
public import Sarkozy.SpectralD.RootModelH
public import Sarkozy.SpectralD.RootChecks

/-!
# Finite spectral tests from bounds on the model matrices

A norm bound for the degree-one matrix and an upper bound for H+ suffice for
the two finite tests. At class three the existing exact row sums certify both
root tests, with the tail caps 113 and 45 after the stated scalar allowances.
The analytic estimates that must fit those allowances are separate obligations.
-/

@[expose] public section

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

omit [DecidableEq U] in
theorem azero_normLe_all (hp2 : p ≠ 2) (ς : U → U → ZMod p) {L : ℝ}
    (hD : NormLe (deltaE ς) L) (ξ : ZMod p) : NormLe (azero ς ξ) L := by
  intro w z
  unfold azero
  rw [bform_smul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_chi_eps_le hp2 ξ)).trans (hD w z)

omit [DecidableEq U] in
theorem qform_lower_of_normLe {A : U → U → ℂ} {L : ℝ}
    (hA : NormLe A L) (w : U → ℂ) :
    -(L * Sarkozy.Spectral.sqn w) ≤ (qform A w).re := by
  have h := hA w w
  change ‖qform A w‖ ≤ L * vnorm w * vnorm w at h
  rw [mul_assoc, ← pow_two, vnorm_sq] at h
  change ‖qform A w‖ ≤ L * Sarkozy.Spectral.sqn w at h
  have hneg := Complex.re_le_norm (-(qform A w))
  simp only [Complex.neg_re, norm_neg] at hneg
  linarith

omit [DecidableEq U] in
theorem finiteTest_of_form_bounds {qA qX : (U → ℂ) → ℝ} {L A c s ηQ ηB : ℝ}
    (hs : 0 < s) (hA : ∀ w, -(A * Sarkozy.Spectral.sqn w) ≤ qA w)
    (hX : ∀ w, qX w ≤ L * Sarkozy.Spectral.sqn w)
    (hnum : A + L / s + ηQ + ηB / s ≤ c + s) :
    Sarkozy.Spectral.FiniteTest qA qX c s ηQ ηB := by
  intro w
  have h1 := hA w
  have h2 := div_le_div_of_nonneg_right (hX w) hs.le
  have h3 := mul_le_mul_of_nonneg_right hnum (Sarkozy.Spectral.sqn_nonneg w)
  rw [mul_div_right_comm] at h2
  nlinarith

theorem finiteTest_of_model_bound (hp2 : p ≠ 2) (Adj : U → U → Prop)
    [DecidableRel Adj] (N : U → Finset U) (ς : U → U → ZMod p)
    {L A c s ηQ ηB : ℝ} (hs : 0 < s) (hD : NormLe (deltaE ς) A)
    (hplus : ∀ w, (qform (PaleyB.hplusM Adj N ς) w).re ≤ L * ∑ j, ‖w j‖ ^ 2)
    (hnum : A + L / s + ηQ + ηB / s ≤ c + s) (ξ : ZMod p) :
    Sarkozy.Spectral.FiniteTest (fun w => (qform (azero ς ξ) w).re)
      (qXcx Adj N ς ξ) c s ηQ ηB := by
  apply finiteTest_of_form_bounds hs
    (qform_lower_of_normLe (azero_normLe_all hp2 ς hD ξ)) _ hnum
  intro w
  unfold qXcx
  rw [spectral_qform_eq]
  exact (sub_le_self _ (Sarkozy.Spectral.sqn_nonneg _)).trans (hplus w)

theorem finiteTest_three_of_model_bound (hp3 : p % 4 = 3) (Adj : U → U → Prop)
    [DecidableRel Adj] (N : U → Finset U) (ς : U → U → ZMod p)
    {L A c s ηQ ηB : ℝ} (hs : 0 < s) (hD : NormLe (deltaE ς) A)
    (hH : ∀ w, (qform (PaleyB.modelHC N ς) w).re ≤ L * ∑ j, ‖w j‖ ^ 2)
    (hnum : A + L / s + ηQ + ηB / s ≤ c + s) (ξ : ZMod p) :
    Sarkozy.Spectral.FiniteTest (fun w => (qform (azero ς ξ) w).re)
      (qXcx Adj N ς ξ) c s ηQ ηB := by
  apply finiteTest_of_model_bound (by omega) Adj N ς hs hD _ hnum ξ
  intro w
  rw [PaleyB.qform_hplusM_re]
  simpa only [hp3, show ¬ (3 : ℕ) = 1 by decide, ite_false, zero_mul, add_zero] using hH w

theorem LL20_tail_finiteTest (hp3 : p % 4 = 3)
    (Adj : Root.LL20.cut.Half → Root.LL20.cut.Half → Prop) [DecidableRel Adj]
    (ξ : ZMod p) :
    Sarkozy.Spectral.FiniteTest (fun w => (qform (azero (sgnZ Root.LL20) ξ) w).re)
      (qXcx Adj Root.LL20.Nset (sgnZ Root.LL20) ξ) (1 / 4) 110 1 1 :=
  finiteTest_three_of_model_bound hp3 Adj Root.LL20.Nset (sgnZ Root.LL20)
    (by norm_num) Root.LL20_deltaE (Root.LL20_lamH hp3) (by norm_num) ξ

theorem LL22_tail_finiteTest (hp3 : p % 4 = 3)
    (Adj : Root.LL22.cut.Half → Root.LL22.cut.Half → Prop) [DecidableRel Adj]
    (ξ : ZMod p) :
    Sarkozy.Spectral.FiniteTest (fun w => (qform (azero (sgnZ Root.LL22) ξ) w).re)
      (qXcx Adj Root.LL22.Nset (sgnZ Root.LL22) ξ) (1 / 4) 44 1 1 :=
  finiteTest_three_of_model_bound hp3 Adj Root.LL22.Nset (sgnZ Root.LL22)
    (by norm_num) Root.LL22_deltaE (Root.LL22_lamH hp3) (by norm_num) ξ

theorem LL20_tail_finite_cap : ((1 / 4 : ℝ) + 110) / (1 - 1 / 100) ≤ 113 := by norm_num

theorem LL22_tail_finite_cap : ((1 / 4 : ℝ) + 44) / (1 - 1 / 100) ≤ 45 := by norm_num

end Sarkozy.SpectralD.Cx
