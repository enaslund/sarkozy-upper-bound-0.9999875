module

public import Sarkozy.MeanCredit2.Comparison
public import Sarkozy.MeanCredit2.Classes

@[expose] public section

/-!
# The completed middle mean is monotone in the totals

`paper/sections/24a_joint_mean.tex`, `prop:joint-middle-mean` ("The completed comparison cost is
nonincreasing in `V_full`, while the mean corrections are nondecreasing in it").

`meanValue x (rU) (σx) U V` is nondecreasing in `x`, `U`, `V` on `0 ≤ x`, `0 < U`, `0 ≤ V`
(**`meanValue_mono`**): every coefficient is nonnegative (`η_{j+2} ≥ η₀`, `ζ_{j+1} ≥ ζ₀`,
`ρ^j ≥ 1`), and `(e^w − 1 − w)/w² = ∑_j w^j/(j+2)!` is nondecreasing on `w > 0`.

So the mean side of the evaluation holds at any totals at least the harness's
(**`seriesBound_paper_mono`**). The formal raw-arm and outside totals may exceed the harness's; the
excess must then be absorbed on the comparison side (`C_v ≤ 𝓔_h + τ`, `τ ≤ 3·10⁻²` since RG's
rebase, `2·10⁻³` before; about `161.3 δ_A + 218.9 δ_S` in `63 𝓔`, untrusted). The first-round
constructor `mdInputsOfSel` accepts this `SeriesBound` directly. -/

open Finset

namespace Sarkozy.MeanCredit2

open Sarkozy.ClassData Sarkozy.MeanCredit

/-- `(e^w − 1 − w)/w²` is nondecreasing on `w > 0`. -/
theorem phi_mono {w w' : ℝ} (hw : 0 < w) (hww : w ≤ w') :
    (Real.exp w - 1 - w) / w ^ 2 ≤ (Real.exp w' - 1 - w') / w' ^ 2 := by
  have h1 := hasSum_exp_shift2 w hw.ne'
  have h2 := hasSum_exp_shift2 w' (by linarith)
  exact hasSum_le (fun j => div_le_div_of_nonneg_right (pow_le_pow_left₀ hw.le hww j)
    (Nat.cast_nonneg _)) h1 h2

theorem phi_nonneg {w : ℝ} (hw : 0 < w) : 0 ≤ (Real.exp w - 1 - w) / w ^ 2 :=
  (hasSum_exp_shift2 w hw.ne').nonneg fun j => by positivity

/-- The background value is nondecreasing in `U`, `V` when `a₀ ≥ 0` and `a_j ≥ a₀`. -/
theorem bgVal_mono (a : ℕ → ℝ) (a0 : ℝ) (J : ℕ) (ha0 : 0 ≤ a0) (ha : ∀ j ≤ J, a0 ≤ a j)
    {U U' V V' : ℝ} (hU : U ≤ U') (hV0 : 0 ≤ V) (hV : V ≤ V') :
    bgVal a a0 J U V ≤ bgVal a a0 J U' V' := by
  unfold bgVal
  have h1 : a0 * Real.exp U ≤ a0 * Real.exp U' :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hU) ha0
  have h2 : ∑ j ∈ range (J + 1), (a j - a0) * (V ^ j / j.factorial) ≤
      ∑ j ∈ range (J + 1), (a j - a0) * (V' ^ j / j.factorial) := by
    refine sum_le_sum fun j hj => ?_
    have hj' : j ≤ J := by rw [mem_range] at hj; omega
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ hV0 hV j) (Nat.cast_nonneg _)) (by linarith [ha j hj'])
  linarith

theorem bgVal_nonneg (a : ℕ → ℝ) (a0 : ℝ) (J : ℕ) (ha0 : 0 ≤ a0) (ha : ∀ j ≤ J, a0 ≤ a j)
    (U : ℝ) {V : ℝ} (hV0 : 0 ≤ V) : 0 ≤ bgVal a a0 J U V := by
  unfold bgVal
  have h1 : 0 ≤ a0 * Real.exp U := mul_nonneg ha0 (Real.exp_pos U).le
  have h2 : 0 ≤ ∑ j ∈ range (J + 1), (a j - a0) * (V ^ j / j.factorial) := by
    refine sum_nonneg fun j hj => ?_
    have hj' : j ≤ J := by rw [mem_range] at hj; omega
    exact mul_nonneg (by linarith [ha j hj']) (by positivity)
  linarith

theorem aEta_ge (j : ℕ) (hj : j ≤ 8) : (eta0 : ℝ) ≤ aEta j := by
  unfold aEta
  exact_mod_cast eta_ge (by omega) (by omega)

theorem aZeta_ge (j : ℕ) (hj : j ≤ 8) : (zeta0 : ℝ) ≤ aZeta j := by
  unfold aZeta
  exact_mod_cast zeta_ge (by omega) (by omega)

theorem aRho_ge (j : ℕ) : (1 : ℝ) ≤ aRho j := by
  unfold aRho
  exact one_le_pow₀ (by norm_num [rhoQ, ratioR])

/-- **The completed middle mean is nondecreasing in the totals.** -/
theorem meanValue_mono (r : ℝ) (hr : 0 < r) {x x' U U' V V' : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ x')
    (hU0 : 0 < U) (hU : U ≤ U') (hV0 : 0 ≤ V) (hV : V ≤ V') :
    meanValue x (r * U) ((sigmaQ : ℝ) * x) U V ≤
      meanValue x' (r * U') ((sigmaQ : ℝ) * x') U' V' := by
  have hs : (0 : ℝ) ≤ sigmaQ := by norm_num [sigmaQ]
  have he0 : (0 : ℝ) ≤ eta0 := by norm_num [eta0]
  have hz0 : (0 : ℝ) ≤ zeta0 := by norm_num [zeta0]
  have hw : 0 < r * U := mul_pos hr hU0
  have hww : r * U ≤ r * U' := mul_le_mul_of_nonneg_left hU hr.le
  have hx2 : x ^ 2 ≤ x' ^ 2 := pow_le_pow_left₀ hx0 hx 2
  have hy0 : 0 ≤ (sigmaQ : ℝ) * x := mul_nonneg hs hx0
  have hy : (sigmaQ : ℝ) * x ≤ sigmaQ * x' := mul_le_mul_of_nonneg_left hx hs
  have hφ := phi_mono hw hww
  have hφ0 := phi_nonneg hw
  have hE := bgVal_mono aEta (eta0 : ℝ) 8 he0 aEta_ge hU hV0 hV
  have hZ := bgVal_mono aZeta (zeta0 : ℝ) 8 hz0 aZeta_ge hU hV0 hV
  have hR := bgVal_mono aRho 1 10 zero_le_one (fun j _ => aRho_ge j) hU hV0 hV
  have hE0 := bgVal_nonneg aEta (eta0 : ℝ) 8 he0 aEta_ge U hV0
  have hZ0 := bgVal_nonneg aZeta (zeta0 : ℝ) 8 hz0 aZeta_ge U hV0
  have hR0 := bgVal_nonneg aRho 1 10 zero_le_one (fun j _ => aRho_ge j) U hV0
  have hH : (0 : ℝ) < 16 * (hStar : ℝ) ^ 2 := by norm_num [hStar]
  unfold meanValue
  set y := (sigmaQ : ℝ) * x
  set y' := (sigmaQ : ℝ) * x'
  have t1 : 64 * (x ^ 2 / (16 * (hStar : ℝ) ^ 2) *
      ((Real.exp (r * U) - 1 - r * U) / (r * U) ^ 2)) ≤
      64 * (x' ^ 2 / (16 * (hStar : ℝ) ^ 2) *
      ((Real.exp (r * U') - 1 - r * U') / (r * U') ^ 2)) := by
    have := mul_le_mul (div_le_div_of_nonneg_right hx2 hH.le) hφ hφ0 (by positivity)
    linarith
  have t2 := mul_le_mul (div_le_div_of_nonneg_right hx2 (by norm_num : (0 : ℝ) ≤ 2)) hE hE0
    (by positivity)
  have hp3 : x * y + x * (y ^ 3 / 6) + x * (y ^ 5 / 120) ≤
      x' * y' + x' * (y' ^ 3 / 6) + x' * (y' ^ 5 / 120) := by
    have a1 := mul_le_mul hx hy hy0 (by linarith)
    have a2 := mul_le_mul hx (div_le_div_of_nonneg_right (pow_le_pow_left₀ hy0 hy 3)
      (by norm_num : (0 : ℝ) ≤ 6)) (by positivity) (by linarith)
    have a3 := mul_le_mul hx (div_le_div_of_nonneg_right (pow_le_pow_left₀ hy0 hy 5)
      (by norm_num : (0 : ℝ) ≤ 120)) (by positivity) (by linarith)
    linarith
  have hx'0 : 0 ≤ x' := le_trans hx0 hx
  have hy'0 : 0 ≤ y' := le_trans hy0 hy
  have hp3' : 0 ≤ x' * y' + x' * (y' ^ 3 / 6) + x' * (y' ^ 5 / 120) := by
    have b1 := mul_nonneg hx'0 hy'0
    have b2 := mul_nonneg hx'0 (div_nonneg (pow_nonneg hy'0 3) (by norm_num : (0 : ℝ) ≤ 6))
    have b3 := mul_nonneg hx'0 (div_nonneg (pow_nonneg hy'0 5) (by norm_num : (0 : ℝ) ≤ 120))
    linarith
  have t3 := mul_le_mul hp3 hZ hZ0 hp3'
  have hp4 : y ^ 2 / 2 + y ^ 4 / 24 + y ^ 6 / 720 ≤ y' ^ 2 / 2 + y' ^ 4 / 24 + y' ^ 6 / 720 := by
    have a1 := pow_le_pow_left₀ hy0 hy 2
    have a2 := pow_le_pow_left₀ hy0 hy 4
    have a3 := pow_le_pow_left₀ hy0 hy 6
    linarith
  have t4 := mul_le_mul hp4 hR hR0 (by positivity)
  linarith

variable {C : Type} [Fintype C]

/-- **The evaluation at totals at least the harness's** (`seriesBound_paper` with
`x ≥ xq`, `U ≥ Uq`, `V ≥ Vq`): the mean side by `meanValue_mono` and `meanValue_ge`. -/
theorem seriesBound_paper_mono (c : (MLetter ⊕ C → ℕ) → ℝ) (X : MLetter ⊕ C → ℝ)
    (hX0 : ∀ l, 0 ≤ X l) (x U V : ℝ) (hx : (xq : ℝ) ≤ x) (hU : (Uq : ℝ) ≤ U)
    (hV : (Vq : ℝ) ≤ V) (hVU : V ≤ U) (hXm : ∀ l, X (.inl l) = mTot x 0 0 V (U - V) l)
    (hres : ∀ d, 0 ≤ 63 * c d - mLift d) (Cv τ : ℝ)
    (hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv)
    (hCv : Cv ≤ harnessE + τ) :
    SeriesBound (fun d => 63 * c d - mLift d) X
      (63 * (harnessE : ℝ) - 64 * (ledgerMid : ℝ) + (63 * τ - 4 / 10 ^ 11)) := by
  have hr : 0 < rH := by unfold rH; norm_num [rhoHq]
  have hUq : (0 : ℝ) < Uq := by norm_num [Uq]
  have hVq : (0 : ℝ) ≤ Vq := by norm_num [Vq]
  have hw : rH * U ≠ 0 := (mul_pos hr (by linarith)).ne'
  have hM := hasSum_mLift x U V (by linarith) hVU hw X hXm
  refine (seriesBound_of_hasSum c mLift X hX0 hres Cv _ hC hM).mono ?_
  have h1 := meanValue_mono rH hr (by norm_num [xq] : (0 : ℝ) ≤ xq) hx hUq hU hVq hV
  have e1 : rH * (Uq : ℝ) = (wq : ℝ) := by unfold rH; push_cast [wq]; ring
  have e2 : (sigmaQ : ℝ) * (xq : ℝ) = (yq : ℝ) := by push_cast [yq]; ring
  rw [e1, e2] at h1
  have := meanValue_ge
  linarith

end Sarkozy.MeanCredit2
