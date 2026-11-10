module

public import Sarkozy.MeanCredit2.Comparison

@[expose] public section

/-!
# Non-vacuity of the numerical hypotheses of `seriesBound_split`

`seriesBound_split` (and the constructors built on it) asks, about numbers only:
* `hres`: `63(c_B − s) − mLift ≥ 0`;
* `hB`: the class-free completion is `Bh(e^{Sh} cosh Ah − 1)`;
* `hS`, `hSv`: the savings completion reaches `D_cls + D_var`;
* `hXm`: the mean letters at the harness totals.

**`split_hypotheses_satisfiable`** exhibits one instance, on `MLetter ⊕ Unit`:
* `c_B = mLift/63`, plus the degree-0 term `K₀ = Bh(e^{Sh} cosh Ah − 1) − M/63`;
* `s` the degree-0 term `D_cls + D_var`.

So these hypotheses are not contradictory. Their content is in the identification with the formal
data (`hcomp`, `hmean`), which forces `c` to be the comparison's coefficients on the actual
selections' degrees.

Numerics: `M = meanValue ≤ 10` (crude, `e^U, e^w < 3`); `e^{S+A} ≥ 2.339`, `e^{A−S} ≤ 2.171`
(kernel; RG's values at `a_G`).
-/

open Finset

namespace Sarkozy.MeanCredit2

open Sarkozy.ClassData Sarkozy.MeanCredit

theorem exp_SA_ge : ((2339 / 1000 : ℚ) : ℝ) ≤ Real.exp ((Sh + Ah : ℚ) : ℝ) :=
  le_exp_of_ps (by norm_num [Sh, Ah]) (by norm_num [Sh, Ah]) (n := 20) (by norm_num)
    (by decide +kernel)

theorem exp_AS_le : Real.exp ((Ah - Sh : ℚ) : ℝ) ≤ ((2171 / 1000 : ℚ) : ℝ) :=
  exp_le_of_ps (by norm_num [Sh, Ah]) (by norm_num [Sh, Ah]) (n := 20) (by norm_num)
    (by decide +kernel)

/-- `e^{Sh} cosh Ah − 1 ≥ 0.3998` (kernel exponentials; RG's values at `a_G`). -/
theorem expcosh_ge : (3998 / 10000 : ℝ) ≤ Real.exp (Sh : ℝ) * Real.cosh Ah - 1 := by
  have h1 := exp_SA_ge
  have h2 := exp_AS_le
  have e : Real.exp (Sh : ℝ) * Real.cosh Ah =
      (Real.exp ((Sh + Ah : ℚ) : ℝ) + (Real.exp ((Ah - Sh : ℚ) : ℝ))⁻¹) / 2 := by
    rw [Real.cosh_eq, ← Real.exp_neg]
    push_cast
    rw [mul_div_assoc', mul_add, ← Real.exp_add, ← Real.exp_add]
    congr 3
    ring
  have hpos : 0 < Real.exp ((Ah - Sh : ℚ) : ℝ) := Real.exp_pos _
  have h3 : ((2171 / 1000 : ℚ) : ℝ)⁻¹ ≤ (Real.exp ((Ah - Sh : ℚ) : ℝ))⁻¹ := inv_anti₀ hpos h2
  rw [e]
  norm_num at h1 h3 ⊢
  linarith

/-- **A crude upper bound for the completed middle mean**: `meanValue ≤ 10` at the harness's totals
(`e^U, e^w ≤ 3`). -/
theorem meanValue_le : meanValue xq wq yq Uq Vq ≤ 10 := by
  have hU0 : Real.exp (Uq : ℝ) ≤ 3 := by
    have := Real.exp_one_lt_d9
    have h : Real.exp (Uq : ℝ) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num [Uq])
    linarith
  have hw0' : Real.exp (wq : ℝ) ≤ 3 := by
    have := Real.exp_one_lt_d9
    have h : Real.exp (wq : ℝ) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by norm_num [wq, Uq, rhoHq])
    linarith
  have hw0 : (0 : ℝ) < (wq : ℝ) := by norm_num [wq, Uq, rhoHq]
  have hx0 : (0 : ℝ) ≤ (xq : ℝ) := by norm_num [xq]
  have hy0 : (0 : ℝ) ≤ (yq : ℝ) := by norm_num [yq, xq, sigmaQ]
  set eU := Real.exp (Uq : ℝ)
  set ew := Real.exp (wq : ℝ)
  have hcW : 0 ≤ 64 * ((xq : ℝ) ^ 2 / (16 * (hStar : ℝ) ^ 2)) / (wq : ℝ) ^ 2 := by positivity
  have hcU : 0 ≤ (xq : ℝ) ^ 2 / 2 * (eta0 : ℝ) +
      ((xq : ℝ) * yq + xq * (yq ^ 3 / 6) + xq * (yq ^ 5 / 120)) * (zeta0 : ℝ) +
      ((yq : ℝ) ^ 2 / 2 + yq ^ 4 / 24 + yq ^ 6 / 720) := by
    have : (0 : ℝ) ≤ eta0 := by norm_num [eta0]
    have : (0 : ℝ) ≤ zeta0 := by norm_num [zeta0]
    positivity
  have e : meanValue xq wq yq Uq Vq - (meanLowQ : ℝ) =
      64 * ((xq : ℝ) ^ 2 / (16 * (hStar : ℝ) ^ 2)) / (wq : ℝ) ^ 2 * (ew - ewlo) +
      ((xq : ℝ) ^ 2 / 2 * (eta0 : ℝ) +
        ((xq : ℝ) * yq + xq * (yq ^ 3 / 6) + xq * (yq ^ 5 / 120)) * (zeta0 : ℝ) +
        ((yq : ℝ) ^ 2 / 2 + yq ^ 4 / 24 + yq ^ 6 / 720)) * (eU - eUlo) := by
    unfold meanValue bgVal meanLowQ
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_sub,
      Rat.cast_ofNat, Rat.cast_one, cast_bgQ, aEta, aZeta, aRho]
    field_simp
    ring
  have h1 := mul_le_mul_of_nonneg_left (sub_le_sub_right hw0' (ewlo : ℝ)) hcW
  have h2 := mul_le_mul_of_nonneg_left (sub_le_sub_right hU0 (eUlo : ℝ)) hcU
  have hq : (meanLowQ : ℝ) + 64 * ((xq : ℝ) ^ 2 / (16 * (hStar : ℝ) ^ 2)) / (wq : ℝ) ^ 2 *
      (3 - ewlo) + ((xq : ℝ) ^ 2 / 2 * (eta0 : ℝ) +
        ((xq : ℝ) * yq + xq * (yq ^ 3 / 6) + xq * (yq ^ 5 / 120)) * (zeta0 : ℝ) +
        ((yq : ℝ) ^ 2 / 2 + yq ^ 4 / 24 + yq ^ 6 / 720)) * (3 - eUlo) ≤ 10 := by
    have : ((meanLowQ + 64 * (xq ^ 2 / (16 * hStar ^ 2)) / wq ^ 2 * (3 - ewlo) +
        (xq ^ 2 / 2 * eta0 + (xq * yq + xq * (yq ^ 3 / 6) + xq * (yq ^ 5 / 120)) * zeta0 +
          (yq ^ 2 / 2 + yq ^ 4 / 24 + yq ^ 6 / 720)) * (3 - eUlo) : ℚ) : ℝ) ≤ ((10 : ℚ) : ℝ) := by
      exact_mod_cast (show meanLowQ + 64 * (xq ^ 2 / (16 * hStar ^ 2)) / wq ^ 2 * (3 - ewlo) +
        (xq ^ 2 / 2 * eta0 + (xq * yq + xq * (yq ^ 3 / 6) + xq * (yq ^ 5 / 120)) * zeta0 +
          (yq ^ 2 / 2 + yq ^ 4 / 24 + yq ^ 6 / 720)) * (3 - eUlo) ≤ 10 by decide +kernel)
    push_cast at this
    exact this
  linarith

theorem famCoef_zero (f o e k : ℕ) (a : ℕ → ℝ) (a0 : ℝ) (J : ℕ) (hfe : f ≠ 0 ∨ e ≠ 0) :
    famCoef f o e k a a0 J 0 = 0 := by
  unfold famCoef
  split_ifs with h
  · rcases hfe with hf | he
    · exact absurd (congrFun h .F).symm hf
    · exact absurd (congrFun h .E).symm he
  · rfl

theorem famI_zero (r : ℝ) : famI r 0 = 0 := by
  unfold famI
  split_ifs with h
  · exact absurd (congrFun h .F) (by decide)
  · rfl

theorem mPaper_zero (r : ℝ) : mPaper r 0 = 0 := by
  simp only [mPaper, famI_zero]
  rw [famCoef_zero _ _ _ _ _ _ _ (by decide), famCoef_zero _ _ _ _ _ _ _ (by decide),
    famCoef_zero _ _ _ _ _ _ _ (by decide), famCoef_zero _ _ _ _ _ _ _ (by decide),
    famCoef_zero _ _ _ _ _ _ _ (by decide), famCoef_zero _ _ _ _ _ _ _ (by decide),
    famCoef_zero _ _ _ _ _ _ _ (by decide)]
  ring

/-- The mean letters at the harness totals, and `0` on the extra letter. -/
noncomputable def Xtoy : MLetter ⊕ Unit → ℝ := Sum.elim (mTot xq 0 0 Vq (Uq - Vq)) fun _ => 0

/-- **The numerical hypotheses of `seriesBound_split` are satisfiable.** -/
theorem split_hypotheses_satisfiable :
    ∃ (cB s : (MLetter ⊕ Unit → ℕ) → ℝ) (Sv : ℝ),
      (∀ l, 0 ≤ Xtoy l) ∧ (∀ l, Xtoy (.inl l) = mTot xq 0 0 Vq (Uq - Vq) l) ∧
      (∀ d, 0 ≤ 63 * (cB d - s d) - mLift d) ∧
      HasSum (fun d => cB d * ∏ l, Xtoy l ^ d l / (d l).factorial)
        ((Bh : ℝ) * (Real.exp Sh * Real.cosh Ah - 1)) ∧
      HasSum (fun d => s d * ∏ l, Xtoy l ^ d l / (d l).factorial) Sv ∧
      ((Dcls + Dvar : ℚ) : ℝ) ≤ Sv := by
  set M := meanValue xq wq yq Uq Vq with hMdef
  set K0 : ℝ := (Bh : ℝ) * (Real.exp Sh * Real.cosh Ah - 1) - M / 63 with hK0
  refine ⟨fun d => mLift d / 63 + (if d = 0 then K0 else 0),
    fun d => if d = 0 then ((Dcls + Dvar : ℚ) : ℝ) else 0, ((Dcls + Dvar : ℚ) : ℝ),
    ?_, fun l => rfl, ?_, ?_, ?_, le_rfl⟩
  · intro l
    rcases l with l | u
    · cases l <;> simp only [Xtoy, Sum.elim_inl, mTot] <;> norm_num [xq, Vq, Uq]
    · simp [Xtoy]
  · intro d
    by_cases hd : d = 0
    · subst hd
      have hm0 : mLift (0 : MLetter ⊕ Unit → ℕ) = 0 := by
        have e0 : toM (0 : MLetter ⊕ Unit → ℕ) = 0 := rfl
        simp only [mLift, e0, mPaper_zero, ite_self]
      simp only [hm0, ↓reduceIte]
      have hc := expcosh_ge
      have hM := meanValue_le
      have hB : (Bh : ℝ) = 2016052216151308472944308654391 / 1000000000000000000000000000000 := by
        norm_num [Bh]
      have hD : ((Dcls + Dvar : ℚ) : ℝ) ≤ 28 / 100 := by norm_num [Dcls, Dvar]
      have hBc : (2016 / 1000 : ℝ) * (3998 / 10000) ≤ (Bh : ℝ) * (Real.exp Sh * Real.cosh Ah - 1) :=
        mul_le_mul (by rw [hB]; norm_num) hc (by norm_num) (by rw [hB]; norm_num)
      norm_num at hBc
      linarith
    · simp only [hd, ↓reduceIte, add_zero, sub_zero]
      linarith
  · have hw : rH * (Uq : ℝ) ≠ 0 := by unfold rH; norm_num [Uq, rhoHq]
    have h1 := (hasSum_mLift (C := Unit) (xq : ℝ) Uq Vq (by norm_num [Vq]) (by norm_num [Vq, Uq])
      hw Xtoy fun l => rfl).div_const 63
    have e1 : rH * (Uq : ℝ) = (wq : ℝ) := by unfold rH; push_cast [wq]; ring
    have e2 : (sigmaQ : ℝ) * (xq : ℝ) = (yq : ℝ) := by push_cast [yq]; ring
    rw [e1, e2] at h1
    have h0 : HasSum (fun d : MLetter ⊕ Unit → ℕ =>
        (if d = 0 then K0 else 0) * ∏ l, Xtoy l ^ d l / (d l).factorial) K0 := by
      have := hasSum_ite_eq (0 : MLetter ⊕ Unit → ℕ) K0
      convert this using 1
      funext d
      by_cases hd : d = 0
      · subst hd; simp
      · simp [hd]
    have h := h1.add h0
    convert h using 1
    · funext d
      ring
    · rw [hK0]
      ring
  · have := hasSum_ite_eq (0 : MLetter ⊕ Unit → ℕ) ((Dcls + Dvar : ℚ) : ℝ)
    convert this using 1
    funext d
    by_cases hd : d = 0
    · subst hd; simp
    · simp [hd]

end Sarkozy.MeanCredit2
