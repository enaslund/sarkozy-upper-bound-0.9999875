module

public import Sarkozy.SpectralD.RootChecks
public import Sarkozy.SpectralD.CxSmallCut
public import Sarkozy.TraceMixing.PhiBound

/-!
# Monotonicity in `p` and rational upper evaluation of the count errors

`paper/sections/14_spectral.tex`, `lem:spectral-monotone` and the scalar inputs of
`thm:spectral-criterion`: the count errors `e_t(p, n) = 2^t (h_t r + n r²)` (`eq:graphs:et`,
`TraceMixing.coarseErr`), the small-pair constants `δ_t = (e_t + e_{t+1})/(1 - e_t)`
(`SpectralD.Cx.smallConst`, `lem:spec:degone`) and the factor `p/(p - 1)·p^{-1/2}` decrease in
`p`. So a bound of an input at the piece start `X` holds at every `p ≥ X` (the "transfer" of the
anchor values, `lem:spectral-monotone`).

* `eQ`, `scQ`: `e_t` and `δ_t` over `ℚ`, with a rational `r ≥ X^{-1/2}` in place of
  `X^{-1/2}`; `coarseErr_le_eQ`, `smallConst_le_scQ`: the real values at `X` are at most these.
* `smallConst_anti`: `δ_t(p) ≤ δ_t(X)` for `X ≤ p`.
* `sqrtFactor_anti`: `p/(p-1)·p^{-1/2} ≤ X/(X-1)·X^{-1/2}` for `1 < X ≤ p`.
* `inv_sqrt_le_of_sq`: `X^{-1/2} ≤ r` from `r ≥ 0`, `r² X ≥ 1`.
-/

@[expose] public section

namespace Sarkozy.MiddlePrimeInputs

open Finset Sarkozy.SpectralD.Cx

/-- The count error `e_t(X, n)` over `ℚ`, with `r` in place of `X^{-1/2}`. -/
def eQ (t n : ℕ) (P r : ℚ) : ℚ := 2 ^ t * (((t : ℚ) / 2 - 1 + (1 / 2) ^ t) * r + n / P)

/-- The small-pair constant `δ_d = (e_d + e_{d+1})/(1 - e_d)` over `ℚ`. -/
def scQ (d n : ℕ) (P r : ℚ) : ℚ := (eQ d n P r + eQ (d + 1) n P r) / (1 - eQ d n P r)

/-- `X^{-1/2} ≤ r` from `0 ≤ r` and `1 ≤ r² X`. -/
theorem inv_sqrt_le_of_sq {X : ℕ} {r : ℚ} (hr0 : 0 ≤ r) (hr : 1 ≤ r ^ 2 * X) :
    (Real.sqrt X)⁻¹ ≤ (r : ℝ) := by
  have hr' : (1 : ℝ) ≤ (r : ℝ) ^ 2 * X := by exact_mod_cast hr
  have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hX0 : (0 : ℝ) < X := by
    rcases Nat.eq_zero_or_pos X with h | h
    · subst h; norm_num at hr'
    · exact_mod_cast h
  have hs0 : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hss : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  rw [inv_le_iff_one_le_mul₀ hs0]
  have h1 : (1 : ℝ) ≤ ((r : ℝ) * Real.sqrt X) ^ 2 := by nlinarith
  have h2 : 0 ≤ (r : ℝ) * Real.sqrt X := mul_nonneg hr0' hs0.le
  nlinarith

/-- **`e_t(X, n) ≤ eQ t n X r`** for `X^{-1/2} ≤ r`. -/
theorem coarseErr_le_eQ {X : ℕ} {r : ℚ} (hr : (Real.sqrt X)⁻¹ ≤ (r : ℝ)) (t n : ℕ) :
    TraceMixing.coarseErr X t n ≤ (eQ t n X r : ℝ) := by
  unfold TraceMixing.coarseErr eQ
  push_cast
  have hH := TraceMixing.coarseH_nonneg t
  have h1 := mul_le_mul_of_nonneg_left hr hH
  have h2 : (0 : ℝ) ≤ 2 ^ t := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) h2

/-- `(a + b)/(1 - a)` is monotone in `a < 1` and `b`, for `a, b ≥ 0`. -/
theorem frac_mono {a b a' b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haa : a ≤ a') (hbb : b ≤ b')
    (ha1 : a' < 1) : (a + b) / (1 - a) ≤ (a' + b') / (1 - a') := by
  have h1 : 0 < 1 - a' := by linarith
  have h2 : 1 - a' ≤ 1 - a := by linarith
  calc (a + b) / (1 - a) ≤ (a' + b') / (1 - a) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
    _ ≤ (a' + b') / (1 - a') := div_le_div_of_nonneg_left (by linarith) h1 h2

/-- **`δ_d(X) ≤ scQ d n X r`** for `X^{-1/2} ≤ r` and `eQ d n X r < 1`. -/
theorem smallConst_le_scQ {X : ℕ} (hX : 0 < X) {r : ℚ} (hr : (Real.sqrt X)⁻¹ ≤ (r : ℝ))
    (d n : ℕ) (h1 : eQ d n X r < 1) :
    smallConst X d n ≤ (scQ d n X r : ℝ) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have h1' : (eQ d n X r : ℝ) < 1 := by exact_mod_cast h1
  unfold smallConst
  have := frac_mono (TraceMixing.coarseErr_nonneg hX0 d n)
    (TraceMixing.coarseErr_nonneg hX0 (d + 1) n) (coarseErr_le_eQ hr d n)
    (coarseErr_le_eQ hr (d + 1) n) h1'
  unfold scQ
  push_cast
  exact this

/-- **`δ_d(p) ≤ δ_d(X)`** for `0 < X ≤ p` and `e_d(X, n) < 1` (`lem:spectral-monotone`). -/
theorem smallConst_anti {X p : ℕ} (hX : 0 < X) (hXp : X ≤ p) (d n : ℕ)
    (h1 : TraceMixing.coarseErr X d n < 1) : smallConst p d n ≤ smallConst X d n := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hXp' : (X : ℝ) ≤ p := by exact_mod_cast hXp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le hX0 hXp'
  unfold smallConst
  exact frac_mono (TraceMixing.coarseErr_nonneg hp0 d n)
    (TraceMixing.coarseErr_nonneg hp0 (d + 1) n)
    (SpectralD.Root.coarseErr_antitone hX0 hXp' d n)
    (SpectralD.Root.coarseErr_antitone hX0 hXp' (d + 1) n) h1

/-- `0 ≤ δ_d(p)` when `e_d(p, n) < 1`. -/
theorem smallConst_nonneg' {p : ℕ} (hp : 0 < p) (d n : ℕ)
    (h1 : TraceMixing.coarseErr p d n < 1) : 0 ≤ smallConst p d n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  unfold smallConst
  exact div_nonneg (add_nonneg (TraceMixing.coarseErr_nonneg hp0 d n)
    (TraceMixing.coarseErr_nonneg hp0 (d + 1) n)) (by linarith)

/-- **`p/(p-1)·p^{-1/2} ≤ X/(X-1)·X^{-1/2}`** for `1 < X ≤ p`. -/
theorem sqrtFactor_anti {X P : ℝ} (hX : 1 < X) (hXP : X ≤ P) :
    P / (P - 1) * (Real.sqrt P)⁻¹ ≤ X / (X - 1) * (Real.sqrt X)⁻¹ := by
  have hP : 1 < P := lt_of_lt_of_le hX hXP
  set s := Real.sqrt P with hs
  set t := Real.sqrt X with ht
  have ht1 : 1 < t := by
    rw [ht, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) hX
  have hts : t ≤ s := Real.sqrt_le_sqrt hXP
  have hss : s * s = P := Real.mul_self_sqrt (by linarith)
  have htt : t * t = X := Real.mul_self_sqrt (by linarith)
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have e1 : P / (P - 1) * s⁻¹ = s / (P - 1) := by
    field_simp
    rw [← hss]
    ring
  have e2 : X / (X - 1) * t⁻¹ = t / (X - 1) := by
    field_simp
    rw [← htt]
    ring
  rw [e1, e2, div_le_div_iff₀ (by linarith) (by linarith)]
  rw [← hss, ← htt]
  nlinarith [mul_nonneg (sub_nonneg.mpr hts) (by positivity : (0 : ℝ) ≤ s * t + 1)]

end Sarkozy.MiddlePrimeInputs
