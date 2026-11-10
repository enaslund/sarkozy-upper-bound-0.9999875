module

public import Sarkozy.DensityUpgrade.Conditioning

/-!
# A collision conditioning bound: range `4/3 ≤ r ≤ 3/2` and the conditioning assertion
(`lem:density:conditioning`)

`paper/sections/31_density_induction_upgrade.tex`, Lemma "A collision conditioning
bound" (`lem:density:conditioning`). Its first assertion reads:

> For `d₀ ≤ 6` nonnegative functions `f_i`, each depending on one coordinate and
> normalized by `‖f_i‖_r = 1` under its own marginal `μ_i`, put `M = ∏_i E_{μ_i} f_i`.
> Under any joint law (coupling) on the product space whose one-coordinate marginals
> are exactly the `μ_i`, `E ∏_i f_i ≥ M − B_r (1 − M)`, where one may take
> `B_r = 1280` for `2 ≤ r ≤ 6`, or `B_r = 1024` for `4/3 ≤ r ≤ 3/2`.

The range `2 ≤ r` is `conditioning_collision_bound` in
`Sarkozy.DensityUpgrade.Conditioning`. This file proves the range `4/3 ≤ r ≤ 3/2` with
`B_r = 1024` (`conditioning_collision_bound_small_exponent`), in the same formalization:
nonnegative real random variables `X i` (`i : Fin d`) on a finite probability space
`(Ω, p)` with `E (X i)^r = 1` (real power) and `M = ∏ i, E (X i)`; only the joint law
enters. The general form `conditioning_collision_bound_of_le_two` holds for every
`1 < r ≤ 2`, any `d`, and any `B ≥ max 1 (18 d / (r (r - 1)))`; for `4/3 ≤ r ≤ 3/2` and
`d ≤ 6` this is at most `243`.

The proof follows the paper: `∏ x_i ≥ (1 − W)(1 + Z) = 1 + ∑ (x_i − 1) − W Z`
(`conditioning_prod_ge`), the lower bounds of `φ_r(x) = x^r − 1 − r (x − 1)`
(`conditioning_phi_dev`: `r(r−1)(x−1)^2/4` on `[0,1]`, `r(r−1)(x−1)^2/6` on `[1,2]`,
`r(r−1)(x−1)/6` on `[2,∞)`), and normalization by `m_i = E X i` when `M ≥ 1/2`
(positivity handles `M < 1/2`). Deviations: the `φ_r` bounds are obtained from Bernoulli's
inequality at the midpoint `(1 + x)/2` (or at `3/2`) rather than from Taylor's formula;
each product `w_i z_j` is bounded by `w_i^2/2 + min(z_j^2, z_j)` and summed over all
`d^2` pairs; and `∑ (m_i^{-r} − 1) ≤ ∑ (m_i^{-2} − 1) ≤ M^{-2} − 1` replaces
`m_i^{-r} − 1 ≤ r 2^{r+1} (1 − m_i)`.

The lemma's second (conditioning) assertion reads:

> Suppose a positive law `π_0` has unit mixed `L^s`, and `π` is `π_0` conditioned on the
> complement of an event of `π_0`-mass `η`, and `π_0` conditioned on the event has the same
> one-coordinate marginals as `π_0`. If `r > s` lies in one of these ranges, then `π` has
> unit mixed `L^r` whenever `(B_r + 1) η ≤ (r − s)/(s (r − 1))`.

It is formalized as `conditioning_unit_mixed` (range `2 ≤ r ≤ 6`, gate
`(1280 + 1) η ≤ (r − s)/(s (r − 1))`) and `conditioning_unit_mixed_small_exponent` (range
`4/3 ≤ r ≤ 3/2`, gate `(1024 + 1) η ≤ …`), for weights on `Fin d → X` (`d ≤ 6`, `X` a
finite nonempty alphabet), with `conditioningUnitMixed` the real-function form of
`def:density:mixed-moment` (`paper/sections/30_density_moment_upgrade.tex`), the norms
taken for the uniform probability on `X` (`conditioningNorm`), and
`conditioningUniformCoords` the uniform-coordinate condition. The law is written as a
mixture `π_0 = (1 − η) π + η ρ` of probability weights; conditioning `π_0` on the
complement of an event of mass `η` and on the event is the special case with disjoint
supports, and "the same one-coordinate marginals as `π_0`" is the hypothesis that `ρ`
and `π_0` both have uniform coordinates. The proof is the paper's: normalize the inputs
in `L^r` and take absolute values (`conditioning_unit_mixed_of_first`); interpolation
`‖f_v‖_s ≤ m_v^α`, `α = (r − s)/(s (r − 1))` (`conditioning_interpolation`, Jensen for
the tilted law `π_0 f_v / m_v`); `M^α ≤ 1 − α (1 − M)`; the first assertion for `ρ`; and
division by `1 − η` (`conditioning_gate_core`). Deviations: only real (not complex)
inputs; `1 < s` is assumed (the paper allows `s ≥ 1`); positivity of `π_0` is not used.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.DensityUpgrade

/-- Tangent line of `x ↦ x^r` at `x0 > 0` (Bernoulli's inequality). -/
theorem conditioning_tangent {x x0 r : ℝ} (hx : 0 ≤ x) (hx0 : 0 < x0) (hr : 1 ≤ r) :
    x0 ^ r + r * (x0 ^ r / x0) * (x - x0) ≤ x ^ r := by
  have hs : -1 ≤ x / x0 - 1 := by have := div_nonneg hx hx0.le; linarith
  have hB := one_add_mul_self_le_rpow_one_add hs hr
  rw [show 1 + (x / x0 - 1) = x / x0 by ring, Real.div_rpow hx hx0.le] at hB
  have hP : 0 < x0 ^ r := Real.rpow_pos_of_pos hx0 r
  rw [le_div_iff₀ hP] at hB
  have h : x0 ^ r + r * (x0 ^ r / x0) * (x - x0) = (1 + r * (x / x0 - 1)) * x0 ^ r := by
    field_simp
  linarith

/-- `φ_r(x) = x^r - 1 - r (x - 1) ≥ r (x - x0) (x0^{r-1} - 1)` for every `x0 > 0`. -/
theorem conditioning_phi_ge {x x0 r : ℝ} (hx : 0 ≤ x) (hx0 : 0 < x0) (hr : 1 ≤ r) :
    r * (x - x0) * (x0 ^ r / x0 - 1) ≤ x ^ r - 1 - r * (x - 1) := by
  have hT := conditioning_tangent hx hx0 hr
  have hB := one_add_mul_self_le_rpow_one_add (s := x0 - 1) (by linarith) hr
  rw [show 1 + (x0 - 1) = x0 by ring] at hB
  linarith

/-- Lower bounds of `φ_r` for `1 ≤ r ≤ 2`: `φ_r(x) ≥ r(r-1)(x-1)^2/4` on `[0,1]`,
`≥ r(r-1)(x-1)^2/6` on `[1,2]`, `≥ r(r-1)(x-1)/6` on `[2,∞)`, combined in the
form needed for the opposite-deviation products. -/
theorem conditioning_phi_dev {y r : ℝ} (hy : 0 ≤ y) (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
    r * (r - 1) * ((max (1 - y) 0) ^ 2 / 2 + min ((max (y - 1) 0) ^ 2) (max (y - 1) 0))
      ≤ 6 * (y ^ r - 1 - r * (y - 1)) := by
  have hr0 : 0 ≤ r := by linarith
  have hrr : 0 ≤ r * (r - 1) := mul_nonneg hr0 (by linarith)
  rcases le_total y 1 with h1 | h1
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - y), max_eq_right (by linarith : y - 1 ≤ 0)]
    have hx0 : 0 < (1 + y) / 2 := by linarith
    have hphi := conditioning_phi_ge hy hx0 hr1
    have hQ := rpow_one_add_le_one_add_mul_self (s := (1 + y) / 2 - 1) (by linarith)
      (p := r - 1) (by linarith) (by linarith)
    rw [show 1 + ((1 + y) / 2 - 1) = (1 + y) / 2 by ring, Real.rpow_sub_one hx0.ne'] at hQ
    generalize ((1 + y) / 2) ^ r / ((1 + y) / 2) = Q at hphi hQ
    have key : r * (r - 1) * (y - 1) ^ 2 / 4 ≤ r * (y - (1 + y) / 2) * (Q - 1) := by
      nlinarith [mul_nonneg (mul_nonneg hr0 (by linarith : (0 : ℝ) ≤ (1 + y) / 2 - y))
        (sub_nonneg.2 hQ)]
    have : min ((0 : ℝ) ^ 2) 0 = 0 := by norm_num
    rw [this]
    nlinarith
  · rw [max_eq_right (by linarith : 1 - y ≤ 0), max_eq_left (by linarith : (0 : ℝ) ≤ y - 1)]
    have h0 : ((0 : ℝ) ^ 2 / 2) = 0 := by norm_num
    rw [h0, zero_add]
    rcases le_total y 2 with h2 | h2
    · have hmin := min_le_left ((y - 1) ^ 2) (y - 1)
      have hx0 : 0 < (1 + y) / 2 := by linarith
      have hphi := conditioning_phi_ge hy hx0 hr1
      have hB := one_add_mul_self_le_rpow_one_add (s := (1 + y) / 2 - 1) (by linarith) hr1
      rw [show 1 + ((1 + y) / 2 - 1) = (1 + y) / 2 by ring] at hB
      have hPQ : ((1 + y) / 2) ^ r = (1 + y) / 2 * (((1 + y) / 2) ^ r / ((1 + y) / 2)) := by
        field_simp
      rw [hPQ] at hB
      generalize ((1 + y) / 2) ^ r / ((1 + y) / 2) = Q at hphi hB
      have hQ1 : (r - 1) * ((1 + y) / 2 - 1) ≤ (1 + y) / 2 * (Q - 1) := by linarith
      have hQ0 : 0 ≤ Q - 1 := by
        by_contra hc
        rw [not_le] at hc
        have : (1 + y) / 2 * (Q - 1) < 0 := mul_neg_of_pos_of_neg hx0 hc
        nlinarith
      have hQ2 : (r - 1) * ((1 + y) / 2 - 1) ≤ 3 / 2 * (Q - 1) := by nlinarith
      have key : r * (r - 1) * (y - 1) ^ 2 / 6 ≤ r * (y - (1 + y) / 2) * (Q - 1) := by
        nlinarith [mul_nonneg (mul_nonneg hr0 (by linarith : (0 : ℝ) ≤ (1 + y) / 2 - 1))
          (sub_nonneg.2 hQ2)]
      nlinarith [mul_le_mul_of_nonneg_left hmin hrr]
    · have hmin := min_le_right ((y - 1) ^ 2) (y - 1)
      have hx0 : (0 : ℝ) < 3 / 2 := by norm_num
      have hphi := conditioning_phi_ge hy hx0 hr1
      have hB := one_add_mul_self_le_rpow_one_add (s := (3 / 2 : ℝ) - 1) (by norm_num) hr1
      rw [show 1 + ((3 / 2 : ℝ) - 1) = 3 / 2 by ring] at hB
      have hPQ : ((3 / 2 : ℝ)) ^ r = 3 / 2 * (((3 / 2 : ℝ)) ^ r / (3 / 2)) := by
        field_simp
      rw [hPQ] at hB
      generalize ((3 / 2 : ℝ)) ^ r / (3 / 2) = Q at hphi hB
      have hQ2 : (r - 1) / 3 ≤ Q - 1 := by linarith
      have key : r * (r - 1) * (y - 1) / 6 ≤ r * (y - 3 / 2) * (Q - 1) := by
        nlinarith [mul_nonneg (mul_nonneg hr0 (by linarith : (0 : ℝ) ≤ y - 3 / 2))
          (sub_nonneg.2 hQ2), mul_nonneg hr0 (by linarith : (0 : ℝ) ≤ r - 1)]
      nlinarith [mul_le_mul_of_nonneg_left hmin hrr]

/-- `w z ≤ w^2/2 + min(z^2, z)` for `w ≤ 1`, `0 ≤ z`. -/
theorem conditioning_wz_le {w z : ℝ} (hw1 : w ≤ 1) (hz : 0 ≤ z) :
    w * z ≤ w ^ 2 / 2 + min (z ^ 2) z := by
  rcases le_total z 1 with h | h
  · rw [min_eq_left (by nlinarith)]
    nlinarith [sq_nonneg (w - z)]
  · rw [min_eq_right (by nlinarith)]
    nlinarith

/-- The pointwise inequality `∏ y_i ≥ (1 - W)(1 + Z) = 1 + ∑ (y_i - 1) - W Z` for
nonnegative `y_i`, where `W = ∑ (1 - y_i)_+` and `Z = ∑ (y_i - 1)_+`. -/
theorem conditioning_prod_ge {d : ℕ} (y : Fin d → ℝ) (hy : ∀ i, 0 ≤ y i) :
    1 + ∑ i, (y i - 1) - (∑ i, max (1 - y i) 0) * (∑ i, max (y i - 1) 0) ≤ ∏ i, y i := by
  obtain ⟨w, hw⟩ : ∃ w : Fin d → ℝ, ∀ i, w i = max (1 - y i) 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : Fin d → ℝ, ∀ i, z i = max (y i - 1) 0 := ⟨_, fun _ => rfl⟩
  simp only [← hw, ← hz]
  have hcase : ∀ i, (w i = 1 - y i ∧ z i = 0) ∨ (w i = 0 ∧ z i = y i - 1) := by
    intro i
    rw [hw i, hz i]
    rcases le_total (y i) 1 with h | h
    · left; exact ⟨max_eq_left (by linarith), max_eq_right (by linarith)⟩
    · right; exact ⟨max_eq_right (by linarith), max_eq_left (by linarith)⟩
  have hw0 : ∀ i, 0 ≤ w i := fun i => by rw [hw i]; exact le_max_right _ _
  have hw1 : ∀ i, w i ≤ 1 := fun i => by
    rcases hcase i with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; linarith [hy i]
    · rw [h1]; exact zero_le_one
  have hz0 : ∀ i, 0 ≤ z i := fun i => by rw [hz i]; exact le_max_right _ _
  have hfac : ∀ i, y i = (1 - w i) * (1 + z i) := fun i => by
    rcases hcase i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> ring
  have hdiff : ∀ i, y i - 1 = z i - w i := fun i => by
    rcases hcase i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> ring
  have hprod : ∏ i, y i = (∏ i, (1 - w i)) * ∏ i, (1 + z i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hfac i)
  have hA := conditioning_one_sub_sum_le_prod Finset.univ w (fun i _ => hw0 i)
    (fun i _ => hw1 i)
  have hB := conditioning_one_add_sum_le_prod Finset.univ z (fun i _ => hz0 i)
  have hW0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw0 i)
  have hZ0 : 0 ≤ ∑ i, z i := Finset.sum_nonneg (fun i _ => hz0 i)
  have hmain : (1 - ∑ i, w i) * (1 + ∑ i, z i) ≤ ∏ i, y i := by
    rcases le_total (∑ i, w i) 1 with h | h
    · rw [hprod]
      calc (1 - ∑ i, w i) * (1 + ∑ i, z i)
          ≤ (1 - ∑ i, w i) * ∏ i, (1 + z i) :=
            mul_le_mul_of_nonneg_left hB (by linarith)
        _ ≤ (∏ i, (1 - w i)) * ∏ i, (1 + z i) :=
            mul_le_mul_of_nonneg_right hA (by linarith)
    · have : 0 ≤ ∏ i, y i := Finset.prod_nonneg (fun i _ => hy i)
      nlinarith
  have hsum : ∑ i, (y i - 1) = ∑ i, z i - ∑ i, w i := by
    rw [Finset.sum_congr rfl (fun i _ => hdiff i), Finset.sum_sub_distrib]
  rw [hsum]
  nlinarith

/-- The pointwise inequality in the `φ_r` form used for `1 ≤ r ≤ 2`:
`r (r - 1) (1 + ∑ (y_i - 1) - ∏ y_i) ≤ 6 d ∑ φ_r(y_i)`. -/
theorem conditioning_pointwise_phi {d : ℕ} (y : Fin d → ℝ) (hy : ∀ i, 0 ≤ y i) {r : ℝ}
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
    r * (r - 1) * (1 + ∑ i, (y i - 1) - ∏ i, y i)
      ≤ 6 * d * ∑ i, (y i ^ r - 1 - r * (y i - 1)) := by
  have hP := conditioning_prod_ge y hy
  have hrr : 0 ≤ r * (r - 1) := mul_nonneg (by linarith) (by linarith)
  have hWZ : (∑ i, max (1 - y i) 0) * (∑ i, max (y i - 1) 0)
      ≤ (d : ℝ) * ∑ i, ((max (1 - y i) 0) ^ 2 / 2 + min ((max (y i - 1) 0) ^ 2)
        (max (y i - 1) 0)) := by
    rw [Finset.sum_mul_sum]
    calc ∑ i, ∑ j, max (1 - y i) 0 * max (y j - 1) 0
        ≤ ∑ i, ∑ j, ((max (1 - y i) 0) ^ 2 / 2
          + min ((max (y j - 1) 0) ^ 2) (max (y j - 1) 0)) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
            conditioning_wz_le (max_le (by linarith [hy i]) zero_le_one) (le_max_right _ _)))
      _ = (d : ℝ) * ∑ i, ((max (1 - y i) 0) ^ 2 / 2 + min ((max (y i - 1) 0) ^ 2)
          (max (y i - 1) 0)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_add, Finset.mul_sum]
  have hphi : r * (r - 1) * ∑ i, ((max (1 - y i) 0) ^ 2 / 2 + min ((max (y i - 1) 0) ^ 2)
      (max (y i - 1) 0)) ≤ 6 * ∑ i, (y i ^ r - 1 - r * (y i - 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => conditioning_phi_dev (hy i) hr1 hr2)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : r * (r - 1) * (1 + ∑ i, (y i - 1) - ∏ i, y i)
      ≤ r * (r - 1) * ((∑ i, max (1 - y i) 0) * (∑ i, max (y i - 1) 0)) :=
    mul_le_mul_of_nonneg_left (by linarith) hrr
  have h2 := mul_le_mul_of_nonneg_left hWZ hrr
  have h3 := mul_le_mul_of_nonneg_left hphi hd
  nlinarith

/-- `E φ_r(x/m) = 1/m^r - 1` when `E x^r = 1` and `E x = m > 0`. -/
theorem conditioning_phi_moment {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp1 : ∑ ω, p ω = 1)
    (x : Ω → ℝ) (hx : ∀ ω, 0 ≤ x ω) {m : ℝ} (hm : ∑ ω, p ω * x ω = m) (hm0 : 0 < m) (r : ℝ)
    (hnorm : ∑ ω, p ω * x ω ^ r = 1) :
    ∑ ω, p ω * ((x ω / m) ^ r - 1 - r * (x ω / m - 1)) = 1 / m ^ r - 1 := by
  have h1 := (conditioning_normalized_moments p hp1 x hm hm0.ne').1
  have h : ∀ ω, p ω * ((x ω / m) ^ r - 1 - r * (x ω / m - 1))
      = (p ω * x ω ^ r) * (m ^ r)⁻¹ - p ω - r * (p ω * (x ω / m - 1)) := fun ω => by
    rw [Real.div_rpow (hx ω) hm0.le]; ring
  rw [Finset.sum_congr rfl (fun ω _ => h ω), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hnorm, hp1, h1]
  ring

/-- The closing algebra: from `E ∏ Y ≥ 1 - c S`, `S ≤ 1/M^2 - 1`, `1/2 ≤ M ≤ 1` and
`3 c ≤ B`, `M E ∏ Y ≥ M - B (1 - M)`. -/
theorem conditioning_final_step {M u S c E B : ℝ} (hlarge : 1 / 2 ≤ M) (hM1 : M ≤ 1)
    (huM : u * M = 1) (hS1 : S ≤ u ^ 2 - 1) (hc : 0 ≤ c)
    (hE : 1 - c * S ≤ E) (hB : 3 * c ≤ B) : M - B * (1 - M) ≤ M * E := by
  have hM0 : 0 ≤ M := by linarith
  have hMS : M * S ≤ u - M := by
    have : M * S ≤ M * (u ^ 2 - 1) := mul_le_mul_of_nonneg_left hS1 hM0
    nlinarith
  have hu3 : u - M ≤ 3 * (1 - M) := by nlinarith
  have hstep : M * (1 - c * S) ≤ M * E := mul_le_mul_of_nonneg_left hE hM0
  nlinarith

/-- `lem:density:conditioning`, first assertion, general form for `1 < r ≤ 2`: for
nonnegative real random variables `X i` (`i : Fin d`) on a finite probability space
`(Ω, p)` with `E (X i)^r = 1`, and any `B ≥ max 1 (18 d / (r (r - 1)))`,
`E ∏ X i ≥ M - B (1 - M)` where `M = ∏ i, E (X i)`. -/
theorem conditioning_collision_bound_of_le_two {Ω : Type*} [Fintype Ω] {d : ℕ}
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : Fin d → Ω → ℝ) (hX : ∀ i ω, 0 ≤ X i ω) {r : ℝ} (hr1 : 1 < r) (hr2 : r ≤ 2)
    (hnorm : ∀ i, ∑ ω, p ω * X i ω ^ r = 1) {B : ℝ} (hB1 : 1 ≤ B)
    (hBd : 18 * (d : ℝ) / (r * (r - 1)) ≤ B) :
    (∏ i, ∑ ω, p ω * X i ω) - B * (1 - ∏ i, ∑ ω, p ω * X i ω)
      ≤ ∑ ω, p ω * ∏ i, X i ω := by
  obtain ⟨m, hm⟩ : ∃ m : Fin d → ℝ, ∀ i, ∑ ω, p ω * X i ω = m i := ⟨_, fun _ => rfl⟩
  simp only [hm]
  have hm0 : ∀ i, 0 ≤ m i := fun i => by
    rw [← hm i]; exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hp ω) (hX i ω))
  have hm1 : ∀ i, m i ≤ 1 := fun i => by
    rw [← hm i]
    exact conditioning_mean_le_one p hp hp1 (X i) (hX i) hr1.le (hnorm i).le
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∏ i, m i = M := ⟨_, rfl⟩
  rw [hM]
  have hM0 : 0 ≤ M := by rw [← hM]; exact Finset.prod_nonneg (fun i _ => hm0 i)
  have hM1 : M ≤ 1 := by
    rw [← hM]; exact Finset.prod_le_one₀ (fun i _ => hm0 i) (fun i _ => hm1 i)
  have hE0 : 0 ≤ ∑ ω, p ω * ∏ i, X i ω :=
    Finset.sum_nonneg (fun ω _ => mul_nonneg (hp ω) (Finset.prod_nonneg (fun i _ => hX i ω)))
  rcases lt_or_ge M (1 / 2) with hsmall | hlarge
  · nlinarith
  have hmpos : ∀ i, 0 < m i := by
    intro i
    rcases (hm0 i).lt_or_eq with h | h
    · exact h
    · exfalso
      have : M = 0 := by rw [← hM]; exact Finset.prod_eq_zero (Finset.mem_univ i) h.symm
      linarith
  have hrr : 0 < r * (r - 1) := mul_pos (by linarith) (by linarith)
  have hpt : ∀ ω, r * (r - 1) * (1 + ∑ i, (X i ω / m i - 1) - ∏ i, (X i ω / m i))
      ≤ 6 * d * ∑ i, ((X i ω / m i) ^ r - 1 - r * (X i ω / m i - 1)) := fun ω =>
    conditioning_pointwise_phi (fun i => X i ω / m i) (fun i => div_nonneg (hX i ω) (hm0 i))
      hr1.le hr2
  have hsum := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpt ω) (hp ω))
  have hL : ∑ ω, p ω * (r * (r - 1) * (1 + ∑ i, (X i ω / m i - 1) - ∏ i, (X i ω / m i)))
      = r * (r - 1) * (1 + ∑ i, ∑ ω, p ω * (X i ω / m i - 1)
        - ∑ ω, p ω * ∏ i, (X i ω / m i)) := by
    have h : ∀ ω, p ω * (r * (r - 1) * (1 + ∑ i, (X i ω / m i - 1) - ∏ i, (X i ω / m i)))
        = r * (r - 1) * (p ω + ∑ i, p ω * (X i ω / m i - 1)
          - p ω * ∏ i, (X i ω / m i)) := fun ω => by
      rw [← Finset.mul_sum]; ring
    rw [Finset.sum_congr rfl (fun ω _ => h ω), ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, hp1, Finset.sum_comm (f := fun ω i => p ω * (X i ω / m i - 1))]
  have hR : ∑ ω, p ω * (6 * d * ∑ i, ((X i ω / m i) ^ r - 1 - r * (X i ω / m i - 1)))
      = 6 * d * ∑ i, ∑ ω, p ω * ((X i ω / m i) ^ r - 1 - r * (X i ω / m i - 1)) := by
    have h : ∀ ω, p ω * (6 * d * ∑ i, ((X i ω / m i) ^ r - 1 - r * (X i ω / m i - 1)))
        = 6 * d * ∑ i, p ω * ((X i ω / m i) ^ r - 1 - r * (X i ω / m i - 1)) := fun ω => by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [Finset.sum_congr rfl (fun ω _ => h ω), ← Finset.mul_sum,
      Finset.sum_comm (f := fun ω i => p ω * ((X i ω / m i) ^ r - 1 - r * (X i ω / m i - 1)))]
  rw [hL, hR, Finset.sum_congr rfl (fun i _ =>
      (conditioning_normalized_moments p hp1 (X i) (hm i) (hmpos i).ne').1),
    Finset.sum_congr rfl (fun i _ =>
      conditioning_phi_moment p hp1 (X i) (hX i) (hm i) (hmpos i) r (hnorm i)),
    Finset.sum_const_zero, add_zero] at hsum
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∑ i, (1 / m i ^ r - 1) = S := ⟨_, rfl⟩
  rw [hS] at hsum
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨c, hc⟩ : ∃ c : ℝ, 6 * (d : ℝ) / (r * (r - 1)) = c := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [← hc]; positivity
  have hEY : 1 - c * S ≤ ∑ ω, p ω * ∏ i, (X i ω / m i) := by
    have h1 : c * S = 6 * d * S / (r * (r - 1)) := by rw [← hc]; ring
    have h2 : 1 - ∑ ω, p ω * ∏ i, (X i ω / m i) ≤ 6 * d * S / (r * (r - 1)) := by
      rw [le_div_iff₀ hrr]; linarith
    linarith
  have hEXY : ∑ ω, p ω * ∏ i, X i ω = M * ∑ ω, p ω * ∏ i, (X i ω / m i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    have : ∏ i, X i ω = M * ∏ i, (X i ω / m i) := by
      rw [← hM, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      field_simp [(hmpos i).ne']
    rw [this]
    ring
  have hMpos : 0 < M := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / M := ⟨_, rfl⟩
  have huM : u * M = 1 := by rw [hu]; field_simp
  have hS1 : S ≤ u ^ 2 - 1 := by
    have h1 : S ≤ ∑ i, (1 / m i ^ 2 - 1) := by
      rw [← hS]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have h2 : m i ^ (2 : ℝ) ≤ m i ^ r :=
        Real.rpow_le_rpow_of_exponent_ge (hmpos i) (hm1 i) hr2
      rw [Real.rpow_two] at h2
      have h3 : 0 < m i ^ 2 := pow_pos (hmpos i) 2
      have h4 : 1 / m i ^ r ≤ 1 / m i ^ 2 := one_div_le_one_div_of_le h3 h2
      linarith
    have h2 := conditioning_one_add_sum_le_prod Finset.univ (fun i => 1 / m i ^ 2 - 1)
      (fun i _ => by
        have h := hmpos i
        have h' := hm1 i
        rw [sub_nonneg, le_div_iff₀ (by positivity)]
        nlinarith)
    have h3 : ∏ i, (1 + (1 / m i ^ 2 - 1)) = u ^ 2 := by
      rw [Finset.prod_congr rfl (fun i _ => (by ring : 1 + (1 / m i ^ 2 - 1) = 1 / m i ^ 2)),
        Finset.prod_div_distrib, Finset.prod_const_one, Finset.prod_pow, hM, hu]
      ring
    linarith
  rw [hEXY]
  refine conditioning_final_step hlarge hM1 huM hS1 hc0 hEY ?_
  rw [← hc]
  calc 3 * (6 * (d : ℝ) / (r * (r - 1))) = 18 * d / (r * (r - 1)) := by ring
    _ ≤ B := hBd

/-- `lem:density:conditioning`, first assertion, range `4/3 ≤ r ≤ 3/2` with the paper's
constant `B_r = 1024` and `d₀ ≤ 6`: for nonnegative real random variables `X i`
(`i : Fin d`, `d ≤ 6`) on a finite probability space `(Ω, p)` with `E (X i)^r = 1`,
`E ∏ X i ≥ M - 1024 (1 - M)`, `M = ∏ i, E (X i)`. -/
theorem conditioning_collision_bound_small_exponent {Ω : Type*} [Fintype Ω] {d : ℕ}
    (hd : d ≤ 6) (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : Fin d → Ω → ℝ) (hX : ∀ i ω, 0 ≤ X i ω) {r : ℝ} (hr1 : 4 / 3 ≤ r) (hr2 : r ≤ 3 / 2)
    (hnorm : ∀ i, ∑ ω, p ω * X i ω ^ r = 1) :
    (∏ i, ∑ ω, p ω * X i ω) - 1024 * (1 - ∏ i, ∑ ω, p ω * X i ω)
      ≤ ∑ ω, p ω * ∏ i, X i ω := by
  refine conditioning_collision_bound_of_le_two p hp hp1 X hX (by linarith) (by linarith)
    hnorm (by norm_num) ?_
  have hrr : 4 / 9 ≤ r * (r - 1) := by nlinarith
  have hd' : (d : ℝ) ≤ 6 := by exact_mod_cast hd
  rw [div_le_iff₀ (by linarith)]
  nlinarith


/-- Interpolation between `L^1` and `L^r` on a finite probability space: for `f ≥ 0`
with `E f^r = 1`, `E f = m > 0` and `1 < s < r`, `E f^s ≤ m^((r - s)/(r - 1))`. -/
theorem conditioning_interpolation {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) {r s : ℝ} (hs : 1 < s) (hsr : s < r)
    (hnorm : ∑ ω, p ω * f ω ^ r = 1) {m : ℝ} (hm : ∑ ω, p ω * f ω = m) (hm0 : 0 < m) :
    ∑ ω, p ω * f ω ^ s ≤ m ^ ((r - s) / (r - 1)) := by
  have hs1 : s - 1 ≠ 0 := (by linarith : (0 : ℝ) < s - 1).ne'
  have hr1 : r - 1 ≠ 0 := (by linarith : (0 : ℝ) < r - 1).ne'
  have hP : 1 ≤ (r - 1) / (s - 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hq : ∀ ω ∈ Finset.univ, 0 ≤ p ω * f ω / m := fun ω _ =>
    div_nonneg (mul_nonneg (hp ω) (hf ω)) hm0.le
  have hq1 : ∑ ω, p ω * f ω / m = 1 := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, hm, mul_inv_cancel₀ hm0.ne']
  have hz : ∀ ω ∈ Finset.univ, 0 ≤ f ω ^ (s - 1) := fun ω _ => Real.rpow_nonneg (hf ω) _
  have hJ := Real.arith_mean_le_rpow_mean (s := Finset.univ) (fun ω => p ω * f ω / m)
    (fun ω => f ω ^ (s - 1)) hq hq1 hz hP
  have e1 : ∀ ω, p ω * f ω / m * f ω ^ (s - 1) = p ω * f ω ^ s * m⁻¹ := fun ω => by
    have : f ω ^ s = f ω ^ (1 + (s - 1)) := by ring_nf
    rw [this, Real.rpow_add' (hf ω) (by linarith), Real.rpow_one]
    ring
  have e2 : ∀ ω, p ω * f ω / m * (f ω ^ (s - 1)) ^ ((r - 1) / (s - 1))
      = p ω * f ω ^ r * m⁻¹ := fun ω => by
    rw [← Real.rpow_mul (hf ω), show (s - 1) * ((r - 1) / (s - 1)) = r - 1 by
      field_simp]
    have : f ω ^ r = f ω ^ (1 + (r - 1)) := by ring_nf
    rw [this, Real.rpow_add' (hf ω) (by linarith), Real.rpow_one]
    ring
  simp only [e1, e2] at hJ
  rw [← Finset.sum_mul, ← Finset.sum_mul, hnorm, one_mul, Real.inv_rpow hm0.le] at hJ
  have h3 : m ^ ((r - s) / (r - 1)) = m * (m ^ (1 / ((r - 1) / (s - 1))))⁻¹ := by
    rw [show (r - s) / (r - 1) = 1 - 1 / ((r - 1) / (s - 1)) by
      field_simp
      ring, Real.rpow_sub hm0, Real.rpow_one, div_eq_mul_inv]
  rw [h3]
  have h4 := mul_le_mul_of_nonneg_left hJ hm0.le
  calc ∑ ω, p ω * f ω ^ s = m * ((∑ ω, p ω * f ω ^ s) * m⁻¹) := by
        field_simp
    _ ≤ _ := h4

/-- `(∏ f_i)^a = ∏ f_i^a` for nonnegative `f_i`. -/
theorem conditioning_prod_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    (a : ℝ) : (∏ i ∈ s, f i) ^ a = ∏ i ∈ s, f i ^ a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj,
      Real.mul_rpow (hf j (Finset.mem_insert_self j s))
        (Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- `lem:density:conditioning`, conditioning assertion, core form for nonnegative inputs
normalized in `L^r`. The law `π₀ = (1 - η) π + η ρ` is a mixture of probability laws `π`
(the conditioned law) and `ρ` (the law on the event, here any law), the random variables
`X v ≥ 0` have `E_{π₀} (X v)^r = 1`, `ρ` has the same means as `π₀` (`hmean`), `ρ` satisfies
the first assertion with constant `B` (`hfirst`), and `π₀` satisfies the unit mixed `L^s`
bound for these inputs (`hunit`). Under the gate `(B + 1) η ≤ (r - s)/(s (r - 1))`,
`E_π ∏ X v ≤ 1`. -/
theorem conditioning_gate_core {Ω : Type*} [Fintype Ω] {d : ℕ}
    (π₀ π ρ : Ω → ℝ) (hπ : ∀ ω, 0 ≤ π ω) (hπ1 : ∑ ω, π ω = 1) (hρ : ∀ ω, 0 ≤ ρ ω)
    (hρ1 : ∑ ω, ρ ω = 1) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hmix : ∀ ω, π₀ ω = (1 - η) * π ω + η * ρ ω)
    (X : Fin d → Ω → ℝ) (hX : ∀ v ω, 0 ≤ X v ω) {r s B : ℝ} (hs : 1 < s) (hsr : s < r)
    (hnorm : ∀ v, ∑ ω, π₀ ω * X v ω ^ r = 1)
    (hmean : ∀ v, ∑ ω, ρ ω * X v ω = ∑ ω, π₀ ω * X v ω)
    (hfirst : (∏ v, ∑ ω, ρ ω * X v ω) - B * (1 - ∏ v, ∑ ω, ρ ω * X v ω)
      ≤ ∑ ω, ρ ω * ∏ v, X v ω)
    (hunit : ∑ ω, π₀ ω * ∏ v, X v ω ≤ ∏ v, (∑ ω, π₀ ω * X v ω ^ s) ^ (1 / s))
    (hgate : (B + 1) * η ≤ (r - s) / (s * (r - 1))) :
    ∑ ω, π ω * ∏ v, X v ω ≤ 1 := by
  have hπ₀ : ∀ ω, 0 ≤ π₀ ω := fun ω => by
    rw [hmix ω]
    exact add_nonneg (mul_nonneg (by linarith) (hπ ω)) (mul_nonneg hη0 (hρ ω))
  have hπ₀1 : ∑ ω, π₀ ω = 1 := by
    rw [Finset.sum_congr rfl (fun ω _ => hmix ω), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hπ1, hρ1]
    ring
  simp only [hmean] at hfirst
  obtain ⟨m, hm⟩ : ∃ m : Fin d → ℝ, ∀ v, ∑ ω, π₀ ω * X v ω = m v := ⟨_, fun _ => rfl⟩
  simp only [hm] at hfirst
  have hm0 : ∀ v, 0 ≤ m v := fun v => by
    rw [← hm v]; exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hπ₀ ω) (hX v ω))
  have hm1 : ∀ v, m v ≤ 1 := fun v => by
    rw [← hm v]
    exact conditioning_mean_le_one π₀ hπ₀ hπ₀1 (X v) (hX v) (by linarith) (hnorm v).le
  have hmpos : ∀ v, 0 < m v := by
    intro v
    rcases (hm0 v).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : ∀ ω ∈ Finset.univ, π₀ ω * X v ω = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ => mul_nonneg (hπ₀ ω) (hX v ω))).1
          ((hm v).trans h.symm)
      have hz' : ∑ ω, π₀ ω * X v ω ^ r = 0 := by
        refine Finset.sum_eq_zero (fun ω hω => ?_)
        rcases mul_eq_zero.1 (hz ω hω) with h1 | h1
        · rw [h1, zero_mul]
        · rw [h1, Real.zero_rpow (by linarith), mul_zero]
      rw [hnorm v] at hz'
      exact one_ne_zero hz'
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∏ v, m v = M := ⟨_, rfl⟩
  rw [hM] at hfirst
  have hM0 : 0 ≤ M := by rw [← hM]; exact Finset.prod_nonneg (fun v _ => hm0 v)
  have hM1 : M ≤ 1 := by
    rw [← hM]; exact Finset.prod_le_one₀ (fun v _ => hm0 v) (fun v _ => hm1 v)
  obtain ⟨α, hα⟩ : ∃ α : ℝ, (r - s) / (s * (r - 1)) = α := ⟨_, rfl⟩
  rw [hα] at hgate
  have hα0 : 0 ≤ α := by
    rw [← hα]; exact div_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have hα1 : α ≤ 1 := by
    rw [← hα, div_le_one (mul_pos (by linarith) (by linarith))]; nlinarith
  -- interpolation: `‖X v‖_s ≤ m_v^α`
  have hint : ∀ v, (∑ ω, π₀ ω * X v ω ^ s) ^ (1 / s) ≤ m v ^ α := fun v => by
    have h := conditioning_interpolation π₀ hπ₀ (X v) (hX v) hs hsr (hnorm v) (hm v) (hmpos v)
    have h2 := Real.rpow_le_rpow (Finset.sum_nonneg (fun ω _ => mul_nonneg (hπ₀ ω)
      (Real.rpow_nonneg (hX v ω) s))) h (by positivity : (0 : ℝ) ≤ 1 / s)
    rw [← Real.rpow_mul (hmpos v).le] at h2
    rw [show (r - s) / (r - 1) * (1 / s) = α by
      rw [← hα]; field_simp] at h2
    exact h2
  have hprod : ∏ v, (∑ ω, π₀ ω * X v ω ^ s) ^ (1 / s) ≤ M ^ α := by
    rw [← hM, conditioning_prod_rpow Finset.univ m (fun v _ => hm0 v) α]
    exact Finset.prod_le_prod₀ (fun v _ => Real.rpow_nonneg (Finset.sum_nonneg (fun ω _ =>
      mul_nonneg (hπ₀ ω) (Real.rpow_nonneg (hX v ω) s))) _) (fun v _ => hint v)
  have hconc := rpow_one_add_le_one_add_mul_self (s := M - 1) (by linarith) hα0 hα1
  rw [show 1 + (M - 1) = M by ring] at hconc
  have hsplit : ∑ ω, π₀ ω * ∏ v, X v ω
      = (1 - η) * ∑ ω, π ω * ∏ v, X v ω + η * ∑ ω, ρ ω * ∏ v, X v ω := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [hmix ω]
    ring
  have hfin : (1 - η) * ∑ ω, π ω * ∏ v, X v ω ≤ 1 - η := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - M)
      (by linarith : (0 : ℝ) ≤ α - (B + 1) * η)]
  have hη' : 0 < 1 - η := by linarith
  by_contra hc
  rw [not_le] at hc
  have := mul_lt_mul_of_pos_left hc hη'
  linarith

/-- `lem:density:conditioning`, conditioning assertion, range `2 ≤ r ≤ 6` (`B_r = 1280`,
`d₀ ≤ 6`), for nonnegative inputs normalized in `L^r`: `π₀ = (1 - η) π + η ρ`, the law `ρ`
on the event has the same one-coordinate moments as `π₀` (`hmargr`, `hmean`), and `π₀`
satisfies the unit mixed `L^s` bound for these inputs (`hunit`). If
`(1280 + 1) η ≤ (r - s)/(s (r - 1))` then `E_π ∏ X v ≤ 1`. -/
theorem conditioning_gate {Ω : Type*} [Fintype Ω] {d : ℕ} (hd : d ≤ 6)
    (π₀ π ρ : Ω → ℝ) (hπ : ∀ ω, 0 ≤ π ω) (hπ1 : ∑ ω, π ω = 1) (hρ : ∀ ω, 0 ≤ ρ ω)
    (hρ1 : ∑ ω, ρ ω = 1) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hmix : ∀ ω, π₀ ω = (1 - η) * π ω + η * ρ ω)
    (X : Fin d → Ω → ℝ) (hX : ∀ v ω, 0 ≤ X v ω) {r s : ℝ} (hs : 1 < s) (hsr : s < r)
    (hr : 2 ≤ r) (hr6 : r ≤ 6)
    (hnorm : ∀ v, ∑ ω, π₀ ω * X v ω ^ r = 1) (hmargr : ∀ v, ∑ ω, ρ ω * X v ω ^ r = 1)
    (hmean : ∀ v, ∑ ω, ρ ω * X v ω = ∑ ω, π₀ ω * X v ω)
    (hunit : ∑ ω, π₀ ω * ∏ v, X v ω ≤ ∏ v, (∑ ω, π₀ ω * X v ω ^ s) ^ (1 / s))
    (hgate : (1280 + 1) * η ≤ (r - s) / (s * (r - 1))) :
    ∑ ω, π ω * ∏ v, X v ω ≤ 1 :=
  conditioning_gate_core π₀ π ρ hπ hπ1 hρ hρ1 hη0 hη1 hmix X hX hs hsr hnorm hmean
    (conditioning_collision_bound hd ρ hρ hρ1 X hX hr hr6 hmargr) hunit hgate

/-- `lem:density:conditioning`, conditioning assertion, range `4/3 ≤ r ≤ 3/2`
(`B_r = 1024`, `d₀ ≤ 6`), in the form of `conditioning_gate`: if
`(1024 + 1) η ≤ (r - s)/(s (r - 1))` then `E_π ∏ X v ≤ 1`. -/
theorem conditioning_gate_small_exponent {Ω : Type*} [Fintype Ω] {d : ℕ} (hd : d ≤ 6)
    (π₀ π ρ : Ω → ℝ) (hπ : ∀ ω, 0 ≤ π ω) (hπ1 : ∑ ω, π ω = 1) (hρ : ∀ ω, 0 ≤ ρ ω)
    (hρ1 : ∑ ω, ρ ω = 1) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hmix : ∀ ω, π₀ ω = (1 - η) * π ω + η * ρ ω)
    (X : Fin d → Ω → ℝ) (hX : ∀ v ω, 0 ≤ X v ω) {r s : ℝ} (hs : 1 < s) (hsr : s < r)
    (hr1 : 4 / 3 ≤ r) (hr2 : r ≤ 3 / 2)
    (hnorm : ∀ v, ∑ ω, π₀ ω * X v ω ^ r = 1) (hmargr : ∀ v, ∑ ω, ρ ω * X v ω ^ r = 1)
    (hmean : ∀ v, ∑ ω, ρ ω * X v ω = ∑ ω, π₀ ω * X v ω)
    (hunit : ∑ ω, π₀ ω * ∏ v, X v ω ≤ ∏ v, (∑ ω, π₀ ω * X v ω ^ s) ^ (1 / s))
    (hgate : (1024 + 1) * η ≤ (r - s) / (s * (r - 1))) :
    ∑ ω, π ω * ∏ v, X v ω ≤ 1 :=
  conditioning_gate_core π₀ π ρ hπ hπ1 hρ hρ1 hη0 hη1 hmix X hX hs hsr hnorm hmean
    (conditioning_collision_bound_small_exponent hd ρ hρ hρ1 X hX hr1 hr2 hmargr) hunit hgate


/-- The `L^r` norm of `g : X → ℝ` for the uniform probability on the finite set `X`. -/
noncomputable def conditioningNorm {X : Type*} [Fintype X] (r : ℝ) (g : X → ℝ) : ℝ :=
  ((∑ a, |g a| ^ r) / Fintype.card X) ^ r⁻¹

/-- `def:density:mixed-moment`, for real functions: a weight `π` on `Fin d → X` has
unit mixed `L^r` norm if `|∑ x, π x ∏ v, f v (x v)| ≤ ∏ v, ‖f v‖_{L^r(X)}`. -/
def conditioningUnitMixed {X : Type*} [Fintype X] {d : ℕ} (π : (Fin d → X) → ℝ) (r : ℝ) :
    Prop :=
  ∀ f : Fin d → X → ℝ, |∑ x, π x * ∏ v, f v (x v)| ≤ ∏ v, conditioningNorm r (f v)

/-- Each coordinate of the weight `π` on `Fin d → X` is uniform on `X`. -/
def conditioningUniformCoords {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}
    (π : (Fin d → X) → ℝ) : Prop :=
  ∀ v a, ∑ x ∈ Finset.univ.filter (fun x : Fin d → X => x v = a), π x = 1 / Fintype.card X

/-- One-coordinate expectations under a law with uniform coordinates. -/
theorem conditioning_marginal_sum {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}
    (π : (Fin d → X) → ℝ) (hπ : conditioningUniformCoords π) (v : Fin d) (g : X → ℝ) :
    ∑ x, π x * g (x v) = (∑ a, g a) * (Fintype.card X : ℝ)⁻¹ := by
  rw [← Finset.sum_fiberwise Finset.univ (fun x : Fin d → X => x v)
    (fun x => π x * g (x v)), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]),
    ← Finset.sum_mul, hπ v a]
  ring

/-- `lem:density:conditioning`, conditioning assertion, for real inputs and a generic
constant `B` for which the first assertion holds under `ρ` (`hfirst`): if
`π₀ = (1 - η) π + η ρ`, `π₀` and `ρ` have uniform coordinates, `π₀` has unit mixed `L^s`,
and `(B + 1) η ≤ (r - s)/(s (r - 1))`, then `π` has unit mixed `L^r`. -/
theorem conditioning_unit_mixed_of_first {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d : ℕ} (π₀ π ρ : (Fin d → X) → ℝ) (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hmix : ∀ x, π₀ x = (1 - η) * π x + η * ρ x)
    (hπ₀u : conditioningUniformCoords π₀) (hρu : conditioningUniformCoords ρ)
    {r s B : ℝ} (hs : 1 < s) (hsr : s < r)
    (hfirst : ∀ Y : Fin d → (Fin d → X) → ℝ, (∀ v x, 0 ≤ Y v x) →
      (∀ v, ∑ x, ρ x * Y v x ^ r = 1) →
      (∏ v, ∑ x, ρ x * Y v x) - B * (1 - ∏ v, ∑ x, ρ x * Y v x) ≤ ∑ x, ρ x * ∏ v, Y v x)
    (hunit : conditioningUnitMixed π₀ s)
    (hgate : (B + 1) * η ≤ (r - s) / (s * (r - 1))) :
    conditioningUnitMixed π r := by
  intro f
  have hr0 : r ≠ 0 := by linarith
  have hcard : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hN0 : ∀ v, 0 ≤ conditioningNorm r (f v) := fun v =>
    Real.rpow_nonneg (div_nonneg (Finset.sum_nonneg (fun a _ =>
      Real.rpow_nonneg (abs_nonneg _) _)) hcard.le) _
  by_cases hz : ∃ v, conditioningNorm r (f v) = 0
  · obtain ⟨v, hv⟩ := hz
    have hf0 : ∀ a, f v a = 0 := by
      intro a
      have h1 := (Real.rpow_eq_zero_iff_of_nonneg (div_nonneg (Finset.sum_nonneg (fun a _ =>
        Real.rpow_nonneg (abs_nonneg _) _)) hcard.le)).1 hv
      have h2 : ∑ a, |f v a| ^ r = 0 := by
        rcases div_eq_zero_iff.1 h1.1 with h | h
        · exact h
        · exact absurd h hcard.ne'
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
        Real.rpow_nonneg (abs_nonneg (f v a)) r)).1 h2 a (Finset.mem_univ a)
      have h4 := ((Real.rpow_eq_zero_iff_of_nonneg (abs_nonneg (f v a))).1 h3).1
      exact abs_eq_zero.1 h4
    have hL : ∑ x, π x * ∏ w, f w (x w) = 0 :=
      Finset.sum_eq_zero (fun x _ => by
        rw [Finset.prod_eq_zero (Finset.mem_univ v) (hf0 (x v)), mul_zero])
    rw [hL, abs_zero, Finset.prod_eq_zero (Finset.mem_univ v) hv]
  · rw [not_exists] at hz
    have hNpos : ∀ v, 0 < conditioningNorm r (f v) := fun v =>
      lt_of_le_of_ne (hN0 v) (Ne.symm (hz v))
    set N : Fin d → ℝ := fun v => conditioningNorm r (f v) with hNdef
    have hNr : ∀ v, N v ^ r = (∑ a, |f v a| ^ r) / Fintype.card X := fun v => by
      simp only [hNdef, conditioningNorm]
      exact Real.rpow_inv_rpow (div_nonneg (Finset.sum_nonneg (fun a _ =>
        Real.rpow_nonneg (abs_nonneg _) _)) hcard.le) hr0
    set Y : Fin d → (Fin d → X) → ℝ := fun v x => |f v (x v)| / N v with hYdef
    have hY0 : ∀ v x, 0 ≤ Y v x := fun v x => div_nonneg (abs_nonneg _) (hNpos v).le
    have hmomr : ∀ μ : (Fin d → X) → ℝ, conditioningUniformCoords μ →
        ∀ v, ∑ x, μ x * Y v x ^ r = 1 := by
      intro μ hμ v
      have h := conditioning_marginal_sum μ hμ v (fun a => |f v a| ^ r * (N v ^ r)⁻¹)
      have e : ∀ x, μ x * Y v x ^ r = μ x * (|f v (x v)| ^ r * (N v ^ r)⁻¹) := fun x => by
        simp only [hYdef]
        rw [Real.div_rpow (abs_nonneg _) (hNpos v).le, div_eq_mul_inv]
      rw [Finset.sum_congr rfl (fun x _ => e x), h, ← Finset.sum_mul, hNr v]
      have : (∑ a, |f v a| ^ r) ≠ 0 := by
        intro h0
        have := hNr v
        rw [h0, zero_div] at this
        exact (Real.rpow_pos_of_pos (hNpos v) r).ne' this
      field_simp
    have hmean : ∀ v, ∑ x, ρ x * Y v x = ∑ x, π₀ x * Y v x := fun v => by
      rw [conditioning_marginal_sum ρ hρu v (fun a => |f v a| / N v),
        conditioning_marginal_sum π₀ hπ₀u v (fun a => |f v a| / N v)]
    have hunit' : ∑ x, π₀ x * ∏ v, Y v x ≤ ∏ v, (∑ x, π₀ x * Y v x ^ s) ^ (1 / s) := by
      have h := hunit (fun v a => |f v a| / N v)
      have e : ∀ v, conditioningNorm s (fun a => |f v a| / N v)
          = (∑ x, π₀ x * Y v x ^ s) ^ (1 / s) := fun v => by
        rw [conditioning_marginal_sum π₀ hπ₀u v (fun a => (|f v a| / N v) ^ s), one_div]
        simp only [conditioningNorm, div_eq_mul_inv]
        congr 2
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (inv_nonneg.2 (hNpos v).le))]
      simp only [e] at h
      exact (le_abs_self _).trans h
    have hcore := conditioning_gate_core π₀ π ρ hπ hπ1 hρ hρ1 hη0 hη1 hmix Y hY0 hs hsr
      (hmomr π₀ hπ₀u) hmean (hfirst Y hY0 (hmomr ρ hρu)) hunit' hgate
    have hfac : ∀ x, |∏ v, f v (x v)| = (∏ v, N v) * ∏ v, Y v x := fun x => by
      rw [Finset.abs_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun v _ => ?_)
      have hNv : N v ≠ 0 := (hNpos v).ne'
      simp only [hYdef]
      field_simp
    calc |∑ x, π x * ∏ v, f v (x v)|
        ≤ ∑ x, |π x * ∏ v, f v (x v)| := Finset.abs_sum_le_sum_abs _ _
      _ = (∏ v, N v) * ∑ x, π x * ∏ v, Y v x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [abs_mul, abs_of_nonneg (hπ x), hfac x]
        ring
      _ ≤ (∏ v, N v) * 1 :=
        mul_le_mul_of_nonneg_left hcore (Finset.prod_nonneg (fun v _ => (hNpos v).le))
      _ = ∏ v, conditioningNorm r (f v) := by rw [mul_one]

/-- `lem:density:conditioning`, conditioning assertion, range `2 ≤ r ≤ 6` (`B_r = 1280`,
`d₀ ≤ 6`): if `π₀ = (1 - η) π + η ρ` with `π`, `ρ` probability weights on `Fin d → X`,
`π₀` and `ρ` have uniform coordinates (the same one-coordinate marginals), `π₀` has unit
mixed `L^s` with `1 < s < r`, and `(1280 + 1) η ≤ (r - s)/(s (r - 1))`, then `π` has unit
mixed `L^r`. Conditioning `π₀` on the complement of an event of mass `η` is the case
where `π` and `ρ` are `π₀` conditioned on the complement and on the event. -/
theorem conditioning_unit_mixed {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d : ℕ} (hd : d ≤ 6) (π₀ π ρ : (Fin d → X) → ℝ) (hπ : ∀ x, 0 ≤ π x)
    (hπ1 : ∑ x, π x = 1) (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1) {η : ℝ} (hη0 : 0 ≤ η)
    (hη1 : η < 1) (hmix : ∀ x, π₀ x = (1 - η) * π x + η * ρ x)
    (hπ₀u : conditioningUniformCoords π₀) (hρu : conditioningUniformCoords ρ)
    {r s : ℝ} (hs : 1 < s) (hsr : s < r) (hr : 2 ≤ r) (hr6 : r ≤ 6)
    (hunit : conditioningUnitMixed π₀ s)
    (hgate : (1280 + 1) * η ≤ (r - s) / (s * (r - 1))) :
    conditioningUnitMixed π r :=
  conditioning_unit_mixed_of_first π₀ π ρ hπ hπ1 hρ hρ1 hη0 hη1 hmix hπ₀u hρu hs hsr
    (fun Y hY hYr => conditioning_collision_bound hd ρ hρ hρ1 Y hY hr hr6 hYr) hunit hgate

/-- `lem:density:conditioning`, conditioning assertion, range `4/3 ≤ r ≤ 3/2`
(`B_r = 1024`, `d₀ ≤ 6`), as `conditioning_unit_mixed` with the gate
`(1024 + 1) η ≤ (r - s)/(s (r - 1))`. -/
theorem conditioning_unit_mixed_small_exponent {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] {d : ℕ} (hd : d ≤ 6) (π₀ π ρ : (Fin d → X) → ℝ) (hπ : ∀ x, 0 ≤ π x)
    (hπ1 : ∑ x, π x = 1) (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1) {η : ℝ} (hη0 : 0 ≤ η)
    (hη1 : η < 1) (hmix : ∀ x, π₀ x = (1 - η) * π x + η * ρ x)
    (hπ₀u : conditioningUniformCoords π₀) (hρu : conditioningUniformCoords ρ)
    {r s : ℝ} (hs : 1 < s) (hsr : s < r) (hr1 : 4 / 3 ≤ r) (hr2 : r ≤ 3 / 2)
    (hunit : conditioningUnitMixed π₀ s)
    (hgate : (1024 + 1) * η ≤ (r - s) / (s * (r - 1))) :
    conditioningUnitMixed π r :=
  conditioning_unit_mixed_of_first π₀ π ρ hπ hπ1 hρ hρ1 hη0 hη1 hmix hπ₀u hρu hs hsr
    (fun Y hY hYr => conditioning_collision_bound_small_exponent hd ρ hρ hρ1 Y hY hr1 hr2 hYr)
    hunit hgate

end Sarkozy.DensityUpgrade
