module

public import Sarkozy.PositiveRoots.Square

@[expose] public section

/-!
# Normalization, marginal and conditional prices (`lem:root-normalization`)

`paper/sections/20b_positive_roots.tex`, `lem:root-normalization`. Part (b) (the score moments and
the conditioning on global injectivity) is in `Moments`. Here:

* **(a), the square price** (`raw_sq_price`): `K₀∘V − K₀ = h_p^{-1}J^*(K_soft∘V − K_soft)J −
  T_coll∘(V − 1)`; with the soft price of `lem:root-square` compressed by `1/h_p ≤ 1/h'_p`
  (`lem:restriction`(b)), the ordinary collisions `|V − 1| ≤ (2 + r)² − 1` against
  `‖T_coll‖ ≤ D_bal`
  and the spikes `𝔰/(h'_p q)`, the total is
  `ε^raw_sq = (4q𝔯₂² + 256c₀𝔯₊q)/h'_p + ((2 + r)² − 1)D_bal + 𝔰/(h'_p q)`, and
  `ε_sq = ε^raw_sq/(1 − ε_Z)` after division by `Z₀ ≥ 1 − ε_Z` (`sq_price_normalized`).
* **(a), the linear price** (`raw_lin_price`): `ε^raw_lin = ε_lin/h'_p + c_lin`.
* **(a), the marginal** (`marginal_price`): `lem:restriction`(b) with both events of probability
  `h_p` gives `‖P₀(K^μ∘H̄)1‖ ≤ ‖P₀(K∘H̄)1‖/√h_p + ‖P₀(K∘H̄)P₀‖(1 − h_p)^{1/2}/h_p`; with
  `1 − h_p = (8q − 20q²)/(1 − q) ≤ 8q/(1 − q)` (`one_sub_hP`), `h_p ≥ h'_p` (`hP_ge`) and
  `lem:root-linear` this is at most
  `(𝔩₀r + ε_lin)/√h'_p + [r(1 + 2𝔩₀) + ε_lin]√(8q/(1 − q))/h'_p`; adding `c_lin` and dividing by
  `Z₀` gives the paper's `𝔩` (`ell_price`).
* **(c), the core count** (`core_mass_sum`, `core_tested_sum`): the two polynomial identities of the
  proof, `(1 − q)⁴ − 16r − 112q − 256qr − C_coll = Δ_core` with `C_coll = 32q + 256qr + 512q²`, and
  `m² + 16rm + 80q + 32qm + 256qr + C_coll = 148q + 616qr + 580q²` for the test mean bound
  `m = 2r + 2q` (`q = r²`);
* `Delta_core_pos`: **`Δ_core > 0` for `p ≥ 2²⁰`** (`r ≤ 2^{-10}`), as the lemma states;
* **(c), the ratio** (`cond_ratio`): `|N/D| ≤ A/ρ_in` from `|N| ≤ A`, `D ≥ ρ_in > 0` — the last step
  defining `c_cond`.

**Hypotheses.** The soft price (`lem:root-square`), the collision cap `‖T_coll‖ ≤ D_bal`
(`prop:l20-collisions`(a)), the spike row bounds (Schur's test, the proof's "Spikes"), the
compression `lem:restriction`(b), the class prices (`lem:root-linear`) and the counts of (c) are
inputs; the arithmetic combining them into the paper's constants is proved.
-/

namespace Sarkozy.PositiveRoots

open Finset

/-! ## (a) -/

/-- **`lem:root-normalization`(a), the raw square price**: the three pieces of
`K₀∘V − K₀ = h_p^{-1}J^*(K_soft∘V − K_soft)J − T_coll∘(V − 1)` add up to `ε^raw_sq`. Stated for the
norm bounds `a₁ ≤ (4q𝔯₂² + 256c₀𝔯₊q)/h_p`, `a₂ ≤ ((2 + r)² − 1)D_bal`, `a₃ ≤ 𝔰/(h_p q)` and
`h_p ≥ h'_p`. -/
theorem raw_sq_price {q r r2 c0 rp hP hP' Dbal s a1 a2 a3 : ℝ} (hq : 0 < q) (hP0 : 0 < hP')
    (hPP : hP' ≤ hP) (hnum : 0 ≤ 4 * q * r2 ^ 2 + 256 * c0 * rp * q) (hs : 0 ≤ s)
    (h1 : a1 ≤ (4 * q * r2 ^ 2 + 256 * c0 * rp * q) / hP)
    (h2 : a2 ≤ ((2 + r) ^ 2 - 1) * Dbal) (h3 : a3 ≤ s / (hP * q)) :
    a1 + a2 + a3 ≤ (4 * q * r2 ^ 2 + 256 * c0 * rp * q) / hP' + ((2 + r) ^ 2 - 1) * Dbal +
      s / (hP' * q) := by
  have e1 : (4 * q * r2 ^ 2 + 256 * c0 * rp * q) / hP ≤
      (4 * q * r2 ^ 2 + 256 * c0 * rp * q) / hP' :=
    div_le_div_of_nonneg_left hnum hP0 hPP
  have e3 : s / (hP * q) ≤ s / (hP' * q) :=
    div_le_div_of_nonneg_left hs (mul_pos hP0 hq) (mul_le_mul_of_nonneg_right hPP hq.le)
  linarith

/-- `ε_sq = ε^raw_sq/(1 − ε_Z)`: a raw bound `a ≤ ε^raw` divided by `Z₀ ≥ 1 − ε_Z > 0`. -/
theorem sq_price_normalized {a ε Z εZ : ℝ} (ha : 0 ≤ a) (h : a ≤ ε) (hεZ : εZ < 1)
    (hZ : 1 - εZ ≤ Z) : a / Z ≤ ε / (1 - εZ) := by
  have h1 : 0 < 1 - εZ := by linarith
  calc a / Z ≤ a / (1 - εZ) := div_le_div_of_nonneg_left ha h1 hZ
    _ ≤ ε / (1 - εZ) := div_le_div_of_nonneg_right h h1.le

/-- **`lem:root-normalization`(a), the raw linear price** `ε^raw_lin = ε_lin/h'_p + c_lin`. -/
theorem raw_lin_price {εlin clin hP hP' a1 a2 : ℝ} (hP0 : 0 < hP') (hPP : hP' ≤ hP)
    (hε : 0 ≤ εlin) (h1 : a1 ≤ εlin / hP) (h2 : a2 ≤ clin) :
    a1 + a2 ≤ εlin / hP' + clin := by
  have : εlin / hP ≤ εlin / hP' := div_le_div_of_nonneg_left hε hP0 hPP
  linarith

/-- `h_p = (1 − 4q)(1 − 5q)/(1 − q)` and `1 − h_p = (8q − 20q²)/(1 − q)`. -/
theorem one_sub_hP {q : ℝ} (hq : q < 1) :
    1 - (1 - 4 * q) * (1 - 5 * q) / (1 - q) = (8 * q - 20 * q ^ 2) / (1 - q) := by
  have : 1 - q ≠ 0 := by linarith
  field_simp
  ring

/-- `1 − h_p ≤ 8q/(1 − q)`. -/
theorem one_sub_hP_le {q : ℝ} (hq : q < 1) :
    1 - (1 - 4 * q) * (1 - 5 * q) / (1 - q) ≤ 8 * q / (1 - q) := by
  rw [one_sub_hP hq]
  exact div_le_div_of_nonneg_right (by nlinarith) (by linarith)

/-- `h_p ≥ h'_p = (1 − 4q)(1 − 5q)`. -/
theorem hP_ge {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 5) :
    (1 - 4 * q) * (1 - 5 * q) ≤ (1 - 4 * q) * (1 - 5 * q) / (1 - q) := by
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 ≤ (1 - 4 * q) * (1 - 5 * q) := mul_nonneg (by linarith) (by linarith)
  rw [le_div_iff₀ h1]
  nlinarith

/-- **`lem:root-normalization`(a), the marginal**: the restriction estimate
`‖P₀(K^μ∘H̄)1‖ ≤ ‖P₀(K∘H̄)1‖/√h_p + ‖P₀(K∘H̄)P₀‖(1 − h_p)^{1/2}/h_p` (`lem:restriction`(b), as the
hypothesis `hres`) with the bounds of `lem:root-linear` gives
`(𝔩₀r + ε_lin)/√h'_p + [r(1 + 2𝔩₀) + ε_lin]√(8q/(1 − q))/h'_p`. -/
theorem marginal_price {q r l0 εlin hP hP' m1 m2 a : ℝ} (hq : q < 1)
    (hP0 : 0 < hP') (hPP : hP' ≤ hP) (hhP : hP = (1 - 4 * q) * (1 - 5 * q) / (1 - q))
    (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (h1 : m1 ≤ l0 * r + εlin) (h2 : m2 ≤ r * (1 + 2 * l0) + εlin)
    (hres : a ≤ m1 / Real.sqrt hP + m2 * Real.sqrt (1 - hP) / hP) :
    a ≤ (l0 * r + εlin) / Real.sqrt hP' +
      (r * (1 + 2 * l0) + εlin) * Real.sqrt (8 * q / (1 - q)) / hP' := by
  have hP0' : 0 < hP := lt_of_lt_of_le hP0 hPP
  have s1 : Real.sqrt hP' ≤ Real.sqrt hP := Real.sqrt_le_sqrt hPP
  have s0 : 0 < Real.sqrt hP' := Real.sqrt_pos.mpr hP0
  have t1 : m1 / Real.sqrt hP ≤ (l0 * r + εlin) / Real.sqrt hP' := by
    calc m1 / Real.sqrt hP ≤ m1 / Real.sqrt hP' := div_le_div_of_nonneg_left hm1 s0 s1
      _ ≤ _ := div_le_div_of_nonneg_right h1 s0.le
  have s2 : Real.sqrt (1 - hP) ≤ Real.sqrt (8 * q / (1 - q)) := by
    apply Real.sqrt_le_sqrt
    rw [hhP]
    exact one_sub_hP_le hq
  have t2 : m2 * Real.sqrt (1 - hP) / hP ≤
      (r * (1 + 2 * l0) + εlin) * Real.sqrt (8 * q / (1 - q)) / hP' := by
    have hm2' : 0 ≤ r * (1 + 2 * l0) + εlin := hm2.trans h2
    calc m2 * Real.sqrt (1 - hP) / hP ≤ m2 * Real.sqrt (1 - hP) / hP' :=
          div_le_div_of_nonneg_left (mul_nonneg hm2 (Real.sqrt_nonneg _)) hP0 hPP
      _ ≤ (r * (1 + 2 * l0) + εlin) * Real.sqrt (8 * q / (1 - q)) / hP' := by
          apply div_le_div_of_nonneg_right _ hP0.le
          exact mul_le_mul h2 s2 (Real.sqrt_nonneg _) hm2'
  linarith

/-- **The paper's `𝔩`** (`lem:root-normalization`(a)): adding `c_lin` to the marginal bound and
dividing by `Z₀ ≥ 1 − ε_Z` gives
`𝔩 = {(𝔩₀r + ε_lin)/√h'_p + [r(1 + 2𝔩₀) + ε_lin]√(8q/(1 − q))/h'_p + c_lin}/(1 − ε_Z)`. -/
theorem ell_price {a M clin Z εZ : ℝ} (ha : 0 ≤ a) (hM : a ≤ M + clin) (hεZ : εZ < 1)
    (hZ : 1 - εZ ≤ Z) : a / Z ≤ (M + clin) / (1 - εZ) :=
  sq_price_normalized ha hM hεZ hZ

/-! ## (c) -/

/-- **The normalizing mass of the core count** (`lem:root-normalization`(c)):
`(1 − q)⁴ − 16r − 112q − 256qr − C_coll = Δ_core`, `C_coll = 32q + 256qr + 512q²`. -/
theorem core_mass_sum (q r : ℝ) :
    (1 - q) ^ 4 - 16 * r - 112 * q - 256 * q * r - (32 * q + 256 * q * r + 512 * q ^ 2) =
      (1 - q) ^ 4 - 16 * r - 144 * q - 512 * q * r - 512 * q ^ 2 := by
  ring

/-- **The tested core count** (`lem:root-normalization`(c)): with the test mean bound
`m = 2r + 2q` and `q = r²`,
`m² + 16rm + 80q + 32qm + 256qr + C_coll = 148q + 616qr + 580q²`. -/
theorem core_tested_sum (r : ℝ) :
    (2 * r + 2 * r ^ 2) ^ 2 + 16 * r * (2 * r + 2 * r ^ 2) + 80 * r ^ 2 +
        32 * r ^ 2 * (2 * r + 2 * r ^ 2) + 256 * r ^ 2 * r +
        (32 * r ^ 2 + 256 * r ^ 2 * r + 512 * (r ^ 2) ^ 2) =
      148 * r ^ 2 + 616 * r ^ 2 * r + 580 * (r ^ 2) ^ 2 := by
  ring

/-- `Δ_core = (1 − q)⁴ − 16r − 144q − 512qr − 512q²`. -/
def deltaCore (q r : ℝ) : ℝ := (1 - q) ^ 4 - 16 * r - 144 * q - 512 * q * r - 512 * q ^ 2

/-- **`Δ_core > 0` for `p ≥ 2²⁰`** (`lem:root-normalization`(c): "positive for `p ≥ 2²⁰`"): for
`0 ≤ r ≤ 2^{-10}` and `q = r²`, `Δ_core ≥ Δ_core(2^{-20}, 2^{-10}) > 0`. -/
theorem Delta_core_pos {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 ^ 10) : 0 < deltaCore (r ^ 2) r := by
  unfold deltaCore
  have hq : r ^ 2 ≤ 1 / 2 ^ 20 := by
    have := pow_le_pow_left₀ hr0 hr 2
    calc r ^ 2 ≤ (1 / 2 ^ 10) ^ 2 := this
      _ = 1 / 2 ^ 20 := by norm_num
  have hq0 : 0 ≤ r ^ 2 := sq_nonneg r
  have h1 : (1 - 1 / 2 ^ 20 : ℝ) ^ 4 ≤ (1 - r ^ 2) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 4
  have h2 : r ^ 2 * r ≤ 1 / 2 ^ 20 * (1 / 2 ^ 10) := mul_le_mul hq hr hr0 (by norm_num)
  have h3 : (r ^ 2) ^ 2 ≤ (1 / 2 ^ 20) ^ 2 := pow_le_pow_left₀ hq0 hq 2
  nlinarith

/-- **`lem:root-normalization`(c), the ratio**: if the numerator of the conditional score mean is
at most `A` in modulus and the physical row mass is at least `ρ_in > 0`, the conditional mean is at
most `A/ρ_in` (`= c_cond` with the paper's `A`). -/
theorem cond_ratio {N D A ρ : ℝ} (hρ : 0 < ρ) (hD : ρ ≤ D) (hN : |N| ≤ A) : |N / D| ≤ A / ρ := by
  have hD0 : 0 < D := lt_of_lt_of_le hρ hD
  rw [abs_div, abs_of_pos hD0]
  have hA : 0 ≤ A := le_trans (abs_nonneg _) hN
  calc |N| / D ≤ A / D := div_le_div_of_nonneg_right hN hD0.le
    _ ≤ A / ρ := div_le_div_of_nonneg_left hA hρ hD

end Sarkozy.PositiveRoots
