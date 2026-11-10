module

public import Sarkozy.BlockRows.Product

@[expose] public section

/-!
# Block rows, II: the evaluation at the piece start

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(i), proof, "The block" and
"Evaluation at the piece start"; the row constants
`f_j = (R_j(X)^n ρ_{F,j}(X) + 2υ_j + υ_j²)/X^{-1/2}`, `h_j = ρ_{E,j}(X)/X^{-1/2}` with
`n = L/log X` and `υ_j² = e^{n(R_j(X)-1)²} - 1`.

* `rowR₁`, `rowR₂`: the density ratios `R₁(p) = (p-1)/(p-3)` and
  `R₂(p) = (p-3)(p-7)/((p-11)(p-15))` of `lem:record:class-three`(iii);
* `rowR₁_mono`, `rowR₂_mono`: `R_j ≥ 1`, `R_j(p) ≤ R_j(X)` and `(R_j(p)-1)² p ≤ (R_j(X)-1)² X` for
  `19 ≤ X ≤ p` (the majorant properties used by the paper);
* `upsAllow n R = (e^{n(R-1)²} - 1)^{1/2}`;
* **`block_eval`**: on a block of at most `n` primes, all at least `b ≥ X`, with per-prime ratios
  `R_i` satisfying these properties,
  `(∏ R_i) ρ b^{-1/2} + 2υ + υ² ≤ (R(X)^n ρ + (2υ_X + υ_X²) X^{1/2}) b^{-1/2}`
  (`υ = chiAllow R`, the block chi-square allowance of `rows_of_product`). The proof is the
  paper's: densities multiply (`∏ R_i ≤ R(X)^n`); `1 + υ² ≤ ∏(1 + (R_i-1)²) ≤ e^{n(R(X)-1)² X/b}`;
  and convexity of `exp` gives `e^{t y} - 1 ≤ t (e^y - 1)` for `t = X/b ≤ 1`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.BlockRows

/-! ## The density ratios -/

/-- `R₁(p) = (p - 1)/(p - 3)` (one layer, `lem:record:class-three`(iii)). -/
noncomputable def rowR₁ (p : ℝ) : ℝ := (p - 1) / (p - 3)

/-- `R₂(p) = (p - 3)(p - 7)/((p - 11)(p - 15))` (two layers, `lem:record:class-three`(iii)). -/
noncomputable def rowR₂ (p : ℝ) : ℝ := (p - 3) * (p - 7) / ((p - 11) * (p - 15))

/-- The majorant properties of a density ratio on `[X, ∞)`: `R ≥ 1`, `R(p) ≤ R(X)`,
`(R(p) - 1) p ≤ (R(X) - 1) X`. -/
def RatioMono (R : ℝ → ℝ) (X : ℝ) : Prop :=
  ∀ p, X ≤ p → 1 ≤ R p ∧ R p ≤ R X ∧ (R p - 1) * p ≤ (R X - 1) * X

theorem rowR₁_mono {X : ℝ} (hX : 19 ≤ X) : RatioMono rowR₁ X := by
  intro p hp
  have hp3 : 0 < p - 3 := by linarith
  have hX3 : 0 < X - 3 := by linarith
  unfold rowR₁
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hp3]
    linarith
  · rw [div_le_div_iff₀ hp3 hX3]
    nlinarith
  · have e1 : (p - 1) / (p - 3) - 1 = 2 / (p - 3) := by field_simp; ring
    have e2 : (X - 1) / (X - 3) - 1 = 2 / (X - 3) := by field_simp; ring
    rw [e1, e2, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ hp3 hX3]
    nlinarith

theorem rowR₂_mono {X : ℝ} (hX : 19 ≤ X) : RatioMono rowR₂ X := by
  intro p hp
  have hpd : 0 < (p - 11) * (p - 15) := mul_pos (by linarith) (by linarith)
  have hXd : 0 < (X - 11) * (X - 15) := mul_pos (by linarith) (by linarith)
  unfold rowR₂
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hpd]
    nlinarith
  · rw [div_le_div_iff₀ hpd hXd]
    have h1 : 0 ≤ (p - X) * ((p - 9) * (X - 9) - 12) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  · have e1 : (p - 3) * (p - 7) / ((p - 11) * (p - 15)) - 1 =
        (16 * p - 144) / ((p - 11) * (p - 15)) := by
      rw [div_sub_one hpd.ne']
      congr 1
      ring
    have e2 : (X - 3) * (X - 7) / ((X - 11) * (X - 15)) - 1 =
        (16 * X - 144) / ((X - 11) * (X - 15)) := by
      rw [div_sub_one hXd.ne']
      congr 1
      ring
    rw [e1, e2, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ hpd hXd]
    have h1 : 0 ≤ (p - X) * (17 * p * X - 165 * (p + X) + 1485) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith

/-- `(R(p) - 1)² p ≤ (R(X) - 1)² X` from the majorant properties. -/
theorem RatioMono.sq {R : ℝ → ℝ} {X : ℝ} (h : RatioMono R X) (hX : 0 ≤ X) {p : ℝ}
    (hp : X ≤ p) : (R p - 1) ^ 2 * p ≤ (R X - 1) ^ 2 * X := by
  obtain ⟨h1, h2, h3⟩ := h p hp
  have hp0 : 0 ≤ (R p - 1) * p := mul_nonneg (by linarith) (by linarith)
  calc (R p - 1) ^ 2 * p = (R p - 1) * ((R p - 1) * p) := by ring
    _ ≤ (R X - 1) * ((R X - 1) * X) := mul_le_mul (by linarith) h3 hp0 (by linarith)
    _ = (R X - 1) ^ 2 * X := by ring

/-! ## The block evaluation -/

/-- `υ = (e^{n(R-1)²} - 1)^{1/2}`, the paper's `υ_j` at `R = R_j(X)`. -/
noncomputable def upsAllow (n R : ℝ) : ℝ := √(Real.exp (n * (R - 1) ^ 2) - 1)

theorem upsAllow_nonneg (n R : ℝ) : 0 ≤ upsAllow n R := Real.sqrt_nonneg _

/-- Convexity of `exp`: `e^{t y} - 1 ≤ t (e^y - 1)` for `0 ≤ t ≤ 1`. -/
theorem exp_mul_sub_one_le {t y : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (t * y) - 1 ≤ t * (Real.exp y - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ y) (Set.mem_univ 0) ht0 (sub_nonneg.mpr ht1)
    (by ring : t + (1 - t) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  linarith

variable {ι : Type*} [Fintype ι]

/-- **The block evaluation** (`lem:front12:reference`(i), "The block" and "Evaluation at the piece
start"): on a block of at most `n` primes, all at least `b ≥ X > 0`, with per-prime ratios
`R_i ∈ [1, R_X]` and `(R_i - 1)² b ≤ (R_X - 1)² X`,
`(∏ R_i) (ρ b^{-1/2}) + 2υ + υ² ≤ (R_X^n ρ + (2υ_X + υ_X²) √X) b^{-1/2}`. -/
theorem block_eval (R : ι → ℝ) {X b n RX ρ : ℝ} (hX : 0 < X) (hXb : X ≤ b)
    (hcard : (Fintype.card ι : ℝ) ≤ n) (hRX1 : 1 ≤ RX) (hR1 : ∀ i, 1 ≤ R i)
    (hRX : ∀ i, R i ≤ RX) (hchi : ∀ i, (R i - 1) ^ 2 * b ≤ (RX - 1) ^ 2 * X) (hρ : 0 ≤ ρ) :
    (∏ i, R i) * (ρ * (√b)⁻¹) + 2 * chiAllow R + chiAllow R ^ 2 ≤
      (RX ^ n * ρ + (2 * upsAllow n RX + upsAllow n RX ^ 2) * √X) * (√b)⁻¹ := by
  have hb : 0 < b := lt_of_lt_of_le hX hXb
  have hn0 : 0 ≤ n := le_trans (Nat.cast_nonneg _) hcard
  set t : ℝ := X / b with ht
  have ht0 : 0 ≤ t := div_nonneg hX.le hb.le
  have ht1 : t ≤ 1 := (div_le_one hb).mpr hXb
  have hsb : 0 < √b := Real.sqrt_pos.mpr hb
  -- the densities multiply
  have hH : ∏ i, R i ≤ RX ^ n := by
    have h1 : ∏ i, R i ≤ ∏ _i : ι, RX :=
      prod_le_prod₀ (fun i _ => zero_le_one.trans (hR1 i)) (fun i _ => hRX i)
    rw [prod_const, card_univ, ← Real.rpow_natCast] at h1
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hRX1 hcard)
  -- the chi-square defects multiply
  set c : ℝ := (RX - 1) ^ 2 * X / b with hc
  have hc0 : 0 ≤ c := div_nonneg (mul_nonneg (sq_nonneg _) hX.le) hb.le
  have hci : ∀ i, (R i - 1) ^ 2 ≤ c := fun i => (le_div_iff₀ hb).mpr (hchi i)
  set P : ℝ := ∏ i, (1 + (R i - 1) ^ 2) with hP
  have hP1 : 1 ≤ P := by
    have h := prod_le_prod₀ (s := (univ : Finset ι)) (f := fun _ => (1 : ℝ))
      (g := fun i => 1 + (R i - 1) ^ 2) (fun _ _ => zero_le_one)
      (fun i _ => by nlinarith [sq_nonneg (R i - 1)])
    rwa [prod_const_one] at h
  have hPc : P ≤ Real.exp (n * c) := by
    have h1 : P ≤ ∏ _i : ι, (1 + c) :=
      prod_le_prod₀ (fun i _ => by nlinarith [sq_nonneg (R i - 1)]) (fun i _ => by linarith [hci i])
    rw [prod_const, card_univ] at h1
    have h2 : (1 + c) ^ Fintype.card ι ≤ Real.exp c ^ Fintype.card ι :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp c]) _
    rw [← Real.exp_nat_mul] at h2
    exact h1.trans (h2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcard hc0)))
  set Y : ℝ := n * (RX - 1) ^ 2 with hY
  have hY0 : 0 ≤ Y := mul_nonneg hn0 (sq_nonneg _)
  have hnc : n * c = t * Y := by rw [hc, ht, hY]; field_simp
  have hυ2 : chiAllow R ^ 2 ≤ t * upsAllow n RX ^ 2 := by
    unfold chiAllow upsAllow
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith [Real.add_one_le_exp Y])]
    have := exp_mul_sub_one_le (y := Y) ht0 ht1
    rw [← hnc] at this
    linarith
  -- `√t = √X / √b`
  have hst : √t = √X * (√b)⁻¹ := by rw [ht, Real.sqrt_div hX.le, div_eq_mul_inv]
  have hυ : chiAllow R ≤ √t * upsAllow n RX := by
    have h := Real.sqrt_le_sqrt hυ2
    rwa [Real.sqrt_sq (chiAllow_nonneg R), Real.sqrt_mul ht0,
      Real.sqrt_sq (upsAllow_nonneg n RX)] at h
  have htt : t ≤ √t := by
    have h1 : √t ≤ 1 := Real.sqrt_le_one.mpr ht1
    have h2 : √t * √t = t := Real.mul_self_sqrt ht0
    nlinarith [Real.sqrt_nonneg t]
  have hυ2' : chiAllow R ^ 2 ≤ √t * upsAllow n RX ^ 2 :=
    hυ2.trans (mul_le_mul_of_nonneg_right htt (sq_nonneg _))
  have hmain : (∏ i, R i) * (ρ * (√b)⁻¹) ≤ RX ^ n * ρ * (√b)⁻¹ := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hH hρ) (by positivity)
  calc (∏ i, R i) * (ρ * (√b)⁻¹) + 2 * chiAllow R + chiAllow R ^ 2
      ≤ RX ^ n * ρ * (√b)⁻¹ + 2 * (√t * upsAllow n RX) + √t * upsAllow n RX ^ 2 := by
        linarith
    _ = (RX ^ n * ρ + (2 * upsAllow n RX + upsAllow n RX ^ 2) * √X) * (√b)⁻¹ := by
        rw [hst]
        ring

end Sarkozy.BlockRows
