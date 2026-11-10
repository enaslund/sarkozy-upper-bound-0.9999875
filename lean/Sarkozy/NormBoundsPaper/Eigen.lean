module

public import Sarkozy.NormBoundsPaper.Fourier

@[expose] public section

/-!
# The eigenvalues of the constant records and the support bounds (`lem:record:accepting-c2`)

`paper/sections/21_middle_records.tex`, `lem:record:accepting-c2` and its proof.

At a prime `p ≡ 3 (4)` the old one-object law of a constant record is the uniform law on ordered
distinct pairs, the kernel `k_D(d) = [d ≠ 0]/(p − 1)` relative to the uniform law, and the
replacement is the uniform strict Paley edge, `k_P(d) = 2 [χ(d) = 1]/(p − 1)` (`kD`, `kP`). Their
eigenvalues on the character `e_ξ` are (`hatD_eq`, `hatP_eq`)
* `1` and `1` for `ξ = 0`;
* `−η_p` and `−η_p ± i γ_p` for `ξ ≠ 0`, with `η_p = 1/(p − 1)`, `γ_p = √p/(p − 1)`
  (`hatP_re`, `hatP_im`, `hatP_normSq`: `|·|² = ρ_p² = (p + 1)/(p − 1)²`).

On a block the eigenvalue on `Ψ_ξ` is the product over the support `T = {i : ξ_i ≠ 0}`.
**`support_bounds`** is the paper's case analysis: the symmetric difference
`Re ∏_T w_i − ∏_T(−η_i)` vanishes on `|T| ≤ 1`, is `−Im w_j Im w_k` on `|T| = 2` and is at most
`ρ³ + η³` on `|T| ≥ 3`; the skew part `Im ∏_T w_i` is at most `γ` on `|T| = 1` and at most `ρ²`
on `|T| ≥ 2`. With the numerical facts `ρ_b ≤ 1/2`, `ρ_b² ≤ γ_b`, `ρ_b³ + η_b³ ≤ γ_b²` for
`b ≥ 7` (`paper_numbers`) this gives **`block_eig_bounds`**: every eigenvalue of the symmetric
difference is at most `γ_b²` and every eigenvalue of the skew difference at most `γ_b` in absolute
value, uniformly in the primes `p ≥ b` of the block.
-/

namespace Sarkozy.NormBoundsPaper

open Finset Complex Sarkozy.SpectralC Sarkozy.Characters
open scoped BigOperators ComplexConjugate

/-! ## One prime -/

section Prime

variable (p : ℕ) [Fact p.Prime]

/-- The kernel of the uniform ordered distinct pairs relative to the uniform law. -/
noncomputable def kD (d : ZMod p) : ℝ := if d = 0 then 0 else 1 / ((p : ℝ) - 1)

/-- The kernel of the uniform strict Paley edge relative to the uniform law. -/
noncomputable def kP (d : ZMod p) : ℝ :=
  if quadraticChar (ZMod p) d = 1 then 2 / ((p : ℝ) - 1) else 0

variable {p}

/-- The one-prime transform `k̂(ξ) = ∑_x k(x) e_ξ(x)`. -/
noncomputable def hat1 (k : ZMod p → ℝ) (ξ : ZMod p) : ℂ := ∑ x, (k x : ℂ) * ech ξ x

theorem p_gt_one : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

theorem hatD_eq (ξ : ZMod p) :
    hat1 (kD p) ξ = if ξ = 0 then 1 else ((-(1 / ((p : ℝ) - 1)) : ℝ) : ℂ) := by
  have hp1 : ((p : ℂ) - 1) ≠ 0 := by
    have := p_gt_one (p := p)
    exact_mod_cast (sub_pos.mpr this).ne'
  have hpt : ∀ x : ZMod p, (kD p x : ℂ) * ech ξ x =
      (1 / ((p : ℂ) - 1)) * ech ξ x - (if x = 0 then (1 / ((p : ℂ) - 1)) * ech ξ x else 0) := by
    intro x
    unfold kD
    by_cases hx : x = 0
    · simp [hx]
    · simp only [hx, ↓reduceIte, sub_zero]
      push_cast
      ring
  unfold hat1
  simp_rw [hpt]
  rw [sum_sub_distrib, ← mul_sum, sum_ech, sum_ite_eq' univ (0 : ZMod p), ite_eq_left (mem_univ _)]
  unfold ech
  rw [mul_zero, AddChar.map_zero_eq_one, mul_one]
  by_cases hξ : ξ = 0
  · simp only [hξ, ↓reduceIte]
    field_simp
  · simp only [hξ, ↓reduceIte]
    push_cast
    field_simp
    ring

theorem kP_eq (hp2 : p ≠ 2) (x : ZMod p) :
    (kP p x : ℂ) = (kD p x : ℂ) + chiC p x / ((p : ℂ) - 1) := by
  have hp1 : ((p : ℂ) - 1) ≠ 0 := by
    have := p_gt_one (p := p)
    exact_mod_cast (sub_pos.mpr this).ne'
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  unfold kP kD
  rw [chiC_apply]
  by_cases hx : x = 0
  · simp [hx]
  · rcases quadraticChar_dichotomy hx with h | h
    · simp only [h, hx, ↓reduceIte]
      push_cast
      field_simp
      ring
    · have : (-1 : ℤ) ≠ 1 := by decide
      simp only [h, hx, ↓reduceIte, this]
      push_cast
      field_simp
      ring

theorem hatP_eq (hp2 : p ≠ 2) (ξ : ZMod p) :
    hat1 (kP p) ξ = hat1 (kD p) ξ + chiC p ξ * Gchi p / ((p : ℂ) - 1) := by
  unfold hat1
  simp_rw [kP_eq hp2, add_mul, sum_add_distrib]
  congr 1
  rw [← sum_chiC_ech hp2 ξ, sum_div]
  refine sum_congr rfl fun x _ => ?_
  ring

theorem hatP_zero (hp2 : p ≠ 2) : hat1 (kP p) 0 = 1 := by
  rw [hatP_eq hp2, hatD_eq, ite_eq_left rfl, chiC_zero, zero_mul, zero_div, add_zero]

/-- **The Paley eigenvalue at `ξ ≠ 0`**: `−1/(p − 1) + i c √p/(p − 1)` with `c = ±1`
(`p ≡ 3 (4)`: `G_χ = ±i√p`). -/
theorem hatP_form (hp2 : p ≠ 2) (h3 : p % 4 = 3) {ξ : ZMod p} (hξ : ξ ≠ 0) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ hat1 (kP p) ξ =
      ((-(1 / ((p : ℝ) - 1)) : ℝ) : ℂ) + ((c * Real.sqrt p / ((p : ℝ) - 1) : ℝ) : ℂ) * I := by
  have hp1 : ((p : ℂ) - 1) ≠ 0 := by
    have := p_gt_one (p := p)
    exact_mod_cast (sub_pos.mpr this).ne'
  have hG : Gchi p = epsG p * ((Real.sqrt p : ℝ) : ℂ) := by
    unfold epsG
    rw [div_mul_cancel₀ _ sqrt_p_ne_zero]
  have hχ : chiC p ξ = 1 ∨ chiC p ξ = -1 := by
    rw [chiC_apply]
    rcases quadraticChar_dichotomy hξ with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  rw [hatP_eq hp2]
  have key : ∀ c : ℝ, chiC p ξ * Gchi p = ((c * Real.sqrt p : ℝ) : ℂ) * I →
      hat1 (kD p) ξ + chiC p ξ * Gchi p / ((p : ℂ) - 1) =
        ((-(1 / ((p : ℝ) - 1)) : ℝ) : ℂ) + ((c * Real.sqrt p / ((p : ℝ) - 1) : ℝ) : ℂ) * I := by
    intro c hc
    rw [hatD_eq, ite_eq_right hξ, hc]
    push_cast
    field_simp
  rcases (epsG_cases (p := p) hp2).2 h3 with he | he <;> rcases hχ with hc | hc
  · refine ⟨1, Or.inl rfl, key 1 ?_⟩
    rw [hc, hG, he]; push_cast; ring
  · refine ⟨-1, Or.inr rfl, key (-1) ?_⟩
    rw [hc, hG, he]; push_cast; ring
  · refine ⟨-1, Or.inr rfl, key (-1) ?_⟩
    rw [hc, hG, he]; push_cast; ring
  · refine ⟨1, Or.inl rfl, key 1 ?_⟩
    rw [hc, hG, he]; push_cast; ring

theorem hatD_ne {ξ : ZMod p} (hξ : ξ ≠ 0) : hat1 (kD p) ξ = ((-(1 / ((p : ℝ) - 1)) : ℝ) : ℂ) := by
  rw [hatD_eq, ite_eq_right hξ]

theorem hatP_re (hp2 : p ≠ 2) (h3 : p % 4 = 3) {ξ : ZMod p} (hξ : ξ ≠ 0) :
    (hat1 (kP p) ξ).re = -(1 / ((p : ℝ) - 1)) := by
  obtain ⟨c, -, hc⟩ := hatP_form hp2 h3 hξ
  rw [hc, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
    add_zero]

theorem hatP_im (hp2 : p ≠ 2) (h3 : p % 4 = 3) {ξ : ZMod p} (hξ : ξ ≠ 0) :
    |(hat1 (kP p) ξ).im| = Real.sqrt p / ((p : ℝ) - 1) := by
  obtain ⟨c, hc1, hc⟩ := hatP_form hp2 h3 hξ
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr p_gt_one
  rw [hc, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
  rw [abs_div, abs_of_pos hp1, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rcases hc1 with h | h <;> simp [h]

theorem hatP_norm_sq (hp2 : p ≠ 2) (h3 : p % 4 = 3) {ξ : ZMod p} (hξ : ξ ≠ 0) :
    ‖hat1 (kP p) ξ‖ ^ 2 = ((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 2 := by
  obtain ⟨c, hc1, hc⟩ := hatP_form hp2 h3 hξ
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr p_gt_one
  have hc2 : c ^ 2 = 1 := by rcases hc1 with h | h <;> simp [h]
  have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  rw [← Complex.normSq_eq_norm_sq, hc, Complex.normSq_apply]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    add_im, mul_im, zero_add, add_zero]
  field_simp
  nlinarith [hc2, hs]

end Prime

/-! ## The support bounds -/

section Support

variable {ι : Type} [DecidableEq ι]

/-- **The support case analysis of `lem:record:accepting-c2`**: for eigenvalues `w_i` with
`Re w_i = −e_i`, `0 ≤ e_i ≤ η`, `|w_i| ≤ ρ`, `|Im w_i| ≤ γ`, the symmetric difference
`Re ∏_T w − ∏_T(−e)` is at most `γ²` and the skew part `Im ∏_T w` at most `γ`, provided
`ρ ≤ 1`, `η ≤ 1`, `ρ² ≤ γ` and `ρ³ + η³ ≤ γ²`. -/
theorem support_bounds (T : Finset ι) (w : ι → ℂ) (e : ι → ℝ) {ρ η γ : ℝ}
    (hre : ∀ i ∈ T, (w i).re = -e i) (he0 : ∀ i ∈ T, 0 ≤ e i) (he : ∀ i ∈ T, e i ≤ η)
    (hn : ∀ i ∈ T, ‖w i‖ ≤ ρ) (him : ∀ i ∈ T, |(w i).im| ≤ γ) (hρ0 : 0 ≤ ρ) (hη0 : 0 ≤ η)
    (hρ1 : ρ ≤ 1) (hη1 : η ≤ 1) (hργ : ρ ^ 2 ≤ γ) (h3 : ρ ^ 3 + η ^ 3 ≤ γ ^ 2) :
    |(∏ i ∈ T, w i).re - ∏ i ∈ T, (-e i)| ≤ γ ^ 2 ∧ |(∏ i ∈ T, w i).im| ≤ γ := by
  have hγ0 : 0 ≤ γ := (pow_nonneg hρ0 2).trans hργ
  have hnorm : ‖∏ i ∈ T, w i‖ ≤ ρ ^ T.card := by
    rw [norm_prod, ← prod_const]
    exact prod_le_prod₀ (fun i _ => norm_nonneg _) hn
  have hD : |∏ i ∈ T, (-e i)| ≤ η ^ T.card := by
    rw [abs_prod, ← prod_const]
    refine prod_le_prod₀ (fun i _ => abs_nonneg _) fun i hi => ?_
    rw [abs_neg, abs_of_nonneg (he0 i hi)]
    exact he i hi
  -- the skew part on `|T| ≥ 2`
  have hskew2 : 2 ≤ T.card → |(∏ i ∈ T, w i).im| ≤ γ := fun h2 =>
    (Complex.abs_im_le_norm _).trans (hnorm.trans ((pow_le_pow_of_le_one hρ0 hρ1 h2).trans hργ))
  rcases Nat.lt_or_ge T.card 3 with hc | hc
  · interval_cases hcard : T.card
    · rw [card_eq_zero] at hcard
      subst hcard
      simp [hγ0]
    · obtain ⟨j, rfl⟩ := card_eq_one.mp hcard
      rw [prod_singleton, prod_singleton, hre j (mem_singleton_self j)]
      refine ⟨by simp [hγ0], him j (mem_singleton_self j)⟩
    · refine ⟨?_, hskew2 le_rfl⟩
      obtain ⟨j, k, hjk, rfl⟩ := card_eq_two.mp hcard
      have hj : j ∈ ({j, k} : Finset ι) := mem_insert_self j _
      have hk : k ∈ ({j, k} : Finset ι) := mem_insert_of_mem (mem_singleton_self k)
      rw [prod_pair hjk, prod_pair hjk, mul_re, hre j hj, hre k hk]
      have h1 := him j hj
      have h2 := him k hk
      have : -e j * -e k - (w j).im * (w k).im - -e j * -e k = -((w j).im * (w k).im) := by ring
      rw [this, abs_neg, abs_mul, sq]
      exact mul_le_mul h1 h2 (abs_nonneg _) hγ0
  · refine ⟨?_, hskew2 (by omega)⟩
    calc |(∏ i ∈ T, w i).re - ∏ i ∈ T, (-e i)|
        ≤ |(∏ i ∈ T, w i).re| + |∏ i ∈ T, (-e i)| := abs_sub _ _
      _ ≤ ρ ^ T.card + η ^ T.card := add_le_add ((Complex.abs_re_le_norm _).trans hnorm) hD
      _ ≤ ρ ^ 3 + η ^ 3 := add_le_add (pow_le_pow_of_le_one hρ0 hρ1 hc)
          (pow_le_pow_of_le_one hη0 hη1 hc)
      _ ≤ γ ^ 2 := h3

end Support

/-! ## The paper's numbers -/

/-- `γ_b = √b/(b − 1) = r/(1 − 1/b)` for `r = b^{-1/2}`. -/
noncomputable def gam (b : ℝ) : ℝ := Real.sqrt b / (b - 1)

/-- `η_b = 1/(b − 1)`. -/
noncomputable def eta (b : ℝ) : ℝ := 1 / (b - 1)

/-- `ρ_b = √(b + 1)/(b − 1)`, as `√((b + 1)/(b − 1)²)`. -/
noncomputable def rho (b : ℝ) : ℝ := Real.sqrt ((b + 1) / (b - 1) ^ 2)

/-- **The numerical facts of the proof of `lem:record:accepting-c2`** for `b ≥ 7`:
`ρ_b ≤ 1/2`, `η_b ≤ 1`, `ρ_b² ≤ γ_b` and `ρ_b³ + η_b³ ≤ γ_b²`. -/
theorem paper_numbers {b : ℝ} (hb : 7 ≤ b) :
    0 ≤ rho b ∧ 0 ≤ eta b ∧ rho b ≤ 1 ∧ eta b ≤ 1 ∧ rho b ^ 2 ≤ gam b ∧
      rho b ^ 3 + eta b ^ 3 ≤ gam b ^ 2 := by
  have hb1 : 0 < b - 1 := by linarith
  have hρ2 : rho b ^ 2 = (b + 1) / (b - 1) ^ 2 := Real.sq_sqrt (by positivity)
  have hρ0 : 0 ≤ rho b := Real.sqrt_nonneg _
  have hρh : rho b ≤ 1 / 2 := by
    have : rho b ^ 2 ≤ (1 / 2) ^ 2 := by
      rw [hρ2, div_le_iff₀ (by positivity)]
      nlinarith
    exact (pow_le_pow_iff_left₀ hρ0 (by norm_num) (by norm_num)).mp this
  have hs : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)
  have hs2 : 2 ≤ Real.sqrt b := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hγ2 : gam b ^ 2 = b / (b - 1) ^ 2 := by unfold gam; rw [div_pow, hs]
  have hη : eta b = 1 / (b - 1) := rfl
  refine ⟨hρ0, by rw [hη]; positivity, by linarith, ?_, ?_, ?_⟩
  · rw [hη, div_le_one hb1]; linarith
  · rw [hρ2]
    unfold gam
    rw [div_le_div_iff₀ (by positivity) hb1]
    nlinarith
  · have h1 : rho b ^ 3 ≤ (1 / 2) * ((b + 1) / (b - 1) ^ 2) := by
      rw [pow_succ, hρ2, mul_comm]
      exact mul_le_mul_of_nonneg_right hρh (by positivity)
    have h2 : eta b ^ 3 = 1 / (b - 1) ^ 3 := by rw [hη, div_pow, one_pow]
    rw [hγ2, h2]
    have key : b / (b - 1) ^ 2 - (1 / 2) * ((b + 1) / (b - 1) ^ 2) - 1 / (b - 1) ^ 3 =
        ((b - 1) ^ 2 - 2) / (2 * (b - 1) ^ 3) := by
      field_simp
      ring
    have hk : 0 ≤ ((b - 1) ^ 2 - 2) / (2 * (b - 1) ^ 3) :=
      div_nonneg (by nlinarith) (by positivity)
    linarith

/-- The one-prime quantities are below those of the least prime `b ≤ p`. -/
theorem prime_le_least {b p : ℝ} (hb : 7 ≤ b) (hbp : b ≤ p) :
    Real.sqrt p / (p - 1) ≤ gam b ∧ 1 / (p - 1) ≤ eta b ∧
      (p + 1) / (p - 1) ^ 2 ≤ rho b ^ 2 := by
  have hb1 : 0 < b - 1 := by linarith
  have hp1 : 0 < p - 1 := by linarith
  refine ⟨?_, one_div_le_one_div_of_le hb1 (by linarith), ?_⟩
  · unfold gam
    rw [div_le_div_iff₀ hp1 hb1]
    have hsp : Real.sqrt p ^ 2 = p := Real.sq_sqrt (by linarith)
    have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)
    have hst : Real.sqrt b ≤ Real.sqrt p := Real.sqrt_le_sqrt hbp
    have h0 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hst) (add_nonneg (mul_nonneg h0 (h0.trans hst))
      zero_le_one)]
  · unfold rho
    rw [Real.sq_sqrt (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have hd : 0 ≤ p - b := by linarith
    nlinarith [mul_nonneg hd (mul_nonneg hb1.le (by linarith : (0 : ℝ) ≤ b + 3)),
      mul_nonneg (mul_nonneg hd hd) (by linarith : (0 : ℝ) ≤ b + 1)]

end Sarkozy.NormBoundsPaper
