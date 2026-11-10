module

public import Sarkozy.Functional.ConductorMoment
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Sarkozy.PartV.IndexIncrement
public import Sarkozy.TheoremC.Defs

@[expose] public section

/-!
# The finite `p`-adic price (`prop:imp:padic-price`, `cor:imp:padic-majorant`)

`paper/sections/27_tail_index.tex`, `lem:imp:padic-envelope` (the depth tails),
`prop:imp:padic-price` and `cor:imp:padic-majorant`; the moment identity is WP-FI's
`Functional.conductorMoment_eq` (`lem:hyb:moment`, `Functional/ConductorMoment.lean`).

**The depth tails** (`lem:imp:padic-envelope`, with `e_p = p^{-m}`):
* odd `p`: `δ_0 = 1`, `δ_k = (p^{-k/2} + e_p)/(1 - e_p)` (`1 ≤ k < 2m`), `δ_{2m} = 0`
  (`oddTail`);
* `p = 2`: `δ_0 = 1`, `δ_1 = δ_2 = (2^{-1/2} + e_2)/(1 - e_2)`,
  `δ_k = (2^{-(k-1)/2} + e_2)/(1 - e_2)` (`3 ≤ k < 2m + 1`), `δ_{2m+1} = e_2/(1 - e_2)`,
  `δ_{2m+2} = 0` (`twoTail`).

The lemma's analytic content (that these tails bound the Gauss multipliers of the conditioned
square increments, so that they supply the index envelope of `lem:record:common-mean`) is **not**
formalized here; the tails enter as the definition of the depth law, as in the paper's
"independent depths `J` with `Pr(J ≥ k) = δ_k`". Proved here: for `m ≥ 3` they are admissible
depth tails (`isDepthTail_oddTail`, `isDepthTail_twoTail`; the paper's "for `m ≥ 3` the `δ_k` are
nonincreasing in `k` and `δ_1 < 1`").

**`prop:imp:padic-price`.**
* The closed forms (`momentFactor_oddTail_eq`, `momentFactor_twoTail_eq`): with `z = p^{2w}`, the
  summation-by-parts factor `1 + (z - 1) ∑_{l ≥ 1} z^{l-1} δ_{2l-1}` of `lem:hyb:moment` is the
  paper's `L_{p,m}` (`Lodd`) and `L_{2,m}` (`Ltwo`).
* **`Mpad_eq_oneQueryMoment`**: `M_pad(K) = K^{a/36} L_{2,m} ∏_{p < Q, p ≡ 3 (4)} L_{p,m}` is the
  exact one-query conductor moment `E (K sq(D_J))^{a/36}` of the independent depths at `2` and
  at the primes `p ≡ 3 (mod 4)` below `Q` (`z_p = p^{a/18}`).
* The prices of `eq:oct24-index-cost`: `J = B e^T (M_pad/2)^6` (`matchingPrice`) and
  `W = B e^{S+A}[(1 + M_pad/(2K^{35/36}))^6 - 1]` (`wrapPrice`). **`wrapPrice_eq_sum`**: `W` is
  the sum over `j = 1, …, 6` active queries of the coefficient `C(6,j) 2^{6-j}/64` times the
  wrap probability `K^{-j}`, the density normalization `K^{j/36}` and the depth average `M^j`,
  as in the proof. The combinatorial input (that `j` queries all wrap with probability `K^{-j}`,
  and `lem:record:direct-gram` for `J`) is the paper's and is not formalized.

**`lem:imp:padic-envelope`, physical cancellation** (`squareIncrementLaw_nonvanishing`,
`indexIncrement_nonvanishing`): every increment of V1's `squareIncrementLaw` (the square of a
residue of valuation `< m`) is a nonvanishing square class (`TheoremC.IsNonvanishingSquareCoord`),
at the moduli `p^{2m}` (odd `p`) and `2^{2m+1}`.

**`cor:imp:padic-majorant`** (finite parts): the surcharge bounds
`L_{p,m} ≤ L_{p,∞}(1 + p^{-m} z^m/(1 - p^{-m}))` and
`L_{2,m} ≤ L_{2,∞}(1 + 2^{-m} z^{m+1}/(1 - 2^{-m}))`
(`Lodd_le_surcharge`, `Ltwo_le_surcharge`); `L_{p,∞} ≤ F_p` for `p ≥ 3`, `1 ≤ z ≤ 5/4`
(`Linf_le_F`, through the polynomial inequality `majorant_poly`);
`Z = Q^{a/18} ≤ 2^{1/375} < 501/500`
(`Z_le`, `two_rpow_lt`); and `E_o + E_2 < 2^{-60}` at the endpoint (`error_terms_lt`).
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Functional

/-! ## The depth tails of `lem:imp:padic-envelope` -/

/-- `e_p = p^{-m}`. -/
noncomputable def topErr (p m : ℕ) : ℝ := ((p : ℝ) ^ m)⁻¹

theorem topErr_pos {p : ℕ} (hp : 0 < p) (m : ℕ) : 0 < topErr p m := by
  unfold topErr
  have : (0 : ℝ) < p := by exact_mod_cast hp
  positivity

theorem topErr_le {p : ℕ} (hp : 2 ≤ p) {m : ℕ} (hm : 3 ≤ m) : topErr p m ≤ 1 / 8 := by
  unfold topErr
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h8 : (8 : ℝ) ≤ (p : ℝ) ^ m := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ (p : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hp' 3
      _ ≤ (p : ℝ) ^ m := pow_le_pow_right₀ (by linarith) hm
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h8

theorem topErr_lt_one {p : ℕ} (hp : 2 ≤ p) {m : ℕ} (hm : 3 ≤ m) : topErr p m < 1 :=
  (topErr_le hp hm).trans_lt (by norm_num)

/-- **The odd-prime depth tails** (`lem:imp:padic-envelope`): `δ_0 = 1`,
`δ_k = (p^{-k/2} + e_p)/(1 - e_p)` for `1 ≤ k < 2m`, and `δ_k = 0` from `k = 2m` on. -/
noncomputable def oddTail (p m k : ℕ) : ℝ :=
  if k = 0 then 1
  else if k < 2 * m then ((p : ℝ) ^ (-(k : ℝ) / 2) + topErr p m) / (1 - topErr p m)
  else 0

/-- **The 2-adic depth tails** (`lem:imp:padic-envelope`): `δ_0 = 1`,
`δ_1 = δ_2 = (2^{-1/2} + e_2)/(1 - e_2)`, `δ_k = (2^{-(k-1)/2} + e_2)/(1 - e_2)` for
`3 ≤ k < 2m + 1`, `δ_{2m+1} = e_2/(1 - e_2)`, and `δ_k = 0` from `k = 2m + 2` on. -/
noncomputable def twoTail (m k : ℕ) : ℝ :=
  if k = 0 then 1
  else if k ≤ 2 then ((2 : ℝ) ^ (-(1 : ℝ) / 2) + topErr 2 m) / (1 - topErr 2 m)
  else if k < 2 * m + 1 then ((2 : ℝ) ^ (-((k : ℝ) - 1) / 2) + topErr 2 m) / (1 - topErr 2 m)
  else if k = 2 * m + 1 then topErr 2 m / (1 - topErr 2 m)
  else 0

/-- `p^{-1/2} ≤ 3/5` for `p ≥ 3`, and `2^{-1/2} ≤ 3/4`. -/
theorem rpow_neg_half_le {x c : ℝ} (hc : 0 < c) (hx : (1 / c) ^ 2 ≤ x) :
    x ^ (-(1 : ℝ) / 2) ≤ c := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  rw [neg_div, Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow]
  have hs : 1 / c ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hx
  rw [inv_le_comm₀ (Real.sqrt_pos.mpr hx0) hc]
  rwa [one_div] at hs

theorem rpow_neg_half_nonneg (x : ℝ) (hx : 0 ≤ x) (k : ℝ) : 0 ≤ x ^ (-k / 2) :=
  Real.rpow_nonneg hx _

/-- The exponents decrease: `x^{-(k+1)/2} ≤ x^{-k/2}` for `x ≥ 1`. -/
theorem rpow_neg_half_anti {x : ℝ} (hx : 1 ≤ x) (k : ℝ) :
    x ^ (-(k + 1) / 2) ≤ x ^ (-k / 2) :=
  Real.rpow_le_rpow_of_exponent_le hx (by linarith)

/-- **The odd tails are admissible depth tails** for `p ≥ 3`, `m ≥ 3` (`lem:imp:padic-envelope`:
"for `m ≥ 3` the `δ_k` are nonincreasing in `k` and `δ_1 < 1`"). -/
theorem isDepthTail_oddTail {p m : ℕ} (hp : 3 ≤ p) (hm : 3 ≤ m) :
    IsDepthTail (2 * m) (oddTail p m) := by
  have he := topErr_le (by omega : 2 ≤ p) hm
  have he0 := topErr_pos (by omega : 0 < p) m
  have hden : 0 < 1 - topErr p m := by linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  refine ⟨by simp [oddTail], fun j hj => ?_, ?_⟩
  swap
  · have h1 : 2 * m ≠ 0 := by omega
    simp only [oddTail, h1, lt_irrefl, ↓reduceIte, le_refl]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · -- `δ_1 ≤ 1`
    have h1 : ((p : ℝ)) ^ (-(1 : ℝ) / 2) ≤ 3 / 5 :=
      rpow_neg_half_le (by norm_num) (by
        have : (3 : ℝ) ≤ p := by exact_mod_cast hp
        norm_num; linarith)
    simp only [oddTail, show (0 + 1 : ℕ) ≠ 0 from by omega, ↓reduceIte,
      show 0 + 1 < 2 * m from by omega, zero_add, Nat.cast_one]
    rw [div_le_one hden]
    linarith
  · by_cases hj1 : j + 1 < 2 * m
    · simp only [oddTail, show j + 1 ≠ 0 from by omega, ↓reduceIte, hj1,
        show j ≠ 0 from by omega, show j < 2 * m from by omega]
      apply div_le_div_of_nonneg_right _ hden.le
      have := rpow_neg_half_anti hp1 (j : ℝ)
      push_cast
      linarith
    · simp only [oddTail, show j + 1 ≠ 0 from by omega, ↓reduceIte, hj1,
        show j ≠ 0 from by omega, show j < 2 * m from by omega]
      exact div_nonneg (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) he0.le) hden.le

/-- **The 2-adic tails are admissible depth tails** for `m ≥ 3`. -/
theorem isDepthTail_twoTail {m : ℕ} (hm : 3 ≤ m) : IsDepthTail (2 * m + 2) (twoTail m) := by
  have he := topErr_le (le_refl 2) hm
  have he0 := topErr_pos (by norm_num : 0 < 2) m
  have hden : 0 < 1 - topErr 2 m := by linarith
  have h2 : (1 : ℝ) ≤ (2 : ℕ) := by norm_num
  have hhalf : (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ 3 / 4 := rpow_neg_half_le (by norm_num) (by norm_num)
  have hnn : ∀ k : ℝ, 0 ≤ (2 : ℝ) ^ k := fun k => Real.rpow_nonneg (by norm_num) _
  refine ⟨by simp [twoTail], fun j hj => ?_, ?_⟩
  · rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j
      · simp only [twoTail, show (0 + 1 : ℕ) ≠ 0 from by omega, ↓reduceIte,
          show 0 + 1 ≤ 2 from by omega]
        rw [div_le_one hden]
        linarith
      · simp only [twoTail, show (1 + 1 : ℕ) ≠ 0 from by omega, ↓reduceIte,
          show 1 + 1 ≤ 2 from by omega, show (1 : ℕ) ≠ 0 from by omega,
          show (1 : ℕ) ≤ 2 from by omega, le_refl]
    · rcases Nat.lt_or_ge j (2 * m) with hjm | hjm
      · -- `3 ≤ j + 1 < 2m + 1`
        by_cases hj2' : j = 2
        · subst hj2'
          simp only [twoTail, show (2 + 1 : ℕ) ≠ 0 from by omega, ↓reduceIte,
            show ¬ (2 + 1 ≤ 2) from by omega, show 2 + 1 < 2 * m + 1 from by omega,
            show (2 : ℕ) ≠ 0 from by omega, le_refl]
          apply div_le_div_of_nonneg_right _ hden.le
          have : (2 : ℝ) ^ (-((((2 + 1 : ℕ)) : ℝ) - 1) / 2) ≤ (2 : ℝ) ^ (-(1 : ℝ) / 2) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; norm_num)
          linarith
        · simp only [twoTail, show j + 1 ≠ 0 from by omega, ↓reduceIte,
            show ¬ (j + 1 ≤ 2) from by omega, show j + 1 < 2 * m + 1 from by omega,
            show j ≠ 0 from by omega, show ¬ (j ≤ 2) from by omega,
            show j < 2 * m + 1 from by omega]
          apply div_le_div_of_nonneg_right _ hden.le
          have : (2 : ℝ) ^ (-(((j + 1 : ℕ) : ℝ) - 1) / 2) ≤ (2 : ℝ) ^ (-((j : ℝ) - 1) / 2) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
          linarith
      · by_cases hjeq : j = 2 * m
        · subst hjeq
          simp only [twoTail, show 2 * m + 1 ≠ 0 from by omega, ↓reduceIte,
            show ¬ (2 * m + 1 ≤ 2) from by omega, lt_irrefl, show 2 * m ≠ 0 from by omega,
            show ¬ (2 * m ≤ 2) from by omega, show 2 * m < 2 * m + 1 from by omega]
          apply div_le_div_of_nonneg_right _ hden.le
          linarith [hnn (-(((2 * m : ℕ) : ℝ) - 1) / 2)]
        · have hj' : j = 2 * m + 1 := by omega
          subst hj'
          simp only [twoTail, show 2 * m + 1 + 1 ≠ 0 from by omega, ↓reduceIte,
            show ¬ (2 * m + 1 + 1 ≤ 2) from by omega,
            show ¬ (2 * m + 1 + 1 < 2 * m + 1) from by omega,
            show 2 * m + 1 + 1 ≠ 2 * m + 1 from by omega, show 2 * m + 1 ≠ 0 from by omega,
            show ¬ (2 * m + 1 ≤ 2) from by omega, lt_irrefl]
          exact div_nonneg he0.le hden.le
  · simp only [twoTail, show 2 * m + 2 ≠ 0 from by omega, ↓reduceIte,
      show ¬ (2 * m + 2 ≤ 2) from by omega, show ¬ (2 * m + 2 < 2 * m + 1) from by omega,
      show 2 * m + 2 ≠ 2 * m + 1 from by omega, le_refl]

/-! ## The closed forms `L_{p,m}` and `L_{2,m}` -/

/-- `x^{-(2i+1)/2} = x^{-1/2} (x⁻¹)^i`. -/
theorem rpow_odd_half {x : ℝ} (hx : 0 < x) (i : ℕ) :
    x ^ (-((2 * i + 1 : ℕ) : ℝ) / 2) = x ^ (-(1 : ℝ) / 2) * (x⁻¹) ^ i := by
  have : -((2 * i + 1 : ℕ) : ℝ) / 2 = -(1 : ℝ) / 2 + (-(i : ℝ)) := by push_cast; ring
  rw [this, Real.rpow_add hx, Real.rpow_neg hx.le, Real.rpow_natCast, inv_pow]

/-- The summation-by-parts factor reindexed:
`∑_{l=1}^{c} z^{l-1} δ_{2l-1} = ∑_{i<c} z^i δ_{2i+1}`. -/
theorem sum_Icc_odd (z : ℝ) (δ : ℕ → ℝ) (c : ℕ) :
    ∑ l ∈ Icc 1 c, z ^ (l - 1) * δ (2 * l - 1) = ∑ i ∈ range c, z ^ i * δ (2 * i + 1) := by
  rw [← sum_Icc_one_sub_one (fun i => z ^ i * δ (2 * i + 1)) c]
  refine sum_congr rfl fun l hl => ?_
  have := (mem_Icc.mp hl).1
  congr 2
  omega

/-- **The odd factor in geometric form**: with `z = p^{2w}` and `e = p^{-m}`,
`1 + (z - 1) ∑_{l=1}^{m} z^{l-1} δ_{2l-1}
  = 1 + (z - 1)(p^{-1/2} ∑_{i<m} (z/p)^i + e ∑_{i<m} z^i)/(1 - e)`. -/
theorem momentFactor_oddTail (p m : ℕ) (hp : 0 < p) (w : ℝ) :
    momentFactor p (2 * m) (oddTail p m) w =
      1 + ((p : ℝ) ^ (2 * w) - 1) *
        (((p : ℝ) ^ (-(1 : ℝ) / 2) * ∑ i ∈ range m, ((p : ℝ) ^ (2 * w) / p) ^ i +
          topErr p m * ∑ i ∈ range m, ((p : ℝ) ^ (2 * w)) ^ i) / (1 - topErr p m)) := by
  unfold momentFactor
  have hI : (2 * m + 1) / 2 = m := by omega
  rw [hI, sum_Icc_odd]
  have hx : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : ∀ i ∈ range m, ((p : ℝ) ^ (2 * w)) ^ i * oddTail p m (2 * i + 1) =
      ((p : ℝ) ^ (-(1 : ℝ) / 2) * ((p : ℝ) ^ (2 * w) / p) ^ i +
        topErr p m * ((p : ℝ) ^ (2 * w)) ^ i) / (1 - topErr p m) := by
    intro i hi
    have hi' := mem_range.mp hi
    simp only [oddTail, show 2 * i + 1 ≠ 0 from by omega, ↓reduceIte,
      show 2 * i + 1 < 2 * m from by omega]
    rw [rpow_odd_half hx i, div_eq_mul_inv ((p : ℝ) ^ (2 * w)), mul_pow]
    ring
  rw [sum_congr rfl h2, ← sum_div, sum_add_distrib, ← mul_sum, ← mul_sum]

/-- **`L_{p,m}`** (`prop:imp:padic-price`, odd `p`), as a function of `z = z_p`:
`1 + ((z - 1) p^{-1/2} [1 - (z/p)^m]/(1 - z/p) + e(z^m - 1))/(1 - e)`, `e = p^{-m}`. -/
noncomputable def Lodd (p m : ℕ) (z : ℝ) : ℝ :=
  1 + ((z - 1) * (p : ℝ) ^ (-(1 : ℝ) / 2) * ((1 - (z / p) ^ m) / (1 - z / p)) +
    topErr p m * (z ^ m - 1)) / (1 - topErr p m)

theorem one_sub_div_one_sub (x : ℝ) (n : ℕ) : (1 - x ^ n) / (1 - x) = (x ^ n - 1) / (x - 1) := by
  rw [← neg_sub (x ^ n) 1, ← neg_sub x 1, neg_div_neg_eq]

/-- **`prop:imp:padic-price`, odd factors**: the summation-by-parts factor of the odd tails is
`L_{p,m}` at `z_p = p^{2w}` (for `z_p ≠ p`; the paper's `z_p = p^{a/18}`, `w = a/36`). -/
theorem momentFactor_oddTail_eq (p m : ℕ) (hp : 0 < p) (w : ℝ) (hz : (p : ℝ) ^ (2 * w) ≠ p) :
    momentFactor p (2 * m) (oddTail p m) w = Lodd p m ((p : ℝ) ^ (2 * w)) := by
  rw [momentFactor_oddTail p m hp w, Lodd]
  set z := (p : ℝ) ^ (2 * w)
  have hx : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hzp : z / p ≠ 1 := by
    intro h
    apply hz
    rwa [div_eq_one_iff_eq hx] at h
  have hg : (z - 1) * ∑ i ∈ range m, z ^ i = z ^ m - 1 := by
    rw [mul_comm]
    exact geom_sum_mul z m
  rw [geom_sum_eq hzp m, one_sub_div_one_sub, ← hg]
  ring

/-- **The 2-adic factor in geometric form**: with `z = 2^{2w}` and `e = 2^{-m}`,
`1 + (z - 1)(2^{-1/2} + ∑_{1 ≤ i < m} (z/2)^i + e ∑_{i ≤ m} z^i)/(1 - e)`. -/
theorem momentFactor_twoTail (m : ℕ) (hm : 1 ≤ m) (w : ℝ) :
    momentFactor 2 (2 * m + 2) (twoTail m) w =
      1 + (((2 : ℕ) : ℝ) ^ (2 * w) - 1) *
        (((2 : ℝ) ^ (-(1 : ℝ) / 2) + ∑ i ∈ Ico 1 m, (((2 : ℕ) : ℝ) ^ (2 * w) / 2) ^ i +
          topErr 2 m * ∑ i ∈ range (m + 1), (((2 : ℕ) : ℝ) ^ (2 * w)) ^ i) / (1 - topErr 2 m)) := by
  unfold momentFactor
  have hI : (2 * m + 2 + 1) / 2 = m + 1 := by omega
  rw [hI, sum_Icc_odd]
  set z := (((2 : ℕ) : ℝ) ^ (2 * w))
  -- the terms
  set a : ℕ → ℝ := fun i => if i = 0 then (2 : ℝ) ^ (-(1 : ℝ) / 2) else if i < m then (z / 2) ^ i
    else 0 with ha
  have hterm : ∀ i ∈ range (m + 1), z ^ i * twoTail m (2 * i + 1) =
      (a i + topErr 2 m * z ^ i) / (1 - topErr 2 m) := by
    intro i hi
    have hi' := mem_range.mp hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp only [twoTail, ha, show 2 * 0 + 1 ≠ 0 from by omega, ↓reduceIte,
        show 2 * 0 + 1 ≤ 2 from by omega, pow_zero, one_mul, mul_one]
    · by_cases him : i < m
      · simp only [twoTail, ha, show 2 * i + 1 ≠ 0 from by omega, ↓reduceIte,
          show ¬ (2 * i + 1 ≤ 2) from by omega, show 2 * i + 1 < 2 * m + 1 from by omega,
          show i ≠ 0 from by omega, him]
        have hexp : -(((2 * i + 1 : ℕ) : ℝ) - 1) / 2 = -(i : ℝ) := by push_cast; ring
        rw [hexp, Real.rpow_neg (by norm_num), Real.rpow_natCast, div_pow]
        ring
      · have hieq : i = m := by omega
        subst hieq
        simp only [twoTail, ha, show 2 * i + 1 ≠ 0 from by omega, ↓reduceIte,
          show ¬ (2 * i + 1 ≤ 2) from by omega, lt_irrefl, show i ≠ 0 from by omega]
        ring
  rw [sum_congr rfl hterm, ← sum_div, sum_add_distrib, ← mul_sum]
  congr 3
  rw [sum_range_succ, sum_range_eq_add_Ico _ (by omega : 0 < m)]
  have h0 : a 0 = (2 : ℝ) ^ (-(1 : ℝ) / 2) := by simp [ha]
  have hm' : a m = 0 := by simp only [ha, show m ≠ 0 from by omega, ↓reduceIte, lt_irrefl]
  have hmid : ∑ i ∈ Ico 1 m, a i = ∑ i ∈ Ico 1 m, (z / 2) ^ i := by
    refine sum_congr rfl fun i hi => ?_
    have := mem_Ico.mp hi
    simp only [ha, show i ≠ 0 from by omega, ↓reduceIte, show i < m from this.2]
  rw [h0, hm', hmid, add_zero]

/-- **`L_{2,m}`** (`prop:imp:padic-price`), as a function of `z = z_2`:
`1 + ((z - 1)[2^{-1/2} + z(1 - (z/2)^{m-1})/(2 - z)] + 2^{-m}(z^{m+1} - 1))/(1 - 2^{-m})`. -/
noncomputable def Ltwo (m : ℕ) (z : ℝ) : ℝ :=
  1 + ((z - 1) * ((2 : ℝ) ^ (-(1 : ℝ) / 2) + z * (1 - (z / 2) ^ (m - 1)) / (2 - z)) +
    topErr 2 m * (z ^ (m + 1) - 1)) / (1 - topErr 2 m)

/-- **`prop:imp:padic-price`, the factor at `2`**: the summation-by-parts factor of the 2-adic
tails is `L_{2,m}` at `z_2 = 2^{2w}` (for `z_2 ≠ 2`). -/
theorem momentFactor_twoTail_eq (m : ℕ) (hm : 1 ≤ m) (w : ℝ)
    (hz : ((2 : ℕ) : ℝ) ^ (2 * w) ≠ 2) :
    momentFactor 2 (2 * m + 2) (twoTail m) w = Ltwo m (((2 : ℕ) : ℝ) ^ (2 * w)) := by
  rw [momentFactor_twoTail m hm w, Ltwo]
  set z := (((2 : ℕ) : ℝ) ^ (2 * w))
  have hz2 : z / 2 ≠ 1 := by
    intro h
    apply hz
    rwa [div_eq_one_iff_eq (by norm_num)] at h
  have h2z : (2 : ℝ) - z ≠ 0 := fun h => hz (by linarith)
  have hg : (z - 1) * ∑ i ∈ range (m + 1), z ^ i = z ^ (m + 1) - 1 := by
    rw [mul_comm]
    exact geom_sum_mul z (m + 1)
  have hIco : ∑ i ∈ Ico 1 m, (z / 2) ^ i = z * (1 - (z / 2) ^ (m - 1)) / (2 - z) := by
    rw [geom_sum_Ico hz2 hm]
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [show n + 1 - 1 = n by omega, pow_succ, pow_one]
    have h2 : (z / 2 - 1) = -(2 - z) / 2 := by ring
    rw [h2]
    field_simp
    ring
  rw [hIco, ← hg]
  ring

/-! ## `M_pad(K)` is the exact one-query conductor moment -/

/-- The odd prime coordinates of the index law: the primes `p ≡ 3 (mod 4)` below `Q`. -/
def indexPrimes (Q : ℕ) : Finset ℕ := (range Q).filter fun p => p.Prime ∧ p % 4 = 3

/-- **The exact one-query conductor moment** (`prop:imp:padic-price`):
`M_pad(K) = K^{a/36} L_{2,m} ∏_{p < Q, p ≡ 3 (4)} L_{p,m}`, with `z_p = p^{a/18}`. -/
noncomputable def Mpad (a : ℝ) (m Q : ℕ) (K : ℝ) : ℝ :=
  K ^ (a / 36) * (Ltwo m ((2 : ℝ) ^ (a / 18)) *
    ∏ p ∈ indexPrimes Q, Lodd p m ((p : ℝ) ^ (a / 18)))

/-- The coordinates of the index law: `2` (`none`) and the primes of `indexPrimes Q`. -/
abbrev IndexCoord (Q : ℕ) : Type := Option (indexPrimes Q)

/-- The prime of a coordinate. -/
def indexPrime {Q : ℕ} : IndexCoord Q → ℕ
  | none => 2
  | some p => p.1

/-- The depth bound of a coordinate: `2m + 2` at `2`, `2m` at the odd primes. -/
def indexDepth (m : ℕ) {Q : ℕ} : IndexCoord Q → ℕ
  | none => 2 * m + 2
  | some _ => 2 * m

/-- The depth tails of a coordinate (`lem:imp:padic-envelope`). -/
noncomputable def indexTail (m : ℕ) {Q : ℕ} : IndexCoord Q → ℕ → ℝ
  | none => twoTail m
  | some p => oddTail p.1 m

theorem mem_indexPrimes {Q p : ℕ} (hp : p ∈ indexPrimes Q) : p.Prime ∧ p % 4 = 3 := by
  unfold indexPrimes at hp
  exact (mem_filter.mp hp).2

theorem three_le_of_mem_indexPrimes {Q p : ℕ} (hp : p ∈ indexPrimes Q) : 3 ≤ p := by
  obtain ⟨hpr, h4⟩ := mem_indexPrimes hp
  have := hpr.two_le
  omega

theorem isDepthTail_index {m Q : ℕ} (hm : 3 ≤ m) :
    ∀ i : IndexCoord Q, IsDepthTail (indexDepth m i) (indexTail m i)
  | none => isDepthTail_twoTail hm
  | some p => isDepthTail_oddTail (three_le_of_mem_indexPrimes p.2) hm

theorem indexPrime_prime {Q : ℕ} : ∀ i : IndexCoord Q, (indexPrime i).Prime
  | none => Nat.prime_two
  | some p => (mem_indexPrimes p.2).1

theorem indexPrime_injective {Q : ℕ} : Function.Injective (indexPrime (Q := Q)) := by
  intro i j hij
  rcases i with _ | p <;> rcases j with _ | q
  · rfl
  · have := three_le_of_mem_indexPrimes q.2
    simp only [indexPrime] at hij
    omega
  · have := three_le_of_mem_indexPrimes p.2
    simp only [indexPrime] at hij
    omega
  · simp only [indexPrime] at hij
    exact congrArg some (Subtype.ext hij)

/-- `x^{a/18} < x` for `x > 1`, `a < 18`. -/
theorem rpow_lt_self' {x a : ℝ} (hx : 1 < x) (ha : a < 18) : x ^ (a / 18) < x := by
  have := Real.rpow_lt_rpow_of_exponent_lt hx (show a / 18 < 1 by linarith)
  rwa [Real.rpow_one] at this

/-- **`prop:imp:padic-price`, the moment**: `M_pad(K)` is the exact one-query conductor moment
`E (K sq(D_J))^{a/36}` of independent depths with the tails of `lem:imp:padic-envelope` at `2`
and at the primes `p ≡ 3 (mod 4)` below `Q` (for `m ≥ 3`, `0 ≤ K`, `a < 18`). -/
theorem Mpad_eq_oneQueryMoment {a : ℝ} (ha : a < 18) {m : ℕ} (hm : 3 ≤ m) (Q : ℕ) {K : ℝ}
    (hK : 0 ≤ K) :
    Mpad a m Q K =
      oneQueryMoment indexPrime (indexDepth m) (indexTail m) (isDepthTail_index (Q := Q) hm) K
        (a / 36) := by
  unfold oneQueryMoment
  rw [conductorMoment_eq indexPrime indexPrime_prime indexPrime_injective _ _ _ hK,
    Fintype.prod_option, Mpad]
  have hw : 2 * (a / 36) = a / 18 := by ring
  congr 2
  · change _ = momentFactor 2 (2 * m + 2) (twoTail m) (a / 36)
    rw [momentFactor_twoTail_eq m (by omega) _ (by
      rw [hw]; push_cast; exact (rpow_lt_self' (by norm_num) ha).ne), hw]
    norm_num
  · rw [← Finset.prod_coe_sort (indexPrimes Q)]
    refine Fintype.prod_congr _ _ fun p => ?_
    change _ = momentFactor p.1 (2 * m) (oddTail p.1 m) (a / 36)
    have hp3 := three_le_of_mem_indexPrimes p.2
    rw [momentFactor_oddTail_eq p.1 m (by omega) _ (by
      rw [hw]; exact (rpow_lt_self' (by exact_mod_cast (by omega : 1 < p.1)) ha).ne), hw]

/-! ## The matching and wrap prices (`eq:oct24-index-cost`) -/

/-- **The matching price** `J = B e^T (M_pad(K)/2)^6` (`eq:oct24-index-cost`). -/
noncomputable def matchingPrice (B T M : ℝ) : ℝ := B * Real.exp T * (M / 2) ^ 6

/-- **The wrap price** `W = B e^{S+A}[(1 + M_pad(K)/(2K^{35/36}))^6 - 1]`
(`eq:oct24-index-cost`). -/
noncomputable def wrapPrice (B S A M K : ℝ) : ℝ :=
  B * Real.exp (S + A) * ((1 + M / (2 * K ^ (35 / 36 : ℝ))) ^ 6 - 1)

/-- `K^{-j} K^{j/36} M^j = (M/K^{35/36})^j`: the wrap probability, the density normalization and
the depth average of `j` active queries. -/
theorem wrap_term {K : ℝ} (hK : 0 < K) (M : ℝ) (j : ℕ) :
    K ^ (-(j : ℝ)) * K ^ ((j : ℝ) / 36) * M ^ j = (M / K ^ (35 / 36 : ℝ)) ^ j := by
  have h1 : K ^ (-(j : ℝ)) * K ^ ((j : ℝ) / 36) = K ^ (-(35 / 36 * (j : ℝ))) := by
    rw [← Real.rpow_add hK]
    congr 1
    ring
  have h2 : (M / K ^ (35 / 36 : ℝ)) ^ j = M ^ j * K ^ (-(35 / 36 * (j : ℝ))) := by
    rw [div_pow, ← Real.rpow_natCast (K ^ (35 / 36 : ℝ)) j, ← Real.rpow_mul hK.le,
      Real.rpow_neg hK.le, div_eq_mul_inv]
  rw [h1, h2, mul_comm]

/-- **`prop:imp:padic-price`, the wrap price**: `W` is `B e^{S+A}` times the sum over the
`j = 1, …, 6` active queries of the coefficient `C(6,j) 2^{6-j}/64` times
`K^{-j} K^{j/36} M_pad(K)^j`. -/
theorem wrapPrice_eq_sum (B S A M K : ℝ) (hK : 0 < K) :
    wrapPrice B S A M K = B * Real.exp (S + A) *
      ∑ j ∈ Icc 1 6, (Nat.choose 6 j : ℝ) * 2 ^ (6 - j) / 64 *
        (K ^ (-(j : ℝ)) * K ^ ((j : ℝ) / 36) * M ^ j) := by
  unfold wrapPrice
  congr 1
  rw [sum_congr rfl fun j _ => by rw [wrap_term hK M j]]
  set x := M / K ^ (35 / 36 : ℝ)
  have hx : M / (2 * K ^ (35 / 36 : ℝ)) = x / 2 := by
    rw [div_mul_eq_div_div_swap]
  rw [hx]
  have hI : Icc 1 6 = ({1, 2, 3, 4, 5, 6} : Finset ℕ) := by decide
  rw [hI]
  simp only [mem_insert, mem_singleton, not_false_eq_true, sum_insert,
    sum_singleton, Nat.reduceEqDiff, or_self]
  norm_num [Nat.choose]
  ring

/-! ## The compact majorant (`cor:imp:padic-majorant`), finite parts -/

/-- `L_{p,∞} = 1 + √p (z - 1)/(p - z)` (`cor:imp:padic-majorant`). -/
noncomputable def Linf (p : ℕ) (z : ℝ) : ℝ := 1 + Real.sqrt p * (z - 1) / (p - z)

/-- `L_{2,∞} = 1 + (z - 1)(2^{-1/2} + z/(2 - z))` (`cor:imp:padic-majorant`). -/
noncomputable def Linf2 (z : ℝ) : ℝ := 1 + (z - 1) * ((2 : ℝ) ^ (-(1 : ℝ) / 2) + z / (2 - z))

/-- `F_p = 1 + √(p+1)(z - 1)/(p - 1)` (`cor:imp:padic-majorant`). -/
noncomputable def Fp (p : ℕ) (z : ℝ) : ℝ := 1 + Real.sqrt (p + 1) * (z - 1) / (p - 1)

/-- `√p = p · p^{-1/2}`. -/
theorem sqrt_eq_mul_rpow {x : ℝ} (hx : 0 < x) : Real.sqrt x = x * x ^ (-(1 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, show (1 / 2 : ℝ) = 1 + (-(1 : ℝ) / 2) by norm_num, Real.rpow_add hx,
    Real.rpow_one]

/-- **`cor:imp:padic-majorant`, the odd surcharge**: discarding the negative geometric tails,
`L_{p,m} ≤ L_{p,∞}(1 + p^{-m} z^m/(1 - p^{-m}))` for `1 ≤ z < p`, `p ≥ 2`, `m ≥ 3`. -/
theorem Lodd_le_surcharge {p m : ℕ} (hp : 2 ≤ p) (hm : 3 ≤ m) {z : ℝ} (hz1 : 1 ≤ z)
    (hzp : z < p) :
    Lodd p m z ≤ Linf p z * (1 + topErr p m * z ^ m / (1 - topErr p m)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have he0 := topErr_pos (by omega : 0 < p) m
  have he1 := topErr_lt_one hp hm
  set e := topErr p m with he
  have hden : 0 < 1 - e := by linarith
  have hpz : 0 < (p : ℝ) - z := by linarith
  set A := Real.sqrt p * (z - 1) / (p - z) with hA
  have hA0 : 0 ≤ A := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) hpz.le
  have hq : 0 ≤ (z / p) ^ m := pow_nonneg (div_nonneg (by linarith) hp0.le) _
  have hzm : 1 ≤ z ^ m := one_le_pow₀ hz1
  -- `L_{p,m} = 1 + (A(1 - (z/p)^m) + e(z^m - 1))/(1 - e)`
  have hL : Lodd p m z = 1 + (A * (1 - (z / p) ^ m) + e * (z ^ m - 1)) / (1 - e) := by
    unfold Lodd
    rw [← he]
    congr 2
    rw [hA, sqrt_eq_mul_rpow hp0]
    have h1 : (1 : ℝ) - z / p = (p - z) / p := by field_simp
    rw [h1]
    field_simp
  rw [hL, Linf, ← hA]
  rw [← sub_nonneg]
  have : (1 + A) * (1 + e * z ^ m / (1 - e)) - (1 + (A * (1 - (z / p) ^ m) + e * (z ^ m - 1)) /
      (1 - e)) = (A * e * (z ^ m - 1) + A * (z / p) ^ m + e) / (1 - e) := by
    field_simp
    ring
  rw [this]
  apply div_nonneg _ hden.le
  have := mul_nonneg (mul_nonneg hA0 he0.le) (sub_nonneg.mpr hzm)
  nlinarith [mul_nonneg hA0 hq]

/-- **`cor:imp:padic-majorant`, the surcharge at `2`**:
`L_{2,m} ≤ L_{2,∞}(1 + 2^{-m} z^{m+1}/(1 - 2^{-m}))` for `1 ≤ z < 2`, `m ≥ 3`. -/
theorem Ltwo_le_surcharge {m : ℕ} (hm : 3 ≤ m) {z : ℝ} (hz1 : 1 ≤ z) (hz2 : z < 2) :
    Ltwo m z ≤ Linf2 z * (1 + topErr 2 m * z ^ (m + 1) / (1 - topErr 2 m)) := by
  have he0 := topErr_pos (by norm_num : 0 < 2) m
  have he1 := topErr_lt_one (le_refl 2) hm
  set e := topErr 2 m with he
  have hden : 0 < 1 - e := by linarith
  have h2z : 0 < 2 - z := by linarith
  set c := (2 : ℝ) ^ (-(1 : ℝ) / 2) with hc'
  have hc : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  set B := (z - 1) * (c + z / (2 - z)) with hB
  have hq : 0 ≤ (z / 2) ^ (m - 1) := pow_nonneg (by linarith) _
  have hB0 : 0 ≤ B := mul_nonneg (by linarith) (add_nonneg hc (div_nonneg (by linarith) h2z.le))
  have hzm : 1 ≤ z ^ (m + 1) := one_le_pow₀ hz1
  have hL : Ltwo m z = 1 + (B - (z - 1) * (z * (z / 2) ^ (m - 1) / (2 - z)) +
      e * (z ^ (m + 1) - 1)) / (1 - e) := by
    unfold Ltwo
    rw [← he, ← hc']
    congr 2
    rw [hB]
    field_simp
    ring
  rw [hL, Linf2, ← hc', ← hB, ← sub_nonneg]
  have : (1 + B) * (1 + e * z ^ (m + 1) / (1 - e)) - (1 + (B - (z - 1) * (z * (z / 2) ^ (m - 1) /
      (2 - z)) + e * (z ^ (m + 1) - 1)) / (1 - e)) =
      (B * e * (z ^ (m + 1) - 1) + (z - 1) * (z * (z / 2) ^ (m - 1) / (2 - z)) + e) / (1 - e) := by
    field_simp
    ring
  rw [this]
  apply div_nonneg _ hden.le
  have h1 := mul_nonneg (mul_nonneg hB0 he0.le) (sub_nonneg.mpr hzm)
  have h2 : 0 ≤ (z - 1) * (z * (z / 2) ^ (m - 1) / (2 - z)) :=
    mul_nonneg (by linarith) (div_nonneg (mul_nonneg (by linarith) hq) h2z.le)
  linarith

/-- **The polynomial inequality of `cor:imp:padic-majorant`**: for `p ≥ 3`, `z ≤ 5/4` (the paper
has `1 ≤ z ≤ 5/4`; the lower bound is not needed),
`(p+1)(p-z)² - p(p-1)² ≥ (8p² - 31p + 25)/16 ≥ 1/4`. -/
theorem majorant_poly {p z : ℝ} (hp : 3 ≤ p) (hz2 : z ≤ 5 / 4) :
    (8 * p ^ 2 - 31 * p + 25) / 16 ≤ (p + 1) * (p - z) ^ 2 - p * (p - 1) ^ 2 ∧
      (1 : ℝ) / 4 ≤ (8 * p ^ 2 - 31 * p + 25) / 16 := by
  constructor
  · have h1 : (p - 5 / 4) ^ 2 ≤ (p - z) ^ 2 := by
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    have h2 : (p + 1) * (p - 5 / 4) ^ 2 ≤ (p + 1) * (p - z) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith [h2]
  · nlinarith

/-- **`L_{p,∞} ≤ F_p`** for `p ≥ 3`, `1 ≤ z ≤ 5/4` (`cor:imp:padic-majorant`). -/
theorem Linf_le_F {p : ℕ} (hp : 3 ≤ p) {z : ℝ} (hz1 : 1 ≤ z) (hz2 : z ≤ 5 / 4) :
    Linf p z ≤ Fp p z := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hpz : 0 < (p : ℝ) - z := by linarith
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  unfold Linf Fp
  refine add_le_add le_rfl ?_
  rw [div_le_div_iff₀ hpz hp1]
  have hsq : Real.sqrt p * ((p : ℝ) - 1) ≤ Real.sqrt (p + 1) * (p - z) := by
    have e1 : Real.sqrt p * ((p : ℝ) - 1) = Real.sqrt (p * (p - 1) ^ 2) := by
      rw [Real.sqrt_mul (by linarith), Real.sqrt_sq hp1.le]
    have e2 : Real.sqrt (p + 1) * ((p : ℝ) - z) = Real.sqrt ((p + 1) * (p - z) ^ 2) := by
      rw [Real.sqrt_mul (by linarith), Real.sqrt_sq hpz.le]
    rw [e1, e2]
    apply Real.sqrt_le_sqrt
    have := majorant_poly hp' hz2
    linarith [this.1, this.2]
  have hz0 : 0 ≤ z - 1 := by linarith
  calc Real.sqrt p * (z - 1) * ((p : ℝ) - 1) = (Real.sqrt p * ((p : ℝ) - 1)) * (z - 1) := by ring
    _ ≤ (Real.sqrt (p + 1) * (p - z)) * (z - 1) := mul_le_mul_of_nonneg_right hsq hz0
    _ = Real.sqrt (p + 1) * (z - 1) * (p - z) := by ring

/-- **`Z = Q^{a/18} ≤ 2^{1/375}`** for `1 ≤ Q ≤ 2^{40}`, `0 ≤ a ≤ 3/2500`
(`cor:imp:padic-majorant`). -/
theorem Z_le {Q a : ℝ} (hQ1 : 1 ≤ Q) (hQ : Q ≤ 2 ^ 40) (ha0 : 0 ≤ a) (ha : a ≤ 3 / 2500) :
    Q ^ (a / 18) ≤ (2 : ℝ) ^ (1 / 375 : ℝ) := by
  calc Q ^ (a / 18) ≤ ((2 : ℝ) ^ 40) ^ (a / 18) :=
        Real.rpow_le_rpow (by linarith) hQ (by linarith)
    _ = (2 : ℝ) ^ (40 * (a / 18)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num
    _ ≤ (2 : ℝ) ^ (1 / 375 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- **`2^{1/375} < 501/500`**, from the rational inequality `(501/500)^{375} > 2`
(`cor:imp:padic-majorant`). -/
theorem two_rpow_lt : (2 : ℝ) ^ (1 / 375 : ℝ) < 501 / 500 := by
  have hnat : 2 * 500 ^ 375 < 501 ^ 375 := by decide +kernel
  have h : (2 : ℝ) < (501 / 500) ^ (375 : ℕ) := by
    rw [div_pow, lt_div_iff₀ (by positivity)]
    exact_mod_cast hnat
  have h' := Real.rpow_lt_rpow (by norm_num) h (by norm_num : (0 : ℝ) < 1 / 375)
  rwa [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), show ((375 : ℕ) : ℝ) * (1 / 375) = 1
    by norm_num, Real.rpow_one] at h'

/-- **The error terms at the endpoint** (`cor:imp:padic-majorant`, last display):
`2^{40} 3^{-64} (501/500)^{64}/(1 - 3^{-64}) + 2^{-64}(501/500)^{65}/(1 - 2^{-64}) < 2^{-60}`. -/
theorem error_terms_lt :
    (2 : ℝ) ^ 40 * ((3 : ℝ) ^ 64)⁻¹ * (501 / 500) ^ 64 / (1 - ((3 : ℝ) ^ 64)⁻¹) +
      ((2 : ℝ) ^ 64)⁻¹ * (501 / 500) ^ 65 / (1 - ((2 : ℝ) ^ 64)⁻¹) < ((2 : ℝ) ^ 60)⁻¹ := by
  norm_num

/-- **`E_o + E_2 < 2^{-60}` on the domain of `cor:imp:padic-majorant`**: `m = 64`,
`0 ≤ a ≤ 3/2500`, `2 ≤ Q ≤ 2^{40}`, `Z = Q^{a/18}`, `z_2 = 2^{a/18}`,
`E_o = Q 3^{-m} Z^m/(1 - 3^{-m})`, `E_2 = 2^{-m} z_2^{m+1}/(1 - 2^{-m})`. -/
theorem error_terms_domain {Q a : ℝ} (hQ2 : 2 ≤ Q) (hQ : Q ≤ 2 ^ 40) (ha0 : 0 ≤ a)
    (ha : a ≤ 3 / 2500) :
    Q * topErr 3 64 * (Q ^ (a / 18)) ^ 64 / (1 - topErr 3 64) +
      topErr 2 64 * ((2 : ℝ) ^ (a / 18)) ^ (64 + 1) / (1 - topErr 2 64) < ((2 : ℝ) ^ 60)⁻¹ := by
  have hZ : Q ^ (a / 18) ≤ 501 / 500 := (Z_le (by linarith) hQ ha0 ha).trans two_rpow_lt.le
  have hz2 : (2 : ℝ) ^ (a / 18) ≤ 501 / 500 :=
    (Z_le (by norm_num) (by norm_num) ha0 ha).trans two_rpow_lt.le
  have hZ0 : 0 ≤ Q ^ (a / 18) := Real.rpow_nonneg (by linarith) _
  have hz0 : 0 ≤ (2 : ℝ) ^ (a / 18) := Real.rpow_nonneg (by norm_num) _
  have e3 : topErr 3 64 = ((3 : ℝ) ^ 64)⁻¹ := by unfold topErr; norm_num
  have e2 : topErr 2 64 = ((2 : ℝ) ^ 64)⁻¹ := by unfold topErr; norm_num
  rw [e3, e2]
  have h3 : (0 : ℝ) < 1 - ((3 : ℝ) ^ 64)⁻¹ := by norm_num
  have h2 : (0 : ℝ) < 1 - ((2 : ℝ) ^ 64)⁻¹ := by norm_num
  have t1 : Q * ((3 : ℝ) ^ 64)⁻¹ * (Q ^ (a / 18)) ^ 64 / (1 - ((3 : ℝ) ^ 64)⁻¹) ≤
      (2 : ℝ) ^ 40 * ((3 : ℝ) ^ 64)⁻¹ * (501 / 500) ^ 64 / (1 - ((3 : ℝ) ^ 64)⁻¹) := by
    apply div_le_div_of_nonneg_right _ h3.le
    apply mul_le_mul (mul_le_mul_of_nonneg_right hQ (by norm_num))
      (pow_le_pow_left₀ hZ0 hZ 64) (pow_nonneg hZ0 _) (by positivity)
  have t2 : ((2 : ℝ) ^ 64)⁻¹ * ((2 : ℝ) ^ (a / 18)) ^ (64 + 1) / (1 - ((2 : ℝ) ^ 64)⁻¹) ≤
      ((2 : ℝ) ^ 64)⁻¹ * (501 / 500) ^ 65 / (1 - ((2 : ℝ) ^ 64)⁻¹) := by
    apply div_le_div_of_nonneg_right _ h2.le
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hz2 _) (by positivity)
  linarith [error_terms_lt]

/-! ## The logarithmic majorant (`cor:imp:padic-majorant`) -/

/-- **The auxiliary moment** `M_a(K) = (144K)^{a/36} ∏_{7 ≤ p < Q, p ≡ 3 (4)} F_p(p^{a/18})`
(`eq:oct24-moment`). -/
noncomputable def Ma (a : ℝ) (Q : ℕ) (K : ℝ) : ℝ :=
  (144 * K) ^ (a / 36) * ∏ p ∈ (indexPrimes Q).filter (fun p => 7 ≤ p), Fp p ((p : ℝ) ^ (a / 18))

/-- `1 ≤ L_{p,m}(p^{a/18})` (it is a moment factor). -/
theorem one_le_Lodd {p m : ℕ} (hp : 3 ≤ p) (hm : 3 ≤ m) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 18) :
    1 ≤ Lodd p m ((p : ℝ) ^ (a / 18)) := by
  have hw : a / 18 = 2 * (a / 36) := by ring
  have hpz : (p : ℝ) ^ (2 * (a / 36)) ≠ p := by
    rw [← hw]
    exact (rpow_lt_self' (by exact_mod_cast (by omega : 1 < p)) ha).ne
  rw [hw, ← momentFactor_oddTail_eq p m (by omega) _ hpz]
  exact one_le_momentFactor (by omega) ((isDepthTail_oddTail hp hm).nonneg_le) (by linarith)

/-- `1 ≤ L_{2,m}(2^{a/18})`. -/
theorem one_le_Ltwo {m : ℕ} (hm : 3 ≤ m) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 18) :
    1 ≤ Ltwo m ((2 : ℝ) ^ (a / 18)) := by
  have hw : a / 18 = 2 * (a / 36) := by ring
  have hz : ((2 : ℕ) : ℝ) ^ (2 * (a / 36)) ≠ 2 := by
    rw [← hw]
    push_cast
    exact (rpow_lt_self' (by norm_num) ha).ne
  have h := momentFactor_twoTail_eq m (by omega) (a / 36) hz
  have h1 := one_le_momentFactor (by norm_num : 1 ≤ 2) ((isDepthTail_twoTail hm).nonneg_le)
    (by linarith : 0 ≤ a / 36)
  rw [h] at h1
  rw [hw]
  exact_mod_cast h1

theorem one_le_rpow_nat {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha0 : 0 ≤ a) : 1 ≤ (p : ℝ) ^ (a / 18) :=
  Real.one_le_rpow (by exact_mod_cast hp) (by linarith)

/-- **`cor:imp:padic-majorant`**: with `m = 64`, `0 ≤ a ≤ 3/2500`, `2^{16} ≤ Q ≤ 2^{40}`, any upper
bound `M_old⁺ ≥ M_a(K)` and any cutoff `U ≤ Q`,
`log M_pad(K) ≤ log M_old⁺ - (a/36) log 144 + log L_{2,∞} + log L_{3,∞}
  - ∑_{7 ≤ p < U, p ≡ 3 (4)} log(F_p/L_{p,∞}) + E_o + E_2`,
with `E_o = Q 3^{-m} Z^m/(1 - 3^{-m})`, `Z = Q^{a/18}`, and `E_2 = 2^{-m} z_2^{m+1}/(1 - 2^{-m})`;
and `E_o + E_2 < 2^{-60}` (`error_terms_domain`). -/
theorem padic_majorant {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 3 / 2500) {Q U : ℕ} (hQ : 2 ^ 16 ≤ Q)
    (hQ' : Q ≤ 2 ^ 40) (hU : U ≤ Q) {K Mold : ℝ} (hK : 0 < K) (hMold : Ma a Q K ≤ Mold) :
    Real.log (Mpad a 64 Q K) ≤ Real.log Mold - a / 36 * Real.log 144 +
      Real.log (Linf2 ((2 : ℝ) ^ (a / 18))) + Real.log (Linf 3 ((3 : ℝ) ^ (a / 18))) -
      ∑ p ∈ (indexPrimes U).filter (fun p => 7 ≤ p),
        Real.log (Fp p ((p : ℝ) ^ (a / 18)) / Linf p ((p : ℝ) ^ (a / 18))) +
      (Q * topErr 3 64 * ((Q : ℝ) ^ (a / 18)) ^ 64 / (1 - topErr 3 64) +
        topErr 2 64 * ((2 : ℝ) ^ (a / 18)) ^ (64 + 1) / (1 - topErr 2 64)) := by
  have ha18 : a < 18 := by linarith
  set S := indexPrimes Q
  set S7 := S.filter (fun p => 7 ≤ p)
  set z : ℕ → ℝ := fun p => (p : ℝ) ^ (a / 18) with hz
  have hQr : (2 : ℝ) ^ 16 ≤ Q := by exact_mod_cast hQ
  have hQr' : (Q : ℝ) ≤ 2 ^ 40 := by exact_mod_cast hQ'
  -- facts about the primes of `S`
  have hS3 : ∀ p ∈ S, 3 ≤ p := fun p hp => three_le_of_mem_indexPrimes hp
  have hSlt : ∀ p ∈ S, p < Q := fun p hp => (mem_range.mp (mem_filter.mp hp).1)
  have hz1 : ∀ p : ℕ, 1 ≤ p → 1 ≤ z p := fun p hp => one_le_rpow_nat hp ha0
  have hZ : (Q : ℝ) ^ (a / 18) ≤ 501 / 500 :=
    (Z_le (by linarith) hQr' ha0 ha).trans two_rpow_lt.le
  have hzZ : ∀ p ∈ S, z p ≤ (Q : ℝ) ^ (a / 18) := fun p hp =>
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (hSlt p hp).le) (by linarith)
  have hzp : ∀ p ∈ S, z p < p := fun p hp =>
    rpow_lt_self' (by exact_mod_cast (by linarith [hS3 p hp] : 1 < p)) ha18
  have hLinf_pos : ∀ p ∈ S, 0 < Linf p (z p) := by
    intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hS3 p hp
    unfold Linf
    have := hzp p hp
    have := hz1 p (by linarith [hS3 p hp])
    have : 0 ≤ Real.sqrt p * (z p - 1) / (p - z p) :=
      div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) (by linarith)
    linarith
  have hF_pos : ∀ p ∈ S, 0 < Fp p (z p) := by
    intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hS3 p hp
    unfold Fp
    have := hz1 p (by linarith [hS3 p hp])
    have : 0 ≤ Real.sqrt (p + 1) * (z p - 1) / (p - 1) :=
      div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) (by linarith)
    linarith
  have hLF : ∀ p ∈ S, Linf p (z p) ≤ Fp p (z p) := fun p hp =>
    Linf_le_F (hS3 p hp) (hz1 p (by linarith [hS3 p hp])) ((hzZ p hp).trans (hZ.trans
      (by norm_num)))
  -- the surcharges
  set s : ℝ := topErr 3 64 * ((Q : ℝ) ^ (a / 18)) ^ 64 / (1 - topErr 3 64) with hs
  have he3 : topErr 3 64 < 1 := topErr_lt_one (by norm_num) (by norm_num)
  have hsp : ∀ p ∈ S, topErr p 64 * z p ^ 64 / (1 - topErr p 64) ≤ s := by
    intro p hp
    have hp3 := hS3 p hp
    have hep : topErr p 64 ≤ topErr 3 64 := by
      unfold topErr
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp3) 64
    have hep0 := topErr_pos (by omega : 0 < p) 64
    have hep1 := topErr_lt_one (by omega : 2 ≤ p) (by norm_num : 3 ≤ 64)
    have hz0 : 0 ≤ z p := le_trans zero_le_one (hz1 p (by omega))
    have hpow : z p ^ 64 ≤ ((Q : ℝ) ^ (a / 18)) ^ 64 := pow_le_pow_left₀ hz0 (hzZ p hp) 64
    rw [hs, div_le_div_iff₀ (by linarith) (by linarith)]
    have h1 : topErr p 64 * z p ^ 64 ≤ topErr 3 64 * ((Q : ℝ) ^ (a / 18)) ^ 64 :=
      mul_le_mul hep hpow (pow_nonneg hz0 _) (topErr_pos (by norm_num) 64).le
    have h2 : 1 - topErr 3 64 ≤ 1 - topErr p 64 := by linarith
    exact mul_le_mul h1 h2 (by linarith) (mul_nonneg (topErr_pos (by norm_num) 64).le
      (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _))
  -- `log L_{p,m} ≤ log L_{p,∞} + s`
  have hLodd : ∀ p ∈ S, Real.log (Lodd p 64 (z p)) ≤ Real.log (Linf p (z p)) + s := by
    intro p hp
    have hsurch := Lodd_le_surcharge (by linarith [hS3 p hp] : 2 ≤ p) (by norm_num : 3 ≤ 64)
      (hz1 p (by linarith [hS3 p hp])) (hzp p hp)
    have hL1 := one_le_Lodd (hS3 p hp) (by norm_num : 3 ≤ 64) ha0 ha18
    have hep0 := topErr_pos (by linarith [hS3 p hp] : 0 < p) 64
    have hep1 := topErr_lt_one (by linarith [hS3 p hp] : 2 ≤ p) (by norm_num : 3 ≤ 64)
    have hsp0 : 0 ≤ topErr p 64 * z p ^ 64 / (1 - topErr p 64) :=
      div_nonneg (mul_nonneg hep0.le (pow_nonneg (le_trans zero_le_one
        (hz1 p (by linarith [hS3 p hp]))) _)) (by linarith)
    calc Real.log (Lodd p 64 (z p))
        ≤ Real.log (Linf p (z p) * (1 + topErr p 64 * z p ^ 64 / (1 - topErr p 64))) :=
          Real.log_le_log (by linarith) hsurch
      _ = Real.log (Linf p (z p)) + Real.log (1 + topErr p 64 * z p ^ 64 / (1 - topErr p 64)) :=
          Real.log_mul (hLinf_pos p hp).ne' (by linarith)
      _ ≤ Real.log (Linf p (z p)) + topErr p 64 * z p ^ 64 / (1 - topErr p 64) := by
          have := Real.log_le_sub_one_of_pos (by linarith :
            0 < 1 + topErr p 64 * z p ^ 64 / (1 - topErr p 64))
          linarith
      _ ≤ Real.log (Linf p (z p)) + s := by linarith [hsp p hp]
  -- the factor at `2`
  set E2 : ℝ := topErr 2 64 * ((2 : ℝ) ^ (a / 18)) ^ (64 + 1) / (1 - topErr 2 64) with hE2
  have hz2 : (1 : ℝ) ≤ (2 : ℝ) ^ (a / 18) := Real.one_le_rpow (by norm_num) (by linarith)
  have hz2' : (2 : ℝ) ^ (a / 18) < 2 := rpow_lt_self' (by norm_num) ha18
  have hLinf2_pos : 0 < Linf2 ((2 : ℝ) ^ (a / 18)) := by
    unfold Linf2
    have : 0 ≤ ((2 : ℝ) ^ (a / 18) - 1) * ((2 : ℝ) ^ (-(1 : ℝ) / 2) +
        (2 : ℝ) ^ (a / 18) / (2 - (2 : ℝ) ^ (a / 18))) :=
      mul_nonneg (by linarith) (add_nonneg (Real.rpow_nonneg (by norm_num) _)
        (div_nonneg (by linarith) (by linarith)))
    linarith
  have hE20 : 0 ≤ E2 := div_nonneg (mul_nonneg (topErr_pos (by norm_num) 64).le
    (pow_nonneg (by linarith) _)) (by linarith [topErr_lt_one (le_refl 2) (by norm_num : 3 ≤ 64)])
  have hLtwo : Real.log (Ltwo 64 ((2 : ℝ) ^ (a / 18))) ≤
      Real.log (Linf2 ((2 : ℝ) ^ (a / 18))) + E2 := by
    have hsurch := Ltwo_le_surcharge (by norm_num : 3 ≤ 64) hz2 hz2'
    have hL1 := one_le_Ltwo (by norm_num : 3 ≤ 64) ha0 ha18
    calc Real.log (Ltwo 64 ((2 : ℝ) ^ (a / 18)))
        ≤ Real.log (Linf2 ((2 : ℝ) ^ (a / 18)) * (1 + E2)) :=
          Real.log_le_log (by linarith) hsurch
      _ = Real.log (Linf2 ((2 : ℝ) ^ (a / 18))) + Real.log (1 + E2) :=
          Real.log_mul hLinf2_pos.ne' (by linarith)
      _ ≤ Real.log (Linf2 ((2 : ℝ) ^ (a / 18))) + E2 := by
          have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + E2)
          linarith
  -- `log M_pad`
  have hLodd_pos : ∀ p ∈ S, 0 < Lodd p 64 (z p) := fun p hp =>
    lt_of_lt_of_le one_pos (one_le_Lodd (hS3 p hp) (by norm_num) ha0 ha18)
  have hLtwo_pos : 0 < Ltwo 64 ((2 : ℝ) ^ (a / 18)) :=
    lt_of_lt_of_le one_pos (one_le_Ltwo (by norm_num) ha0 ha18)
  have hMpad : Real.log (Mpad a 64 Q K) = a / 36 * Real.log K +
      (Real.log (Ltwo 64 ((2 : ℝ) ^ (a / 18))) + ∑ p ∈ S, Real.log (Lodd p 64 (z p))) := by
    unfold Mpad
    rw [Real.log_mul (Real.rpow_pos_of_pos hK _).ne' (mul_pos hLtwo_pos
      (prod_pos hLodd_pos)).ne', Real.log_rpow hK, Real.log_mul hLtwo_pos.ne'
      (prod_pos hLodd_pos).ne', Real.log_prod (fun p hp => (hLodd_pos p hp).ne')]
  -- the split `S = {3} ∪ S7`
  have hsplit : ∀ f : ℕ → ℝ, ∑ p ∈ S, f p = f 3 + ∑ p ∈ S7, f p := by
    intro f
    rw [← sum_filter_add_sum_filter_not S (fun p => 7 ≤ p), add_comm]
    congr 1
    have h3 : S.filter (fun p => ¬ 7 ≤ p) = {3} := by
      ext p
      simp only [mem_filter, mem_singleton, not_le]
      constructor
      · rintro ⟨hp, hp7⟩
        have := hS3 p hp
        have := (mem_indexPrimes hp).2
        omega
      · rintro rfl
        refine ⟨?_, by norm_num⟩
        unfold S indexPrimes
        rw [mem_filter, mem_range]
        exact ⟨by omega, Nat.prime_three, by norm_num⟩
    rw [h3, sum_singleton]
  have hS7S : S7 ⊆ S := filter_subset _ _
  have h3S : (3 : ℕ) ∈ S := by
    unfold S indexPrimes
    rw [mem_filter, mem_range]
    exact ⟨by omega, Nat.prime_three, by norm_num⟩
  -- `∑_{S7} log L_{p,∞} ≤ ∑_{S7} log F_p - ∑_{S7U} log(F_p/L_{p,∞})`
  have hU7 : (indexPrimes U).filter (fun p => 7 ≤ p) ⊆ S7 := by
    intro p hp
    rw [mem_filter] at hp ⊢
    refine ⟨?_, hp.2⟩
    unfold S indexPrimes
    obtain ⟨hp1, -⟩ := hp
    unfold indexPrimes at hp1
    rw [mem_filter, mem_range] at hp1 ⊢
    exact ⟨lt_of_lt_of_le hp1.1 hU, hp1.2⟩
  have hratio : ∀ p ∈ S7, 0 ≤ Real.log (Fp p (z p) / Linf p (z p)) := fun p hp =>
    Real.log_nonneg ((one_le_div (hLinf_pos p (hS7S hp))).mpr (hLF p (hS7S hp)))
  have hsum7 : ∑ p ∈ S7, Real.log (Linf p (z p)) ≤ ∑ p ∈ S7, Real.log (Fp p (z p)) -
      ∑ p ∈ (indexPrimes U).filter (fun p => 7 ≤ p),
        Real.log (Fp p (z p) / Linf p (z p)) := by
    have hle := sum_le_sum_of_subset_of_nonneg hU7 (fun p hp _ => hratio p hp)
    have heq : ∑ p ∈ S7, Real.log (Linf p (z p)) = ∑ p ∈ S7, Real.log (Fp p (z p)) -
        ∑ p ∈ S7, Real.log (Fp p (z p) / Linf p (z p)) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun p hp => ?_
      rw [Real.log_div (hF_pos p (hS7S hp)).ne' (hLinf_pos p (hS7S hp)).ne']
      ring
    linarith
  -- `log M_a(K) ≤ log M_old`
  have hFprod_pos : 0 < ∏ p ∈ S7, Fp p (z p) := prod_pos fun p hp => hF_pos p (hS7S hp)
  have hMa_pos : 0 < Ma a Q K := mul_pos (Real.rpow_pos_of_pos (by linarith) _) hFprod_pos
  have hMa : Real.log (Ma a Q K) = a / 36 * (Real.log 144 + Real.log K) +
      ∑ p ∈ S7, Real.log (Fp p (z p)) := by
    unfold Ma
    rw [Real.log_mul (Real.rpow_pos_of_pos (by linarith) _).ne' hFprod_pos.ne',
      Real.log_rpow (by linarith), Real.log_mul (by norm_num) hK.ne',
      Real.log_prod (fun p hp => (hF_pos p (hS7S hp)).ne')]
  have hMold' : Real.log (Ma a Q K) ≤ Real.log Mold := Real.log_le_log hMa_pos hMold
  -- the surcharge total
  have hcard : (S.card : ℝ) ≤ Q := by
    have : S.card ≤ Q := (card_filter_le _ _).trans (card_range Q).le
    exact_mod_cast this
  have hs0 : 0 ≤ s := div_nonneg (mul_nonneg (topErr_pos (by norm_num) 64).le
    (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _)) (by linarith)
  have hsumLodd : ∑ p ∈ S, Real.log (Lodd p 64 (z p)) ≤
      ∑ p ∈ S, Real.log (Linf p (z p)) + Q * s := by
    have := sum_le_sum hLodd
    rw [sum_add_distrib, sum_const, nsmul_eq_mul] at this
    nlinarith [mul_le_mul_of_nonneg_right hcard hs0]
  have hEo : (Q : ℝ) * s = Q * topErr 3 64 * ((Q : ℝ) ^ (a / 18)) ^ 64 / (1 - topErr 3 64) := by
    rw [hs]
    ring
  rw [hsplit (fun p => Real.log (Linf p (z p)))] at hsumLodd
  have h3z : z 3 = (3 : ℝ) ^ (a / 18) := by simp [hz]
  rw [h3z] at hsumLodd
  rw [hMpad]
  rw [← hEo]
  linarith [hsum7, hMa, hMold', hLtwo, hsumLodd]

/-! ## The increments are nonvanishing square classes (`lem:imp:padic-envelope`) -/

/-- The square of a residue of valuation `j` (`p^j ∥ n`, `2j < h`) modulo `p^h`. -/
theorem sq_mod_val {p h j u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) (hjh : 2 * j < h) :
    (p ^ j * u) * (p ^ j * u) % p ^ h = p ^ (2 * j) * (u * u % p ^ (h - 2 * j)) ∧
      ¬ p ∣ u * u % p ^ (h - 2 * j) := by
  have hsplit : p ^ h = p ^ (2 * j) * p ^ (h - 2 * j) := by
    rw [← pow_add]; congr 1; omega
  refine ⟨?_, ?_⟩
  · rw [hsplit, show (p ^ j * u) * (p ^ j * u) = p ^ (2 * j) * (u * u) by ring,
      Nat.mul_mod_mul_left]
  · intro hd
    have hpk : p ∣ p ^ (h - 2 * j) := dvd_pow_self p (by omega)
    have : p ∣ u * u := by
      have := (Nat.dvd_mod_iff hpk).mp hd
      exact this
    rcases (Nat.Prime.dvd_mul hp).mp this with h1 | h1 <;> exact hu h1

/-- **The squares of residues of valuation `< v` are nonvanishing square classes**
(`lem:imp:padic-envelope`, physical cancellation). -/
theorem isNonvanishingSquareCoord_sq {p h v : ℕ} [hp : Fact p.Prime] (x : ZMod (p ^ h))
    (hx : ¬ p ^ v ∣ x.val) (hvh : 2 * v ≤ h) (h2 : p = 2 → 2 * v + 1 ≤ h) :
    TheoremC.IsNonvanishingSquareCoord p h (x ^ 2) := by
  set n := x.val with hn
  have hn0 : n ≠ 0 := by
    intro h0
    apply hx
    rw [h0]
    exact dvd_zero _
  set j := padicValNat p n
  have hjv : j < v := by
    by_contra hcon
    push Not at hcon
    apply hx
    exact (pow_dvd_pow p hcon).trans pow_padicValNat_dvd
  obtain ⟨u, hu⟩ : p ^ j ∣ n := pow_padicValNat_dvd
  have hpu : ¬ p ∣ u := by
    intro hd
    obtain ⟨u', rfl⟩ := hd
    have : p ^ (j + 1) ∣ n := ⟨u', by rw [hu]; ring⟩
    exact pow_succ_padicValNat_not_dvd hn0 this
  have hjh : 2 * j < h := by omega
  obtain ⟨hval, hw⟩ := sq_mod_val hp.out hpu hjh
  have hsq : (x ^ 2).val = p ^ (2 * j) * (u * u % p ^ (h - 2 * j)) := by
    rw [pow_two, ZMod.val_mul, ← hn, hu]
    exact hval
  set w := u * u % p ^ (h - 2 * j)
  have hw0 : w ≠ 0 := fun h0 => hw (h0 ▸ dvd_zero p)
  have hvalr : padicValNat p (x ^ 2).val = 2 * j := by
    rw [hsq, padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hw0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hw, add_zero]
  have hdiv : (x ^ 2).val / p ^ padicValNat p (x ^ 2).val = w := by
    rw [hvalr, hsq, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos _)]
  refine ⟨by rw [hsq]; exact mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) hw0, ?_, ?_⟩
  · rw [hvalr]; exact even_two_mul j
  · split_ifs with hp2
    · subst hp2
      refine ⟨by rw [hvalr]; have := h2 rfl; omega, ?_⟩
      rw [hdiv]
      have h8 : 8 ∣ 2 ^ (h - 2 * j) := by
        have : (8 : ℕ) = 2 ^ 3 := by norm_num
        rw [this]
        exact pow_dvd_pow 2 (by have := h2 rfl; omega)
      have hodd : u % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one u with h0 | h1
        · exact absurd (Nat.dvd_of_mod_eq_zero h0) hpu
        · exact h1
      change u * u % 2 ^ (h - 2 * j) % 8 = 1
      rw [Nat.mod_mod_of_dvd _ h8]
      have : u % 8 = 1 ∨ u % 8 = 3 ∨ u % 8 = 5 ∨ u % 8 = 7 := by omega
      rcases this with h | h | h | h <;> simp [Nat.mul_mod, h]
    · rw [hdiv]
      have hcast : ((w : ℕ) : ZMod p) = (u : ZMod p) * (u : ZMod p) := by
        change ((u * u % p ^ (h - 2 * j) : ℕ) : ZMod p) = _
        conv_rhs => rw [← Nat.cast_mul, ← Nat.div_add_mod (u * u) (p ^ (h - 2 * j))]
        push_cast
        rw [ZMod.natCast_self, zero_pow (by omega), zero_mul, zero_add]
      refine ⟨⟨(u : ZMod p), hcast⟩, ?_⟩
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact hw

/-- **Every increment of `squareIncrementLaw p h v` is a nonvanishing square class**
(`lem:imp:padic-envelope`, physical cancellation; `TheoremC.IsNonvanishingSquareCoord`): every
retained root has valuation `j < v`, and its square has valuation `2j`, with unit part a nonzero
square modulo `p` (odd `p`, `2v ≤ h`), resp. `≡ 1 (mod 8)` with `2j + 3 ≤ h` (`p = 2`,
`2v + 1 ≤ h`). -/
theorem squareIncrementLaw_nonvanishing {p h v : ℕ} [Fact p.Prime] [NeZero (p ^ h)]
    (hne : (PartV.lowValuation p h v).Nonempty) (hvh : 2 * v ≤ h) (h2 : p = 2 → 2 * v + 1 ≤ h)
    {r : ZMod (p ^ h)} (hr : (PartV.squareIncrementLaw p h v hne).weight r ≠ 0) :
    TheoremC.IsNonvanishingSquareCoord p h r := by
  obtain ⟨x, hx, rfl⟩ := PartV.squareIncrementLaw_support hne hr
  have hx' : ¬ p ^ v ∣ x.val := by
    unfold PartV.lowValuation at hx
    exact (mem_filter.mp hx).2
  exact isNonvanishingSquareCoord_sq x hx' hvh h2

/-- **The construction's increments are nonvanishing square classes** (`def:construction`(a),
`m_ext = 64`: `h_2 = 129`, `h_p = 128`). This is the clause "nonvanishing square increments
modulo `M₀`" of (CP0)(d) for V1's `indexIncrement`. -/
theorem indexIncrement_nonvanishing (p : ℕ) [Fact p.Prime] (hp : 2 ≤ p)
    [NeZero (p ^ PartV.smallModulusExponent p)] {r : ZMod (p ^ PartV.smallModulusExponent p)}
    (hr : (PartV.indexIncrement p hp).weight r ≠ 0) :
    TheoremC.IsNonvanishingSquareCoord p (PartV.smallModulusExponent p) r := by
  refine squareIncrementLaw_nonvanishing _ ?_ ?_ hr
  · unfold PartV.smallModulusExponent PartV.mExt
    split_ifs <;> norm_num
  · intro h2
    unfold PartV.smallModulusExponent PartV.mExt
    simp [h2]

end Sarkozy.PartVLaws
