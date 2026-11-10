module

public import Sarkozy.FiniteProbability
public import Mathlib.Algebra.BigOperators.Field

/-!
# `lem:push:localvariance` (a) and `lem:projection-diagonal`

`paper/sections/14_spectral.tex`, Section `subsec:spec:completion-variance`.

* `variance_le_range`, `relVariance_le_range`, `relVariance_le_ratio` — `lem:push:localvariance`
  (a), the range bound: if `0 < l ≤ C ≤ u` then
  `Var C ≤ (u - C̄)(C̄ - l) ≤ (u - l)² C̄² / (4ul)`, and for `u = R' l`,
  `Var C / C̄² ≤ δ'² / (4(1 + δ'))` with `δ' = R' - 1`.
* `projection_diagonal` — `lem:projection-diagonal`, for one `x` and `k`: the error function
  `E = pP_k - φ_k` of instance (A), with `pP_k = α⁻¹ C/C̄` and `φ_k = 2^{r_k}` on `Φ_k`
  (`α = |Φ_k|/p`), `E = 0` off `Φ_k ∪ x(U⁺)` and `|E| ≤ 2^{r_k}` on `x(U⁺)`, satisfies
  `‖E‖² ≤ n 4^{r_k}/p + 2^{r_k}/(1 - ê) (v̄ + ê²)` when `α⁻¹ ≤ 2^{r_k}/(1 - ê)`,
  `|1 - 2^{r_k} α| ≤ ê` and the relative variance of `C` on `Φ_k` is at most `v̄`.
  The norm is that of `L²(𝔽_p)` with the uniform probability.

Part (b) of `lem:push:localvariance` (the internal-neighbourhood bound) is in
`Sarkozy.Spectral.LocalVariance` (the averaging, the linear part and the assembly from the per-`z`
inputs) and `Sarkozy.Spectral.TwoVariable` (the two-variable bounds (ii), from
`Target.TwoVariable`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Spectral

open Sarkozy

variable {Ω : Type*} [Fintype Ω]

/-- **`lem:push:localvariance` (a), first inequality**: `Var C ≤ (u - C̄)(C̄ - l)`. -/
theorem variance_le_range (μ : FiniteLaw Ω) (C : Ω → ℝ) {l u : ℝ}
    (hl : ∀ ω, l ≤ C ω) (hu : ∀ ω, C ω ≤ u) :
    μ.expect (fun ω => (C ω - μ.expect C) ^ 2) ≤ (u - μ.expect C) * (μ.expect C - l) := by
  set m := μ.expect C with hm
  -- `E[(u - C)(C - l)] ≥ 0`
  have h0 : 0 ≤ μ.expect (fun ω => (u - C ω) * (C ω - l)) :=
    μ.expect_nonneg fun ω => mul_nonneg (by linarith [hu ω]) (by linarith [hl ω])
  have e1 : μ.expect (fun ω => (u - C ω) * (C ω - l)) =
      (u + l) * m - u * l - μ.expect (fun ω => C ω ^ 2) := by
    have : (fun ω => (u - C ω) * (C ω - l)) =
        fun ω => ((u + l) * C ω - u * l) - C ω ^ 2 := by
      funext ω; ring
    rw [this, FiniteLaw.expect_sub, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
      FiniteLaw.expect_const]
  have e2 : μ.expect (fun ω => (C ω - m) ^ 2) = μ.expect (fun ω => C ω ^ 2) - m ^ 2 := by
    have : (fun ω => (C ω - m) ^ 2) = fun ω => (C ω ^ 2 - (2 * m) * C ω) + m ^ 2 := by
      funext ω; ring
    rw [this, FiniteLaw.expect_add, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
      FiniteLaw.expect_const, ← hm]
    ring
  rw [e2]
  nlinarith

/-- `(u - m)(m - l) ≤ (u - l)² m² / (4ul)` for `0 < l ≤ u`. -/
theorem range_le_quarter {l u m : ℝ} (hl : 0 < l) (hlu : l ≤ u) :
    (u - m) * (m - l) ≤ (u - l) ^ 2 * m ^ 2 / (4 * u * l) := by
  have hu : 0 < u := lt_of_lt_of_le hl hlu
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg ((u + l) * m - 2 * u * l)]

/-- **`lem:push:localvariance` (a)**: the relative variance `Var C / C̄²` is at most
`(u - C̄)(C̄ - l)/C̄² ≤ (u - l)²/(4ul)`. -/
theorem relVariance_le_range (μ : FiniteLaw Ω) (C : Ω → ℝ) {l u : ℝ} (hl0 : 0 < l)
    (hl : ∀ ω, l ≤ C ω) (hu : ∀ ω, C ω ≤ u) :
    μ.expect (fun ω => (C ω - μ.expect C) ^ 2) / μ.expect C ^ 2 ≤ (u - l) ^ 2 / (4 * u * l) := by
  have hm : l ≤ μ.expect C := μ.const_le_expect hl
  have hm0 : 0 < μ.expect C := lt_of_lt_of_le hl0 hm
  have hne : Nonempty Ω := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h1 := μ.total
    simp at h1
  obtain ⟨ω₀⟩ := hne
  have hlu : l ≤ u := (hl ω₀).trans (hu ω₀)
  rw [div_le_iff₀ (by positivity)]
  calc μ.expect (fun ω => (C ω - μ.expect C) ^ 2) ≤ (u - μ.expect C) * (μ.expect C - l) :=
        variance_le_range μ C hl hu
    _ ≤ (u - l) ^ 2 * μ.expect C ^ 2 / (4 * u * l) := range_le_quarter hl0 hlu
    _ = (u - l) ^ 2 / (4 * u * l) * μ.expect C ^ 2 := by ring

/-- **`lem:push:localvariance` (a), "in particular"**: if `u = R' l` with `R' ≥ 1`, the bound
is `δ'²/(4(1 + δ'))` with `δ' = R' - 1`. -/
theorem relVariance_le_ratio (μ : FiniteLaw Ω) (C : Ω → ℝ) {l R : ℝ} (hl0 : 0 < l)
    (hR : 1 ≤ R) (hl : ∀ ω, l ≤ C ω) (hu : ∀ ω, C ω ≤ R * l) :
    μ.expect (fun ω => (C ω - μ.expect C) ^ 2) / μ.expect C ^ 2 ≤
      (R - 1) ^ 2 / (4 * (1 + (R - 1))) := by
  refine (relVariance_le_range μ C hl0 hl hu).trans_eq ?_
  have hR0 : 0 < R := by linarith
  rw [show 1 + (R - 1) = R by ring, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **`lem:projection-diagonal`**, for one `x` and `k`. Here `F = 𝔽_p` (any finite type, with
`p = |F|`), `Φ = Φ_k(x)`, `X = x(U⁺)` with `|X| ≤ n`, `C = C_k` the completion counts with mean
`C̄` on `Φ`, `α = |Φ|/p`, `κ = 2^{r_k}`, and `E = E_k(·; x)`. -/
theorem projection_diagonal {F : Type*} [Fintype F] [DecidableEq F] (Φ X : Finset F)
    (hdisj : Disjoint Φ X) (hΦ : Φ.Nonempty) (C E : F → ℝ) {α Cbar κ ehat vbar : ℝ} {n : ℕ}
    (hα : α = (Φ.card : ℝ) / Fintype.card F) (hCbar : Cbar = (∑ a ∈ Φ, C a) / Φ.card)
    (hCbar0 : Cbar ≠ 0) (hX : X.card ≤ n)
    (hEΦ : ∀ a ∈ Φ, E a = α⁻¹ * (C a / Cbar - 1) + (α⁻¹ - κ))
    (hEX : ∀ a ∈ X, |E a| ≤ κ) (hE0 : ∀ a, a ∉ Φ → a ∉ X → E a = 0)
    (hv : (∑ a ∈ Φ, (C a / Cbar - 1) ^ 2) / Φ.card ≤ vbar)
    (hαinv : α⁻¹ ≤ κ / (1 - ehat)) (hκα : |1 - κ * α| ≤ ehat) (hκ : 0 ≤ κ) (hehat : ehat < 1) :
    (∑ a, E a ^ 2) / Fintype.card F ≤ n * κ ^ 2 / Fintype.card F + κ / (1 - ehat) *
      (vbar + ehat ^ 2) := by
  have hΦc : (0 : ℝ) < Φ.card := by exact_mod_cast hΦ.card_pos
  have hFc : (0 : ℝ) < Fintype.card F := by
    obtain ⟨a, -⟩ := hΦ
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨a⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  have hd : 0 < 1 - ehat := by linarith
  -- split the sum over `Φ`, `X` and the rest
  have hsplit : ∑ a, E a ^ 2 = ∑ a ∈ Φ, E a ^ 2 + ∑ a ∈ X, E a ^ 2 := by
    rw [← Finset.sum_union hdisj]
    refine (Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_).symm
    rw [Finset.mem_union, not_or] at ha
    rw [hE0 a ha.1 ha.2]
    ring
  -- the part on `Φ`: the cross term vanishes
  have hmean : ∑ a ∈ Φ, (C a / Cbar - 1) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : ∑ a ∈ Φ, C a = Cbar * Φ.card := by
      rw [hCbar]
      field_simp
    rw [this]
    field_simp
    ring
  have hΦsum : ∑ a ∈ Φ, E a ^ 2 = α⁻¹ ^ 2 * ∑ a ∈ Φ, (C a / Cbar - 1) ^ 2 +
      Φ.card * (α⁻¹ - κ) ^ 2 := by
    rw [Finset.sum_congr rfl fun a ha => by rw [hEΦ a ha]]
    have e : ∀ a ∈ Φ, (α⁻¹ * (C a / Cbar - 1) + (α⁻¹ - κ)) ^ 2 =
        α⁻¹ ^ 2 * (C a / Cbar - 1) ^ 2 + (2 * α⁻¹ * (α⁻¹ - κ)) * (C a / Cbar - 1) +
          (α⁻¹ - κ) ^ 2 := fun a _ => by ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hmean, mul_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul]
  have hXsum : ∑ a ∈ X, E a ^ 2 ≤ n * κ ^ 2 := by
    calc ∑ a ∈ X, E a ^ 2 ≤ ∑ a ∈ X, κ ^ 2 := Finset.sum_le_sum fun a ha => by
          have h1 := hEX a ha
          have h2 := abs_nonneg (E a)
          nlinarith [sq_abs (E a)]
      _ = X.card * κ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * κ ^ 2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hX) (sq_nonneg _)
  -- `(1/p) ∑_Φ E² = α⁻¹ v + α⁻¹ (1 - κα)²`
  have hcardΦ : (Φ.card : ℝ) = α * Fintype.card F := by
    rw [hα]
    field_simp
  set v : ℝ := (∑ a ∈ Φ, (C a / Cbar - 1) ^ 2) / (Φ.card : ℝ) with hvdef
  have hΦp : (∑ a ∈ Φ, E a ^ 2) / Fintype.card F = α⁻¹ * v + α⁻¹ * (1 - κ * α) ^ 2 := by
    rw [hΦsum, hvdef, hcardΦ]
    field_simp
  have hv0 : 0 ≤ v := div_nonneg (Finset.sum_nonneg fun a _ => sq_nonneg _) hΦc.le
  have hsq : (1 - κ * α) ^ 2 ≤ ehat ^ 2 := by
    have := sq_abs (1 - κ * α)
    nlinarith [abs_nonneg (1 - κ * α)]
  have hb1 : α⁻¹ * v ≤ κ / (1 - ehat) * vbar :=
    mul_le_mul hαinv hv (hv0) (div_nonneg hκ hd.le)
  have hb2 : α⁻¹ * (1 - κ * α) ^ 2 ≤ κ / (1 - ehat) * ehat ^ 2 :=
    mul_le_mul hαinv hsq (sq_nonneg _) (div_nonneg hκ hd.le)
  rw [hsplit, add_div, hΦp]
  have hXp : (∑ a ∈ X, E a ^ 2) / Fintype.card F ≤ n * κ ^ 2 / Fintype.card F :=
    div_le_div_of_nonneg_right hXsum hFc.le
  nlinarith

end Sarkozy.Spectral
