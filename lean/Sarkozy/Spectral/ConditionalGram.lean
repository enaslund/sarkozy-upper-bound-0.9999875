module

public import Sarkozy.Spectral.RouteA
public import Sarkozy.FiniteProbability

/-!
# `lem:push:conditionalgram`: the conditional-density Gram refinement

`paper/sections/14_spectral.tex`, `lem:push:conditionalgram`, in abstract form, with the
weighted Schur bound used for its inputs.

* `weighted_schur`: a *weighted Schur bound* `s ≥ max_k (Y w)_k / w_k` of a nonnegative
  symmetric `Y` bounds `|u^* X u| ≤ s |u|²` for every `X` with `|X_kl| ≤ Y_kl`.
* `synthesis_norm_sq_le_schur`: for vectors `D_k` with `|⟪D_k, D_l⟫| ≤ Y_kl`, the synthesis
  operator `w ↦ ∑ w_k D_k` has `‖∑ w_k D_k‖² ≤ s |w|²` (the input `Γ_D`).
* `synthesis_norm_sq_le_trace`: the trace bound `‖∑ w_k D_k‖² ≤ (∑_k ‖D_k‖²) |w|²`.
* `conditional_gram_pointwise`, `conditional_gram`: if, at every `x`, the synthesis operator of
  the model densities `ψ_k(x, ·)` satisfies `‖A_x w‖² ≤ w^* H w + h₀ |w|²` with
  `w^* H w ≤ λ̄(H) |w|²`, and that of the corrections `D_k(x, ·)` satisfies
  `‖D_x w‖² ≤ Γ_D |w|²`, then the conditional-density Gram matrix
  `w^* H̃ w = E_x ‖A_x w + D_x w‖²` satisfies `w^* H̃ w ≤ w^* H w + ε^loc_H |w|²` with
  `ε^loc_H = h₀ + 2 (Γ_D (λ̄(H) + h₀))^{1/2} + Γ_D` (`eq:push:conditionalgram`).
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate BigOperators
open RCLike

namespace Sarkozy.Spectral

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-- **The weighted Schur bound**: if `‖G k l‖ ≤ Y k l` with `Y` symmetric, `w > 0` and
`(Y w)_k ≤ s w_k` for all `k`, then `‖∑_{k,l} conj(u_k) G_kl u_l‖ ≤ s ∑_k |u_k|²`. -/
theorem weighted_schur (G : ι → ι → 𝕜) (Y : ι → ι → ℝ) (hGY : ∀ k l, ‖G k l‖ ≤ Y k l)
    (hY : ∀ k l, Y k l = Y l k) (w : ι → ℝ) (hw : ∀ k, 0 < w k) {s : ℝ}
    (hs : ∀ k, ∑ l, Y k l * w l ≤ s * w k) (u : ι → 𝕜) :
    ‖∑ k, ∑ l, conj (u k) * G k l * u l‖ ≤ s * sqn u := by
  have hY0 : ∀ k l, 0 ≤ Y k l := fun k l => (norm_nonneg _).trans (hGY k l)
  -- `|u_k| |u_l| ≤ (w_l/w_k |u_k|² + w_k/w_l |u_l|²)/2`
  have hamgm : ∀ k l, ‖u k‖ * ‖u l‖ ≤
      (w l / w k * ‖u k‖ ^ 2 + w k / w l * ‖u l‖ ^ 2) / 2 := by
    intro k l
    have hk := hw k
    have hl := hw l
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have e : w l / w k * ‖u k‖ ^ 2 + w k / w l * ‖u l‖ ^ 2 - ‖u k‖ * ‖u l‖ * 2 =
        (w l * ‖u k‖ - w k * ‖u l‖) ^ 2 / (w k * w l) := by
      field_simp
      ring
    have : 0 ≤ (w l * ‖u k‖ - w k * ‖u l‖) ^ 2 / (w k * w l) := by positivity
    linarith
  calc ‖∑ k, ∑ l, conj (u k) * G k l * u l‖
      ≤ ∑ k, ∑ l, ‖conj (u k) * G k l * u l‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _)
    _ ≤ ∑ k, ∑ l, Y k l * (‖u k‖ * ‖u l‖) := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
        rw [norm_mul, norm_mul, RCLike.norm_conj]
        nlinarith [hGY k l, norm_nonneg (u k), norm_nonneg (u l), norm_nonneg (G k l),
          mul_nonneg (norm_nonneg (u k)) (norm_nonneg (u l))]
    _ ≤ ∑ k, ∑ l, Y k l * ((w l / w k * ‖u k‖ ^ 2 + w k / w l * ‖u l‖ ^ 2) / 2) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_left (hamgm k l) (hY0 k l)
    _ = ∑ k, ‖u k‖ ^ 2 * ((∑ l, Y k l * w l) / w k) := by
        -- split the two halves and swap the summation order in the second
        have e1 : ∀ k l, Y k l * ((w l / w k * ‖u k‖ ^ 2 + w k / w l * ‖u l‖ ^ 2) / 2) =
            Y k l * w l / w k * ‖u k‖ ^ 2 / 2 + Y k l * w k / w l * ‖u l‖ ^ 2 / 2 :=
          fun k l => by ring
        simp_rw [e1, Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun k l => Y k l * w k / w l * ‖u l‖ ^ 2 / 2)]
        simp_rw [hY]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
    _ ≤ ∑ k, ‖u k‖ ^ 2 * s := Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left ((div_le_iff₀ (hw k)).mpr (hs k)) (sq_nonneg _)
    _ = s * sqn u := by rw [sqn, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- The squared norm of a synthesis `∑_k w_k D_k` is the Gram form. -/
theorem norm_sq_synthesis (D : ι → W) (w : ι → 𝕜) :
    ‖∑ k, w k • D k‖ ^ 2 = re (∑ k, ∑ l, conj (w k) * ⟪D k, D l⟫ * w l) := by
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), sum_inner]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [inner_smul_right]
  ring

/-- **The input `Γ_D` by a weighted Schur bound**: if `|⟪D_k, D_l⟫| ≤ Y_kl` with `Y`
symmetric and `(Y w')_k ≤ s w'_k` for positive weights `w'`, then `‖∑ w_k D_k‖² ≤ s |w|²`. -/
theorem synthesis_norm_sq_le_schur (D : ι → W) (Y : ι → ι → ℝ)
    (hDY : ∀ k l, ‖⟪D k, D l⟫‖ ≤ Y k l) (hY : ∀ k l, Y k l = Y l k) (w' : ι → ℝ)
    (hw' : ∀ k, 0 < w' k) {s : ℝ} (hs : ∀ k, ∑ l, Y k l * w' l ≤ s * w' k) (w : ι → 𝕜) :
    ‖∑ k, w k • D k‖ ^ 2 ≤ s * sqn w := by
  rw [norm_sq_synthesis]
  exact (re_le_norm _).trans (weighted_schur (fun k l => ⟪D k, D l⟫) Y hDY hY w' hw' hs w)

/-- **The trace bound** `‖∑ w_k D_k‖² ≤ (∑_k ‖D_k‖²) |w|²` (no positivity needed). -/
theorem synthesis_norm_sq_le_trace (D : ι → W) (w : ι → 𝕜) :
    ‖∑ k, w k • D k‖ ^ 2 ≤ (∑ k, ‖D k‖ ^ 2) * sqn w := by
  have h1 : ‖∑ k, w k • D k‖ ≤ ∑ k, ‖w k‖ * ‖D k‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_smul (w k) (D k)).le)
  have h2 : (∑ k, ‖w k‖ * ‖D k‖) ^ 2 ≤ (∑ k, ‖w k‖ ^ 2) * ∑ k, ‖D k‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ‖∑ k, w k • D k‖ ^ 2 ≤ (∑ k, ‖w k‖ * ‖D k‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [sqn]
  linarith

/-- **`lem:push:conditionalgram`, pointwise in `x`.** -/
theorem conditional_gram_pointwise (A D : W) {Hw h₀ lam ΓD sw : ℝ} (hsw : 0 ≤ sw)
    (hA : ‖A‖ ^ 2 ≤ Hw + h₀ * sw) (hH : Hw ≤ lam * sw) (hD : ‖D‖ ^ 2 ≤ ΓD * sw)
    (hΓ : 0 ≤ ΓD) (hlh : 0 ≤ lam + h₀) :
    ‖A + D‖ ^ 2 ≤ Hw + (h₀ + 2 * √(ΓD * (lam + h₀)) + ΓD) * sw := by
  have hAn : ‖A‖ ≤ √((lam + h₀) * sw) := by
    rw [← Real.sqrt_sq (norm_nonneg A)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hDn : ‖D‖ ≤ √(ΓD * sw) := by
    rw [← Real.sqrt_sq (norm_nonneg D)]
    exact Real.sqrt_le_sqrt hD
  have hprod : ‖A‖ * ‖D‖ ≤ √(ΓD * (lam + h₀)) * sw := by
    calc ‖A‖ * ‖D‖ ≤ √((lam + h₀) * sw) * √(ΓD * sw) :=
          mul_le_mul hAn hDn (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = √(ΓD * (lam + h₀)) * sw := by
          rw [← Real.sqrt_mul (mul_nonneg hlh hsw),
            show (lam + h₀) * sw * (ΓD * sw) = ΓD * (lam + h₀) * sw ^ 2 by ring,
            Real.sqrt_mul (mul_nonneg hΓ hlh), Real.sqrt_sq hsw]
  have htri : ‖A + D‖ ≤ ‖A‖ + ‖D‖ := norm_add_le A D
  have hsq : ‖A + D‖ ^ 2 ≤ (‖A‖ + ‖D‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith

/-- **`lem:push:conditionalgram`** (`eq:push:conditionalgram`): averaging the pointwise bound
over `x` with a law `ν` (the half marginal `m_p` of instance (A)), the conditional-density
Gram form `E_x ‖A_x w + D_x w‖²` is at most `w^* H w + ε^loc_H |w|²`. -/
theorem conditional_gram {X : Type*} [Fintype X] (ν : FiniteLaw X) (A D : X → W)
    {Hw h₀ lam ΓD sw : ℝ} (hsw : 0 ≤ sw) (hA : ∀ x, ‖A x‖ ^ 2 ≤ Hw + h₀ * sw)
    (hH : Hw ≤ lam * sw) (hD : ∀ x, ‖D x‖ ^ 2 ≤ ΓD * sw) (hΓ : 0 ≤ ΓD) (hlh : 0 ≤ lam + h₀) :
    ν.expect (fun x => ‖A x + D x‖ ^ 2) ≤
      Hw + (h₀ + 2 * √(ΓD * (lam + h₀)) + ΓD) * sw :=
  ν.expect_le_const fun x =>
    conditional_gram_pointwise (A x) (D x) hsw (hA x) hH (hD x) hΓ hlh

end Sarkozy.Spectral
