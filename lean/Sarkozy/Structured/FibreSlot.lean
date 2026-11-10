module

public import Sarkozy.Structured.MainTerm
public import Sarkozy.Comparison.FibreEnergy

/-!
# The bound at a changed slot

The changed-slot step of the proof of `prop:record:density-structured`
(`paper/sections/08_scale_comparison.tex`). At a changed slot, for fixed `ω` and
`z`, the square-step model is `g̃ = λ (D/R) ∑_{j ∈ J_𝔞} h_j ∘ T_j` with `|J_𝔞| = R/D`
(`lem:record:fibre-scale`(b)). If the maps `T_j` preserve the reference law, the
children satisfy `Z_𝒮(h_j) ≤ C₀ ℓ^{-a} α_j^θ` (restoration `lem:record:fibre-scale`(c)
and the hypothesis on the smaller scale `ℓ`), `(D/R) ∑_j α_j = α_f/λ`, `1 ≤ λ`,
`λ^{72} ≤ 1 + u` and `ℓ ≥ L/ξ`, then

  `Z_𝒮(g̃) ≤ λ^{72-θ} C₀ ℓ^{-a} α_f^θ ≤ (1 + u) C₀ L^{-a} ξ^a α_f^θ`

(`changed_slot_bound`). It reuses `Sarkozy.SignedHolder.fibre_energy_le`
(`Sarkozy/Comparison/FibreEnergy.lean`), which does the triangle inequality,
invariance and concavity of `x ↦ x^{θ/72}`. Averaging over `(ω, z)` with Jensen's
inequality (`θ ≤ 1`) gives `E Z_𝒮(g̃_v) ≤ (1 + u) C₀ L^{-a} ξ_v^a ᾱ_v^θ` when
`E α_{f,v} = ᾱ_v` (`expect_changed_slot_bound`).
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

variable {X : Type*} [Fintype X]

/-- `ℓ^{-a} ≤ L^{-a} ξ^a` when `ℓ ≥ L/ξ > 0` and `a ≥ 0`. -/
theorem rpow_neg_le_of_ge_div {ℓ L ξ a : ℝ} (hL : 0 < L) (hξ : 0 < ξ) (hℓ : L / ξ ≤ ℓ)
    (ha : 0 ≤ a) : ℓ ^ (-a) ≤ L ^ (-a) * ξ ^ a := by
  have hLξ : 0 < L / ξ := div_pos hL hξ
  have h1 : ℓ ^ (-a) ≤ (L / ξ) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos hLξ hℓ (by linarith)
  refine h1.trans_eq ?_
  rw [Real.div_rpow hL.le hξ.le, Real.rpow_neg hξ.le, div_eq_mul_inv, inv_inv]

/-- **The bound at a changed slot**, for fixed `(ω, z)`. -/
theorem changed_slot_bound (μS : FiniteLaw (Slot → X))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) {ι : Type*} (J : Finset ι)
    (hJ : J.Nonempty) (h : ι → X → ℝ) (T : ι → X → X)
    (hinv : ∀ j ∈ J, referenceEnergy μS (h j ∘ T j) = referenceEnergy μS (h j))
    {lam C0 a θ ℓ L ξ αf u : ℝ} (hlam1 : 1 ≤ lam) (hlamu : lam ^ 72 ≤ 1 + u)
    (hC0 : 0 ≤ C0) (ha : 0 ≤ a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 72) (hL : 0 < L) (hξ : 0 < ξ)
    (hℓ : L / ξ ≤ ℓ) (α : ι → ℝ) (hα : ∀ j ∈ J, 0 ≤ α j)
    (hZ : ∀ j ∈ J, referenceEnergy μS (h j) ≤ C0 * ℓ ^ (-a) * α j ^ θ)
    (hmean : (J.card : ℝ)⁻¹ * ∑ j ∈ J, α j = αf / lam) :
    referenceEnergy μS (lam • ∑ j ∈ J, ((J.card : ℝ)⁻¹) • (h j ∘ T j)) ≤
      (1 + u) * C0 * L ^ (-a) * ξ ^ a * αf ^ θ := by
  have hL0 : 0 < ℓ := lt_of_lt_of_le (div_pos hL hξ) hℓ
  have hB : 0 ≤ C0 * ℓ ^ (-a) := mul_nonneg hC0 (Real.rpow_nonneg hL0.le _)
  have hlam0 : 0 ≤ lam := by linarith
  have hfib := (slot_signedHolder hμS).fibre_energy_le J hJ h T hinv hlam0 hB hθ0
    (by rw [card_slot]; exact_mod_cast hθ1) α hα hZ
  rw [card_slot, hmean] at hfib
  -- the mean of the children is `αf/λ`; then `λ^{72} (αf/λ)^θ ≤ λ^{72} αf^θ`
  have hαf : 0 ≤ αf := by
    have hmean0 : 0 ≤ (J.card : ℝ)⁻¹ * ∑ j ∈ J, α j :=
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (sum_nonneg hα)
    rw [hmean] at hmean0
    have : 0 < lam := by linarith
    have h2 := mul_nonneg hmean0 this.le
    rwa [div_mul_cancel₀ _ this.ne'] at h2
  have hdivle : (αf / lam) ^ θ ≤ αf ^ θ :=
    Real.rpow_le_rpow (div_nonneg hαf hlam0) (div_le_self hαf hlam1) hθ0
  have hpowpos : 0 ≤ lam ^ 72 := pow_nonneg hlam0 72
  calc referenceEnergy μS (lam • ∑ j ∈ J, ((J.card : ℝ)⁻¹) • (h j ∘ T j))
      ≤ lam ^ 72 * (C0 * ℓ ^ (-a)) * (αf / lam) ^ θ := hfib
    _ ≤ (1 + u) * (C0 * ℓ ^ (-a)) * αf ^ θ := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hlamu hB) hdivle
          (Real.rpow_nonneg (div_nonneg hαf hlam0) _)
        exact mul_nonneg (le_trans hpowpos hlamu) hB
    _ ≤ (1 + u) * (C0 * (L ^ (-a) * ξ ^ a)) * αf ^ θ := by
        have hu : 0 ≤ 1 + u := le_trans hpowpos hlamu
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hαf _)
        apply mul_le_mul_of_nonneg_left _ hu
        exact mul_le_mul_of_nonneg_left (rpow_neg_le_of_ge_div hL hξ hℓ ha) hC0
    _ = (1 + u) * C0 * L ^ (-a) * ξ ^ a * αf ^ θ := by ring

/-- **Averaging the changed-slot bound** with Jensen's inequality (`θ ≤ 1`): if
`Z_𝒮(g̃) ≤ K α_f^θ` at every sample and `E α_f = ᾱ`, then `E Z_𝒮(g̃) ≤ K ᾱ^θ`. -/
theorem expect_changed_slot_bound {Ω' : Type*} [Fintype Ω'] (Jt : FiniteLaw Ω')
    (μS : FiniteLaw (Slot → X)) (G : Ω' → X → ℝ) (αf : Ω' → ℝ) (hαf : ∀ p, 0 ≤ αf p)
    {K θ αbar : ℝ} (hK : 0 ≤ K) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hpoint : ∀ p, referenceEnergy μS (G p) ≤ K * αf p ^ θ)
    (hmean : Jt.expect αf = αbar) :
    Jt.expect (fun p => referenceEnergy μS (G p)) ≤ K * αbar ^ θ := by
  calc Jt.expect (fun p => referenceEnergy μS (G p)) ≤ Jt.expect (fun p => K * αf p ^ θ) :=
        Jt.expect_mono hpoint
    _ = K * Jt.expect (fun p => αf p ^ θ) := Jt.expect_const_mul _ _
    _ ≤ K * Jt.expect αf ^ θ :=
        mul_le_mul_of_nonneg_left (expect_rpow_le_rpow_expect Jt hαf hθ0 hθ1) hK
    _ = K * αbar ^ θ := by rw [hmean]

end Sarkozy.Structured
