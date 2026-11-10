module

public import Sarkozy.Cancellation.Summation

@[expose] public section

/-!
# Assembly of `lem:record:density-can` (Steps 1–4)

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`. The proof combines

* Step 1 (pair decomposition): `|∫∏G_w dϱ|² ≤ (∫‖W_x‖²) (T₀^{-2γ} ∫‖φ_x‖² + ∑_{q_U ≤ T₀} q_U^{-2γ} ∫‖E_U φ_x‖²)`,
  which is `lem:tr:pairsupport` (`Sarkozy.Mixing.pair_support`) followed by Cauchy–Schwarz over
  the prefix labels;
* Step 2 (moments): `∫‖W_x‖² ≤ C N^ε α`, `∫‖φ_x‖² ≤ C N^ε α` (`lem:record:lift-moments`(c));
* Step 3 (low pair support): `∫‖E_U φ_x‖² ≤ C' N^{-1/60+ε} α` for every `U` with `q_U ≤ T₀`;
* Step 4 (summation): `∑_{q_U ≤ T₀} q_U^{-2γ} ≤ 1 + T₀^{1-2γ}/(1-2γ)` (`Summation.lean`).

`density_can_assembly` proves the conclusion
`|∫∏G_w dϱ| ≤ C N^ε α (N^{-γ t_an} + N^{-1/120 + t_an(1/2-γ)})` from these four inputs, and
`density_can_stage` the final form `≤ 2 C L^{-σ} α` at the analytic stage
(`def:record:analytic-stage`: `γ = 255/1024`, `t_an = 1/60`, `σ = 1/825`, `δ = 10^{-10}`,
`ε = 72δ`), from (S2) and (S3).

New material for this paper.
-/

namespace Sarkozy.Cancellation

open Finset

lemma sqrt_add_le_add_sqrt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- **Assembly of Steps 1–4 of `lem:record:density-can`.** Abstract form: `I` is the integral
`∫∏_w G_w dϱ`, `Wsq = ∫‖W_x‖²`, `φsq = ∫‖φ_x‖²`, and `e U = ∫‖E_U φ_x‖²` for the pair supports `U`
in `𝒰 = {U : q_U ≤ T₀}`, `T₀ = N^t`. -/
theorem density_can_assembly {ι : Type*} (𝒰 : Finset ι) (qU e : ι → ℝ)
    (I Wsq φsq α N ε γ t C₂ C₃ : ℝ)
    (hN : 1 ≤ N) (hα : 0 ≤ α) (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2) (ht : 0 ≤ t)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hstep1 : I ^ 2 ≤ Wsq * ((N ^ t) ^ (-2 * γ) * φsq + ∑ U ∈ 𝒰, qU U ^ (-2 * γ) * e U))
    (hW : Wsq ≤ C₂ * N ^ ε * α) (hφ0 : 0 ≤ φsq) (hφ : φsq ≤ C₂ * N ^ ε * α)
    (hq : ∀ U ∈ 𝒰, 0 < qU U) (he0 : ∀ U ∈ 𝒰, 0 ≤ e U)
    (he : ∀ U ∈ 𝒰, e U ≤ C₃ * N ^ (-(1 : ℝ) / 60 + ε) * α)
    (hsum : ∑ U ∈ 𝒰, qU U ^ (-2 * γ) ≤ 1 + (N ^ t) ^ (1 - 2 * γ) / (1 - 2 * γ)) :
    |I| ≤ (Real.sqrt C₂ * (Real.sqrt C₂ + Real.sqrt (C₃ * (1 + 1 / (1 - 2 * γ))))) *
      N ^ ε * α * (N ^ (-(γ * t)) + N ^ (-(1 : ℝ) / 120 + t * (1 / 2 - γ))) := by
  have hN0 : 0 < N := by linarith
  have h2γ : 0 < 1 - 2 * γ := by linarith
  set P := N ^ ε * α with hP
  have hP0 : 0 ≤ P := by positivity
  -- the sum over the pair supports
  have hsumU : ∑ U ∈ 𝒰, qU U ^ (-2 * γ) * e U ≤
      (1 + (N ^ t) ^ (1 - 2 * γ) / (1 - 2 * γ)) * (C₃ * N ^ (-(1 : ℝ) / 60 + ε) * α) := by
    calc ∑ U ∈ 𝒰, qU U ^ (-2 * γ) * e U
        ≤ ∑ U ∈ 𝒰, qU U ^ (-2 * γ) * (C₃ * N ^ (-(1 : ℝ) / 60 + ε) * α) := by
          apply sum_le_sum
          intro U hU
          exact mul_le_mul_of_nonneg_left (he U hU) (Real.rpow_nonneg (hq U hU).le _)
      _ = (∑ U ∈ 𝒰, qU U ^ (-2 * γ)) * (C₃ * N ^ (-(1 : ℝ) / 60 + ε) * α) := by
          rw [sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsum (by positivity)
  -- powers of `N`
  have hNt : 1 ≤ (N ^ t) ^ (1 - 2 * γ) := by
    apply Real.one_le_rpow (Real.one_le_rpow hN ht) h2γ.le
  have e1 : (N ^ t) ^ (-2 * γ) = (N ^ (-(γ * t))) ^ 2 := by
    rw [← Real.rpow_mul hN0.le, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1; push_cast; ring
  have e2 : (N ^ t) ^ (1 - 2 * γ) * N ^ (-(1 : ℝ) / 60 + ε) =
      (N ^ (-(1 : ℝ) / 120 + t * (1 / 2 - γ))) ^ 2 * N ^ ε := by
    rw [← Real.rpow_mul hN0.le, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
      ← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1; push_cast; ring
  set a := N ^ (-(γ * t)) with ha
  set b := N ^ (-(1 : ℝ) / 120 + t * (1 / 2 - γ)) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  set K₃ := C₃ * (1 + 1 / (1 - 2 * γ)) with hK₃
  have hK₃0 : 0 ≤ K₃ := by positivity
  -- the bracket
  have hbracket : (N ^ t) ^ (-2 * γ) * φsq + ∑ U ∈ 𝒰, qU U ^ (-2 * γ) * e U ≤
      P * (C₂ * a ^ 2 + K₃ * b ^ 2) := by
    have h1 : (N ^ t) ^ (-2 * γ) * φsq ≤ a ^ 2 * (C₂ * P) := by
      rw [e1]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
      rw [hP]; linarith
    have h2 : (1 + (N ^ t) ^ (1 - 2 * γ) / (1 - 2 * γ)) ≤
        (N ^ t) ^ (1 - 2 * γ) * (1 + 1 / (1 - 2 * γ)) := by
      rw [mul_add, mul_one, mul_one_div]
      linarith
    have h3 : (1 + (N ^ t) ^ (1 - 2 * γ) / (1 - 2 * γ)) * (C₃ * N ^ (-(1 : ℝ) / 60 + ε) * α) ≤
        K₃ * b ^ 2 * P := by
      calc (1 + (N ^ t) ^ (1 - 2 * γ) / (1 - 2 * γ)) * (C₃ * N ^ (-(1 : ℝ) / 60 + ε) * α)
          ≤ ((N ^ t) ^ (1 - 2 * γ) * (1 + 1 / (1 - 2 * γ))) *
              (C₃ * N ^ (-(1 : ℝ) / 60 + ε) * α) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = K₃ * ((N ^ t) ^ (1 - 2 * γ) * N ^ (-(1 : ℝ) / 60 + ε)) * α := by
            rw [hK₃]; ring
        _ = K₃ * b ^ 2 * P := by rw [e2, hP]; ring
    nlinarith [hsumU, h1, h3]
  have hI2 : I ^ 2 ≤ (Real.sqrt C₂ * P) ^ 2 * (C₂ * a ^ 2 + K₃ * b ^ 2) := by
    calc I ^ 2 ≤ Wsq * ((N ^ t) ^ (-2 * γ) * φsq + ∑ U ∈ 𝒰, qU U ^ (-2 * γ) * e U) := hstep1
      _ ≤ (C₂ * P) * (P * (C₂ * a ^ 2 + K₃ * b ^ 2)) := by
          apply mul_le_mul _ hbracket (add_nonneg
            (mul_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hN0.le t) (-2 * γ)) hφ0)
            (sum_nonneg fun U hU => mul_nonneg (Real.rpow_nonneg (hq U hU).le _) (he0 U hU)))
            (by positivity)
          rw [hP]; linarith
      _ = (Real.sqrt C₂ * P) ^ 2 * (C₂ * a ^ 2 + K₃ * b ^ 2) := by
          rw [mul_pow, Real.sq_sqrt hC₂]; ring
  have hroot : |I| ≤ Real.sqrt C₂ * P * Real.sqrt (C₂ * a ^ 2 + K₃ * b ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt (I ^ 2) ≤ Real.sqrt ((Real.sqrt C₂ * P) ^ 2 * (C₂ * a ^ 2 + K₃ * b ^ 2)) :=
          Real.sqrt_le_sqrt hI2
      _ = Real.sqrt C₂ * P * Real.sqrt (C₂ * a ^ 2 + K₃ * b ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hsplit : Real.sqrt (C₂ * a ^ 2 + K₃ * b ^ 2) ≤ Real.sqrt C₂ * a + Real.sqrt K₃ * b := by
    apply (sqrt_add_le_add_sqrt _ _ (by positivity) (by positivity)).trans
    rw [Real.sqrt_mul hC₂, Real.sqrt_mul hK₃0, Real.sqrt_sq ha0, Real.sqrt_sq hb0]
  have hfin : Real.sqrt C₂ * a + Real.sqrt K₃ * b ≤ (Real.sqrt C₂ + Real.sqrt K₃) * (a + b) := by
    nlinarith [Real.sqrt_nonneg C₂, Real.sqrt_nonneg K₃]
  calc |I| ≤ Real.sqrt C₂ * P * Real.sqrt (C₂ * a ^ 2 + K₃ * b ^ 2) := hroot
    _ ≤ Real.sqrt C₂ * P * ((Real.sqrt C₂ + Real.sqrt K₃) * (a + b)) := by
        apply mul_le_mul_of_nonneg_left (hsplit.trans hfin) (by positivity)
    _ = _ := by rw [hP]; ring

/-! ## The analytic stage -/

/-- The mixing exponent `γ = 255/1024` (`def:record:analytic-stage`). -/
noncomputable def stageGamma : ℝ := 255 / 1024
/-- The truncation exponent `t_an = 1/60`. -/
noncomputable def stageTan : ℝ := 1 / 60
/-- The error exponent `σ = 1/825`. -/
noncomputable def stageSigma : ℝ := 1 / 825
/-- The moment loss per slot `δ = 10^{-10}`. -/
noncomputable def stageDelta : ℝ := 1 / 10 ^ 10

/-- (S2): `γ t_an − 72δ − σ > 0`; (S3): `β/6 − t_an(1/2 − γ) − 72δ − σ > 0` with `β = 1/20`. -/
theorem stage_S2_S3 :
    stageGamma * stageTan - 72 * stageDelta - stageSigma > 0 ∧
      (1 / 20) / 6 - stageTan * (1 / 2 - stageGamma) - 72 * stageDelta - stageSigma > 0 := by
  unfold stageGamma stageTan stageDelta stageSigma
  constructor <;> norm_num

/-- The final form of `lem:record:density-can` at the analytic stage: from
`|I| ≤ C N^{72δ} α (N^{-γ t_an} + N^{-1/120 + t_an(1/2-γ)})` and `1 ≤ L ≤ N`,
`|I| ≤ 2 C L^{-σ} α`, by (S2) and (S3). -/
theorem density_can_stage (I α N L C : ℝ) (hL : 1 ≤ L) (hLN : L ≤ N) (hC : 0 ≤ C)
    (hα : 0 ≤ α)
    (h : |I| ≤ C * N ^ (72 * stageDelta) * α *
      (N ^ (-(stageGamma * stageTan)) + N ^ (-(1 : ℝ) / 120 + stageTan * (1 / 2 - stageGamma)))) :
    |I| ≤ 2 * C * L ^ (-stageSigma) * α := by
  have hN : 1 ≤ N := hL.trans hLN
  have hN0 : 0 < N := by linarith
  have hS2 : 72 * stageDelta + -(stageGamma * stageTan) ≤ -stageSigma := by
    unfold stageGamma stageTan stageDelta stageSigma; norm_num
  have hS3 : 72 * stageDelta + (-(1 : ℝ) / 120 + stageTan * (1 / 2 - stageGamma)) ≤ -stageSigma := by
    unfold stageGamma stageTan stageDelta stageSigma; norm_num
  have h1 : N ^ (72 * stageDelta) * N ^ (-(stageGamma * stageTan)) ≤ N ^ (-stageSigma) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN hS2
  have h2 : N ^ (72 * stageDelta) * N ^ (-(1 : ℝ) / 120 + stageTan * (1 / 2 - stageGamma)) ≤
      N ^ (-stageSigma) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN hS3
  have h3 : N ^ (-stageSigma) ≤ L ^ (-stageSigma) := by
    apply Real.rpow_le_rpow_of_nonpos (by linarith) hLN
    unfold stageSigma; norm_num
  calc |I| ≤ C * N ^ (72 * stageDelta) * α *
        (N ^ (-(stageGamma * stageTan)) + N ^ (-(1 : ℝ) / 120 + stageTan * (1 / 2 - stageGamma))) := h
    _ = C * α * (N ^ (72 * stageDelta) * N ^ (-(stageGamma * stageTan)) +
          N ^ (72 * stageDelta) * N ^ (-(1 : ℝ) / 120 + stageTan * (1 / 2 - stageGamma))) := by ring
    _ ≤ C * α * (L ^ (-stageSigma) + L ^ (-stageSigma)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (h1.trans h3) (h2.trans h3)
    _ = 2 * C * L ^ (-stageSigma) * α := by ring

/-- **`lem:record:density-can` from its four inputs, at the analytic stage.** With
`ε = 72δ`, `γ = 255/1024`, `t_an = 1/60`, `T₀ = N^{t_an}`: if Step 1 (pair decomposition),
Step 2 (moments), Step 3 (low pair support, for every `U ∈ 𝒰`) and Step 4 (summation) hold, then
`|∫∏G_w dϱ| ≤ C_can N^{72δ} α (N^{-γ t_an} + N^{-1/120 + t_an(1/2-γ)}) ≤ 2 C_can L^{-σ} α`,
with `C_can = √C₂ (√C₂ + √(C₃ (1 + 1/(1-2γ))))`. -/
theorem density_can_of_inputs {ι : Type*} (𝒰 : Finset ι) (qU e : ι → ℝ)
    (I Wsq φsq α N L C₂ C₃ : ℝ) (hL : 1 ≤ L) (hLN : L ≤ N) (hα : 0 ≤ α)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hstep1 : I ^ 2 ≤ Wsq * ((N ^ stageTan) ^ (-2 * stageGamma) * φsq +
      ∑ U ∈ 𝒰, qU U ^ (-2 * stageGamma) * e U))
    (hW : Wsq ≤ C₂ * N ^ (72 * stageDelta) * α)
    (hφ0 : 0 ≤ φsq) (hφ : φsq ≤ C₂ * N ^ (72 * stageDelta) * α)
    (hq : ∀ U ∈ 𝒰, 0 < qU U) (he0 : ∀ U ∈ 𝒰, 0 ≤ e U)
    (he : ∀ U ∈ 𝒰, e U ≤ C₃ * N ^ (-(1 : ℝ) / 60 + 72 * stageDelta) * α)
    (hsum : ∑ U ∈ 𝒰, qU U ^ (-2 * stageGamma) ≤
      1 + (N ^ stageTan) ^ (1 - 2 * stageGamma) / (1 - 2 * stageGamma)) :
    let Ccan := Real.sqrt C₂ * (Real.sqrt C₂ + Real.sqrt (C₃ * (1 + 1 / (1 - 2 * stageGamma))))
    |I| ≤ Ccan * N ^ (72 * stageDelta) * α *
        (N ^ (-(stageGamma * stageTan)) + N ^ (-(1 : ℝ) / 120 + stageTan * (1 / 2 - stageGamma))) ∧
      |I| ≤ 2 * Ccan * L ^ (-stageSigma) * α := by
  intro Ccan
  have hN : 1 ≤ N := hL.trans hLN
  have hγ0 : 0 < stageGamma := by unfold stageGamma; norm_num
  have hγ1 : stageGamma < 1 / 2 := by unfold stageGamma; norm_num
  have ht : 0 ≤ stageTan := by unfold stageTan; norm_num
  have h1 := density_can_assembly 𝒰 qU e I Wsq φsq α N (72 * stageDelta) stageGamma stageTan C₂ C₃
    hN hα hγ0 hγ1 ht hC₂ hC₃ hstep1 hW hφ0 hφ hq he0 he hsum
  refine ⟨h1, ?_⟩
  exact density_can_stage I α N L Ccan hL hLN (by positivity) hα h1

end Sarkozy.Cancellation
