module

public import Sarkozy.DensityDC.Telescoping
public import Sarkozy.Moments.Holder

/-!
# Step 2 of `lem:record:density-dc`: averaging

`lem:record:density-dc` (`paper/sections/08_scale_comparison.tex`), Step 2, for structured
energies (`Sarkozy.Structured.structuredEnergy`). The setting:
* the changed slots form `C`, and outside `C` the inputs `g` and `g̃` agree;
* every telescoping term (`Sarkozy.DensityDC.hybrid`) satisfies a per-sample bound of
  the shape of `lem:record:prefix-conductor`:
  `|Λ(Y)| ≤ c ‖Y_v‖₂ ∏_{w≠v} ‖Y_w‖₁₄₂` (`hpc`).

Hölder's inequality with the exponents `2` and `142` (71 times) on the probability space
of `(ω, z)` with law `P ⊗ |ρ|/‖ρ‖`, `1/2 + 71/142 = 1`, then gives
`|𝔈 - 𝔈̃| ≤ ‖ρ‖ |C| c B₂^{1/2} B^{71/142}`. Here `B₂` bounds the averaged second moments
of `g_v - g̃_v`, and `B` bounds the averaged `142`-th moments of `g_w` and of `g̃_w`.

* `abs_structuredEnergy_sub_le`: `|𝔈 - 𝔈̃| ≤ ‖ρ‖ E_{P ⊗ |ρ|/‖ρ‖} |Λ(g) - Λ(g̃)|`.
* `holder_two_142`: the Hölder step for one telescoping term.
* `abs_structuredEnergy_sub_le_of_conductor`: the averaged bound.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.DensityDC

open Sarkozy.Structured

variable {X XE Ω : Type*} [Fintype X] [Fintype XE] [Fintype Ω]

/-- The difference of two structured energies is at most `‖ρ‖` times the average of the
difference of the multilinear averages under `P ⊗ |ρ|/‖ρ‖`. -/
theorem abs_structuredEnergy_sub_le (μS : FiniteLaw (Slot → X)) (P : FiniteLaw Ω)
    (ρ : (Slot → XE) → ℝ) (hρ : 0 < totalVariation ρ) (g gt : Ω → Slot → XE → X → ℝ) :
    |structuredEnergy μS P ρ g - structuredEnergy μS P ρ gt| ≤
      totalVariation ρ * (P.product (variationLaw ρ hρ)).expect (fun p =>
        |multilinearIntegral (signedIntegral μS.weight) (fun v => g p.1 v (p.2 v)) -
          multilinearIntegral (signedIntegral μS.weight) (fun v => gt p.1 v (p.2 v))|) := by
  unfold structuredEnergy
  rw [← P.expect_sub, FiniteLaw.expect_product]
  refine (P.abs_expect_le _).trans ?_
  rw [← P.expect_const_mul]
  apply P.expect_mono
  intro ω
  rw [expect_variationLaw, mul_div_cancel₀ _ hρ.ne', ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  apply sum_congr rfl
  intro z _
  rw [← mul_sub, abs_mul]

/-- The expectation of a finite sum of functions. -/
theorem expect_finset_sum {Θ ι : Type*} [Fintype Θ] (μ : FiniteLaw Θ) (s : Finset ι)
    (f : ι → Θ → ℝ) : μ.expect (∑ i ∈ s, f i) = ∑ i ∈ s, μ.expect (f i) := by
  unfold FiniteLaw.expect
  simp only [Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- `1/2 + 71/142 = 1` for the exponents `2` at `v` and `142` elsewhere. -/
theorem sum_inv_exponents (v : Slot) :
    ∑ w : Slot, 1 / (if w = v then (2 : ℝ) else 142) = 1 := by
  have h : ∀ w : Slot, 1 / (if w = v then (2 : ℝ) else 142) =
      1 / 142 + (if w = v then (1 / 2 - 1 / 142 : ℝ) else 0) := by
    intro w
    by_cases hw : w = v
    · rw [ite_eq_left hw, ite_eq_left hw]
      ring
    · rw [ite_eq_right hw, ite_eq_right hw]
      ring
  simp_rw [h]
  rw [sum_add_distrib, sum_const, card_univ, card_slot, Fintype.sum_ite_eq']
  norm_num

/-- **The Hölder step** for one telescoping term: with `F_v = ‖Y_v‖₂` and `F_w = ‖Y_w‖₁₄₂`
(`w ≠ v`), `E[F_v ∏_{w≠v} F_w] ≤ (E ‖Y_v‖₂²)^{1/2} ∏_{w≠v} (E ‖Y_w‖₁₄₂^{142})^{1/142}`. -/
theorem holder_two_142 {Θ : Type*} [Fintype Θ] (Jt : FiniteLaw Θ) (U : FiniteLaw X)
    (Y : Θ → Slot → X → ℝ) (v : Slot) :
    Jt.expect (fun p => U.lpNorm 2 (Y p v) * ∏ w : {w // w ≠ v}, U.lpNorm 142 (Y p w)) ≤
      (Jt.expect (fun p => U.moment 2 (Y p v))) ^ ((1 : ℝ) / 2) *
        ∏ w : {w // w ≠ v}, (Jt.expect (fun p => U.moment 142 (Y p w))) ^ ((1 : ℝ) / 142) := by
  set pexp : Slot → ℝ := fun w => if w = v then 2 else 142 with hpexp
  set F : Slot → Θ → ℝ := fun w p => U.lpNorm (pexp w) (Y p w) with hF
  have hprod : ∀ p, U.lpNorm 2 (Y p v) * ∏ w : {w // w ≠ v}, U.lpNorm 142 (Y p w) =
      ∏ w, F w p := by
    intro p
    rw [Fintype.prod_eq_mul_prod_subtype_ne (fun w => F w p) v]
    simp only [hF, hpexp]
    congr 1
    apply prod_congr rfl
    intro w _
    rw [ite_eq_right w.2]
  have hpos : ∀ w, 0 < pexp w := by
    intro w
    simp only [hpexp]
    split_ifs <;> norm_num
  have hH := Jt.abs_expect_prod_le_lpNorm pexp hpos (sum_inv_exponents v) F
  have hnorm : ∀ w, Jt.lpNorm (pexp w) (F w) =
      (Jt.expect (fun p => U.moment (pexp w) (Y p w))) ^ (1 / pexp w) := by
    intro w
    unfold FiniteLaw.lpNorm FiniteLaw.moment
    congr 1
    apply Jt.expect_congr
    intro p
    rw [abs_of_nonneg (U.lpNorm_nonneg _ _)]
    exact U.lpNorm_rpow (hpos w).ne' (Y p w)
  calc Jt.expect (fun p => U.lpNorm 2 (Y p v) * ∏ w : {w // w ≠ v}, U.lpNorm 142 (Y p w))
      = Jt.expect (fun p => ∏ w, F w p) := Jt.expect_congr hprod
    _ ≤ |Jt.expect (fun p => ∏ w, F w p)| := le_abs_self _
    _ ≤ ∏ w, Jt.lpNorm (pexp w) (F w) := hH
    _ = (Jt.expect (fun p => U.moment 2 (Y p v))) ^ ((1 : ℝ) / 2) *
        ∏ w : {w // w ≠ v}, (Jt.expect (fun p => U.moment 142 (Y p w))) ^ ((1 : ℝ) / 142) := by
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ v, hnorm v]
      simp only [hpexp, ite_eq_left rfl]
      congr 1
      apply prod_congr rfl
      intro w _
      rw [hnorm w]
      simp only [hpexp, ite_eq_right w.2]

/-- **`lem:record:density-dc`, Steps 1 and 2, abstract form.** Suppose:
* `g` and `g̃` agree outside the changed slots `C`;
* every telescoping term satisfies the per-sample bound
  `|Λ(Y)| ≤ c ‖Y_v‖₂ ∏_{w≠v} ‖Y_w‖₁₄₂` (norms for a law `U` on the labels,
  `lem:record:prefix-conductor`);
* the averaged moments satisfy `E ‖g_v - g̃_v‖₂² ≤ B₂` at the changed slots, and
  `E ‖g_w‖₁₄₂^{142} ≤ B`, `E ‖g̃_w‖₁₄₂^{142} ≤ B` at every slot.

Then `|𝔈 - 𝔈̃| ≤ ‖ρ‖ · |C| · c · B₂^{1/2} B^{71/142}`. -/
theorem abs_structuredEnergy_sub_le_of_conductor (μS : FiniteLaw (Slot → X)) (U : FiniteLaw X)
    (P : FiniteLaw Ω) (ρ : (Slot → XE) → ℝ) (g gt : Ω → Slot → XE → X → ℝ) (C : Finset Slot)
    (hunch : ∀ w, w ∉ C → ∀ ω x, g ω w x = gt ω w x) {c B2 B : ℝ} (hc : 0 ≤ c)
    (hB2 : 0 ≤ B2) (hB : 0 ≤ B)
    (hpc : ∀ ω (z : Slot → XE) v, v ∈ C → ∀ T : Finset Slot, v ∉ T →
      |multilinearIntegral (signedIntegral μS.weight)
          (hybrid (fun w => g ω w (z w)) (fun w => gt ω w (z w)) v T)| ≤
        c * U.lpNorm 2 (hybrid (fun w => g ω w (z w)) (fun w => gt ω w (z w)) v T v) *
          ∏ w : {w // w ≠ v},
            U.lpNorm 142 (hybrid (fun w => g ω w (z w)) (fun w => gt ω w (z w)) v T w))
    (hm2 : ∀ hρ : 0 < totalVariation ρ, ∀ v, v ∈ C →
      (P.product (variationLaw ρ hρ)).expect
        (fun p => U.moment 2 (fun y => g p.1 v (p.2 v) y - gt p.1 v (p.2 v) y)) ≤ B2)
    (hmg : ∀ hρ : 0 < totalVariation ρ, ∀ w,
      (P.product (variationLaw ρ hρ)).expect (fun p => U.moment 142 (g p.1 w (p.2 w))) ≤ B)
    (hmgt : ∀ hρ : 0 < totalVariation ρ, ∀ w,
      (P.product (variationLaw ρ hρ)).expect (fun p => U.moment 142 (gt p.1 w (p.2 w))) ≤ B) :
    |structuredEnergy μS P ρ g - structuredEnergy μS P ρ gt| ≤
      totalVariation ρ * ((C.card : ℝ) * (c * (B2 ^ ((1 : ℝ) / 2) * B ^ ((71 : ℝ) / 142)))) := by
  have hK : 0 ≤ (C.card : ℝ) * (c * (B2 ^ ((1 : ℝ) / 2) * B ^ ((71 : ℝ) / 142))) := by
    have h1 : 0 ≤ B2 ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hB2 _
    have h2 : 0 ≤ B ^ ((71 : ℝ) / 142) := Real.rpow_nonneg hB _
    positivity
  rcases (totalVariation_nonneg ρ).lt_or_eq with hρ | hρ0
  · obtain ⟨T, hT, htel⟩ := multilinear_sub_eq_sum_hybrid (signedIntegral μS.weight) C
    set Jt := P.product (variationLaw ρ hρ) with hJt
    refine (abs_structuredEnergy_sub_le μS P ρ hρ g gt).trans ?_
    apply mul_le_mul_of_nonneg_left _ (totalVariation_nonneg ρ)
    -- the telescoping terms
    set Yh : Slot → (Ω × (Slot → XE)) → Slot → X → ℝ := fun v p =>
      hybrid (fun w => g p.1 w (p.2 w)) (fun w => gt p.1 w (p.2 w)) v (T v) with hYh
    have hpoint : ∀ p : Ω × (Slot → XE),
        |multilinearIntegral (signedIntegral μS.weight) (fun v => g p.1 v (p.2 v)) -
          multilinearIntegral (signedIntegral μS.weight) (fun v => gt p.1 v (p.2 v))| ≤
        ∑ v ∈ C, c * (U.lpNorm 2 (Yh v p v) * ∏ w : {w // w ≠ v}, U.lpNorm 142 (Yh v p w)) := by
      intro p
      rw [htel _ _ (fun w hw => hunch w hw p.1 (p.2 w))]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v hv => ?_)
      rw [← mul_assoc]
      exact hpc p.1 p.2 v hv (T v) (hT v)
    refine (Jt.expect_mono hpoint).trans ?_
    rw [show (fun p : Ω × (Slot → XE) => ∑ v ∈ C, c * (U.lpNorm 2 (Yh v p v) *
        ∏ w : {w // w ≠ v}, U.lpNorm 142 (Yh v p w))) =
        ∑ v ∈ C, fun p => c * (U.lpNorm 2 (Yh v p v) *
          ∏ w : {w // w ≠ v}, U.lpNorm 142 (Yh v p w)) from by
      funext p
      rw [Finset.sum_apply]]
    rw [expect_finset_sum]
    rw [show (C.card : ℝ) * (c * (B2 ^ ((1 : ℝ) / 2) * B ^ ((71 : ℝ) / 142))) =
        ∑ _v ∈ C, c * (B2 ^ ((1 : ℝ) / 2) * B ^ ((71 : ℝ) / 142)) from by
      rw [sum_const, nsmul_eq_mul]]
    apply sum_le_sum
    intro v hv
    rw [Jt.expect_const_mul]
    apply mul_le_mul_of_nonneg_left _ hc
    refine (holder_two_142 Jt U (fun p => Yh v p) v).trans ?_
    -- the moments
    have hYv : ∀ p, Yh v p v = fun y => g p.1 v (p.2 v) y - gt p.1 v (p.2 v) y := by
      intro p
      simp only [hYh]
      rw [hybrid_self]
      rfl
    have hm2' : Jt.expect (fun p => U.moment 2 (Yh v p v)) ≤ B2 := by
      simp_rw [hYv]
      exact hm2 hρ v hv
    have hmw : ∀ w : {w // w ≠ v}, Jt.expect (fun p => U.moment 142 (Yh v p w)) ≤ B := by
      intro w
      have hYw : ∀ p, Yh v p w =
          if (w : Slot) ∈ T v then gt p.1 w (p.2 w) else g p.1 w (p.2 w) := by
        intro p
        simp only [hYh]
        rw [hybrid_ne _ _ _ w.2]
      simp_rw [hYw]
      by_cases hwT : (w : Slot) ∈ T v
      · simp_rw [ite_eq_left hwT]
        exact hmgt hρ w
      · simp_rw [ite_eq_right hwT]
        exact hmg hρ w
    have h1 : (Jt.expect (fun p => U.moment 2 (Yh v p v))) ^ ((1 : ℝ) / 2) ≤
        B2 ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (Jt.expect_nonneg fun _ => U.moment_nonneg _ _) hm2' (by norm_num)
    have h2 : ∏ w : {w // w ≠ v}, (Jt.expect (fun p => U.moment 142 (Yh v p w))) ^
        ((1 : ℝ) / 142) ≤ ∏ _w : {w // w ≠ v}, B ^ ((1 : ℝ) / 142) := by
      apply prod_le_prod₀
      · intro w _
        exact Real.rpow_nonneg (Jt.expect_nonneg fun _ => U.moment_nonneg _ _) _
      · intro w _
        exact Real.rpow_le_rpow (Jt.expect_nonneg fun _ => U.moment_nonneg _ _) (hmw w)
          (by norm_num)
    have hcard : Fintype.card {w : Slot // w ≠ v} = 71 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, card_slot]
    have h3 : ∏ _w : {w // w ≠ v}, B ^ ((1 : ℝ) / 142) = B ^ ((71 : ℝ) / 142) := by
      rw [prod_const, card_univ, hcard, ← Real.rpow_natCast, ← Real.rpow_mul hB]
      norm_num
    rw [h3] at h2
    exact mul_le_mul h1 h2 (prod_nonneg fun w _ =>
      Real.rpow_nonneg (Jt.expect_nonneg fun _ => U.moment_nonneg _ _) _)
      (Real.rpow_nonneg hB2 _)
  · rw [structuredEnergy_eq_zero_of_totalVariation μS P ρ hρ0.symm g,
      structuredEnergy_eq_zero_of_totalVariation μS P ρ hρ0.symm gt, sub_zero, abs_zero,
      ← hρ0, zero_mul]

end Sarkozy.DensityDC
