module

public import Sarkozy.Cuts.Tilt
public import Sarkozy.Peyre.Basic
public import Sarkozy.ProbabilityConstructions

/-!
# Cuts, V: kernels depending on few coordinates (`lem:record:projection` (a))

`13_cuts_correlations.tex`, `subsec:cuts:projection`. A law `ν` on `Ω` and two maps
`p_I : Ω → A`, `p_J : Ω → B` (the coordinate projections `x ↦ x_I`, `y ↦ y_J`). A kernel
`κ(x_I, y_J)` depends only on these coordinates. `ν_I = ν ∘ p_I⁻¹` and `ν_J` are the image laws
(`FiniteLaw.map`).

* `projection_norm_iff`: the norm of `κ` on `L²(ν)`, relative to `ν ⊗ ν`, equals its norm from
  `L²(ν_J)` to `L²(ν_I)`. Norms are stated as bounds on forms.
* `kernelForm_density_le`: if `ν_I`, `ν_J` have densities at most `ϱ_I`, `ϱ_J` relative to
  reference laws `υ_I`, `υ_J`, the norm grows by at most `(ϱ_I ϱ_J)^{1/2}`.
* `projection_density`: the two combined.
* `density_norm_le`: the "in particular" clause. A law of density at most `H` relative to a
  reference law gives norms at most `H` times the reference norms.

The paper takes `υ` uniform; here the reference laws are arbitrary. Full support is not needed.
Part (b), the explicit density constants for `ν_F` and `ν_E`, is not formalized.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering Sarkozy.Peyre

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem expect_map' (ν : FiniteLaw Ω) (p : Ω → A) (φ : A → ℝ) :
    (ν.map p).expect φ = ν.expect (fun x => φ (p x)) :=
  FiniteLaw.expect_map ν p φ

/-- The form of `κ` relative to the image laws equals the form of the pulled-back kernel
on pulled-back functions. -/
theorem kernelForm_map (ν : FiniteLaw Ω) (pI : Ω → A) (pJ : Ω → B) (κ : A → B → ℝ)
    (φ : A → ℝ) (ψ : B → ℝ) :
    kernelForm (ν.map pI) (ν.map pJ) κ φ ψ =
      kernelForm ν ν (fun x y => κ (pI x) (pJ y)) (fun x => φ (pI x)) (fun y => ψ (pJ y)) := by
  rw [kernelForm_apply, kernelForm_apply, expect_map']
  refine ν.expect_congr (fun x => ?_)
  rw [expect_map' ν pJ (fun b => κ (pI x) b * ψ b)]

theorem nrm_map (ν : FiniteLaw Ω) (p : Ω → A) (φ : A → ℝ) :
    nrm (ν.map p) φ = nrm ν (fun x => φ (p x)) := by
  unfold nrm ip
  rw [expect_map' ν p (fun a => φ a * φ a)]

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
/-- The form of a kernel depending on `(x_I, y_J)` only sees `E[f | x_I]` and `E[h | y_J]`. -/
theorem kernelForm_condExp (ν : FiniteLaw Ω) (pI : Ω → A) (pJ : Ω → B) (κ : A → B → ℝ)
    (f h : Ω → ℝ) :
    kernelForm ν ν (fun x y => κ (pI x) (pJ y)) f h =
      kernelForm ν ν (fun x y => κ (pI x) (pJ y)) (condExp ν pI f) (condExp ν pJ h) := by
  rw [kernelForm_apply, kernelForm_apply]
  have hin : ∀ x, ν.expect (fun y => κ (pI x) (pJ y) * h y) =
      ν.expect (fun y => κ (pI x) (pJ y) * condExp ν pJ h y) := fun x =>
    (expect_mul_condExp ν pJ h (fun y => κ (pI x) (pJ y)) (isFunOf_comp pJ (κ (pI x)))).symm
  simp only [hin]
  have hF : IsFunOf pI (fun x => ν.expect (fun y => κ (pI x) (pJ y) * condExp ν pJ h y)) := by
    intro x x' hx
    simp only [hx]
  exact (expect_condExp_mul ν pI f _ hF).symm

/-- **`lem:record:projection` (a), first claim.** For a kernel `κ(x_I, y_J)`, a bound `c` for
its form on `L²(ν_I) × L²(ν_J)` is the same as a bound `c` for its form on `L²(ν) × L²(ν)`. -/
theorem projection_norm_iff (ν : FiniteLaw Ω) (pI : Ω → A) (pJ : Ω → B) (κ : A → B → ℝ)
    (c : ℝ) :
    (∀ φ ψ, |kernelForm (ν.map pI) (ν.map pJ) κ φ ψ| ≤ c * nrm (ν.map pI) φ * nrm (ν.map pJ) ψ) ↔
      (∀ f h, |kernelForm ν ν (fun x y => κ (pI x) (pJ y)) f h| ≤ c * nrm ν f * nrm ν h) := by
  constructor
  · intro hb f h
    obtain ⟨F, hF⟩ := exists_fun_of_isFunOf pI (condExp ν pI f) (condExp_isFunOf ν pI f)
    obtain ⟨H, hH⟩ := exists_fun_of_isFunOf pJ (condExp ν pJ h) (condExp_isFunOf ν pJ h)
    have eF : condExp ν pI f = fun x => F (pI x) := funext hF
    have eH : condExp ν pJ h = fun y => H (pJ y) := funext hH
    have hc : 0 ≤ c ∨ c < 0 := le_or_gt 0 c
    have key := hb F H
    rw [kernelForm_map, nrm_map, nrm_map, ← eF, ← eH, ← kernelForm_condExp] at key
    have hnF : nrm ν (condExp ν pI f) ≤ nrm ν f := by
      unfold nrm ip
      apply Real.sqrt_le_sqrt
      have := expect_sq_condExp_le ν pI f
      have e1 : ν.expect (fun x => condExp ν pI f x * condExp ν pI f x) =
          ν.expect (fun x => condExp ν pI f x ^ 2) := ν.expect_congr (fun x => by ring)
      have e2 : ν.expect (fun x => f x * f x) = ν.expect (fun x => f x ^ 2) :=
        ν.expect_congr (fun x => by ring)
      rw [e1, e2]
      exact this
    have hnH : nrm ν (condExp ν pJ h) ≤ nrm ν h := by
      unfold nrm ip
      apply Real.sqrt_le_sqrt
      have := expect_sq_condExp_le ν pJ h
      have e1 : ν.expect (fun x => condExp ν pJ h x * condExp ν pJ h x) =
          ν.expect (fun x => condExp ν pJ h x ^ 2) := ν.expect_congr (fun x => by ring)
      have e2 : ν.expect (fun x => h x * h x) = ν.expect (fun x => h x ^ 2) :=
        ν.expect_congr (fun x => by ring)
      rw [e1, e2]
      exact this
    rcases hc with hc | hc
    · exact key.trans (mul_le_mul (mul_le_mul_of_nonneg_left hnF hc) hnH (nrm_nonneg _ _)
        (mul_nonneg hc (nrm_nonneg _ _)))
    · -- a negative bound is impossible: test it on the constants
      exfalso
      have h1 := hb (fun _ => 1) (fun _ => 1)
      rw [nrm_one, nrm_one, mul_one, mul_one] at h1
      linarith [abs_nonneg (kernelForm (ν.map pI) (ν.map pJ) κ (fun _ => 1) (fun _ => 1))]
  · intro hb φ ψ
    rw [kernelForm_map, nrm_map, nrm_map]
    exact hb _ _

omit [DecidableEq A] [DecidableEq B] in
/-- **`lem:record:projection` (a), density comparison.** If `ν_I = ψ_I υ_I` and
`ν_J = ψ_J υ_J` with `0 ≤ ψ ≤ ϱ`, a bound `c ≥ 0` for the form of `κ` on
`L²(υ_I) × L²(υ_J)` gives the bound `c (ϱ_I ϱ_J)^{1/2}` on `L²(ν_I) × L²(ν_J)`. -/
theorem kernelForm_density_le (νI υI : FiniteLaw A) (νJ υJ : FiniteLaw B) (κ : A → B → ℝ)
    {ψI : A → ℝ} {ψJ : B → ℝ} {ϱI ϱJ c : ℝ} (hc : 0 ≤ c)
    (hdI : ∀ a, νI.weight a = ψI a * υI.weight a) (hdJ : ∀ b, νJ.weight b = ψJ b * υJ.weight b)
    (hψI0 : ∀ a, 0 ≤ ψI a) (hψJ0 : ∀ b, 0 ≤ ψJ b) (hψI : ∀ a, ψI a ≤ ϱI)
    (hψJ : ∀ b, ψJ b ≤ ϱJ)
    (hb : ∀ φ ψ, |kernelForm υI υJ κ φ ψ| ≤ c * nrm υI φ * nrm υJ ψ) (φ : A → ℝ) (ψ : B → ℝ) :
    |kernelForm νI νJ κ φ ψ| ≤ c * √(ϱI * ϱJ) * nrm νI φ * nrm νJ ψ := by
  have e : kernelForm νI νJ κ φ ψ =
      kernelForm υI υJ κ (fun a => ψI a * φ a) (fun b => ψJ b * ψ b) := by
    simp only [kernelForm, LinearMap.mk₂_apply, hdI, hdJ]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  have hnI : nrm υI (fun a => ψI a * φ a) ≤ √ϱI * nrm νI φ := by
    unfold nrm ip
    rw [← Real.sqrt_mul' _ (νI.expect_nonneg (fun a => mul_self_nonneg _))]
    apply Real.sqrt_le_sqrt
    simp only [FiniteLaw.expect, hdI, Finset.mul_sum]
    refine Finset.sum_le_sum (fun a _ => ?_)
    have h1 := hψI0 a
    have h2 := hψI a
    have h3 := υI.nonneg a
    have : ψI a * ψI a ≤ ϱI * ψI a := mul_le_mul_of_nonneg_right h2 h1
    nlinarith [mul_nonneg h3 (mul_self_nonneg (φ a)), mul_le_mul_of_nonneg_left this
      (mul_nonneg h3 (mul_self_nonneg (φ a)))]
  have hnJ : nrm υJ (fun b => ψJ b * ψ b) ≤ √ϱJ * nrm νJ ψ := by
    unfold nrm ip
    rw [← Real.sqrt_mul' _ (νJ.expect_nonneg (fun b => mul_self_nonneg _))]
    apply Real.sqrt_le_sqrt
    simp only [FiniteLaw.expect, hdJ, Finset.mul_sum]
    refine Finset.sum_le_sum (fun b _ => ?_)
    have h1 := hψJ0 b
    have h2 := hψJ b
    have h3 := υJ.nonneg b
    have : ψJ b * ψJ b ≤ ϱJ * ψJ b := mul_le_mul_of_nonneg_right h2 h1
    nlinarith [mul_nonneg h3 (mul_self_nonneg (ψ b)), mul_le_mul_of_nonneg_left this
      (mul_nonneg h3 (mul_self_nonneg (ψ b)))]
  rw [e]
  have hϱI : 0 ≤ ϱI := by
    obtain ⟨a⟩ : Nonempty A := by
      by_contra hA
      have : IsEmpty A := not_nonempty_iff.mp hA
      exact absurd νI.total (by simp)
    exact (hψI0 a).trans (hψI a)
  calc |kernelForm υI υJ κ (fun a => ψI a * φ a) (fun b => ψJ b * ψ b)|
      ≤ c * nrm υI (fun a => ψI a * φ a) * nrm υJ (fun b => ψJ b * ψ b) := hb _ _
    _ ≤ c * (√ϱI * nrm νI φ) * (√ϱJ * nrm νJ ψ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hnI hc) hnJ (nrm_nonneg _ _)
          (mul_nonneg hc (mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _ _)))
    _ = c * √(ϱI * ϱJ) * nrm νI φ * nrm νJ ψ := by
        rw [Real.sqrt_mul hϱI]
        ring

/-- **`lem:record:projection` (a), combined.** With `ν_I`, `ν_J` of densities at most `ϱ_I`,
`ϱ_J` relative to `υ_I`, `υ_J`, the kernel `κ(x_I, y_J)` has norm on `L²(ν)` at most
`(ϱ_I ϱ_J)^{1/2}` times the norm of `κ` from `L²(υ_J)` to `L²(υ_I)`. -/
theorem projection_density (ν : FiniteLaw Ω) (pI : Ω → A) (pJ : Ω → B) (κ : A → B → ℝ)
    (υI : FiniteLaw A) (υJ : FiniteLaw B) {ψI : A → ℝ} {ψJ : B → ℝ} {ϱI ϱJ c : ℝ} (hc : 0 ≤ c)
    (hdI : ∀ a, (ν.map pI).weight a = ψI a * υI.weight a)
    (hdJ : ∀ b, (ν.map pJ).weight b = ψJ b * υJ.weight b)
    (hψI0 : ∀ a, 0 ≤ ψI a) (hψJ0 : ∀ b, 0 ≤ ψJ b) (hψI : ∀ a, ψI a ≤ ϱI)
    (hψJ : ∀ b, ψJ b ≤ ϱJ)
    (hb : ∀ φ ψ, |kernelForm υI υJ κ φ ψ| ≤ c * nrm υI φ * nrm υJ ψ) (f h : Ω → ℝ) :
    |kernelForm ν ν (fun x y => κ (pI x) (pJ y)) f h| ≤ c * √(ϱI * ϱJ) * nrm ν f * nrm ν h :=
  (projection_norm_iff ν pI pJ κ (c * √(ϱI * ϱJ))).1
    (kernelForm_density_le (ν.map pI) υI (ν.map pJ) υJ κ hc hdI hdJ hψI0 hψJ0 hψI hψJ hb) f h

/-- **`lem:record:projection` (a), "in particular".** If `λ = ψ υ` with `0 ≤ ψ ≤ H`, every
kernel has norm on `L²(λ)` at most `H` times its norm on `L²(υ)`. -/
theorem density_norm_le (lam υ : FiniteLaw Ω) (κ : Ω → Ω → ℝ) {ψ : Ω → ℝ} {H c : ℝ}
    (hc : 0 ≤ c) (hd : ∀ x, lam.weight x = ψ x * υ.weight x) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψ : ∀ x, ψ x ≤ H) (hb : ∀ f h, |kernelForm υ υ κ f h| ≤ c * nrm υ f * nrm υ h)
    (f h : Ω → ℝ) : |kernelForm lam lam κ f h| ≤ c * H * nrm lam f * nrm lam h := by
  have hH : 0 ≤ H := by
    obtain ⟨x⟩ : Nonempty Ω := by
      by_contra hΩ
      have : IsEmpty Ω := not_nonempty_iff.mp hΩ
      exact absurd lam.total (by simp)
    exact (hψ0 x).trans (hψ x)
  have := kernelForm_density_le lam υ lam υ κ hc hd hd hψ0 hψ0 hψ hψ hb f h
  rwa [Real.sqrt_mul_self hH] at this

end Sarkozy.Cuts
