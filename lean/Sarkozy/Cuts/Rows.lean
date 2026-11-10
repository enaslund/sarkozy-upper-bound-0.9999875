module

public import Sarkozy.Cuts.Actual

/-!
# Cuts, II: row comparison (`lem:row-comparison`)

`13_cuts_correlations.tex`, `subsec:cuts:rows`. Here `ν` is a reference law on `X`, and `π` is a
law on `X × X` whose marginals have densities `r_L`, `r_R` relative to `ν`. Its maximal
correlation is `maxCorr π fst snd` (`def:prelim:maxcorr`, `Sarkozy.Peyre.maxCorr`). The operator
`T` with kernel `dπ/d(ν⊗ν)` enters only through its form `⟨f, T h⟩_ν = E_π[f(x) h(y)]`, and
`⟨f, J h⟩_ν = (E_ν f)(E_ν h)`.

* `row_comparison_identity`: (a), both expressions of `⟨f, (T - J)h⟩`.
* `row_comparison_fluct`: (a), the fluctuation bound
  `|⟨f₀, T h₀⟩| ≤ (√(H_L H_R) ρ_π + v_L v_R) ‖f₀‖ ‖h₀‖`.
* `row_comparison_norm`: (a), `‖T - J‖ ≤ √(H_L H_R) ρ_π + v_L min{√H_R, 1 + v_R} + v_R`, and the
  cruder `≤ √(H_L H_R) ρ_π + v_L + v_R + v_L v_R`.
* `row_comparison_scaled`: (b), `‖mT - J‖ ≤ H₀ c + H₀ - 1`.
* `chiSq_le_of_range`: (c), last claim, `‖ρ - 1‖² ≤ (u - 1)(1 - l)` for a density `ρ` with mean
  one and values in `[l, u]`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering Sarkozy.Peyre

variable {X : Type*} [Fintype X]

/-- `π` has marginal densities `r_L`, `r_R` relative to `ν`. -/
structure HasMarginalDensities (ν : FiniteLaw X) (π : FiniteLaw (X × X)) (rL rR : X → ℝ) :
    Prop where
  left : ∀ φ : X → ℝ, π.expect (fun q => φ q.1) = ν.expect (fun x => rL x * φ x)
  right : ∀ φ : X → ℝ, π.expect (fun q => φ q.2) = ν.expect (fun x => rR x * φ x)

/-- `E_π[f(x) h(y)] - E_{π_L}f E_{π_R}h`. -/
noncomputable def covPi (π : FiniteLaw (X × X)) (f h : X → ℝ) : ℝ :=
  π.expect (fun q => f q.1 * h q.2) - π.expect (fun q => f q.1) * π.expect (fun q => h q.2)

/-- **`lem:row-comparison` (a), the identities.** With `a = E_ν f`, `b = E_ν h` and centred
parts `f₀`, `h₀`:
`E_π[f h] - ab = Cov_π(f, h) + (E_{π_L} f - a) E_{π_R} h + a (E_{π_R} h - b)`
`= a ⟨r_R - 1, h₀⟩ + b ⟨r_L - 1, f₀⟩ + E_π[f₀(x) h₀(y)]`. -/
theorem row_comparison_identity (ν : FiniteLaw X) (π : FiniteLaw (X × X)) {rL rR : X → ℝ}
    (hr : HasMarginalDensities ν π rL rR) (f h : X → ℝ) :
    (π.expect (fun q => f q.1 * h q.2) - ν.expect f * ν.expect h =
        covPi π f h + (π.expect (fun q => f q.1) - ν.expect f) * π.expect (fun q => h q.2) +
          ν.expect f * (π.expect (fun q => h q.2) - ν.expect h)) ∧
      (π.expect (fun q => f q.1 * h q.2) - ν.expect f * ν.expect h =
        ν.expect f * ip ν (fun x => rR x - 1) (center ν h) +
          ν.expect h * ip ν (fun x => rL x - 1) (center ν f) +
          π.expect (fun q => center ν f q.1 * center ν h q.2)) := by
  constructor
  · unfold covPi
    ring
  · set a := ν.expect f
    set b := ν.expect h
    have hf : ∀ x, f x = center ν f x + a := fun x => by simp only [center, a]; ring
    have hh : ∀ x, h x = center ν h x + b := fun x => by simp only [center, b]; ring
    have e1 : π.expect (fun q => f q.1 * h q.2) =
        π.expect (fun q => center ν f q.1 * center ν h q.2) +
          b * π.expect (fun q => center ν f q.1) + a * π.expect (fun q => center ν h q.2) +
          a * b := by
      have : (fun q : X × X => f q.1 * h q.2) = fun q => (center ν f q.1 * center ν h q.2 +
          b * center ν f q.1 + a * center ν h q.2) + a * b := by
        funext q
        rw [hf q.1, hh q.2]
        ring
      rw [this, FiniteLaw.expect_add, FiniteLaw.expect_add, FiniteLaw.expect_add,
        FiniteLaw.expect_const_mul, FiniteLaw.expect_const_mul, FiniteLaw.expect_const]
    have eL : π.expect (fun q => center ν f q.1) = ip ν (fun x => rL x - 1) (center ν f) := by
      rw [hr.left]
      unfold ip
      have h0 := expect_center ν f
      have : ν.expect (fun x => (rL x - 1) * center ν f x) =
          ν.expect (fun x => rL x * center ν f x) - ν.expect (center ν f) := by
        rw [← FiniteLaw.expect_sub]
        exact ν.expect_congr (fun x => by ring)
      rw [this, h0, sub_zero]
    have eR : π.expect (fun q => center ν h q.2) = ip ν (fun x => rR x - 1) (center ν h) := by
      rw [hr.right]
      unfold ip
      have h0 := expect_center ν h
      have : ν.expect (fun x => (rR x - 1) * center ν h x) =
          ν.expect (fun x => rR x * center ν h x) - ν.expect (center ν h) := by
        rw [← FiniteLaw.expect_sub]
        exact ν.expect_congr (fun x => by ring)
      rw [this, h0, sub_zero]
    rw [e1, eL, eR]
    ring

theorem expect_sq_le_of_density_le (ν : FiniteLaw X) {r : X → ℝ} {H : ℝ}
    (hrH : ∀ x, r x ≤ H) (f : X → ℝ) :
    ν.expect (fun x => r x * f x ^ 2) ≤ H * ν.expect (fun x => f x ^ 2) := by
  rw [← FiniteLaw.expect_const_mul]
  exact ν.expect_mono (fun x => mul_le_mul_of_nonneg_right (hrH x) (sq_nonneg _))

/-- `|Cov_π(f, h)| ≤ ρ_π ‖f‖_{π_L} ‖h‖_{π_R} ≤ ρ_π √(H_L H_R) ‖f‖_ν ‖h‖_ν`. -/
theorem abs_covPi_le (ν : FiniteLaw X) (π : FiniteLaw (X × X)) {rL rR : X → ℝ}
    (hr : HasMarginalDensities ν π rL rR) {HL HR ρπ : ℝ} (hρ : maxCorr π Prod.fst Prod.snd ≤ ρπ)
    (hρ0 : 0 ≤ ρπ) (hL0 : ∀ x, 0 ≤ rL x) (hR0 : ∀ x, 0 ≤ rR x) (hHL : ∀ x, rL x ≤ HL)
    (hHR : ∀ x, rR x ≤ HR) (f h : X → ℝ) :
    |covPi π f h| ≤ ρπ * √(HL * HR) * nrm ν f * nrm ν h := by
  have hcorr := corrLe_of_maxCorr_le hρ
  set cf := π.expect (fun q => f q.1)
  set ch := π.expect (fun q => h q.2)
  have hc := hcorr (fun x => f x - cf) (fun y => h y - ch)
    (by rw [FiniteLaw.expect_sub, FiniteLaw.expect_const, sub_self])
    (by rw [FiniteLaw.expect_sub, FiniteLaw.expect_const, sub_self])
  have ecov : covPi π f h = π.expect (fun q => (f q.1 - cf) * (h q.2 - ch)) := by
    unfold covPi
    have : π.expect (fun q => (f q.1 - cf) * (h q.2 - ch)) =
        π.expect (fun q => f q.1 * h q.2) - cf * π.expect (fun q => h q.2) -
          ch * π.expect (fun q => f q.1) + cf * ch := by
      have e : (fun q : X × X => (f q.1 - cf) * (h q.2 - ch)) =
          fun q => (f q.1 * h q.2 - cf * h q.2 - ch * f q.1) + cf * ch := by
        funext q; ring
      rw [e, FiniteLaw.expect_add, FiniteLaw.expect_sub, FiniteLaw.expect_sub,
        FiniteLaw.expect_const_mul, FiniteLaw.expect_const_mul, FiniteLaw.expect_const]
    rw [this]
    ring
  rw [ecov]
  have hvf : π.expect (fun q => (f q.1 - cf) ^ 2) ≤ HL * nrm ν f ^ 2 := by
    have h1 : π.expect (fun q => (f q.1 - cf) ^ 2) ≤ π.expect (fun q => f q.1 ^ 2) := by
      rw [FiniteLaw.expect_sq_sub_mean π (fun q => f q.1)]
      nlinarith [sq_nonneg cf]
    have h2 : π.expect (fun q => f q.1 ^ 2) = ν.expect (fun x => rL x * f x ^ 2) :=
      hr.left (fun x => f x ^ 2)
    have h3 := expect_sq_le_of_density_le ν hHL f
    have h4 : nrm ν f ^ 2 = ν.expect (fun x => f x ^ 2) := by
      unfold nrm ip
      rw [Real.sq_sqrt (ν.expect_nonneg (fun x => mul_self_nonneg _))]
      exact ν.expect_congr (fun x => by ring)
    rw [h4]
    linarith
  have hvh : π.expect (fun q => (h q.2 - ch) ^ 2) ≤ HR * nrm ν h ^ 2 := by
    have h1 : π.expect (fun q => (h q.2 - ch) ^ 2) ≤ π.expect (fun q => h q.2 ^ 2) := by
      rw [FiniteLaw.expect_sq_sub_mean π (fun q => h q.2)]
      nlinarith [sq_nonneg ch]
    have h2 : π.expect (fun q => h q.2 ^ 2) = ν.expect (fun x => rR x * h x ^ 2) :=
      hr.right (fun x => h x ^ 2)
    have h3 := expect_sq_le_of_density_le ν hHR h
    have h4 : nrm ν h ^ 2 = ν.expect (fun x => h x ^ 2) := by
      unfold nrm ip
      rw [Real.sq_sqrt (ν.expect_nonneg (fun x => mul_self_nonneg _))]
      exact ν.expect_congr (fun x => by ring)
    rw [h4]
    linarith
  have hnf0 : 0 ≤ nrm ν f := Real.sqrt_nonneg _
  have hnh0 : 0 ≤ nrm ν h := Real.sqrt_nonneg _
  have hX : Nonempty X := by
    by_contra hX
    have : IsEmpty X := not_nonempty_iff.mp hX
    exact absurd (FiniteLaw.total ν) (by simp)
  obtain ⟨x₀⟩ := hX
  have hHL0 : 0 ≤ HL := le_trans (hL0 x₀) (hHL x₀)
  have hHR0 : 0 ≤ HR := le_trans (hR0 x₀) (hHR x₀)
  calc |π.expect (fun q => (f q.1 - cf) * (h q.2 - ch))|
      ≤ ρπ * √(π.expect (fun q => (f q.1 - cf) ^ 2)) * √(π.expect (fun q => (h q.2 - ch) ^ 2)) :=
        hc
    _ ≤ ρπ * √(HL * nrm ν f ^ 2) * √(HR * nrm ν h ^ 2) := by
        gcongr
    _ = ρπ * √(HL * HR) * nrm ν f * nrm ν h := by
        rw [Real.sqrt_mul hHL0, Real.sqrt_mul hHR0, Real.sqrt_mul hHL0, Real.sqrt_sq hnf0,
          Real.sqrt_sq hnh0]
        ring

/-- `|E_ν f| ≤ ‖f‖_ν`. -/
theorem abs_expect_le_nrm (ν : FiniteLaw X) (f : X → ℝ) : |ν.expect f| ≤ nrm ν f := by
  have h := abs_ip_le ν (fun _ => 1) f
  rw [ip_one_left] at h
  have h1 : nrm ν (fun _ => (1 : ℝ)) = 1 := by
    unfold nrm ip
    simp only [mul_one]
    rw [expect_one, Real.sqrt_one]
  rw [h1, one_mul] at h
  exact h

/-- `‖r‖_ν = √(1 + ‖r - 1‖²_ν)` for a density with `E_ν r = 1`; in particular `‖r‖ ≤ 1 + ‖r - 1‖`. -/
theorem nrm_le_one_add (ν : FiniteLaw X) {r : X → ℝ} (hr : ν.expect r = 1) :
    nrm ν r ≤ 1 + nrm ν (fun x => r x - 1) := by
  have h0 : 0 ≤ nrm ν (fun x => r x - 1) := Real.sqrt_nonneg _
  have hsq : nrm ν r ^ 2 = 1 + nrm ν (fun x => r x - 1) ^ 2 := by
    unfold nrm ip
    rw [Real.sq_sqrt (ν.expect_nonneg (fun x => mul_self_nonneg _)),
      Real.sq_sqrt (ν.expect_nonneg (fun x => mul_self_nonneg _))]
    have : ν.expect (fun x => (r x - 1) * (r x - 1)) =
        ν.expect (fun x => r x * r x) - 2 * ν.expect r + 1 := by
      have e : (fun x => (r x - 1) * (r x - 1)) = fun x => (r x * r x - 2 * r x) + 1 := by
        funext x; ring
      rw [e, FiniteLaw.expect_add, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
        FiniteLaw.expect_const]
    rw [this, hr]
    ring
  have h1 : nrm ν r ^ 2 ≤ (1 + nrm ν (fun x => r x - 1)) ^ 2 := by
    rw [hsq]
    nlinarith
  exact (abs_le_of_sq_le_sq' h1 (by positivity)).2

/-- **`lem:row-comparison` (a), the fluctuation term.**
`|E_π[f₀(x) h₀(y)]| ≤ (√(H_L H_R) ρ_π + v_L v_R) ‖f₀‖ ‖h₀‖` for `ν`-centred `f₀`, `h₀`. -/
theorem row_comparison_fluct (ν : FiniteLaw X) (π : FiniteLaw (X × X)) {rL rR : X → ℝ}
    (hr : HasMarginalDensities ν π rL rR) {HL HR ρπ vL vR : ℝ}
    (hρ : maxCorr π Prod.fst Prod.snd ≤ ρπ) (hρ0 : 0 ≤ ρπ) (hL0 : ∀ x, 0 ≤ rL x)
    (hR0 : ∀ x, 0 ≤ rR x) (hHL : ∀ x, rL x ≤ HL) (hHR : ∀ x, rR x ≤ HR)
    (hvL : nrm ν (fun x => rL x - 1) ≤ vL) (hvR : nrm ν (fun x => rR x - 1) ≤ vR)
    (f h : X → ℝ) (hf : ν.expect f = 0) (hh : ν.expect h = 0) :
    |π.expect (fun q => f q.1 * h q.2)| ≤ (√(HL * HR) * ρπ + vL * vR) * nrm ν f * nrm ν h := by
  have hcov := abs_covPi_le ν π hr hρ hρ0 hL0 hR0 hHL hHR f h
  have eL : π.expect (fun q => f q.1) = ip ν (fun x => rL x - 1) f := by
    rw [hr.left]
    unfold ip
    have : ν.expect (fun x => (rL x - 1) * f x) =
        ν.expect (fun x => rL x * f x) - ν.expect f := by
      rw [← FiniteLaw.expect_sub]
      exact ν.expect_congr (fun x => by ring)
    rw [this, hf, sub_zero]
  have eR : π.expect (fun q => h q.2) = ip ν (fun x => rR x - 1) h := by
    rw [hr.right]
    unfold ip
    have : ν.expect (fun x => (rR x - 1) * h x) =
        ν.expect (fun x => rR x * h x) - ν.expect h := by
      rw [← FiniteLaw.expect_sub]
      exact ν.expect_congr (fun x => by ring)
    rw [this, hh, sub_zero]
  have hvL0 : 0 ≤ vL := le_trans (Real.sqrt_nonneg _) hvL
  have hnf0 : 0 ≤ nrm ν f := Real.sqrt_nonneg _
  have hnh0 : 0 ≤ nrm ν h := Real.sqrt_nonneg _
  have hmL : |π.expect (fun q => f q.1)| ≤ vL * nrm ν f := by
    rw [eL]
    exact (abs_ip_le ν _ _).trans (mul_le_mul_of_nonneg_right hvL hnf0)
  have hmR : |π.expect (fun q => h q.2)| ≤ vR * nrm ν h := by
    rw [eR]
    exact (abs_ip_le ν _ _).trans (mul_le_mul_of_nonneg_right hvR hnh0)
  have e : π.expect (fun q => f q.1 * h q.2) =
      covPi π f h + π.expect (fun q => f q.1) * π.expect (fun q => h q.2) := by
    unfold covPi; ring
  rw [e]
  calc |covPi π f h + π.expect (fun q => f q.1) * π.expect (fun q => h q.2)|
      ≤ |covPi π f h| + |π.expect (fun q => f q.1)| * |π.expect (fun q => h q.2)| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ ρπ * √(HL * HR) * nrm ν f * nrm ν h + vL * nrm ν f * (vR * nrm ν h) :=
        add_le_add hcov (mul_le_mul hmL hmR (abs_nonneg _) (by positivity))
    _ = (√(HL * HR) * ρπ + vL * vR) * nrm ν f * nrm ν h := by ring

/-- **`lem:row-comparison` (a), the norm bound.**
`|⟨f, (T - J)h⟩| ≤ (√(H_L H_R) ρ_π + v_L min{√H_R, 1 + v_R} + v_R) ‖f‖ ‖h‖`. -/
theorem row_comparison_norm (ν : FiniteLaw X) (π : FiniteLaw (X × X)) {rL rR : X → ℝ}
    (hr : HasMarginalDensities ν π rL rR) (hrR1 : ν.expect rR = 1) {HL HR ρπ vL vR : ℝ}
    (hρ : maxCorr π Prod.fst Prod.snd ≤ ρπ) (hρ0 : 0 ≤ ρπ) (hL0 : ∀ x, 0 ≤ rL x)
    (hR0 : ∀ x, 0 ≤ rR x) (hHL : ∀ x, rL x ≤ HL) (hHR : ∀ x, rR x ≤ HR)
    (hvL : nrm ν (fun x => rL x - 1) ≤ vL) (hvR : nrm ν (fun x => rR x - 1) ≤ vR)
    (f h : X → ℝ) :
    |π.expect (fun q => f q.1 * h q.2) - ν.expect f * ν.expect h| ≤
      (√(HL * HR) * ρπ + vL * min (√HR) (1 + vR) + vR) * nrm ν f * nrm ν h := by
  have hid := (row_comparison_identity ν π hr f h).1
  have hcov := abs_covPi_le ν π hr hρ hρ0 hL0 hR0 hHL hHR f h
  have hvL0 : 0 ≤ vL := le_trans (Real.sqrt_nonneg _) hvL
  have hvR0 : 0 ≤ vR := le_trans (Real.sqrt_nonneg _) hvR
  have hnf0 : 0 ≤ nrm ν f := Real.sqrt_nonneg _
  have hnh0 : 0 ≤ nrm ν h := Real.sqrt_nonneg _
  -- `|E_{π_L} f - a| ≤ v_L ‖f‖`
  have h1 : |π.expect (fun q => f q.1) - ν.expect f| ≤ vL * nrm ν f := by
    have e : π.expect (fun q => f q.1) - ν.expect f = ip ν (fun x => rL x - 1) f := by
      rw [hr.left]
      unfold ip
      rw [← FiniteLaw.expect_sub]
      exact ν.expect_congr (fun x => by ring)
    rw [e]
    exact (abs_ip_le ν _ _).trans (mul_le_mul_of_nonneg_right hvL hnf0)
  -- `|E_{π_R} h| ≤ min{√H_R, 1 + v_R} ‖h‖`
  have h2 : |π.expect (fun q => h q.2)| ≤ min (√HR) (1 + vR) * nrm ν h := by
    have hA : |π.expect (fun q => h q.2)| ≤ √HR * nrm ν h := by
      have hc := abs_expect_le_nrm π (fun q => h q.2)
      have hn : nrm π (fun q => h q.2) ≤ √HR * nrm ν h := by
        unfold nrm ip
        have e1 : π.expect (fun q => h q.2 * h q.2) = ν.expect (fun x => rR x * h x ^ 2) := by
          rw [show (fun q : X × X => h q.2 * h q.2) = fun q => h q.2 ^ 2 from by
            funext q; ring]
          exact hr.right (fun x => h x ^ 2)
        rw [e1]
        have hX : Nonempty X := by
          by_contra hX
          have : IsEmpty X := not_nonempty_iff.mp hX
          exact absurd (FiniteLaw.total ν) (by simp)
        obtain ⟨x₀⟩ := hX
        have hHR0 : 0 ≤ HR := le_trans (hR0 x₀) (hHR x₀)
        rw [← Real.sqrt_mul hHR0]
        apply Real.sqrt_le_sqrt
        have := expect_sq_le_of_density_le ν hHR h
        have e2 : ν.expect (fun x => h x * h x) = ν.expect (fun x => h x ^ 2) :=
          ν.expect_congr (fun x => by ring)
        rw [e2]
        exact this
      exact hc.trans hn
    have hB : |π.expect (fun q => h q.2)| ≤ (1 + vR) * nrm ν h := by
      have e : π.expect (fun q => h q.2) = ip ν rR h := by
        rw [hr.right]; rfl
      rw [e]
      exact (abs_ip_le ν _ _).trans (mul_le_mul_of_nonneg_right
        ((nrm_le_one_add ν hrR1).trans (by linarith)) hnh0)
    rcases le_total (√HR) (1 + vR) with hm | hm
    · rw [min_eq_left hm]; exact hA
    · rw [min_eq_right hm]; exact hB
  -- `|a| ≤ ‖f‖` and `|E_{π_R} h - b| ≤ v_R ‖h‖`
  have h3 : |ν.expect f| ≤ nrm ν f := abs_expect_le_nrm ν f
  have h4 : |π.expect (fun q => h q.2) - ν.expect h| ≤ vR * nrm ν h := by
    have e : π.expect (fun q => h q.2) - ν.expect h = ip ν (fun x => rR x - 1) h := by
      rw [hr.right]
      unfold ip
      rw [← FiniteLaw.expect_sub]
      exact ν.expect_congr (fun x => by ring)
    rw [e]
    exact (abs_ip_le ν _ _).trans (mul_le_mul_of_nonneg_right hvR hnh0)
  rw [hid]
  have hmin0 : 0 ≤ min (√HR) (1 + vR) := le_min (Real.sqrt_nonneg _) (by linarith)
  calc |covPi π f h + (π.expect (fun q => f q.1) - ν.expect f) * π.expect (fun q => h q.2) +
        ν.expect f * (π.expect (fun q => h q.2) - ν.expect h)|
      ≤ |covPi π f h| + |π.expect (fun q => f q.1) - ν.expect f| *
          |π.expect (fun q => h q.2)| + |ν.expect f| *
          |π.expect (fun q => h q.2) - ν.expect h| := by
        rw [← abs_mul, ← abs_mul]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ρπ * √(HL * HR) * nrm ν f * nrm ν h + vL * nrm ν f * (min (√HR) (1 + vR) * nrm ν h) +
          nrm ν f * (vR * nrm ν h) := by
        gcongr
    _ = (√(HL * HR) * ρπ + vL * min (√HR) (1 + vR) + vR) * nrm ν f * nrm ν h := by ring

/-- `lem:row-comparison` (a), the cruder form: `‖T - J‖ ≤ √(H_L H_R) ρ_π + v_L + v_R + v_L v_R`. -/
theorem row_comparison_norm' (ν : FiniteLaw X) (π : FiniteLaw (X × X)) {rL rR : X → ℝ}
    (hr : HasMarginalDensities ν π rL rR) (hrR1 : ν.expect rR = 1) {HL HR ρπ vL vR : ℝ}
    (hρ : maxCorr π Prod.fst Prod.snd ≤ ρπ) (hρ0 : 0 ≤ ρπ) (hL0 : ∀ x, 0 ≤ rL x)
    (hR0 : ∀ x, 0 ≤ rR x) (hHL : ∀ x, rL x ≤ HL) (hHR : ∀ x, rR x ≤ HR)
    (hvL : nrm ν (fun x => rL x - 1) ≤ vL) (hvR : nrm ν (fun x => rR x - 1) ≤ vR)
    (f h : X → ℝ) :
    |π.expect (fun q => f q.1 * h q.2) - ν.expect f * ν.expect h| ≤
      (√(HL * HR) * ρπ + vL + vR + vL * vR) * nrm ν f * nrm ν h := by
  have hb := row_comparison_norm ν π hr hrR1 hρ hρ0 hL0 hR0 hHL hHR hvL hvR f h
  have hvL0 : 0 ≤ vL := le_trans (Real.sqrt_nonneg _) hvL
  have hmin : vL * min (√HR) (1 + vR) ≤ vL * (1 + vR) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hvL0
  refine hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_
    (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  linarith

/-- **`lem:row-comparison` (b).** If `‖T - J‖ ≤ c`, `H₀ ≥ 1`, `0 ≤ m ≤ H₀` and
`|m - 1| ≤ H₀ - 1`, then `‖mT - J‖ ≤ H₀ c + H₀ - 1`. -/
theorem row_comparison_scaled (ν : FiniteLaw X) (π : FiniteLaw (X × X)) {c m H₀ : ℝ}
    (hm0 : 0 ≤ m) (hmH : m ≤ H₀) (hm1 : |m - 1| ≤ H₀ - 1)
    (hc : ∀ f h : X → ℝ, |π.expect (fun q => f q.1 * h q.2) - ν.expect f * ν.expect h| ≤
      c * nrm ν f * nrm ν h) (f h : X → ℝ) :
    |m * π.expect (fun q => f q.1 * h q.2) - ν.expect f * ν.expect h| ≤
      (H₀ * c + H₀ - 1) * nrm ν f * nrm ν h := by
  have e : m * π.expect (fun q => f q.1 * h q.2) - ν.expect f * ν.expect h =
      m * (π.expect (fun q => f q.1 * h q.2) - ν.expect f * ν.expect h) +
        (m - 1) * (ν.expect f * ν.expect h) := by ring
  have hnf0 : 0 ≤ nrm ν f := Real.sqrt_nonneg _
  have hnh0 : 0 ≤ nrm ν h := Real.sqrt_nonneg _
  have hab : |ν.expect f * ν.expect h| ≤ nrm ν f * nrm ν h := by
    rw [abs_mul]
    exact mul_le_mul (abs_expect_le_nrm ν f) (abs_expect_le_nrm ν h) (abs_nonneg _) hnf0
  rw [e]
  calc |m * (π.expect (fun q => f q.1 * h q.2) - ν.expect f * ν.expect h) +
        (m - 1) * (ν.expect f * ν.expect h)|
      ≤ m * |π.expect (fun q => f q.1 * h q.2) - ν.expect f * ν.expect h| +
          |m - 1| * |ν.expect f * ν.expect h| := by
        rw [← abs_of_nonneg hm0, ← abs_mul, ← abs_mul, abs_of_nonneg hm0]
        exact abs_add_le _ _
    _ ≤ H₀ * (c * nrm ν f * nrm ν h) + (H₀ - 1) * (nrm ν f * nrm ν h) := by
        have hH0 : 0 ≤ H₀ := le_trans hm0 hmH
        have hH1 : 0 ≤ H₀ - 1 := le_trans (abs_nonneg _) hm1
        exact add_le_add (mul_le_mul hmH (hc f h) (abs_nonneg _) hH0)
          (mul_le_mul hm1 hab (abs_nonneg _) hH1)
    _ = (H₀ * c + H₀ - 1) * nrm ν f * nrm ν h := by ring

/-- **`lem:row-comparison` (c), last claim.** A density `r` with `E_ν r = 1` and values in
`[l, u]` has `‖r - 1‖²_ν ≤ (u - 1)(1 - l)`. -/
theorem chiSq_le_of_range (ν : FiniteLaw X) {r : X → ℝ} {l u : ℝ} (hr : ν.expect r = 1)
    (hl : ∀ x, l ≤ r x) (hu : ∀ x, r x ≤ u) :
    ν.expect (fun x => (r x - 1) ^ 2) ≤ (u - 1) * (1 - l) := by
  have h1 : ν.expect (fun x => r x ^ 2) ≤ (u + l) * ν.expect r - u * l := by
    rw [← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_const (μ := ν) (u * l),
      ← FiniteLaw.expect_sub]
    refine ν.expect_mono (fun x => ?_)
    nlinarith [mul_nonneg (sub_nonneg.mpr (hu x)) (sub_nonneg.mpr (hl x))]
  have e : ν.expect (fun x => (r x - 1) ^ 2) = ν.expect (fun x => r x ^ 2) - 2 * ν.expect r + 1 := by
    have e' : (fun x => (r x - 1) ^ 2) = fun x => (r x ^ 2 - 2 * r x) + 1 := by funext x; ring
    rw [e', FiniteLaw.expect_add, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
      FiniteLaw.expect_const]
  rw [e, hr]
  rw [hr] at h1
  nlinarith

end Sarkozy.Cuts
