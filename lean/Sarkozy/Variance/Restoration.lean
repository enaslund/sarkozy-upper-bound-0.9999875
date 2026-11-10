module

public import Sarkozy.Variance.Interpolation
public import Sarkozy.Variance.Eligible

/-!
# Restoration on a common chamber (`lem:record:restoration`)

`paper/sections/22_variance.tex`, Section 22.3, `lem:record:restoration` and the restoration
function `𝓕(C, h, M, χ)` after it; `hyp:variance:A` is the density hypothesis (A).

**Setting.** The fold chamber `ϑ_{2j}` is a cut `c`; the selected set `X` of blocks is one factor
`j₀` of a product law, with the outside laws `O j` (`j ≠ j₀`, the reference `μ` outside `X`)
positive at `c` (`(R2)`), and `O j₀ = μ_X` the reference on `X`. So `Y = Y_μ` is
`diagonalIntegral (tensorLaw O) F` and `Y[κ] = energyAt O j₀ κ F`.

* (C) The reference on `X` is `μ_X = (1 + h)⁻¹ (Π^rt + 𝓜)` with the root `Π^rt` (a nonnegative
  weight `w`) and the nonroot part `𝓜` of mass `h = ∏(1 + h_𝔅) - 1 ≤ h_X`; (E1) for `𝓜` is the
  hypothesis `Y[𝓜] ≤ (1 + z) h C_X Y`.
* (B) The root couples two copies of the half law `ν` at `c` (both half marginals of `w` are
  `ν`, `lem:record:fold-identification`), and `Π_X = Diag_c(λ)` for the half law `λ` of the
  record (`λ = ⊗ λ_F^{(j)}`). Hypothesis (A): `ν ≤ M λ`.
* The chi-square bound `∑ (ν - λ)²/λ ≤ χ` (with `ν ≪ λ`).
* **The orbit decomposition** of the bounded-variance step: half laws `o z` (the uniform law on
  the translates of `z`) with `ν = ∑_z ν(z) o_z` and `λ = ∑_z λ(z) o_z`, which holds for
  translation-invariant `ν, λ` (`orbit_decomposition`), and (E1) for their diagonal copies,
  `Y[Diag(o_z)] ≤ (1 + z₂) C_X Y`. (E2), (E3) give `Y[Diag(o_z)] ≥ 0` (proved).

**The `o(1)`.** Explicit: with `l = 1 - (C - 1) h_X`, the conclusion holds with
`l' = l - z h_X C` and `C' = (1 + z₂) C` in place of `l` and `C`; at `z = z₂ = 0` it is the
paper's bound `Y[Π_X] ≥ l₀ Y`.

**Main results.**
* `branchVar_le`: the scalar step of the bounded-variance branch: from
  `l ≤ x + (χ x (C - x))^{1/2}`, `0 ≤ x ≤ C`, `l > 0`, the third expression
  `2l²/(2l + Cχ + (χ(4l(C - l) + C²χ))^{1/2})` is at most `x`.
* `restoration`: **`lem:record:restoration`**, in full given (E1) for `𝓜` and for the orbit laws:
  `Y[Π_X] ≥ 0` and `Y[Π_X] ≥ max(l'/M, l' - (C'/2)√χ, branchVar l' C' χ) Y`.
* `restorationF`, `restoration_F`: the function `𝓕(C, h, M, χ)` and the bound
  `Y[Π_X] ≥ 𝓕(C', h_X, M, χ) Y` (at `z = 0`, with `C' = (1 + z₂) C`).
* `orbit_decomposition`: for a finite group acting on the half labels and a `G`-invariant `ν`,
  `ν = ∑_z ν(z) o_z` with `o_z` the uniform law on the orbit map `g ↦ g • z`.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

/-! ### The scalar branches -/

/-- The third (bounded-variance) expression of `l₀` in `lem:record:restoration`:
`2l²/(2l + Cχ + (χ(4l(C - l) + C²χ))^{1/2})`, the smaller root of
`(1 + χ)x² - (2l + Cχ)x + l²`, rationalized. -/
noncomputable def branchVar (l C χ : ℝ) : ℝ :=
  2 * l ^ 2 / (2 * l + C * χ + Real.sqrt (χ * (4 * l * (C - l) + C ^ 2 * χ)))

/-- The restoration bound `l₀ = max(l/M, l - (C/2)√χ, branchVar l C χ)` of
`lem:record:restoration`. -/
noncomputable def restorationL0 (l C M χ : ℝ) : ℝ :=
  max (l / M) (max (l - C / 2 * Real.sqrt χ) (branchVar l C χ))

/-- The restoration function `𝓕(C, h, M, χ)` of Section 22.3: the largest of `0` and the three
expressions of `l₀` formed with `l = 1 - (C - 1)h` if `l > 0`, and `0` if `l ≤ 0`. -/
noncomputable def restorationF (C h M χ : ℝ) : ℝ :=
  if 0 < 1 - (C - 1) * h then max 0 (restorationL0 (1 - (C - 1) * h) C M χ) else 0

theorem restorationF_nonneg (C h M χ : ℝ) : 0 ≤ restorationF C h M χ := by
  unfold restorationF
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

/-- The bounded-variance branch is at most `l` (for `l > 0`, `C, χ ≥ 0`). -/
theorem branchVar_le_l {l C χ : ℝ} (hl : 0 < l) (hC : 0 ≤ C) (hχ : 0 ≤ χ) :
    branchVar l C χ ≤ l := by
  unfold branchVar
  have hs := Real.sqrt_nonneg (χ * (4 * l * (C - l) + C ^ 2 * χ))
  have hd : 0 < 2 * l + C * χ + Real.sqrt (χ * (4 * l * (C - l) + C ^ 2 * χ)) := by
    have := mul_nonneg hC hχ
    linarith
  rw [div_le_iff₀ hd]
  have := mul_nonneg hC hχ
  nlinarith

/-- **The bounded-variance step** of `lem:record:restoration`: if `0 ≤ x ≤ C`, `l > 0`,
`χ ≥ 0` and `l ≤ x + (χ x (C - x))^{1/2}`, then `branchVar l C χ ≤ x`. -/
theorem branchVar_le {l C χ x : ℝ} (hl : 0 < l) (hχ : 0 ≤ χ) (hx0 : 0 ≤ x) (hxC : x ≤ C)
    (h : l ≤ x + Real.sqrt (χ * x * (C - x))) : branchVar l C χ ≤ x := by
  have hC : 0 ≤ C := hx0.trans hxC
  by_cases hxl : l ≤ x
  · exact (branchVar_le_l hl hC hχ).trans hxl
  push Not at hxl
  -- square `l - x ≤ (χ x (C - x))^{1/2}`
  have hin : 0 ≤ χ * x * (C - x) := mul_nonneg (mul_nonneg hχ hx0) (by linarith)
  have hsq : (l - x) ^ 2 ≤ χ * x * (C - x) := by
    have h1 : l - x ≤ Real.sqrt (χ * x * (C - x)) := by linarith
    have h2 : 0 ≤ l - x := by linarith
    calc (l - x) ^ 2 ≤ Real.sqrt (χ * x * (C - x)) ^ 2 := pow_le_pow_left₀ h2 h1 2
      _ = χ * x * (C - x) := Real.sq_sqrt hin
  set a := 1 + χ with ha
  set b := 2 * l + C * χ with hb
  set D := χ * (4 * l * (C - l) + C ^ 2 * χ) with hD
  have hquad : a * x ^ 2 - b * x + l ^ 2 ≤ 0 := by nlinarith
  have hdisc : (2 * a * x - b) ^ 2 ≤ D := by nlinarith
  have hD0 : 0 ≤ D := (sq_nonneg _).trans hdisc
  set s := Real.sqrt D with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = D := Real.mul_self_sqrt hD0
  have hlin : b - 2 * a * x ≤ s := by
    by_contra hcon
    push Not at hcon
    have : s ^ 2 < (b - 2 * a * x) ^ 2 := by
      have := mul_lt_mul'' hcon hcon hs0 hs0
      nlinarith
    nlinarith
  have hbpos : 0 < b + s := by
    have := mul_nonneg hC hχ
    linarith
  unfold branchVar
  rw [← hb, ← hD, ← hs, div_le_iff₀ (by linarith)]
  -- `2a x (b + s) ≥ (b - s)(b + s) = b² - D = 4 a l²`
  have hkey : 2 * a * x * (b + s) ≥ (b - s) * (b + s) := by
    have := mul_le_mul_of_nonneg_right (show b - s ≤ 2 * a * x by linarith) hbpos.le
    linarith
  have hid : (b - s) * (b + s) = 4 * a * l ^ 2 := by
    have : (b - s) * (b + s) = b * b - s * s := by ring
    rw [this, hss, hb, hD, ha]
    ring
  have hapos : 0 < a := by linarith
  nlinarith

/-! ### Finite chi-square tools -/

section ChiTools

variable {S : Type*} [Fintype S]

/-- Cauchy–Schwarz against a chi-square: `∑ (ν - λ) g ≤ (χ ∑ λ g²)^{1/2}` when `ν ≪ λ`, `λ ≥ 0`
and `∑ (ν - λ)²/λ ≤ χ`. -/
theorem sum_sub_mul_le_sqrt {ν lam g : S → ℝ} {χ : ℝ} (hlam : ∀ x, 0 ≤ lam x)
    (hac : ∀ x, lam x = 0 → ν x = 0) (hχ : ∑ x, (ν x - lam x) ^ 2 / lam x ≤ χ) :
    ∑ x, (ν x - lam x) * g x ≤ Real.sqrt (χ * ∑ x, lam x * g x ^ 2) := by
  have hpt : ∀ x, (ν x - lam x) * g x =
      ((ν x - lam x) / Real.sqrt (lam x)) * (Real.sqrt (lam x) * g x) := by
    intro x
    by_cases h0 : lam x = 0
    · simp [h0, hac x h0]
    · have hp : 0 < lam x := lt_of_le_of_ne (hlam x) (Ne.symm h0)
      have hs : Real.sqrt (lam x) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
      field_simp
  have hf2 : ∀ x, ((ν x - lam x) / Real.sqrt (lam x)) ^ 2 = (ν x - lam x) ^ 2 / lam x := by
    intro x
    rw [div_pow, Real.sq_sqrt (hlam x)]
  have hg2 : ∀ x, (Real.sqrt (lam x) * g x) ^ 2 = lam x * g x ^ 2 := by
    intro x
    rw [mul_pow, Real.sq_sqrt (hlam x)]
  simp_rw [hpt]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => (ν x - lam x) / Real.sqrt (lam x)) (fun x => Real.sqrt (lam x) * g x)
  simp only [hf2, hg2] at hcs
  have hB : 0 ≤ ∑ x, lam x * g x ^ 2 := sum_nonneg fun x _ => mul_nonneg (hlam x) (sq_nonneg _)
  have hA : 0 ≤ ∑ x, (ν x - lam x) ^ 2 / lam x :=
    sum_nonneg fun x _ => div_nonneg (sq_nonneg _) (hlam x)
  apply Real.le_sqrt_of_sq_le
  calc (∑ x, (ν x - lam x) / Real.sqrt (lam x) * (Real.sqrt (lam x) * g x)) ^ 2
      ≤ (∑ x, (ν x - lam x) ^ 2 / lam x) * ∑ x, lam x * g x ^ 2 := hcs
    _ ≤ χ * ∑ x, lam x * g x ^ 2 := mul_le_mul_of_nonneg_right hχ hB

/-- Total variation against a chi-square: `∑ |ν - λ| ≤ √χ` for `λ ≥ 0`, `∑ λ = 1`, `ν ≪ λ`,
`∑ (ν - λ)²/λ ≤ χ`. -/
theorem sum_abs_sub_le_sqrt {ν lam : S → ℝ} {χ : ℝ} (hlam : ∀ x, 0 ≤ lam x)
    (hsum : ∑ x, lam x = 1) (hac : ∀ x, lam x = 0 → ν x = 0)
    (hχ : ∑ x, (ν x - lam x) ^ 2 / lam x ≤ χ) :
    ∑ x, |ν x - lam x| ≤ Real.sqrt χ := by
  have h := sum_sub_mul_le_sqrt (g := fun x => if 0 ≤ ν x - lam x then (1 : ℝ) else -1)
    hlam hac hχ
  have e1 : ∀ x, (ν x - lam x) * (if 0 ≤ ν x - lam x then (1 : ℝ) else -1) = |ν x - lam x| := by
    intro x
    split_ifs with h1
    · rw [abs_of_nonneg h1, mul_one]
    · push Not at h1
      rw [abs_of_neg h1]
      ring
  have e2 : ∀ x, lam x * (if 0 ≤ ν x - lam x then (1 : ℝ) else -1) ^ 2 = lam x := by
    intro x
    split_ifs <;> ring
  simp_rw [e1, e2, hsum, mul_one] at h
  exact h

end ChiTools

/-! ### The restoration lemma -/

section Restoration

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- The diagonal copy is linear in the half law: if `m' = ∑_z m'(z) o_z` pointwise, then
`Diag(m') = ∑_z m'(z) Diag(o_z)`. -/
theorem diagonalLaw_decomp (c : ReflectionCut V) {Y : Type*} [Fintype Y]
    (m' : (c.Half → Y) → ℝ) (o : (c.Half → Y) → (c.Half → Y) → ℝ)
    (hdec : ∀ y, m' y = ∑ z, m' z * o z y) :
    c.diagonalLaw m' = ∑ z, m' z • c.diagonalLaw (o z) := by
  apply LinearMap.ext
  intro f
  rw [LinearMap.sum_apply]
  change ∑ y, m' y * f (c.join y y) = ∑ z, m' z * ∑ y, o z y * f (c.join y y)
  have hpt : ∀ y, m' y * f (c.join y y) = ∑ z, m' z * (o z y * f (c.join y y)) := by
    intro y
    conv_lhs => rw [hdec y]
    rw [sum_mul]
    exact sum_congr rfl fun z _ => by ring
  rw [sum_congr rfl fun y _ => hpt y, sum_comm]
  exact sum_congr rfl fun z _ => by rw [mul_sum]

/-- **`lem:record:restoration`**, at a fold chamber `c = ϑ_{2j}`. Hypotheses, with the
paper's names:
* (C): `μ_X = (1 + h)⁻¹(Π^rt + 𝓜)` (`hmix`), `0 ≤ h ≤ h_X`, (E1) for `𝓜` (`hE1M`);
* (B): `Π^rt = w ≥ 0` with both half marginals `ν` (`hplus`, `hminus`), `Π_X = Diag(λ)`;
* (A) `ν ≤ M λ` (`hA`, `hyp:variance:A`), `M > 0`;
* the chi-square bound `∑ (ν - λ)²/λ ≤ χ_X`, `ν ≪ λ`, `∑ λ = ∑ ν = 1`;
* the orbit decomposition (`hνo`, `hlamo`) and (E1) for the orbit laws (`hE1o`);
* `1 ≤ C_X ≤ C`, `Y > 0`, errors `z, z₂ ≥ 0`.

Conclusion: `Y[Π_X] ≥ 0`, and with `l' = 1 - (C - 1)h_X - z h_X C > 0` and `C' = (1 + z₂)C`,
`Y[Π_X] ≥ max(l'/M, l' - (C'/2)√χ_X, branchVar l' C' χ_X) · Y`. -/
theorem restoration (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (hO : ∀ j, j ≠ j₀ → c.Positive (O j)) (F : (∀ b, X b) → ℝ) {Yμ : ℝ}
    (hYdef : diagonalIntegral (tensorLaw O) F = Yμ) (hY : 0 < Yμ)
    (w : (V → X j₀) → ℝ) (hw : ∀ z, 0 ≤ w z) (Mrest : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) {h hX : ℝ}
    (hh : 0 ≤ h) (hhX : h ≤ hX) (hmix : O j₀ = (1 + h)⁻¹ • (signedIntegral w + Mrest))
    {CX C z z₂ : ℝ} (hCX : 1 ≤ CX) (hC : CX ≤ C) (hz : 0 ≤ z) (hz₂ : 0 ≤ z₂)
    (hE1M : energyAt O j₀ Mrest F ≤ (1 + z) * h * CX * Yμ)
    (ν lam : (c.Half → X j₀) → ℝ) (hplus : plusMarginal c w = ν) (hminus : minusMarginal c w = ν)
    (hlam : ∀ x, 0 ≤ lam x) (hlamsum : ∑ x, lam x = 1) (hνsum : ∑ x, ν x = 1)
    {M : ℝ} (hM : 0 < M) (hA : ∀ x, ν x ≤ M * lam x)
    {χ : ℝ} (hac : ∀ x, lam x = 0 → ν x = 0) (hχ : ∑ x, (ν x - lam x) ^ 2 / lam x ≤ χ)
    (o : (c.Half → X j₀) → (c.Half → X j₀) → ℝ) (ho : ∀ z y, 0 ≤ o z y)
    (hνo : ∀ y, ν y = ∑ z, ν z * o z y) (hlamo : ∀ y, lam y = ∑ z, lam z * o z y)
    (hE1o : ∀ z, energyAt O j₀ (c.diagonalLaw (o z)) F ≤ (1 + z₂) * CX * Yμ) :
    0 ≤ energyAt O j₀ (c.diagonalLaw lam) F ∧
      (0 < 1 - (C - 1) * hX - z * hX * C →
        restorationL0 (1 - (C - 1) * hX - z * hX * C) ((1 + z₂) * C) M χ * Yμ ≤
          energyAt O j₀ (c.diagonalLaw lam) F) := by
  have hnonneg := energy_diagonalLaw_nonneg c O j₀ hO hlam F
  refine ⟨hnonneg, fun hl' => ?_⟩
  set l' := 1 - (C - 1) * hX - z * hX * C with hl'def
  set C' := (1 + z₂) * C with hC'def
  have hν0 : ∀ x, 0 ≤ ν x := fun x => hplus ▸ plusMarginal_nonneg c hw x
  -- (C): the root carries the reference
  have hroot : l' * Yμ ≤ energyAt O j₀ (signedIntegral w) F := by
    have hself : energyAt O j₀ (O j₀) F = Yμ := by
      unfold energyAt
      rw [Function.update_eq_self]
      exact hYdef
    rw [hmix, energyAt_smul, energyAt_add] at hself
    have h1h : 0 < 1 + h := by linarith
    have hsplit : energyAt O j₀ (signedIntegral w) F = (1 + h) * Yμ - energyAt O j₀ Mrest F := by
      rw [← hself]
      field_simp
      ring
    rw [hsplit]
    have hcmp : l' ≤ 1 + h - (1 + z) * h * CX := by
      have e1 : (CX - 1) * h ≤ (C - 1) * hX :=
        mul_le_mul (by linarith) hhX hh (by linarith)
      have e2 : h * CX ≤ hX * C := mul_le_mul hhX hC (by linarith) (by linarith [hh.trans hhX])
      have e3 : z * (h * CX) ≤ z * (hX * C) := mul_le_mul_of_nonneg_left e2 hz
      rw [hl'def]
      nlinarith
    nlinarith
  -- (B): contraction, `Y[Π^rt] ≤ Y[Diag(ν)]`
  have hdiagν0 := energy_diagonalLaw_nonneg c O j₀ hO hν0 F
  have hcontr : energyAt O j₀ (signedIntegral w) F ≤ energyAt O j₀ (c.diagonalLaw ν) F := by
    have h := abs_energy_le_diagonal_marginals c O j₀ hO hw F
    rw [hplus, hminus, Real.mul_self_sqrt hdiagν0] at h
    exact (le_abs_self _).trans h
  have hν : l' * Yμ ≤ energyAt O j₀ (c.diagonalLaw ν) F := hroot.trans hcontr
  -- the orbit energies
  set e : (c.Half → X j₀) → ℝ := fun z => energyAt O j₀ (c.diagonalLaw (o z)) F with he
  have he0 : ∀ z, 0 ≤ e z := fun z => energy_diagonalLaw_nonneg c O j₀ hO (ho z) F
  have heC : ∀ z, e z ≤ C' * Yμ := by
    intro z
    have h1 := hE1o z
    have : (1 + z₂) * CX * Yμ ≤ (1 + z₂) * C * Yμ := by
      have := mul_le_mul_of_nonneg_left hC (by linarith : (0 : ℝ) ≤ 1 + z₂)
      nlinarith
    exact h1.trans this
  have hEν : energyAt O j₀ (c.diagonalLaw ν) F = ∑ x, ν x * e x := by
    rw [diagonalLaw_decomp c ν o hνo, energyAt_sum]
  have hElam : energyAt O j₀ (c.diagonalLaw lam) F = ∑ x, lam x * e x := by
    rw [diagonalLaw_decomp c lam o hlamo, energyAt_sum]
  have hdiff : energyAt O j₀ (c.diagonalLaw ν) F - energyAt O j₀ (c.diagonalLaw lam) F =
      ∑ x, (ν x - lam x) * e x := by
    rw [hEν, hElam, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  have hχ0 : 0 ≤ χ := le_trans (sum_nonneg fun x _ => div_nonneg (sq_nonneg _) (hlam x)) hχ
  have hC'0 : 0 ≤ C' := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + z₂) (by linarith : (0 : ℝ) ≤ C)
    rw [hC'def]
    exact this
  unfold restorationL0
  rw [max_mul_of_nonneg _ _ hY.le, max_mul_of_nonneg _ _ hY.le]
  refine max_le ?_ (max_le ?_ ?_)
  · -- pointwise branch, by (P2)
    have hP2 := energy_diagonal_le_of_le c O j₀ hO hA F
    rw [div_mul_eq_mul_div, div_le_iff₀ hM]
    change l' * Yμ ≤ energyAt O j₀ (c.diagonalLaw lam) F * M
    have := hν.trans hP2
    linarith
  · -- one-sided branch
    have hpos : ∑ x, (ν x - lam x) * e x ≤ C' * Yμ * (∑ x, |ν x - lam x|) / 2 := by
      have hzero : ∑ x, (ν x - lam x) = 0 := by rw [sum_sub_distrib, hνsum, hlamsum, sub_self]
      have hpt : ∀ x, (ν x - lam x) * e x ≤ C' * Yμ * ((ν x - lam x + |ν x - lam x|) / 2) := by
        intro x
        rcases le_or_gt 0 (ν x - lam x) with h1 | h1
        · rw [abs_of_nonneg h1]
          have := mul_le_mul_of_nonneg_left (heC x) h1
          nlinarith
        · rw [abs_of_neg h1]
          have := mul_nonpos_of_nonpos_of_nonneg h1.le (he0 x)
          nlinarith
      have hs := sum_le_sum fun x (_ : x ∈ univ) => hpt x
      rw [← mul_sum, ← sum_div, sum_add_distrib, hzero, zero_add] at hs
      rw [mul_div_assoc]
      exact hs
    have htv := sum_abs_sub_le_sqrt hlam hlamsum hac hχ
    have hCY : 0 ≤ C' * Yμ := mul_nonneg hC'0 hY.le
    have : C' * Yμ * (∑ x, |ν x - lam x|) / 2 ≤ C' * Yμ * Real.sqrt χ / 2 := by
      have := mul_le_mul_of_nonneg_left htv hCY
      linarith
    have h2 := hdiff ▸ hpos.trans this
    nlinarith
  · -- bounded-variance branch
    set ebar := ∑ x, lam x * e x with hebar
    have hebar0 : 0 ≤ ebar := sum_nonneg fun x _ => mul_nonneg (hlam x) (he0 x)
    have hebarC : ebar ≤ C' * Yμ := by
      have : ebar ≤ ∑ x, lam x * (C' * Yμ) :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (heC x) (hlam x)
      rw [← sum_mul, hlamsum, one_mul] at this
      exact this
    -- `∑ (ν - λ) e = ∑ (ν - λ)(e - ē) ≤ (χ Var_λ e)^{1/2} ≤ (χ ē (C'Y - ē))^{1/2}`
    have hzero : ∑ x, (ν x - lam x) = 0 := by rw [sum_sub_distrib, hνsum, hlamsum, sub_self]
    have hcen : ∑ x, (ν x - lam x) * e x = ∑ x, (ν x - lam x) * (e x - ebar) := by
      have : ∑ x, (ν x - lam x) * (e x - ebar) =
          ∑ x, (ν x - lam x) * e x - (∑ x, (ν x - lam x)) * ebar := by
        rw [sum_mul, ← sum_sub_distrib]
        exact sum_congr rfl fun x _ => by ring
      rw [this, hzero, zero_mul, sub_zero]
    have hcs := sum_sub_mul_le_sqrt (g := fun x => e x - ebar) hlam hac hχ
    have hvar : ∑ x, lam x * (e x - ebar) ^ 2 ≤ ebar * (C' * Yμ - ebar) := by
      have h1 : ∑ x, lam x * (e x - ebar) ^ 2 = ∑ x, lam x * e x ^ 2 - ebar ^ 2 := by
        have : ∀ x, lam x * (e x - ebar) ^ 2 =
            lam x * e x ^ 2 - 2 * ebar * (lam x * e x) + ebar ^ 2 * lam x := by
          intro x
          ring
        simp_rw [this]
        rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hlamsum, ← hebar]
        ring
      have h2 : ∑ x, lam x * e x ^ 2 ≤ C' * Yμ * ebar := by
        rw [hebar, mul_sum]
        apply sum_le_sum
        intro x _
        have h5 : e x ^ 2 ≤ C' * Yμ * e x := by
          have := mul_le_mul_of_nonneg_left (heC x) (he0 x)
          rw [sq]
          linarith
        calc lam x * e x ^ 2 ≤ lam x * (C' * Yμ * e x) := mul_le_mul_of_nonneg_left h5 (hlam x)
          _ = C' * Yμ * (lam x * e x) := by ring
      rw [h1]
      have : ebar * (C' * Yμ - ebar) = C' * Yμ * ebar - ebar ^ 2 := by ring
      linarith
    have hbound : energyAt O j₀ (c.diagonalLaw ν) F ≤
        ebar + Real.sqrt (χ * (ebar * (C' * Yμ - ebar))) := by
      have h4 : energyAt O j₀ (c.diagonalLaw ν) F - energyAt O j₀ (c.diagonalLaw lam) F ≤
          Real.sqrt (χ * ∑ x, lam x * (e x - ebar) ^ 2) := by
        rw [hdiff, hcen]
        exact hcs
      have h3 : Real.sqrt (χ * ∑ x, lam x * (e x - ebar) ^ 2) ≤
          Real.sqrt (χ * (ebar * (C' * Yμ - ebar))) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hvar hχ0)
      have h5 : energyAt O j₀ (c.diagonalLaw lam) F = ebar := hElam
      linarith
    -- normalize by `Y`
    set x := ebar / Yμ with hx
    have hxY : ebar = x * Yμ := by rw [hx]; field_simp
    have hx0 : 0 ≤ x := div_nonneg hebar0 hY.le
    have hxC : x ≤ C' := by
      rw [hx, div_le_iff₀ hY]
      exact hebarC
    have hsqrt : Real.sqrt (χ * (ebar * (C' * Yμ - ebar))) =
        Real.sqrt (χ * x * (C' - x)) * Yμ := by
      rw [hxY]
      have : χ * (x * Yμ * (C' * Yμ - x * Yμ)) = (χ * x * (C' - x)) * Yμ ^ 2 := by ring
      rw [this, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hY.le]
    have hmain : l' ≤ x + Real.sqrt (χ * x * (C' - x)) := by
      have := hν.trans hbound
      rw [hsqrt, hxY] at this
      have h4 : l' * Yμ ≤ (x + Real.sqrt (χ * x * (C' - x))) * Yμ := by linarith
      exact le_of_mul_le_mul_right h4 hY
    have hbv := branchVar_le hl' hχ0 hx0 hxC hmain
    have hfin : branchVar l' C' χ * Yμ ≤ ebar := by
      rw [hxY]
      exact mul_le_mul_of_nonneg_right hbv hY.le
    have h5 : energyAt O j₀ (c.diagonalLaw lam) F = ebar := hElam
    linarith

/-- **`lem:record:restoration` in the form `Y[Π_X] ≥ 𝓕(C', h_X, M, χ_X) Y`**, at `z = 0` (no
error in (E1) for the nonroot part), with `C' = (1 + z₂) C`. Both `𝓕` and the lemma use `C'`
in `l = 1 - (C' - 1)h_X`; since `C ≤ C'` the restoration hypothesis is used at the larger cap. -/
theorem restoration_F (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (hO : ∀ j, j ≠ j₀ → c.Positive (O j)) (F : (∀ b, X b) → ℝ) {Yμ : ℝ}
    (hYdef : diagonalIntegral (tensorLaw O) F = Yμ) (hY : 0 < Yμ)
    (w : (V → X j₀) → ℝ) (hw : ∀ z, 0 ≤ w z) (Mrest : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) {h hX : ℝ}
    (hh : 0 ≤ h) (hhX : h ≤ hX) (hmix : O j₀ = (1 + h)⁻¹ • (signedIntegral w + Mrest))
    {CX C : ℝ} (hCX : 1 ≤ CX) (hC : CX ≤ C)
    (hE1M : energyAt O j₀ Mrest F ≤ h * CX * Yμ)
    (ν lam : (c.Half → X j₀) → ℝ) (hplus : plusMarginal c w = ν) (hminus : minusMarginal c w = ν)
    (hlam : ∀ x, 0 ≤ lam x) (hlamsum : ∑ x, lam x = 1) (hνsum : ∑ x, ν x = 1)
    {M : ℝ} (hM : 0 < M) (hA : ∀ x, ν x ≤ M * lam x)
    {χ : ℝ} (hac : ∀ x, lam x = 0 → ν x = 0) (hχ : ∑ x, (ν x - lam x) ^ 2 / lam x ≤ χ)
    (o : (c.Half → X j₀) → (c.Half → X j₀) → ℝ) (ho : ∀ z y, 0 ≤ o z y)
    (hνo : ∀ y, ν y = ∑ z, ν z * o z y) (hlamo : ∀ y, lam y = ∑ z, lam z * o z y)
    {z₂ : ℝ} (hz₂ : 0 ≤ z₂)
    (hE1o : ∀ z, energyAt O j₀ (c.diagonalLaw (o z)) F ≤ (1 + z₂) * CX * Yμ) :
    restorationF ((1 + z₂) * C) hX M χ * Yμ ≤ energyAt O j₀ (c.diagonalLaw lam) F := by
  have hCX' : 1 ≤ (1 + z₂) * CX := by nlinarith
  have hC' : (1 + z₂) * CX ≤ (1 + z₂) * C := mul_le_mul_of_nonneg_left hC (by linarith)
  have hE1M' : energyAt O j₀ Mrest F ≤ (1 + 0) * h * ((1 + z₂) * CX) * Yμ := by
    have : h * CX * Yμ ≤ (1 + 0) * h * ((1 + z₂) * CX) * Yμ := by
      have h1 : 0 ≤ h * CX * Yμ := by
        have := mul_nonneg hh (by linarith : (0 : ℝ) ≤ CX)
        exact mul_nonneg this hY.le
      nlinarith
    linarith
  have hE1o' : ∀ z, energyAt O j₀ (c.diagonalLaw (o z)) F ≤ (1 + 0) * ((1 + z₂) * CX) * Yμ := by
    intro z
    have := hE1o z
    have e : (1 + 0) * ((1 + z₂) * CX) * Yμ = (1 + z₂) * CX * Yμ := by ring
    rw [e]
    exact this
  have hres := restoration c O j₀ hO F hYdef hY w hw Mrest hh hhX hmix
    (CX := (1 + z₂) * CX) (C := (1 + z₂) * C) (z := 0) (z₂ := 0) hCX' hC' le_rfl le_rfl hE1M'
    ν lam hplus hminus hlam hlamsum hνsum hM hA hac hχ o ho hνo hlamo hE1o'
  unfold restorationF
  split_ifs with hl
  · have hl' : 0 < 1 - ((1 + z₂) * C - 1) * hX - 0 * hX * ((1 + z₂) * C) := by
      rw [zero_mul, zero_mul, sub_zero]
      exact hl
    have h2 := hres.2 hl'
    rw [zero_mul, zero_mul, sub_zero, add_zero, one_mul] at h2
    rw [max_def]
    split_ifs
    · exact h2
    · rw [zero_mul]; exact hres.1
  · rw [zero_mul]; exact hres.1

/-- **`lem:record:restoration` from `hyp:variance:A`**: the same conclusion with hypothesis (A)
in the form `RootDensityA ν λ M` (`M⁻¹ λ ≤ ν ≤ M λ`), which also gives `ν ≪ λ`. -/
theorem restoration_of_A (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (hO : ∀ j, j ≠ j₀ → c.Positive (O j)) (F : (∀ b, X b) → ℝ) {Yμ : ℝ}
    (hYdef : diagonalIntegral (tensorLaw O) F = Yμ) (hY : 0 < Yμ)
    (w : (V → X j₀) → ℝ) (hw : ∀ z, 0 ≤ w z) (Mrest : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) {h hX : ℝ}
    (hh : 0 ≤ h) (hhX : h ≤ hX) (hmix : O j₀ = (1 + h)⁻¹ • (signedIntegral w + Mrest))
    {CX C z z₂ : ℝ} (hCX : 1 ≤ CX) (hC : CX ≤ C) (hz : 0 ≤ z) (hz₂ : 0 ≤ z₂)
    (hE1M : energyAt O j₀ Mrest F ≤ (1 + z) * h * CX * Yμ)
    (ν lam : (c.Half → X j₀) → ℝ) (hplus : plusMarginal c w = ν) (hminus : minusMarginal c w = ν)
    (hlam : ∀ x, 0 ≤ lam x) (hlamsum : ∑ x, lam x = 1) (hνsum : ∑ x, ν x = 1)
    {M : ℝ} (hM : 0 < M) (hA : RootDensityA ν lam M)
    {χ : ℝ} (hχ : ∑ x, (ν x - lam x) ^ 2 / lam x ≤ χ)
    (o : (c.Half → X j₀) → (c.Half → X j₀) → ℝ) (ho : ∀ z y, 0 ≤ o z y)
    (hνo : ∀ y, ν y = ∑ z, ν z * o z y) (hlamo : ∀ y, lam y = ∑ z, lam z * o z y)
    (hE1o : ∀ z, energyAt O j₀ (c.diagonalLaw (o z)) F ≤ (1 + z₂) * CX * Yμ) :
    0 ≤ energyAt O j₀ (c.diagonalLaw lam) F ∧
      (0 < 1 - (C - 1) * hX - z * hX * C →
        restorationL0 (1 - (C - 1) * hX - z * hX * C) ((1 + z₂) * C) M χ * Yμ ≤
          energyAt O j₀ (c.diagonalLaw lam) F) :=
  restoration c O j₀ hO F hYdef hY w hw Mrest hh hhX hmix hCX hC hz hz₂ hE1M ν lam hplus hminus
    hlam hlamsum hνsum hM hA.le
    (hA.ac (fun x => hplus ▸ plusMarginal_nonneg c hw x)) hχ o ho hνo hlamo hE1o

end Restoration

/-! ### The orbit decomposition for invariant laws -/

/-- **The orbit decomposition** in the bounded-variance step: for a finite group `G` acting on a
finite set `S`, with the orbit law `o_z(y) = |G|⁻¹ #{g : g • z = y}`, every `G`-invariant `ν`
satisfies `ν = ∑_z ν(z) o_z`. In the paper `G` is the group of independent translations at the
primes of `X`, acting on the half-label tuples. -/
theorem orbit_decomposition {G S : Type*} [Group G] [Fintype G] [MulAction G S] [Fintype S]
    [DecidableEq S] (ν : S → ℝ) (hinv : ∀ (g : G) (y : S), ν (g • y) = ν y) (y : S) :
    ν y = ∑ z, ν z * ((Fintype.card G : ℝ)⁻¹ * ∑ g : G, if g • z = y then 1 else 0) := by
  have hG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : ∀ g : G, ∑ z, ν z * (if g • z = y then (1 : ℝ) else 0) = ν y := by
    intro g
    have : ∀ z, (g • z = y) ↔ (z = g⁻¹ • y) := fun z => by
      constructor
      · intro h; rw [← h, inv_smul_smul]
      · intro h; rw [h, smul_inv_smul]
    simp_rw [mul_ite, mul_one, mul_zero, this]
    rw [sum_ite_eq']
    simp only [mem_univ, ite_true]
    exact hinv g⁻¹ y
  calc ν y = (Fintype.card G : ℝ)⁻¹ * ∑ _g : G, ν y := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        field_simp
    _ = (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ∑ z, ν z * (if g • z = y then (1 : ℝ) else 0) := by
        simp_rw [h1]
    _ = ∑ z, ν z * ((Fintype.card G : ℝ)⁻¹ * ∑ g : G, if g • z = y then 1 else 0) := by
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun z _ => ?_
        rw [mul_sum, mul_sum, mul_sum]
        exact sum_congr rfl fun g _ => by ring

/-- The orbit laws are nonnegative. -/
theorem orbitLaw_nonneg {G S : Type*} [Group G] [Fintype G] [MulAction G S] [DecidableEq S]
    (z y : S) : 0 ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, (if g • z = y then (1 : ℝ) else 0) :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (sum_nonneg fun g _ => by split_ifs <;> norm_num)

end Sarkozy.Variance
