module

public import Sarkozy.RecordExpansion.Variance

/-!
# Centred interpolation at a cut ((P3) of `lem:energy-toolkit`)

`paper/sections/10_comparison_lemmas.tex`, `lem:energy-toolkit`, part (P3), the tool through
which Section 22 (`paper/sections/22_variance.tex`) turns a lower bound for the energy of a
record into one for the product of its actual half marginals (`lem:var-gain`,
`prop:background-variance`).

**The Markov operator.** Let `π` be a measure on the labels with half marginal `m` at a cut
`c`. Its Markov operator `T` on `L²(m)` satisfies `⟨f, T g⟩_m = Q_π(f, g)`, the cut form of `π`
(`c.form π f g`), and the projection `𝒥` onto the constants of `L²(m)` satisfies
`⟨f, 𝒥 g⟩_m = (∑ m f)(∑ m g)/∑ m` (`form_indepLaw`). So the operator-norm bound
`‖T - 𝒥‖ ≤ κ` on `L²(m)` is exactly the bilinear bound
`|Q_π(f, g) - (∑ m f)(∑ m g)/∑ m| ≤ κ ‖f‖_m ‖g‖_m` for all `f, g`, with
`‖f‖_m = (∑ m f²)^{1/2}`. This is `CentredNormLe c π m κ`.

**Main results.**
* `below_centred_interpolation`: **(P3), the order**. If `π` is symmetric at `c` with plus-half
  marginal `m` (`Q_π(F, 1) = ∑ m F`) and `‖T - 𝒥‖ ≤ κ`, then
  `π ⪯_c (1 - κ) J_c(m) + κ Diag_c(m)`. No bound `κ ≤ 1` and no positivity of `π` is needed
  for the order itself (only `m ≥ 0`).
* `energy_le_centred_interpolation`: **(P3), the energy form**, by (E2) with positive outside
  factors: `Y^O[π] ≤ (1 - κ) Y^O[J(m)] + κ Y^O[Diag(m)]`.
* `form_signedIntegral_one_right`, `form_signedIntegral_one_left`: the half marginals of a weight
  in form language, so that the hypotheses apply to `π = signedIntegral w`.
* `energy_indepLaw_nonneg`, `energy_diagonalLaw_nonneg`: (E2), (E3) for `J(m)` and `Diag(m)`.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

section Form

variable {W Y : Type*} [Fintype W] [DecidableEq W] [Fintype Y]

/-- **The centred norm of a Markov operator** (`lem:energy-toolkit`(P3), Section 22's
`‖T - 𝒥‖ ≤ κ` on `L²(m)`): `|Q_π(f, g) - (∑ m f)(∑ m g)/∑ m| ≤ κ ‖f‖_m ‖g‖_m` for all
half-functions. When `π` has half marginal `m` this is `‖T - 𝒥‖ ≤ κ` for its Markov operator
`T` on `L²(m)`, since `⟨f, T g⟩_m = Q_π(f, g)` and `⟨f, 𝒥 g⟩_m = (∑ m f)(∑ m g)/∑ m`. -/
def CentredNormLe (c : ReflectionCut W) (π : ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (m : (c.Half → Y) → ℝ) (κ : ℝ) : Prop :=
  ∀ f g : (c.Half → Y) → ℝ,
    |c.form π f g - (∑ x, m x * f x) * (∑ y, m y * g y) / ∑ x, m x| ≤
      κ * Real.sqrt (∑ x, m x * f x ^ 2) * Real.sqrt (∑ x, m x * g x ^ 2)

/-- A centred-norm bound persists for a larger constant. -/
theorem CentredNormLe.mono {c : ReflectionCut W} {π : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    {m : (c.Half → Y) → ℝ} {κ κ' : ℝ} (h : CentredNormLe c π m κ) (hκ : κ ≤ κ') :
    CentredNormLe c π m κ' := by
  intro f g
  refine (h f g).trans ?_
  have h1 := Real.sqrt_nonneg (∑ x, m x * f x ^ 2)
  have h2 := Real.sqrt_nonneg (∑ x, m x * g x ^ 2)
  have := mul_nonneg h1 h2
  nlinarith

/-- **(P3) of `lem:energy-toolkit`, the order**: a measure `π` symmetric at `c`, with plus-half
marginal `m ≥ 0` (`Q_π(F, 1) = ∑ m F`, `∑ m > 0`) and `‖T - 𝒥‖ ≤ κ` on `L²(m)`, satisfies
`π ⪯_c (1 - κ) J_c(m) + κ Diag_c(m)`. -/
theorem below_centred_interpolation (c : ReflectionCut W) {π : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    {m : (c.Half → Y) → ℝ} (hm : ∀ x, 0 ≤ m x) (hmpos : 0 < ∑ x, m x)
    (hsymm : ∀ F G : (c.Half → Y) → ℝ, c.form π F G = c.form π G F)
    (hplus : ∀ F : (c.Half → Y) → ℝ, c.form π F 1 = ∑ x, m x * F x)
    {κ : ℝ} (hκ : CentredNormLe c π m κ) :
    c.Below π ((1 - κ) • indepLaw c m + κ • c.diagonalLaw m) := by
  have hformD : ∀ F G : (c.Half → Y) → ℝ,
      c.form ((1 - κ) • indepLaw c m + κ • c.diagonalLaw m - π) F G =
        (1 - κ) * ((∑ x, m x * F x) * (∑ y, m y * G y) / ∑ x, m x) +
          κ * ∑ x, m x * (F x * G x) - c.form π F G := by
    intro F G
    change (1 - κ) * c.form (indepLaw c m) F G + κ * c.form (c.diagonalLaw m) F G -
      c.form π F G = _
    rw [form_indepLaw, c.form_diagonalLaw]
  constructor
  · intro F G
    rw [hformD, hformD, hsymm F G]
    have : ∑ x, m x * (F x * G x) = ∑ x, m x * (G x * F x) :=
      sum_congr rfl fun x _ => by ring
    rw [this]
    ring
  · intro F
    rw [hformD]
    -- split `F = a + F₀` with `a = E_m F` and `∑ m F₀ = 0`
    set S := ∑ x, m x with hS
    set a := (∑ x, m x * F x) / S with ha
    set F₀ : (c.Half → Y) → ℝ := fun x => F x - a with hF₀
    have hSne : S ≠ 0 := ne_of_gt hmpos
    have hmean0 : ∑ x, m x * F₀ x = 0 := by
      simp only [hF₀, mul_sub, sum_sub_distrib, ← sum_mul]
      rw [ha]
      field_simp
      ring
    have hF : F = F₀ + a • (1 : (c.Half → Y) → ℝ) := by
      funext x
      simp [hF₀]
    -- the form of `π` at `F = F₀ + a·1`
    have hlin : c.form π F F =
        c.form π F₀ F₀ + a * c.form π F₀ 1 + a * c.form π 1 F₀ + a * a * c.form π 1 1 := by
      have e1 : ∀ G H K : (c.Half → Y) → ℝ, c.form π (G + H) K =
          c.form π G K + c.form π H K := by
        intro G H K
        change π _ = π _ + π _
        rw [← map_add]
        congr 1
        funext z
        simp only [Pi.add_apply]
        ring
      have e2 : ∀ G H K : (c.Half → Y) → ℝ, c.form π K (G + H) =
          c.form π K G + c.form π K H := by
        intro G H K
        change π _ = π _ + π _
        rw [← map_add]
        congr 1
        funext z
        simp only [Pi.add_apply]
        ring
      have e3 : ∀ (t : ℝ) (G K : (c.Half → Y) → ℝ), c.form π (t • G) K = t * c.form π G K := by
        intro t G K
        change π _ = t • π _
        rw [← map_smul]
        congr 1
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      have e4 : ∀ (t : ℝ) (G K : (c.Half → Y) → ℝ), c.form π K (t • G) = t * c.form π K G := by
        intro t G K
        change π _ = t • π _
        rw [← map_smul]
        congr 1
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      conv_lhs => rw [hF]
      rw [e1, e2, e2, e3, e4, e3, e4]
      ring
    have h1 : c.form π F₀ 1 = 0 := by rw [hplus, hmean0]
    have h2 : c.form π 1 F₀ = 0 := by rw [hsymm, h1]
    have h3 : c.form π 1 1 = S := by
      rw [hplus]
      simp only [Pi.one_apply, mul_one]
      exact hS.symm
    have hcen := hκ F₀ F₀
    rw [hmean0, zero_mul, zero_div, sub_zero] at hcen
    have hsq : Real.sqrt (∑ x, m x * F₀ x ^ 2) * Real.sqrt (∑ x, m x * F₀ x ^ 2) =
        ∑ x, m x * F₀ x ^ 2 :=
      Real.mul_self_sqrt (sum_nonneg fun x _ => mul_nonneg (hm x) (sq_nonneg _))
    have hκF := hcen
    rw [mul_assoc, hsq] at hκF
    have hvar : ∑ x, m x * F₀ x ^ 2 = ∑ x, m x * (F x * F x) - a * a * S := by
      have : ∀ x, m x * F₀ x ^ 2 = m x * (F x * F x) - 2 * a * (m x * F x) + a * a * m x := by
        intro x
        simp only [hF₀]
        ring
      simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum]
      rw [ha]
      field_simp
      ring
    have hsumF : ∑ x, m x * F x = a * S := by
      rw [ha]
      field_simp
    have hπF : c.form π F F ≤ a * a * S + κ * ∑ x, m x * F₀ x ^ 2 := by
      rw [hlin, h1, h2, h3]
      have := le_abs_self (c.form π F₀ F₀)
      linarith
    rw [hsumF]
    rw [hvar] at hπF
    have e : (1 - κ) * (a * S * (a * S) / S) = (1 - κ) * (a * a * S) := by
      field_simp
    rw [e]
    nlinarith

end Form

section Marginals

variable {W Y : Type*} [Fintype W] [DecidableEq W] [Fintype Y] [DecidableEq Y]

/-- The plus-half marginal of a weight in form language: `Q_w(F, 1) = ∑ m_+ F`. -/
theorem form_signedIntegral_one_right (c : ReflectionCut W) (w : (W → Y) → ℝ)
    (F : (c.Half → Y) → ℝ) :
    c.form (signedIntegral w) F 1 = ∑ x, plusMarginal c w x * F x := by
  have h : ∑ x, plusMarginal c w x * F x = ∑ z, w z * F (fun v : c.Half => z v.1) :=
    sum_marginal_mul (fun z (v : c.Half) => z v.1) w F
  rw [h]
  change ∑ z, w z * (F (fun v => z v.1) * 1) = _
  simp

/-- The minus-half marginal of a weight in form language: `Q_w(1, G) = ∑ m_- G`. -/
theorem form_signedIntegral_one_left (c : ReflectionCut W) (w : (W → Y) → ℝ)
    (G : (c.Half → Y) → ℝ) :
    c.form (signedIntegral w) 1 G = ∑ x, minusMarginal c w x * G x := by
  have h : ∑ x, minusMarginal c w x * G x = ∑ z, w z * G (fun v : c.Half => z (c.flip v.1)) :=
    sum_marginal_mul (fun z (v : c.Half) => z (c.flip v.1)) w G
  rw [h]
  change ∑ z, w z * (1 * G (fun v => z (c.flip v.1))) = _
  simp

end Marginals

section Energy

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- The energy `Y^O[κ]` with the law `κ` at the selected factor `j₀` and the outside laws `O`
at the other factors (`Y^O[κ] = Y_{κ ⊗ O_{-X}}` in the notation of `lem:energy-toolkit`, the
selected set `X` being one factor). -/
noncomputable abbrev energyAt (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (κ : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, X b) → ℝ) : ℝ :=
  diagonalIntegral (tensorLaw (Function.update O j₀ κ)) F

/-- The energy is linear in the selected factor: sums. -/
theorem energyAt_add (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (κ κ' : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, X b) → ℝ) :
    energyAt O j₀ (κ + κ') F = energyAt O j₀ κ F + energyAt O j₀ κ' F := by
  unfold energyAt
  rw [tensorLaw_update_add]
  rfl

/-- The energy is linear in the selected factor: scalars. -/
theorem energyAt_smul (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J) (a : ℝ)
    (κ : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, X b) → ℝ) :
    energyAt O j₀ (a • κ) F = a * energyAt O j₀ κ F := by
  unfold energyAt
  rw [tensorLaw_update_smul]
  rfl

/-- The energy is linear in the selected factor: differences. -/
theorem energyAt_sub (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (κ κ' : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, X b) → ℝ) :
    energyAt O j₀ (κ - κ') F = energyAt O j₀ κ F - energyAt O j₀ κ' F := by
  unfold energyAt
  rw [tensorLaw_update_sub]
  rfl

/-- The energy of a finite combination at the selected factor. -/
theorem energyAt_sum {ι : Type*} (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (s : Finset ι) (a : ι → ℝ) (K : ι → ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, X b) → ℝ) :
    energyAt O j₀ (∑ i ∈ s, a i • K i) F = ∑ i ∈ s, a i * energyAt O j₀ (K i) F := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    have h := energyAt_smul O j₀ 0 0 F
    rw [zero_smul, zero_mul] at h
    exact h
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi, energyAt_add, energyAt_smul, ih]

/-- (E2) with a positive selected factor: `κ ⪰_c 0` and positive outside factors give
`Y^O[κ] ≥ 0`. -/
theorem energyAt_nonneg (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (hO : ∀ j, j ≠ j₀ → c.Positive (O j)) {κ : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ}
    (hκ : c.Positive κ) (F : (∀ b, X b) → ℝ) : 0 ≤ energyAt O j₀ κ F := by
  apply ReflectionCut.Positive.diagonal_nonneg
  apply ReflectionCut.Positive.tensor
  intro j
  by_cases hj : j = j₀
  · subst hj
    rw [Function.update_self]
    exact hκ
  · rw [Function.update_of_ne hj]
    exact hO j hj

/-- (E2) for the product of the half marginals: `Y^O[J(m)] ≥ 0`, as the cut operator of `J(m)`
is a projection. -/
theorem energy_indepLaw_nonneg (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (j₀ : J) (hO : ∀ j, j ≠ j₀ → c.Positive (O j)) {m : (c.Half → X j₀) → ℝ}
    (hm : ∀ x, 0 ≤ m x) (F : (∀ b, X b) → ℝ) : 0 ≤ energyAt O j₀ (indepLaw c m) F :=
  energyAt_nonneg c O j₀ hO (positive_indepLaw c hm) F

/-- (E3), (E2) for a diagonal copy: `Y^O[Diag(m)] ≥ 0`. -/
theorem energy_diagonalLaw_nonneg (c : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (j₀ : J) (hO : ∀ j, j ≠ j₀ → c.Positive (O j)) {m : (c.Half → X j₀) → ℝ}
    (hm : ∀ x, 0 ≤ m x) (F : (∀ b, X b) → ℝ) : 0 ≤ energyAt O j₀ (c.diagonalLaw m) F :=
  energyAt_nonneg c O j₀ hO (c.diagonalLaw_positive hm) F

/-- **(P3) of `lem:energy-toolkit`, the energy form**: under the hypotheses of
`below_centred_interpolation` and with positive outside factors,
`Y^O[π] ≤ (1 - κ) Y^O[J(m)] + κ Y^O[Diag(m)]`. -/
theorem energy_le_centred_interpolation (c : ReflectionCut V)
    (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J) (hO : ∀ j, j ≠ j₀ → c.Positive (O j))
    {π : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ} {m : (c.Half → X j₀) → ℝ} (hm : ∀ x, 0 ≤ m x)
    (hmpos : 0 < ∑ x, m x)
    (hsymm : ∀ F G : (c.Half → X j₀) → ℝ, c.form π F G = c.form π G F)
    (hplus : ∀ F : (c.Half → X j₀) → ℝ, c.form π F 1 = ∑ x, m x * F x)
    {κ : ℝ} (hκ : CentredNormLe c π m κ) (F : (∀ b, X b) → ℝ) :
    energyAt O j₀ π F ≤
      (1 - κ) * energyAt O j₀ (indepLaw c m) F + κ * energyAt O j₀ (c.diagonalLaw m) F := by
  have h := energy_le_of_below_factor c O j₀ hO
    (below_centred_interpolation c hm hmpos hsymm hplus hκ) F
  have e : energyAt O j₀ ((1 - κ) • indepLaw c m + κ • c.diagonalLaw m) F =
      (1 - κ) * energyAt O j₀ (indepLaw c m) F + κ * energyAt O j₀ (c.diagonalLaw m) F := by
    rw [energyAt_add, energyAt_smul, energyAt_smul]
  unfold energyAt at e
  unfold energyAt
  rw [← e]
  exact h

end Energy

end Sarkozy.Variance
