module

public import Sarkozy.Variance.Interpolation

/-!
# Product centred interpolation ((P3′) of `lem:energy-toolkit`, energy form)

`paper/sections/10_comparison_lemmas.tex`, `lem:energy-toolkit`, (P3′), used in the background
terms of `prop:background-variance` (`paper/sections/22_variance.tex`). Let `π` (on the labels of
`X`, factor `j₀`) be as in (P3), symmetric at `c` with half marginal `m` and `‖T - 𝒥‖ ≤ κ`, and
let `π'` (on the labels of `Z`, factor `j₁ ≠ j₀`) be a nonnegative weight, symmetric at `c`, with
both half marginals `m'`. Then, with positive outside factors,
`Y[π ⊗ π'] ≤ (1 - κ) Y[J(m) ⊗ Diag(m')] + κ Y[Diag(m) ⊗ Diag(m')]`
(`energy_le_product_interpolation`). Here `Diag(m) ⊗ Diag(m')` is the diagonal copy of the
product marginal `m ⊗ m'` (the two factors are separate atoms).

**Route** (as in the paper, no order is tensored with an indefinite factor): write
`π = J(m) + Δ`. Then `κ(Diag(m) - J(m)) ± Δ ⪰_c 0` (`centred_pm`: (P3) for `π` and for
`2J(m) - π`), and `Diag(m') ± π' ⪰_c 0` (`diag_pm_of_weight`: the Markov operator of `π'` is a
contraction). The `±` tensorization ((P5), WP-R's `abs_energy_le_of_add_sub`) gives
`|Y[Δ ⊗ π']| ≤ κ(Y[Diag(m) ⊗ Diag(m')] - Y[J(m) ⊗ Diag(m')])`, and (E2) gives
`Y[J(m) ⊗ π'] ≤ Y[J(m) ⊗ Diag(m')]`.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

section Orders

variable {W Y : Type*} [Fintype W] [DecidableEq W] [Fintype Y]

omit [Fintype Y] in
/-- The zero measure is positive at every cut. -/
theorem positive_zero (c : ReflectionCut W) : c.Positive (0 : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) :=
  ⟨fun _ _ => rfl, fun _ => le_rfl⟩

/-- **The two centred orders** of a measure as in (P3):
`κ(Diag(m) - J(m)) - (π - J(m)) ⪰_c 0` (this is (P3)) and `κ(Diag(m) - J(m)) + (π - J(m)) ⪰_c 0`
((P3) applied to `2J(m) - π`, which has the same half marginal and centred norm). -/
theorem centred_pm (c : ReflectionCut W) {π : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    {m : (c.Half → Y) → ℝ} (hm : ∀ x, 0 ≤ m x) (hmpos : 0 < ∑ x, m x)
    (hsymm : ∀ F G : (c.Half → Y) → ℝ, c.form π F G = c.form π G F)
    (hplus : ∀ F : (c.Half → Y) → ℝ, c.form π F 1 = ∑ x, m x * F x)
    {κ : ℝ} (hκ : CentredNormLe c π m κ) :
    c.Positive (κ • (c.diagonalLaw m - indepLaw c m) - (π - indepLaw c m)) ∧
      c.Positive (κ • (c.diagonalLaw m - indepLaw c m) + (π - indepLaw c m)) := by
  constructor
  · have h := below_centred_interpolation c hm hmpos hsymm hplus hκ
    unfold ReflectionCut.Below at h
    have e : κ • (c.diagonalLaw m - indepLaw c m) - (π - indepLaw c m) =
        (1 - κ) • indepLaw c m + κ • c.diagonalLaw m - π := by
      apply LinearMap.ext
      intro f
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact h
  · -- (P3) for `π̃ = 2J(m) - π`
    set π' := (2 : ℝ) • indepLaw c m - π with hπ'
    have hS : ∑ x, m x ≠ 0 := ne_of_gt hmpos
    have hform' : ∀ F G, c.form π' F G =
        2 * ((∑ x, m x * F x) * (∑ y, m y * G y) / ∑ x, m x) - c.form π F G := by
      intro F G
      change 2 * c.form (indepLaw c m) F G - c.form π F G = _
      rw [form_indepLaw]
    have hsymm' : ∀ F G : (c.Half → Y) → ℝ, c.form π' F G = c.form π' G F := by
      intro F G
      rw [hform', hform', hsymm]
      ring
    have hplus' : ∀ F : (c.Half → Y) → ℝ, c.form π' F 1 = ∑ x, m x * F x := by
      intro F
      rw [hform', hplus]
      simp only [Pi.one_apply, mul_one]
      field_simp
      ring
    have hκ' : CentredNormLe c π' m κ := by
      intro f g
      rw [hform']
      have := hκ f g
      rw [show 2 * ((∑ x, m x * f x) * (∑ y, m y * g y) / ∑ x, m x) - c.form π f g -
          (∑ x, m x * f x) * (∑ y, m y * g y) / ∑ x, m x =
          -(c.form π f g - (∑ x, m x * f x) * (∑ y, m y * g y) / ∑ x, m x) by ring, abs_neg]
      exact this
    have h := below_centred_interpolation c hm hmpos hsymm' hplus' hκ'
    unfold ReflectionCut.Below at h
    have e : κ • (c.diagonalLaw m - indepLaw c m) + (π - indepLaw c m) =
        (1 - κ) • indepLaw c m + κ • c.diagonalLaw m - π' := by
      apply LinearMap.ext
      intro f
      simp only [hπ', LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul]
      ring
    rw [e]
    exact h

end Orders

section WeightOrders

variable {W Y : Type*} [Fintype W] [DecidableEq W] [Fintype Y] [DecidableEq Y]

/-- **The Markov operator of a positive coupling is a contraction**: for a nonnegative weight
`w`, symmetric at `c`, with both half marginals `m'`, `Diag(m') ± w ⪰_c 0`. -/
theorem diag_pm_of_weight (c : ReflectionCut W) {w : (W → Y) → ℝ} (hw : ∀ z, 0 ≤ w z)
    {m' : (c.Half → Y) → ℝ} (hp : plusMarginal c w = m') (hn : minusMarginal c w = m')
    (hsymm : ∀ F G : (c.Half → Y) → ℝ,
      c.form (signedIntegral w) F G = c.form (signedIntegral w) G F) :
    c.Positive (c.diagonalLaw m' + signedIntegral w) ∧
      c.Positive (c.diagonalLaw m' - signedIntegral w) := by
  have hbr := bracket_diagonal_marginals c hw
  rw [hp, hn] at hbr
  have hDs : ∀ F G : (c.Half → Y) → ℝ,
      c.form (c.diagonalLaw m') F G = c.form (c.diagonalLaw m') G F := by
    intro F G
    rw [c.form_diagonalLaw, c.form_diagonalLaw]
    exact sum_congr rfl fun x _ => by ring
  constructor
  · constructor
    · intro F G
      change c.form (c.diagonalLaw m') F G + c.form (signedIntegral w) F G =
        c.form (c.diagonalLaw m') G F + c.form (signedIntegral w) G F
      rw [hDs, hsymm]
    · intro F
      change 0 ≤ c.form (c.diagonalLaw m') F F + c.form (signedIntegral w) F F
      have := hbr.nonneg F F
      linarith
  · constructor
    · intro F G
      change c.form (c.diagonalLaw m') F G - c.form (signedIntegral w) F G =
        c.form (c.diagonalLaw m') G F - c.form (signedIntegral w) G F
      rw [hDs, hsymm]
    · intro F
      change 0 ≤ c.form (c.diagonalLaw m') F F - c.form (signedIntegral w) F F
      have := hbr.nonneg F (-F)
      have e : c.form (signedIntegral w) F (-F) = -c.form (signedIntegral w) F F := by
        change signedIntegral w _ = -signedIntegral w _
        rw [← map_neg]
        congr 1
        funext z
        simp
      have e2 : c.form (c.diagonalLaw m') (-F) (-F) = c.form (c.diagonalLaw m') F F := by
        rw [c.form_diagonalLaw, c.form_diagonalLaw]
        exact sum_congr rfl fun x _ => by simp
      rw [e, e2] at this
      linarith

end WeightOrders

section Energy

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- The energy with laws `a` at `j₀` and `b` at `j₁` and the outside laws `O` elsewhere. -/
noncomputable abbrev energyAt₂ (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ j₁ : J)
    (a : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) (b : ((V → X j₁) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ i, X i) → ℝ) : ℝ :=
  diagonalIntegral (tensorLaw (Function.update (Function.update O j₀ a) j₁ b)) F

theorem energyAt₂_eq (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) {j₀ j₁ : J} (hne : j₀ ≠ j₁)
    (a : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) (b : ((V → X j₁) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ i, X i) → ℝ) :
    energyAt₂ O j₀ j₁ a b F = energyAt (Function.update O j₁ b) j₀ a F := by
  unfold energyAt₂ energyAt
  rw [Function.update_comm hne]

/-- **(P3′) of `lem:energy-toolkit`, energy form**: for `π` at `j₀` as in (P3) (symmetric, half
marginal `m`, `‖T - 𝒥‖ ≤ κ`) and a nonnegative weight `π' = w'` at `j₁ ≠ j₀`, symmetric with both
half marginals `m'`, and outside factors positive at `c`:
`Y[π ⊗ π'] ≤ (1 - κ) Y[J(m) ⊗ Diag(m')] + κ Y[Diag(m) ⊗ Diag(m')]`. -/
theorem energy_le_product_interpolation (c : ReflectionCut V)
    (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) {j₀ j₁ : J} (hne : j₀ ≠ j₁)
    (hO : ∀ j, j ≠ j₀ → j ≠ j₁ → c.Positive (O j)) (F : (∀ i, X i) → ℝ)
    {π : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ} {m : (c.Half → X j₀) → ℝ} (hm : ∀ x, 0 ≤ m x)
    (hmpos : 0 < ∑ x, m x) (hsymm : ∀ G H : (c.Half → X j₀) → ℝ, c.form π G H = c.form π H G)
    (hplus : ∀ G : (c.Half → X j₀) → ℝ, c.form π G 1 = ∑ x, m x * G x)
    {κ : ℝ} (hκ : CentredNormLe c π m κ)
    {w' : (V → X j₁) → ℝ} (hw' : ∀ z, 0 ≤ w' z) {m' : (c.Half → X j₁) → ℝ}
    (hp' : plusMarginal c w' = m') (hn' : minusMarginal c w' = m')
    (hsymm' : ∀ G H : (c.Half → X j₁) → ℝ,
      c.form (signedIntegral w') G H = c.form (signedIntegral w') H G) :
    energyAt₂ O j₀ j₁ π (signedIntegral w') F ≤
      (1 - κ) * energyAt₂ O j₀ j₁ (indepLaw c m) (c.diagonalLaw m') F +
        κ * energyAt₂ O j₀ j₁ (c.diagonalLaw m) (c.diagonalLaw m') F := by
  obtain ⟨hA1, hA2⟩ := centred_pm c hm hmpos hsymm hplus hκ
  obtain ⟨hC1, hC2⟩ := diag_pm_of_weight c hw' hp' hn' hsymm'
  set A := κ • (c.diagonalLaw m - indepLaw c m)
  set B := π - indepLaw c m
  set Kf := Function.update (Function.update O j₀ A) j₁ (c.diagonalLaw m')
  set Zf := Function.update (Function.update O j₀ B) j₁ (signedIntegral w')
  -- the `±` tensorization
  have hpm : |diagonalIntegral (tensorLaw Zf) F| ≤ diagonalIntegral (tensorLaw Kf) F := by
    apply abs_energy_le_of_add_sub
    · intro j
      by_cases h1 : j = j₁
      · subst h1
        simp only [Kf, Zf, Function.update_self]
        exact hC1
      · by_cases h0 : j = j₀
        · subst h0
          simp only [Kf, Zf, Function.update_of_ne h1, Function.update_self]
          exact hA2
        · simp only [Kf, Zf, Function.update_of_ne h1, Function.update_of_ne h0]
          exact (hO j h0 h1).add (hO j h0 h1)
    · intro j
      by_cases h1 : j = j₁
      · subst h1
        simp only [Kf, Zf, Function.update_self]
        exact hC2
      · by_cases h0 : j = j₀
        · subst h0
          simp only [Kf, Zf, Function.update_of_ne h1, Function.update_self]
          exact hA1
        · simp only [Kf, Zf, Function.update_of_ne h1, Function.update_of_ne h0, sub_self]
          exact positive_zero c
  -- linearity in the factor `j₀`
  have eZ : diagonalIntegral (tensorLaw Zf) F =
      energyAt₂ O j₀ j₁ π (signedIntegral w') F -
        energyAt₂ O j₀ j₁ (indepLaw c m) (signedIntegral w') F := by
    change energyAt₂ O j₀ j₁ B (signedIntegral w') F = _
    rw [energyAt₂_eq O hne, energyAt₂_eq O hne, energyAt₂_eq O hne, energyAt_sub]
  have eK : diagonalIntegral (tensorLaw Kf) F =
      κ * (energyAt₂ O j₀ j₁ (c.diagonalLaw m) (c.diagonalLaw m') F -
        energyAt₂ O j₀ j₁ (indepLaw c m) (c.diagonalLaw m') F) := by
    change energyAt₂ O j₀ j₁ A (c.diagonalLaw m') F = _
    rw [energyAt₂_eq O hne, energyAt₂_eq O hne, energyAt₂_eq O hne, energyAt_smul,
      energyAt_sub]
  -- (E2) at `j₁`: `Y[J(m) ⊗ π'] ≤ Y[J(m) ⊗ Diag(m')]`
  have hE2 : energyAt₂ O j₀ j₁ (indepLaw c m) (signedIntegral w') F ≤
      energyAt₂ O j₀ j₁ (indepLaw c m) (c.diagonalLaw m') F := by
    unfold energyAt₂
    apply energy_le_of_below_factor c (Function.update O j₀ (indepLaw c m)) j₁
    · intro j hj
      by_cases h0 : j = j₀
      · subst h0
        rw [Function.update_self]
        exact positive_indepLaw c hm
      · rw [Function.update_of_ne h0]
        exact hO j h0 hj
    · exact hC2
  rw [eZ, eK] at hpm
  have := le_abs_self (energyAt₂ O j₀ j₁ π (signedIntegral w') F -
    energyAt₂ O j₀ j₁ (indepLaw c m) (signedIntegral w') F)
  nlinarith

end Energy

end Sarkozy.Variance
