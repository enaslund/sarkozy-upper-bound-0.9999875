module

public import Sarkozy.Variance.ProductInterpolation
public import Sarkozy.RecordExpansion.SubsetExpansion
public import Sarkozy.Variance.Background

/-!
# The exterior expansion and (P3′) over a set of blocks (`prop:background-variance`(a))

`paper/sections/22_variance.tex`, proof of `prop:background-variance`(a), "Exterior expansion"
and "A background term", and `lem:energy-toolkit`(P3′) for a background set `Z` of several
blocks (several factors of the product law). A set of factors is given by its indicator
`g : J → Bool` (as in WP-R's `SubsetExpansion`), the selected factor `j₀` not in it.

* `energy_le_of_orders`: `0 ⪯ Q_b ⪯ P_b` at every factor gives `Y[⊗Q] ≤ Y[⊗P]` (expansion of
  `⊗(Q + (P - Q))`, all terms nonnegative).
* `energy_le_product_interpolation_set`: **(P3′) for `Z` a set of factors**: with `π` at `j₀` as
  in (P3) and nonnegative symmetric weights `π'_b` with both half marginals `m'_b` on `Z`,
  `Y[π ⊗ ⊗_Z π'] ≤ (1 - κ) Y[J(m) ⊗ ⊗_Z Diag(m')] + κ Y[Diag(m) ⊗ ⊗_Z Diag(m')]`.
* `exterior_expansion_ge`: **the exterior expansion**: if the exterior law is `μ_b + R_b` off
  `j₀` with `R_b ⪰_ι coef_b D_b ⪰ 0` (for the matching diagonals of `E_add`:
  `(Ñ₀ - μ)_𝔅 ⪰ v_D r_𝔅² (1 + h_𝔅)⁻¹ D_{E_s,𝔅}`, `lem:record:gram`(i) and
  `def:record:frame`(b), hypotheses), then for every family `𝒵` of sets `Z ∌ j₀` of factors
  (the kept terms),
  `Y^{μ+R}[κ] ≥ ∑_{Z∈𝒵} (∏_{𝔅∈Z} coef_𝔅) Y[κ ⊗ D_Z]`, `μ` outside `{j₀} ∪ Z`.
* `background_term_set`: **a background term** of `prop:background-variance`(a) for a background
  set `Z` of several blocks: `½ ∑_s Y[J(m_s) ⊗ D_{Z,s}] ≥ (C_m p_E(m,r) - z) Y`, from (P3′) over
  `Z` (proved here), (E1) and `lem:record:paired-e-joint`(b) for `X ∪ Z` (hypotheses).

With `background_selected` (the term `Z = ∅`), `background_assembly` (the sum over the kept
terms with the choice weights) and `class_cost_of_product_energy`, these are the steps of the
proof of `prop:background-variance`(a).
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- A product law with a zero factor has zero energy. -/
theorem energy_eq_zero_of_zero_factor (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₁ : J)
    (h : L j₁ = 0) (F : (∀ b, X b) → ℝ) : diagonalIntegral (tensorLaw L) F = 0 := by
  have hL : L = Function.update L j₁ ((0 : ℝ) • (0 : ((V → X j₁) → ℝ) →ₗ[ℝ] ℝ)) := by
    rw [zero_smul, ← h, Function.update_eq_self]
  rw [hL, tensorLaw_update_smul, zero_smul]
  rfl

/-- The energy of a product of positive factors is nonnegative. -/
theorem energy_nonneg_of_positive (c : ReflectionCut V) {L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ}
    (hL : ∀ j, c.Positive (L j)) (F : (∀ b, X b) → ℝ) : 0 ≤ diagonalIntegral (tensorLaw L) F :=
  (ReflectionCut.Positive.tensor hL).diagonal_nonneg F

/-- **Monotonicity under positive orders**: `0 ⪯_c Q_b ⪯_c P_b` at every factor gives
`Y[⊗Q] ≤ Y[⊗P]`. -/
theorem energy_le_of_orders (c : ReflectionCut V) (P Q : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hQ : ∀ j, c.Positive (Q j)) (hPQ : ∀ j, c.Positive (P j - Q j)) (F : (∀ b, X b) → ℝ) :
    diagonalIntegral (tensorLaw Q) F ≤ diagonalIntegral (tensorLaw P) F := by
  have h := energy_add_eq_sum Q (fun b => P b - Q b) F
  have e : (fun b => Q b + (P b - Q b)) = P := by
    funext b
    abel
  rw [e] at h
  rw [h]
  have hnn : ∀ f : J → Bool, 0 ≤ diagonalIntegral
      (tensorLaw fun b => if f b then P b - Q b else Q b) F := by
    intro f
    apply energy_nonneg_of_positive c
    intro b
    by_cases hb : f b
    · simp only [hb, ↓reduceIte]
      exact hPQ b
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact hQ b
  have h0 : diagonalIntegral (tensorLaw Q) F =
      diagonalIntegral (tensorLaw fun b => if (fun _ => false : J → Bool) b then P b - Q b
        else Q b) F := by
    simp
  rw [h0]
  exact single_le_sum (fun f _ => hnn f) (mem_univ _)

/-- **(P3′) of `lem:energy-toolkit` for a set `Z = {b : g b}` of factors**, energy form: `π` at
`j₀ ∉ Z` symmetric with half marginal `m` and `‖T - 𝒥‖ ≤ κ`; on `Z` nonnegative symmetric
weights `w'_b` with both half marginals `m'_b`; positive outside factors. Then
`Y[π ⊗ ⊗_Z w'] ≤ (1 - κ) Y[J(m) ⊗ ⊗_Z Diag(m')] + κ Y[Diag(m) ⊗ ⊗_Z Diag(m')]`. -/
theorem energy_le_product_interpolation_set (c : ReflectionCut V)
    (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J) (g : J → Bool) (hg : g j₀ = false)
    (hO : ∀ j, j ≠ j₀ → g j = false → c.Positive (O j)) (F : (∀ b, X b) → ℝ)
    {π : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ} {m : (c.Half → X j₀) → ℝ} (hm : ∀ x, 0 ≤ m x)
    (hmpos : 0 < ∑ x, m x) (hsymm : ∀ G H : (c.Half → X j₀) → ℝ, c.form π G H = c.form π H G)
    (hplus : ∀ G : (c.Half → X j₀) → ℝ, c.form π G 1 = ∑ x, m x * G x)
    {κ : ℝ} (hκ : CentredNormLe c π m κ)
    (w' : ∀ j, (V → X j) → ℝ) (hw' : ∀ j, g j = true → ∀ z, 0 ≤ w' j z)
    (m' : ∀ j, (c.Half → X j) → ℝ)
    (hp' : ∀ j, g j = true → plusMarginal c (w' j) = m' j)
    (hn' : ∀ j, g j = true → minusMarginal c (w' j) = m' j)
    (hsymm' : ∀ j, g j = true → ∀ G H : (c.Half → X j) → ℝ,
      c.form (signedIntegral (w' j)) G H = c.form (signedIntegral (w' j)) H G) :
    energyAt (fun b => if g b then signedIntegral (w' b) else O b) j₀ π F ≤
      (1 - κ) * energyAt (fun b => if g b then c.diagonalLaw (m' b) else O b) j₀
          (indepLaw c m) F +
        κ * energyAt (fun b => if g b then c.diagonalLaw (m' b) else O b) j₀
          (c.diagonalLaw m) F := by
  obtain ⟨hA1, hA2⟩ := centred_pm c hm hmpos hsymm hplus hκ
  set base' : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ := fun b => if g b then signedIntegral (w' b) else O b
  set baseD : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ := fun b => if g b then c.diagonalLaw (m' b) else O b
  -- the `±` conditions off `j₀`
  have hoff : ∀ j, j ≠ j₀ → c.Positive (baseD j + base' j) ∧ c.Positive (baseD j - base' j) := by
    intro j hj
    by_cases hgj : g j = true
    · simp only [baseD, base', hgj, ↓reduceIte]
      exact diag_pm_of_weight c (hw' j hgj) (hp' j hgj) (hn' j hgj) (hsymm' j hgj)
    · have hgf : g j = false := by simpa using hgj
      simp only [baseD, base', hgf, Bool.false_eq_true, ↓reduceIte, sub_self]
      exact ⟨(hO j hj hgf).add (hO j hj hgf), positive_zero c⟩
  -- (1) the `±` tensorization for `Δ = π - J(m)`
  have h1 : |energyAt base' j₀ (π - indepLaw c m) F| ≤
      energyAt baseD j₀ (κ • (c.diagonalLaw m - indepLaw c m)) F := by
    apply abs_energy_le_of_add_sub
    · intro j
      by_cases hj : j = j₀
      · subst hj
        simp only [Function.update_self]
        exact hA2
      · simp only [Function.update_of_ne hj]
        exact (hoff j hj).1
    · intro j
      by_cases hj : j = j₀
      · subst hj
        simp only [Function.update_self]
        exact hA1
      · simp only [Function.update_of_ne hj]
        exact (hoff j hj).2
  -- (2) the same for `J(m)` at `j₀`: `Y[J ⊗ ⊗π'] ≤ Y[J ⊗ ⊗Diag(m')]`
  have h2 : |energyAt base' j₀ (indepLaw c m) F| ≤ energyAt baseD j₀ (indepLaw c m) F := by
    apply abs_energy_le_of_add_sub
    · intro j
      by_cases hj : j = j₀
      · subst hj
        simp only [Function.update_self]
        exact (positive_indepLaw c hm).add (positive_indepLaw c hm)
      · simp only [Function.update_of_ne hj]
        exact (hoff j hj).1
    · intro j
      by_cases hj : j = j₀
      · subst hj
        simp only [Function.update_self, sub_self]
        exact positive_zero c
      · simp only [Function.update_of_ne hj]
        exact (hoff j hj).2
  have e1 : energyAt base' j₀ π F =
      energyAt base' j₀ (indepLaw c m) F + energyAt base' j₀ (π - indepLaw c m) F := by
    rw [energyAt_sub]
    ring
  have e2 : energyAt baseD j₀ (κ • (c.diagonalLaw m - indepLaw c m)) F =
      κ * (energyAt baseD j₀ (c.diagonalLaw m) F - energyAt baseD j₀ (indepLaw c m) F) := by
    rw [energyAt_smul, energyAt_sub]
  rw [e2] at h1
  rw [e1]
  have := le_abs_self (energyAt base' j₀ (π - indepLaw c m) F)
  have := le_abs_self (energyAt base' j₀ (indepLaw c m) F)
  nlinarith

/-- **The exterior expansion** of `prop:background-variance`(a): off `j₀` the exterior law is
`μ_b + R_b` with `μ_b ⪰ 0`, `D_b ⪰ 0` and `R_b ⪰ coef_b D_b` (`coef_b ≥ 0`); at `j₀` a positive
`κ`. For every finite family `𝒵` of sets `Z` (indicators) not containing `j₀`,
`∑_{Z∈𝒵} (∏_{b∈Z} coef_b) Y[κ ⊗ D_Z ⊗ μ_{-({j₀}∪Z)}] ≤ Y[κ ⊗ (μ + R)_{-j₀}]`. -/
theorem exterior_expansion_ge (c : ReflectionCut V) (μ R D : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (j₀ : J) {κ : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ} (hκ : c.Positive κ)
    (hμ : ∀ j, j ≠ j₀ → c.Positive (μ j)) (hD : ∀ j, j ≠ j₀ → c.Positive (D j))
    (coef : J → ℝ) (hcoef : ∀ j, 0 ≤ coef j)
    (hR : ∀ j, j ≠ j₀ → c.Positive (R j - coef j • D j))
    (Zs : Finset (J → Bool)) (hZs : ∀ g ∈ Zs, g j₀ = false) (F : (∀ b, X b) → ℝ) :
    ∑ g ∈ Zs, (∏ b, (if g b then coef b else 1)) *
        energyAt (fun b => if g b then D b else μ b) j₀ κ F ≤
      energyAt (fun b => μ b + R b) j₀ κ F := by
  set A := Function.update μ j₀ κ with hA
  set R' := Function.update R j₀ 0 with hR'
  have hsplit : Function.update (fun b => μ b + R b) j₀ κ = fun b => A b + R' b := by
    funext b
    by_cases hb : b = j₀
    · subst hb
      simp [A, R']
    · simp [A, R', Function.update_of_ne hb]
  have hRpos : ∀ j, j ≠ j₀ → c.Positive (R j) := by
    intro j hj
    have h := (hR j hj).add ((hD j hj).smul (hcoef j))
    rwa [sub_add_cancel] at h
  have hApos : ∀ j, c.Positive (A j) := by
    intro j
    by_cases hj : j = j₀
    · subst hj
      simp only [A, Function.update_self]
      exact hκ
    · simp only [A, Function.update_of_ne hj]
      exact hμ j hj
  -- every term of the expansion is nonnegative
  have hterm_nn : ∀ f : J → Bool, 0 ≤ diagonalIntegral
      (tensorLaw fun b => if f b then R' b else A b) F := by
    intro f
    by_cases hf : f j₀ = true
    · rw [energy_eq_zero_of_zero_factor _ j₀ (by simp [hf, R'])]
    · apply energy_nonneg_of_positive c
      intro b
      by_cases hb : f b = true
      · have hbj : b ≠ j₀ := fun h => hf (h ▸ hb)
        simp only [hb, ↓reduceIte, R', Function.update_of_ne hbj]
        exact hRpos b hbj
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact hApos b
  -- each kept term dominates its `D` version
  have hkept : ∀ g ∈ Zs, (∏ b, (if g b then coef b else 1)) *
      energyAt (fun b => if g b then D b else μ b) j₀ κ F ≤
      diagonalIntegral (tensorLaw fun b => if g b then R' b else A b) F := by
    intro g hg
    have hg0 := hZs g hg
    have hfam : Function.update (fun b => if g b then D b else μ b) j₀ κ =
        fun b => if g b then D b else A b := by
      funext b
      by_cases hb : b = j₀
      · subst hb
        simp [hg0, A]
      · simp [A, Function.update_of_ne hb]
    have hsm : (fun b => (if g b then coef b else 1) • (if g b then D b else A b)) =
        fun b => if g b then coef b • D b else A b := by
      funext b
      by_cases hb : g b = true <;> simp [hb]
    have hmono := energy_le_of_orders c (fun b => if g b then R' b else A b)
      (fun b => if g b then coef b • D b else A b)
      (fun b => by
        by_cases hb : g b = true
        · have hbj : b ≠ j₀ := fun h => by rw [h, hg0] at hb; exact Bool.false_ne_true hb
          simp only [hb, ↓reduceIte]
          exact (hD b hbj).smul (hcoef b)
        · simp only [hb, Bool.false_eq_true, ↓reduceIte]
          exact hApos b)
      (fun b => by
        by_cases hb : g b = true
        · have hbj : b ≠ j₀ := fun h => by rw [h, hg0] at hb; exact Bool.false_ne_true hb
          simp only [hb, ↓reduceIte, R', Function.update_of_ne hbj]
          exact hR b hbj
        · simp only [hb, Bool.false_eq_true, ↓reduceIte, sub_self]
          exact positive_zero c) F
    rw [← hsm, tensorLaw_smul] at hmono
    unfold energyAt
    rw [hfam]
    refine le_trans (le_of_eq ?_) hmono
    simp only [diagonalIntegral, multilinearIntegral, LinearMap.smul_apply, smul_eq_mul]
  calc ∑ g ∈ Zs, (∏ b, (if g b then coef b else 1)) *
        energyAt (fun b => if g b then D b else μ b) j₀ κ F
      ≤ ∑ g ∈ Zs, diagonalIntegral (tensorLaw fun b => if g b then R' b else A b) F :=
        sum_le_sum hkept
    _ ≤ ∑ g : J → Bool, diagonalIntegral (tensorLaw fun b => if g b then R' b else A b) F :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun g _ _ => hterm_nn g)
    _ = energyAt (fun b => μ b + R b) j₀ κ F := by
        unfold energyAt
        rw [hsplit, energy_add_eq_sum]

end Sarkozy.Variance

namespace Sarkozy.Variance

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- **`prop:background-variance`(a), a background term, for a background set `Z` of several
blocks** (`Z = {b : g b}`, `j₀ ∉ Z`): the aligned embeddings `E_s` of `X` (factor `j₀`) are as in
(P3) with centred norm `≤ k`, those of `Z` are nonnegative symmetric weights `w_s b` with both
half marginals `m'_s b` (so `D_{Z,s} = ⊗_Z Diag(m'_s)`); with `lem:record:paired-e-joint`(b)
for `X ∪ Z` (hypothesis `hb`) and (E1) for `Diag(m_s) ⊗ D_{Z,s}` (hypotheses `hD0`, `hD1`):
`½ ∑_s Y[J(m_s) ⊗ D_{Z,s}] ≥ (C_m p_E(m,r) - (e + k z₂ C_m C_r)/(1 - k)) Y`. -/
theorem background_term_set (ι : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (g : J → Bool) (hg : g j₀ = false) (hO : ∀ j, j ≠ j₀ → g j = false → ι.Positive (O j))
    (F : (∀ b, X b) → ℝ)
    {E0 E1 : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ} {m0 m1 : (ι.Half → X j₀) → ℝ}
    (hm0 : ∀ x, 0 ≤ m0 x) (hm1 : ∀ x, 0 ≤ m1 x) (hm0p : 0 < ∑ x, m0 x) (hm1p : 0 < ∑ x, m1 x)
    (hs0 : ∀ G H : (ι.Half → X j₀) → ℝ, ι.form E0 G H = ι.form E0 H G)
    (hs1 : ∀ G H : (ι.Half → X j₀) → ℝ, ι.form E1 G H = ι.form E1 H G)
    (hp0 : ∀ G : (ι.Half → X j₀) → ℝ, ι.form E0 G 1 = ∑ x, m0 x * G x)
    (hp1 : ∀ G : (ι.Half → X j₀) → ℝ, ι.form E1 G 1 = ∑ x, m1 x * G x)
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hcen0 : CentredNormLe ι E0 m0 k) (hcen1 : CentredNormLe ι E1 m1 k)
    (w0 w1 : ∀ j, (V → X j) → ℝ) (hw0 : ∀ j, g j = true → ∀ z, 0 ≤ w0 j z)
    (hw1 : ∀ j, g j = true → ∀ z, 0 ≤ w1 j z) (m0' m1' : ∀ j, (ι.Half → X j) → ℝ)
    (hq0 : ∀ j, g j = true → plusMarginal ι (w0 j) = m0' j)
    (hr0 : ∀ j, g j = true → minusMarginal ι (w0 j) = m0' j)
    (hq1 : ∀ j, g j = true → plusMarginal ι (w1 j) = m1' j)
    (hr1 : ∀ j, g j = true → minusMarginal ι (w1 j) = m1' j)
    (ht0 : ∀ j, g j = true → ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (w0 j)) G H = ι.form (signedIntegral (w0 j)) H G)
    (ht1 : ∀ j, g j = true → ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (w1 j)) G H = ι.form (signedIntegral (w1 j)) H G)
    {Yμ ℓ Cm Cr CXZ η e z₂ : ℝ} (hY : 0 ≤ Yμ) (hCm : 0 < Cm) (hCr : 0 ≤ Cr) (hz₂ : 0 ≤ z₂)
    (he : 0 ≤ e) (hCXZ : CXZ ≤ Cm * Cr)
    (hD0 : energyAt (fun b => if g b then ι.diagonalLaw (m0' b) else O b) j₀
      (ι.diagonalLaw m0) F ≤ (1 + z₂) * CXZ * Yμ)
    (hD1 : energyAt (fun b => if g b then ι.diagonalLaw (m1' b) else O b) j₀
      (ι.diagonalLaw m1) F ≤ (1 + z₂) * CXZ * Yμ)
    (hb : (ℓ - Cm * Cr * η - e) * Yμ ≤
      (energyAt (fun b => if g b then signedIntegral (w0 b) else O b) j₀ E0 F +
        energyAt (fun b => if g b then signedIntegral (w1 b) else O b) j₀ E1 F) / 2) :
    (Cm * (max 0 (ℓ / Cm - Cr * (η + k)) / (1 - k)) - (e + k * z₂ * Cm * Cr) / (1 - k)) * Yμ ≤
      (energyAt (fun b => if g b then ι.diagonalLaw (m0' b) else O b) j₀ (indepLaw ι m0) F +
        energyAt (fun b => if g b then ι.diagonalLaw (m1' b) else O b) j₀
          (indepLaw ι m1) F) / 2 := by
  have hP0 := energy_le_product_interpolation_set ι O j₀ g hg hO F hm0 hm0p hs0 hp0 hcen0
    w0 hw0 m0' hq0 hr0 ht0
  have hP1 := energy_le_product_interpolation_set ι O j₀ g hg hO F hm1 hm1p hs1 hp1 hcen1
    w1 hw1 m1' hq1 hr1 ht1
  have hpos : ∀ (m' : ∀ j, (ι.Half → X j) → ℝ) (w : ∀ j, (V → X j) → ℝ),
      (∀ j, g j = true → ∀ z, 0 ≤ w j z) → (∀ j, g j = true → plusMarginal ι (w j) = m' j) →
      ∀ j, j ≠ j₀ → ι.Positive ((fun b => if g b then ι.diagonalLaw (m' b) else O b) j) := by
    intro m' w hw hq j hj
    by_cases hgj : g j = true
    · simp only [hgj, ↓reduceIte]
      exact ι.diagonalLaw_positive fun x => hq j hgj ▸ plusMarginal_nonneg ι (hw j hgj) x
    · have hgf : g j = false := by simpa using hgj
      simp only [hgf, Bool.false_eq_true, ↓reduceIte]
      exact hO j hj hgf
  have hT0 := energy_indepLaw_nonneg ι _ j₀ (hpos m0' w0 hw0 hq0) hm0 F
  have hT1 := energy_indepLaw_nonneg ι _ j₀ (hpos m1' w1 hw1 hq1) hm1 F
  exact background_term hk0 hk1 hY hCm hCr hz₂ he hCXZ hT0 hT1 hP0 hP1 hD0 hD1 hb

end Sarkozy.Variance
