module

public import Sarkozy.Variance.BackgroundVariance
public import Sarkozy.Variance.ProductInterpolationBlocks

/-!
# Positive backgrounds with each block its own factor (`prop:background-variance`(a))

`paper/sections/22_variance.tex`, proof of `prop:background-variance`(a), with the selected set
`X` and every background set `Z` taken as sets of factors (`Xs`, `indSet g`).

* `exterior_expansion_ge_blocks`: the exterior expansion. Off `X` the exterior law is `μ + R`,
  with `R_𝔅 ⪰ c_𝔅 Diag(m'_𝔅)`; on `X` the products `J(m_𝔅)`. For every family `𝒵` of kept sets
  `Z` disjoint from `X`, `∑_{Z∈𝒵} (∏_Z c_𝔅) Y[J_X ⊗ D_Z ⊗ μ] ≤ Y[J_X ⊗ (μ + R)]`.
* `background_selected_blocks`: the selected term,
  `½ ∑_s Y[J_{X,s} ⊗ μ] ≥ (C_m [b_E(m)]_+ - z) Y`, by (P3) with (P4) for the aligned embeddings
  (`energy_le_product_records`) and `lem:record:paired-e-joint`(b) (hypothesis). Since
  `Y[J_s] ≥ 0`, the positive part of `b_E(m)` may be taken.
* `background_term_blocks`: a background term for a kept set `Z`,
  `½ ∑_s Y[J_{X,s} ⊗ D_{Z,s} ⊗ μ] ≥ (C_m p_E(m,r) - z) Y`, by (P3′) with (P4)
  (`energy_le_product_interpolation_blocks`).
* `background_variance_a_blocks`: **the displayed bound of (a)**, assembled
  (`background_assembly`).
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- The set of factors of an indicator. -/
def indSet (g : J → Bool) : Finset J := univ.filter fun b => g b = true

omit [DecidableEq J] in
theorem mem_indSet {g : J → Bool} {b : J} : b ∈ indSet g ↔ g b = true := by
  simp [indSet]

/-- **The exterior expansion, blocks as factors.** -/
theorem exterior_expansion_ge_blocks (c : ReflectionCut V) (μ R : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs : Finset J) (m m' : ∀ j, (c.Half → X j) → ℝ) (hm : ∀ j ∈ Xs, ∀ x, 0 ≤ m j x)
    (hm' : ∀ j, j ∉ Xs → ∀ x, 0 ≤ m' j x) (hμ : ∀ j, j ∉ Xs → c.Positive (μ j))
    (coef : J → ℝ) (hcoef : ∀ j, 0 ≤ coef j)
    (hR : ∀ j, j ∉ Xs → c.Positive (R j - coef j • c.diagonalLaw (m' j)))
    (Zs : Finset (J → Bool)) (hZs : ∀ g ∈ Zs, ∀ j ∈ Xs, g j = false) (F : (∀ b, X b) → ℝ) :
    ∑ g ∈ Zs, setCoeff coef g *
        diagonalIntegral (tensorLaw (diagFamZ c μ Xs (indSet g) ∅ m m')) F ≤
      diagonalIntegral (tensorLaw fun b => if b ∈ Xs then indepLaw c (m b) else μ b + R b) F := by
  obtain ⟨A, hA⟩ : ∃ A : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ,
      A = fun b => if b ∈ Xs then indepLaw c (m b) else μ b := ⟨_, rfl⟩
  obtain ⟨R', hR'⟩ : ∃ R' : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ,
      R' = fun b => if b ∈ Xs then 0 else R b := ⟨_, rfl⟩
  have hsplit : (fun b => if b ∈ Xs then indepLaw c (m b) else μ b + R b) =
      fun b => A b + R' b := by
    funext b
    by_cases hb : b ∈ Xs
    · simp [hA, hR', hb]
    · simp [hA, hR', hb]
  have hRpos : ∀ j, j ∉ Xs → c.Positive (R j) := by
    intro j hj
    have h := (hR j hj).add ((c.diagonalLaw_positive (hm' j hj)).smul (hcoef j))
    rwa [sub_add_cancel] at h
  have hApos : ∀ j, c.Positive (A j) := by
    intro j
    by_cases hj : j ∈ Xs
    · simp only [hA, hj, ↓reduceIte]
      exact positive_indepLaw c (hm j hj)
    · simp only [hA, hj, ↓reduceIte]
      exact hμ j hj
  have hterm_nn : ∀ f : J → Bool, 0 ≤ diagonalIntegral
      (tensorLaw fun b => if f b then R' b else A b) F := by
    intro f
    by_cases hf : ∃ b ∈ Xs, f b = true
    · obtain ⟨b, hbX, hb⟩ := hf
      rw [energy_eq_zero_of_zero_factor _ b (by simp [hb, hR', hbX])]
    · push Not at hf
      apply energy_nonneg_of_positive c
      intro b
      by_cases hb : f b = true
      · have hbX : b ∉ Xs := fun h => hf b h hb
        simp only [hb, ↓reduceIte, hR', hbX]
        exact hRpos b hbX
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact hApos b
  have hkept : ∀ g ∈ Zs, setCoeff coef g *
      diagonalIntegral (tensorLaw (diagFamZ c μ Xs (indSet g) ∅ m m')) F ≤
      diagonalIntegral (tensorLaw fun b => if g b then R' b else A b) F := by
    intro g hg
    have hg0 := hZs g hg
    have hfam : diagFamZ c μ Xs (indSet g) ∅ m m' =
        fun b => if g b then c.diagonalLaw (m' b) else A b := by
      funext b
      by_cases hbX : b ∈ Xs
      · simp [diagFamZ, hA, hbX, hg0 b hbX]
      · by_cases hgb : g b = true
        · simp [diagFamZ, hbX, hgb, mem_indSet]
        · simp [diagFamZ, hA, hbX, hgb, mem_indSet]
    have hsm : (fun b => (if g b then coef b else 1) •
        (if g b then c.diagonalLaw (m' b) else A b)) =
        fun b => if g b then coef b • c.diagonalLaw (m' b) else A b := by
      funext b
      by_cases hb : g b = true <;> simp [hb]
    have hnot : ∀ b, g b = true → b ∉ Xs := fun b hb hbX => by
      rw [hg0 b hbX] at hb
      exact Bool.false_ne_true hb
    have hmono := energy_le_of_orders c (fun b => if g b then R' b else A b)
      (fun b => if g b then coef b • c.diagonalLaw (m' b) else A b)
      (fun b => by
        by_cases hb : g b = true
        · simp only [hb, ↓reduceIte]
          exact (c.diagonalLaw_positive (hm' b (hnot b hb))).smul (hcoef b)
        · simp only [hb, Bool.false_eq_true, ↓reduceIte]
          exact hApos b)
      (fun b => by
        by_cases hb : g b = true
        · simp only [hb, ↓reduceIte, hR', hnot b hb]
          exact hR b (hnot b hb)
        · simp only [hb, Bool.false_eq_true, ↓reduceIte, sub_self]
          exact positive_zero c) F
    rw [← hsm, tensorLaw_smul] at hmono
    rw [hfam]
    refine le_trans (le_of_eq ?_) hmono
    simp only [setCoeff, diagonalIntegral, multilinearIntegral, LinearMap.smul_apply, smul_eq_mul]
  calc ∑ g ∈ Zs, setCoeff coef g *
        diagonalIntegral (tensorLaw (diagFamZ c μ Xs (indSet g) ∅ m m')) F
      ≤ ∑ g ∈ Zs, diagonalIntegral (tensorLaw fun b => if g b then R' b else A b) F :=
        sum_le_sum hkept
    _ ≤ ∑ g : J → Bool, diagonalIntegral (tensorLaw fun b => if g b then R' b else A b) F :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun g _ _ => hterm_nn g)
    _ = diagonalIntegral
          (tensorLaw fun b => if b ∈ Xs then indepLaw c (m b) else μ b + R b) F := by
        rw [hsplit, energy_add_eq_sum]

/-- **The selected term, blocks as factors**: for the aligned embeddings `E^X_s = ⊗_X e_s` (with
centred norms `≤ k`), (P3) with (P4), (E1) for their diagonals and
`lem:record:paired-e-joint`(b) (`hb`) give
`½ ∑_s Y[J_{X,s} ⊗ μ] ≥ (C_m [b_E(m)]_+ - (e + k z₂ C_m)/(1 - k)) Y`. -/
theorem background_selected_blocks (ι : ReflectionCut V) (μ : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs : Finset J) (hμ : ∀ j, j ∉ Xs → ι.Positive (μ j)) (F : (∀ b, X b) → ℝ)
    (e0 e1 : ∀ j, (V → X j) → ℝ) (m0 m1 : ∀ j, (ι.Half → X j) → ℝ)
    (hw0 : ∀ j ∈ Xs, ∀ z, 0 ≤ e0 j z) (hw1 : ∀ j ∈ Xs, ∀ z, 0 ≤ e1 j z)
    (hp0 : ∀ j ∈ Xs, plusMarginal ι (e0 j) = m0 j) (hn0 : ∀ j ∈ Xs, minusMarginal ι (e0 j) = m0 j)
    (hp1 : ∀ j ∈ Xs, plusMarginal ι (e1 j) = m1 j) (hn1 : ∀ j ∈ Xs, minusMarginal ι (e1 j) = m1 j)
    (ht0 : ∀ j ∈ Xs, ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (e0 j)) G H = ι.form (signedIntegral (e0 j)) H G)
    (ht1 : ∀ j ∈ Xs, ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (e1 j)) G H = ι.form (signedIntegral (e1 j)) H G)
    (hmp0 : ∀ j ∈ Xs, 0 < ∑ x, m0 j x) (hmp1 : ∀ j ∈ Xs, 0 < ∑ x, m1 j x) (κj : J → ℝ)
    (hcen0 : ∀ j ∈ Xs, CentredNormLe ι (signedIntegral (e0 j)) (m0 j) (κj j))
    (hcen1 : ∀ j ∈ Xs, CentredNormLe ι (signedIntegral (e1 j)) (m1 j) (κj j))
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hκ : ∀ j ∈ Xs, κj j ≤ k)
    {Yμ CX Cm ℓ η e z₂ : ℝ} (hY : 0 ≤ Yμ) (hCX : CX ≤ Cm) (hCm : 0 < Cm) (hz₂ : 0 ≤ z₂)
    (he : 0 ≤ e)
    (hD0 : diagonalIntegral (tensorLaw (diagFam ι μ Xs Xs m0)) F ≤ (1 + z₂) * CX * Yμ)
    (hD1 : diagonalIntegral (tensorLaw (diagFam ι μ Xs Xs m1)) F ≤ (1 + z₂) * CX * Yμ)
    (hb : (ℓ - Cm * 1 * η - e) * Yμ ≤
      (diagonalIntegral (tensorLaw (recFam ι μ Xs Xs e0 m0)) F +
        diagonalIntegral (tensorLaw (recFam ι μ Xs Xs e1 m1)) F) / 2) :
    (Cm * (max 0 (ℓ / Cm - 1 * (η + k)) / (1 - k)) - (e + k * z₂ * Cm * 1) / (1 - k)) * Yμ ≤
      (diagonalIntegral (tensorLaw (recFam ι μ Xs ∅ e0 m0)) F +
        diagonalIntegral (tensorLaw (recFam ι μ Xs ∅ e1 m1)) F) / 2 := by
  have hm0 : ∀ j ∈ Xs, ∀ x, 0 ≤ m0 j x := fun j hj x =>
    hp0 j hj ▸ plusMarginal_nonneg ι (hw0 j hj) x
  have hm1 : ∀ j ∈ Xs, ∀ x, 0 ≤ m1 j x := fun j hj x =>
    hp1 j hj ▸ plusMarginal_nonneg ι (hw1 j hj) x
  have hP0 := energy_le_product_records ι μ Xs hμ F e0 m0 hw0 hp0 hn0 ht0 hmp0 κj hcen0 hκ
  have hP1 := energy_le_product_records ι μ Xs hμ F e1 m1 hw1 hp1 hn1 ht1 hmp1 κj hcen1 hκ
  have hT : ∀ (m : ∀ j, (ι.Half → X j) → ℝ) (w : ∀ j, (V → X j) → ℝ),
      (∀ j ∈ Xs, ∀ x, 0 ≤ m j x) →
      0 ≤ diagonalIntegral (tensorLaw (recFam ι μ Xs ∅ w m)) F := by
    intro m w hm
    apply energy_nonneg_of_positive ι
    intro j
    simp only [recFam, notMem_empty, ↓reduceIte]
    by_cases hj : j ∈ Xs
    · simp only [hj, ↓reduceIte]
      exact positive_indepLaw ι (hm j hj)
    · simp only [hj, ↓reduceIte]
      exact hμ j hj
  exact background_term hk0 hk1 hY hCm zero_le_one hz₂ he (by linarith) (hT m0 e0 hm0)
    (hT m1 e1 hm1) hP0 hP1 hD0 hD1 hb

/-- **A background term, blocks as factors**: for a kept set `Z = indSet g` disjoint from `X`,
with the records `w_s` of the blocks of `Z` (nonnegative symmetric weights with half marginals
`ms_s`), (P3′) with (P4), (E1) for `Diag_{X∪Z}` and `lem:record:paired-e-joint`(b) for `X ∪ Z`
(`hb`) give `½ ∑_s Y[J_{X,s} ⊗ D_{Z,s} ⊗ μ] ≥ (C_m p_E(m,r) - (e + k z₂ C_m C_r)/(1 - k)) Y`. -/
theorem background_term_blocks (ι : ReflectionCut V) (μ : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs Zs : Finset J) (hμ : ∀ j, j ∉ Xs → j ∉ Zs → ι.Positive (μ j)) (F : (∀ b, X b) → ℝ)
    (e0 e1 : ∀ j, (V → X j) → ℝ) (m0 m1 : ∀ j, (ι.Half → X j) → ℝ)
    (hw0 : ∀ j ∈ Xs, ∀ z, 0 ≤ e0 j z) (hw1 : ∀ j ∈ Xs, ∀ z, 0 ≤ e1 j z)
    (hp0 : ∀ j ∈ Xs, plusMarginal ι (e0 j) = m0 j) (hn0 : ∀ j ∈ Xs, minusMarginal ι (e0 j) = m0 j)
    (hp1 : ∀ j ∈ Xs, plusMarginal ι (e1 j) = m1 j) (hn1 : ∀ j ∈ Xs, minusMarginal ι (e1 j) = m1 j)
    (ht0 : ∀ j ∈ Xs, ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (e0 j)) G H = ι.form (signedIntegral (e0 j)) H G)
    (ht1 : ∀ j ∈ Xs, ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (e1 j)) G H = ι.form (signedIntegral (e1 j)) H G)
    (hmp0 : ∀ j ∈ Xs, 0 < ∑ x, m0 j x) (hmp1 : ∀ j ∈ Xs, 0 < ∑ x, m1 j x) (κj : J → ℝ)
    (hcen0 : ∀ j ∈ Xs, CentredNormLe ι (signedIntegral (e0 j)) (m0 j) (κj j))
    (hcen1 : ∀ j ∈ Xs, CentredNormLe ι (signedIntegral (e1 j)) (m1 j) (κj j))
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hκ : ∀ j ∈ Xs, κj j ≤ k)
    (w0 w1 : ∀ j, (V → X j) → ℝ) (ms0 ms1 : ∀ j, (ι.Half → X j) → ℝ)
    (hv0 : ∀ j ∈ Zs, ∀ z, 0 ≤ w0 j z) (hv1 : ∀ j ∈ Zs, ∀ z, 0 ≤ w1 j z)
    (hq0 : ∀ j ∈ Zs, plusMarginal ι (w0 j) = ms0 j)
    (hr0 : ∀ j ∈ Zs, minusMarginal ι (w0 j) = ms0 j)
    (hq1 : ∀ j ∈ Zs, plusMarginal ι (w1 j) = ms1 j)
    (hr1 : ∀ j ∈ Zs, minusMarginal ι (w1 j) = ms1 j)
    (hu0 : ∀ j ∈ Zs, ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (w0 j)) G H = ι.form (signedIntegral (w0 j)) H G)
    (hu1 : ∀ j ∈ Zs, ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (w1 j)) G H = ι.form (signedIntegral (w1 j)) H G)
    {Yμ ℓ Cm Cr CXZ η e z₂ : ℝ} (hY : 0 ≤ Yμ) (hCm : 0 < Cm) (hCr : 0 ≤ Cr) (hz₂ : 0 ≤ z₂)
    (he : 0 ≤ e) (hCXZ : CXZ ≤ Cm * Cr)
    (hD0 : diagonalIntegral (tensorLaw (diagFamZ ι μ Xs Zs Xs m0 ms0)) F ≤ (1 + z₂) * CXZ * Yμ)
    (hD1 : diagonalIntegral (tensorLaw (diagFamZ ι μ Xs Zs Xs m1 ms1)) F ≤ (1 + z₂) * CXZ * Yμ)
    (hb : (ℓ - Cm * Cr * η - e) * Yμ ≤
      (diagonalIntegral (tensorLaw (recFamZ ι μ Xs Zs Xs e0 m0 w0)) F +
        diagonalIntegral (tensorLaw (recFamZ ι μ Xs Zs Xs e1 m1 w1)) F) / 2) :
    (Cm * (max 0 (ℓ / Cm - Cr * (η + k)) / (1 - k)) - (e + k * z₂ * Cm * Cr) / (1 - k)) * Yμ ≤
      (diagonalIntegral (tensorLaw (diagFamZ ι μ Xs Zs ∅ m0 ms0)) F +
        diagonalIntegral (tensorLaw (diagFamZ ι μ Xs Zs ∅ m1 ms1)) F) / 2 := by
  have hm0 : ∀ j ∈ Xs, ∀ x, 0 ≤ m0 j x := fun j hj x =>
    hp0 j hj ▸ plusMarginal_nonneg ι (hw0 j hj) x
  have hm1 : ∀ j ∈ Xs, ∀ x, 0 ≤ m1 j x := fun j hj x =>
    hp1 j hj ▸ plusMarginal_nonneg ι (hw1 j hj) x
  have hP0 := energy_le_product_interpolation_blocks ι μ Xs Zs hμ F e0 m0 hw0 hp0 hn0 ht0 hmp0
    κj hcen0 hκ w0 ms0 hv0 hq0 hr0 hu0
  have hP1 := energy_le_product_interpolation_blocks ι μ Xs Zs hμ F e1 m1 hw1 hp1 hn1 ht1 hmp1
    κj hcen1 hκ w1 ms1 hv1 hq1 hr1 hu1
  have hT : ∀ (m ms : ∀ j, (ι.Half → X j) → ℝ) (w : ∀ j, (V → X j) → ℝ),
      (∀ j ∈ Xs, ∀ x, 0 ≤ m j x) → (∀ j ∈ Zs, ∀ z, 0 ≤ w j z) →
      (∀ j ∈ Zs, plusMarginal ι (w j) = ms j) →
      0 ≤ diagonalIntegral (tensorLaw (diagFamZ ι μ Xs Zs ∅ m ms)) F := by
    intro m ms w hm hw hq
    apply energy_nonneg_of_positive ι
    intro j
    simp only [diagFamZ, notMem_empty, ↓reduceIte]
    by_cases hjX : j ∈ Xs
    · simp only [hjX, ↓reduceIte]
      exact positive_indepLaw ι (hm j hjX)
    · by_cases hjZ : j ∈ Zs
      · simp only [hjX, hjZ, ↓reduceIte]
        exact ι.diagonalLaw_positive fun x => hq j hjZ ▸ plusMarginal_nonneg ι (hw j hjZ) x
      · simp only [hjX, hjZ, ↓reduceIte]
        exact hμ j hjX hjZ
  exact background_term hk0 hk1 hY hCm hCr hz₂ he hCXZ (hT m0 ms0 w0 hm0 hv0 hq0)
    (hT m1 ms1 w1 hm1 hv1 hq1) hP0 hP1 hD0 hD1 hb

omit [DecidableEq J] in
theorem indSet_false : indSet (fun _ : J => false) = ∅ := by
  ext b
  simp [indSet]

/-- **`prop:background-variance`(a), the displayed bound, blocks as factors**: the exterior
expansion (`exterior_expansion_ge_blocks`, for `s = 0, 1`), the selected term
(`background_selected_blocks`), the background terms of the kept sets
(`background_term_blocks`) and the choice weights (`background_assembly`) give
`½ ∑_s Y^{Ñ₀}[J_{X,s}] ≥ (C_m ([b_E(m)]_+ + ∑_r W_r p_E(m,r)) - z) Y`, with `Ñ₀ = μ + R` off `X`.
The inputs that remain hypotheses are those of `background_variance_a`. -/
theorem background_variance_a_blocks {π : Type*} [DecidableEq π] (ι : ReflectionCut V)
    (μ R : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (Xs : Finset J) (hμ : ∀ j, j ∉ Xs → ι.Positive (μ j))
    (F : (∀ b, X b) → ℝ)
    -- the selected aligned embeddings on `X`
    (e0 e1 : ∀ j, (V → X j) → ℝ) (m0 m1 : ∀ j, (ι.Half → X j) → ℝ)
    (hw0 : ∀ j ∈ Xs, ∀ z, 0 ≤ e0 j z) (hw1 : ∀ j ∈ Xs, ∀ z, 0 ≤ e1 j z)
    (hp0 : ∀ j ∈ Xs, plusMarginal ι (e0 j) = m0 j) (hn0 : ∀ j ∈ Xs, minusMarginal ι (e0 j) = m0 j)
    (hp1 : ∀ j ∈ Xs, plusMarginal ι (e1 j) = m1 j) (hn1 : ∀ j ∈ Xs, minusMarginal ι (e1 j) = m1 j)
    (ht0 : ∀ j ∈ Xs, ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (e0 j)) G H = ι.form (signedIntegral (e0 j)) H G)
    (ht1 : ∀ j ∈ Xs, ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (e1 j)) G H = ι.form (signedIntegral (e1 j)) H G)
    (hmp0 : ∀ j ∈ Xs, 0 < ∑ x, m0 j x) (hmp1 : ∀ j ∈ Xs, 0 < ∑ x, m1 j x) (κj : J → ℝ)
    (hcen0 : ∀ j ∈ Xs, CentredNormLe ι (signedIntegral (e0 j)) (m0 j) (κj j))
    (hcen1 : ∀ j ∈ Xs, CentredNormLe ι (signedIntegral (e1 j)) (m1 j) (κj j))
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hκ : ∀ j ∈ Xs, κj j ≤ k)
    -- the matching records of the other blocks
    (w0 w1 : ∀ j, (V → X j) → ℝ) (ms0 ms1 : ∀ j, (ι.Half → X j) → ℝ)
    (hv0 : ∀ j, j ∉ Xs → ∀ z, 0 ≤ w0 j z) (hv1 : ∀ j, j ∉ Xs → ∀ z, 0 ≤ w1 j z)
    (hq0 : ∀ j, j ∉ Xs → plusMarginal ι (w0 j) = ms0 j)
    (hr0 : ∀ j, j ∉ Xs → minusMarginal ι (w0 j) = ms0 j)
    (hq1 : ∀ j, j ∉ Xs → plusMarginal ι (w1 j) = ms1 j)
    (hr1 : ∀ j, j ∉ Xs → minusMarginal ι (w1 j) = ms1 j)
    (hu0 : ∀ j, j ∉ Xs → ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (w0 j)) G H = ι.form (signedIntegral (w0 j)) H G)
    (hu1 : ∀ j, j ∉ Xs → ∀ G H : (ι.Half → X j) → ℝ,
      ι.form (signedIntegral (w1 j)) G H = ι.form (signedIntegral (w1 j)) H G)
    -- the exterior
    (coef : J → ℝ) (hcoef : ∀ j, 0 ≤ coef j)
    (hR0 : ∀ j, j ∉ Xs → ι.Positive (R j - coef j • ι.diagonalLaw (ms0 j)))
    (hR1 : ∀ j, j ∉ Xs → ι.Positive (R j - coef j • ι.diagonalLaw (ms1 j)))
    -- the kept nonempty sets and their patterns
    (Zs : Finset (J → Bool)) (hZs0 : ∀ g ∈ Zs, ∀ j ∈ Xs, g j = false)
    (hZsne : (fun _ => false) ∉ Zs) (pats : Finset π) (pat : (J → Bool) → π)
    (hpat : ∀ g ∈ Zs, pat g ∈ pats) (W : π → ℝ)
    (hW : ∀ r ∈ pats, W r ≤ ∑ g ∈ Zs.filter (fun g => pat g = r), setCoeff coef g)
    -- the numbers
    {Yμ CX Cm ℓ η e z₂ : ℝ} (hY : 0 ≤ Yμ) (hCX : CX ≤ Cm) (hCm : 0 < Cm) (hz₂ : 0 ≤ z₂)
    (he : 0 ≤ e) (ℓr Cr ηr er CXZ : π → ℝ) (hCr : ∀ r, 0 ≤ Cr r) (her : ∀ r, 0 ≤ er r)
    (hCXZ : ∀ r, CXZ r ≤ Cm * Cr r)
    -- (E1) and `lem:record:paired-e-joint`(b) for `X` and for every `X ∪ Z`
    (hDsel0 : diagonalIntegral (tensorLaw (diagFam ι μ Xs Xs m0)) F ≤ (1 + z₂) * CX * Yμ)
    (hDsel1 : diagonalIntegral (tensorLaw (diagFam ι μ Xs Xs m1)) F ≤ (1 + z₂) * CX * Yμ)
    (hbsel : (ℓ - Cm * 1 * η - e) * Yμ ≤
      (diagonalIntegral (tensorLaw (recFam ι μ Xs Xs e0 m0)) F +
        diagonalIntegral (tensorLaw (recFam ι μ Xs Xs e1 m1)) F) / 2)
    (hDZ0 : ∀ g ∈ Zs, diagonalIntegral (tensorLaw (diagFamZ ι μ Xs (indSet g) Xs m0 ms0)) F ≤
      (1 + z₂) * CXZ (pat g) * Yμ)
    (hDZ1 : ∀ g ∈ Zs, diagonalIntegral (tensorLaw (diagFamZ ι μ Xs (indSet g) Xs m1 ms1)) F ≤
      (1 + z₂) * CXZ (pat g) * Yμ)
    (hbZ : ∀ g ∈ Zs, (ℓr (pat g) - Cm * Cr (pat g) * ηr (pat g) - er (pat g)) * Yμ ≤
      (diagonalIntegral (tensorLaw (recFamZ ι μ Xs (indSet g) Xs e0 m0 w0)) F +
        diagonalIntegral (tensorLaw (recFamZ ι μ Xs (indSet g) Xs e1 m1 w1)) F) / 2) :
    (Cm * (max 0 (ℓ / Cm - 1 * (η + k)) / (1 - k) +
        ∑ r ∈ pats, W r * (max 0 (ℓr r / Cm - Cr r * (ηr r + k)) / (1 - k))) -
      (e + k * z₂ * Cm * 1) / (1 - k) -
      ∑ g ∈ Zs, setCoeff coef g * ((er (pat g) + k * z₂ * Cm * Cr (pat g)) / (1 - k))) * Yμ ≤
      (diagonalIntegral (tensorLaw fun b => if b ∈ Xs then indepLaw ι (m0 b) else μ b + R b) F +
        diagonalIntegral (tensorLaw fun b => if b ∈ Xs then indepLaw ι (m1 b) else μ b + R b)
          F) / 2 := by
  have h1k : 0 < 1 - k := by linarith
  have hm0 : ∀ j ∈ Xs, ∀ x, 0 ≤ m0 j x := fun j hj x =>
    hp0 j hj ▸ plusMarginal_nonneg ι (hw0 j hj) x
  have hm1 : ∀ j ∈ Xs, ∀ x, 0 ≤ m1 j x := fun j hj x =>
    hp1 j hj ▸ plusMarginal_nonneg ι (hw1 j hj) x
  have hms0 : ∀ j, j ∉ Xs → ∀ x, 0 ≤ ms0 j x := fun j hj x =>
    hq0 j hj ▸ plusMarginal_nonneg ι (hv0 j hj) x
  have hms1 : ∀ j, j ∉ Xs → ∀ x, 0 ≤ ms1 j x := fun j hj x =>
    hq1 j hj ▸ plusMarginal_nonneg ι (hv1 j hj) x
  -- the selected term
  have hSel := background_selected_blocks ι μ Xs hμ F e0 e1 m0 m1 hw0 hw1 hp0 hn0 hp1 hn1 ht0 ht1
    hmp0 hmp1 κj hcen0 hcen1 hk0 hk1 hκ hY hCX hCm hz₂ he hDsel0 hDsel1 hbsel
  -- the background terms
  have hT : ∀ g ∈ Zs,
      (Cm * (max 0 (ℓr (pat g) / Cm - Cr (pat g) * (ηr (pat g) + k)) / (1 - k)) -
        (er (pat g) + k * z₂ * Cm * Cr (pat g)) / (1 - k)) * Yμ ≤
      (diagonalIntegral (tensorLaw (diagFamZ ι μ Xs (indSet g) ∅ m0 ms0)) F +
        diagonalIntegral (tensorLaw (diagFamZ ι μ Xs (indSet g) ∅ m1 ms1)) F) / 2 := by
    intro g hg
    have hnot : ∀ j ∈ indSet g, j ∉ Xs := fun j hj hjX => by
      have h1 := mem_indSet.mp hj
      rw [hZs0 g hg j hjX] at h1
      exact Bool.false_ne_true h1
    exact background_term_blocks ι μ Xs (indSet g) (fun j hj _ => hμ j hj) F e0 e1 m0 m1 hw0 hw1
      hp0 hn0 hp1 hn1 ht0 ht1 hmp0 hmp1 κj hcen0 hcen1 hk0 hk1 hκ w0 w1 ms0 ms1
      (fun j hj => hv0 j (hnot j hj)) (fun j hj => hv1 j (hnot j hj))
      (fun j hj => hq0 j (hnot j hj)) (fun j hj => hr0 j (hnot j hj))
      (fun j hj => hq1 j (hnot j hj)) (fun j hj => hr1 j (hnot j hj))
      (fun j hj => hu0 j (hnot j hj)) (fun j hj => hu1 j (hnot j hj)) hY hCm (hCr _) hz₂ (her _)
      (hCXZ _) (hDZ0 g hg) (hDZ1 g hg) (hbZ g hg)
  -- the exterior expansions, with the term `Z = ∅`
  have hZs' : ∀ g ∈ insert (fun _ => false) Zs, ∀ j ∈ Xs, g j = false := by
    intro g hg j hj
    rcases mem_insert.mp hg with h | h
    · rw [h]
    · exact hZs0 g h j hj
  have hempty : ∀ (m ms : ∀ j, (ι.Half → X j) → ℝ) (ew : ∀ j, (V → X j) → ℝ),
      diagFamZ ι μ Xs (indSet (fun _ => false)) ∅ m ms = recFam ι μ Xs ∅ ew m := by
    intro m ms ew
    funext b
    simp [diagFamZ, recFam, indSet_false]
  have hex : ∀ (ms m : ∀ j, (ι.Half → X j) → ℝ) (ew : ∀ j, (V → X j) → ℝ),
      (∀ j ∈ Xs, ∀ x, 0 ≤ m j x) → (∀ j, j ∉ Xs → ∀ x, 0 ≤ ms j x) →
      (∀ j, j ∉ Xs → ι.Positive (R j - coef j • ι.diagonalLaw (ms j))) →
      diagonalIntegral (tensorLaw (recFam ι μ Xs ∅ ew m)) F + ∑ g ∈ Zs, setCoeff coef g *
          diagonalIntegral (tensorLaw (diagFamZ ι μ Xs (indSet g) ∅ m ms)) F ≤
        diagonalIntegral (tensorLaw fun b => if b ∈ Xs then indepLaw ι (m b) else μ b + R b)
          F := by
    intro ms m ew hm hms hRs
    have h := exterior_expansion_ge_blocks ι μ R Xs m ms hm hms hμ coef hcoef hRs
      (insert (fun _ => false) Zs) hZs' F
    rw [sum_insert hZsne, hempty m ms ew] at h
    have e0 : setCoeff coef (fun _ => false) = 1 := by simp [setCoeff]
    rw [e0, one_mul] at h
    exact h
  have hex0 := hex ms0 m0 e0 hm0 hms0 hR0
  have hex1 := hex ms1 m1 e1 hm1 hms1 hR1
  have hext : (diagonalIntegral (tensorLaw (recFam ι μ Xs ∅ e0 m0)) F +
        diagonalIntegral (tensorLaw (recFam ι μ Xs ∅ e1 m1)) F) / 2 +
      ∑ g ∈ Zs, setCoeff coef g *
        ((diagonalIntegral (tensorLaw (diagFamZ ι μ Xs (indSet g) ∅ m0 ms0)) F +
          diagonalIntegral (tensorLaw (diagFamZ ι μ Xs (indSet g) ∅ m1 ms1)) F) / 2) ≤
      (diagonalIntegral (tensorLaw fun b => if b ∈ Xs then indepLaw ι (m0 b) else μ b + R b) F +
        diagonalIntegral (tensorLaw fun b => if b ∈ Xs then indepLaw ι (m1 b) else μ b + R b)
          F) / 2 := by
    have e : ∑ g ∈ Zs, setCoeff coef g *
        ((diagonalIntegral (tensorLaw (diagFamZ ι μ Xs (indSet g) ∅ m0 ms0)) F +
          diagonalIntegral (tensorLaw (diagFamZ ι μ Xs (indSet g) ∅ m1 ms1)) F) / 2) =
        (∑ g ∈ Zs, setCoeff coef g *
          diagonalIntegral (tensorLaw (diagFamZ ι μ Xs (indSet g) ∅ m0 ms0)) F +
        ∑ g ∈ Zs, setCoeff coef g *
          diagonalIntegral (tensorLaw (diagFamZ ι μ Xs (indSet g) ∅ m1 ms1)) F) / 2 := by
      rw [← sum_add_distrib, sum_div]
      exact sum_congr rfl fun g _ => by ring
    rw [e]
    linarith
  have hp : ∀ r ∈ pats, 0 ≤ max 0 (ℓr r / Cm - Cr r * (ηr r + k)) / (1 - k) :=
    fun r _ => div_nonneg (le_max_left _ _) h1k.le
  exact background_assembly Zs pats pat hpat (setCoeff coef)
    (fun g => (diagonalIntegral (tensorLaw (diagFamZ ι μ Xs (indSet g) ∅ m0 ms0)) F +
      diagonalIntegral (tensorLaw (diagFamZ ι μ Xs (indSet g) ∅ m1 ms1)) F) / 2)
    (fun g => (er (pat g) + k * z₂ * Cm * Cr (pat g)) / (1 - k))
    (fun r => max 0 (ℓr r / Cm - Cr r * (ηr r + k)) / (1 - k)) W hY hCm.le
    (fun g _ => setCoeff_nonneg hcoef g) hp hSel hT hext hW

end Sarkozy.Variance
