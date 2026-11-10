module

public import Sarkozy.JointRows.StarJoint

/-!
# `prop:conditional-star`(b) feeding `lem:joint-rows`(a): `hdec` and `hV` on the actual kernels

Sources: `paper/sections/16_extraction.tex`, `prop:conditional-star` and its proof (Step 2), and
the proof of `lem:joint-rows`(a) ("Restriction", "Pure stars").

For coordinate laws `ν_i` on `𝔽_p` (`i ∈ X`), the row law `λ = ⊗ν_i` (`blockLaw νp`), sign data
`D : X → X → ℝ` and a family `𝒮` of sets with at least two elements:
* `starKernel νp D 𝒮`: the star part of `∏_{i,j} (1 + D_{ij} χ(y_j - x_i))`, i.e. the single
  pairs `D_{ij} χ(y_j - x_i)`, the row stars `∏_{j∈T} D_{ij} χ(y_j - x_i)` and the column stars
  `∏_{i∈S} D_{ij} χ(y_j - x_i)`, `S, T ∈ 𝒮`;
* `meanKernel νp D 𝒮`: the terms with complementary means,
  `A_{iT} (∏_{j∈T} (m_{ν_j}(x_i) + φ_{ν_j}(x_i, y_j)) - ∏_{j∈T} φ_{ν_j}(x_i, y_j))` and
  `B_{jS} (∏_{i∈S} (m_{ν_i}(y_j) + φ_{ν_i}(y_j, x_i)) - ∏_{i∈S} φ_{ν_i}(y_j, x_i))`;
* `starKernel_eq` (Step 2): `K_⋆ = K_pure + K_mean` pointwise, using `χ(-1) = -1`;
* `qTc_star_decomp`: **the decomposition `hdec`**: `𝕋 = κ r (𝓕 ⊕ 𝓕) 𝕄 (𝓕 ⊕ 𝓕)^* + 𝕋_mean` on
  `L²_0(λ)²`, with `𝕄 = Sector.qMat (jointZ D_E D_F) (jointA D_E D_F 𝒮) Φ̂` and `𝕋_mean` the joint
  form of the `meanKernel`s (`qmeanStar`);
* `norm_starFeat_le`: **`hV`**: `‖(𝓕 ⊕ 𝓕)^* v‖ ≤ ‖v‖`;
* **`Restrict.joint_rows_a_star`**: `Restrict.joint_rows_a_paley` for `λ = ⊗ν_i` and the actual
  star kernels, with `hdec` and `hV` discharged. Its star input is the bound on `𝕋_mean`
  (`hmean`, Step 5 of `prop:conditional-star`), stated for `qmeanStar`.
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace Sarkozy.JointRows.StarOps

open Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.JointRows.PaleyGauss

variable {p : ℕ} [Fact p.Prime]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The star part** of `∏_{i,j} (1 + D_{ij} χ(y_j - x_i))` (`prop:conditional-star`). -/
noncomputable def starKernel (D : X → X → ℝ) (𝒮 : Finset (Finset X)) (x y : X → ZMod p) : ℝ :=
  (∑ i, ∑ j, D i j * chiR p (y j - x i)) +
    (∑ i, ∑ T ∈ 𝒮, ∏ j ∈ T, (D i j * chiR p (y j - x i))) +
    ∑ j, ∑ S ∈ 𝒮, ∏ i ∈ S, (D i j * chiR p (y j - x i))

/-- **The terms with complementary means** (Step 2). -/
noncomputable def meanKernel (νp : X → FiniteLaw (ZMod p)) (D : X → X → ℝ)
    (𝒮 : Finset (Finset X)) (x y : X → ZMod p) : ℝ :=
  (∑ i, ∑ T ∈ 𝒮, coefA D i T * ((∏ j ∈ T, (mchi (νp j) (x i) + phi (νp j) (x i) (y j))) -
      ∏ j ∈ T, phi (νp j) (x i) (y j))) +
    ∑ j, ∑ S ∈ 𝒮, coefB D j S * ((∏ i ∈ S, (mchi (νp i) (y j) + phi (νp i) (y j) (x i))) -
      ∏ i ∈ S, phi (νp i) (y j) (x i))

omit [Fintype X] [DecidableEq X] in
/-- `χ(t - a) = m_ν(t) + φ_ν(t, a)`. -/
theorem chiR_eq_mchi_add_phi (ν : FiniteLaw (ZMod p)) (t a : ZMod p) :
    chiR p (t - a) = mchi ν t + phi ν t a := by
  unfold phi; ring

omit [DecidableEq X] in
/-- **Step 2: `K_⋆ = K_pure + K_mean`** (using `χ(-1) = -1` for the row stars). -/
theorem starKernel_eq (hp : p % 4 = 3) (νp : X → FiniteLaw (ZMod p)) (D : X → X → ℝ)
    (𝒮 : Finset (Finset X)) (x y : X → ZMod p) :
    starKernel D 𝒮 x y = pureKernel νp νp D 𝒮 (coefA D) 𝒮 (coefB D) x y +
      meanKernel νp D 𝒮 x y := by
  have hrow : ∀ i (T : Finset X), ∏ j ∈ T, (D i j * chiR p (y j - x i)) =
      coefA D i T * ∏ j ∈ T, (mchi (νp j) (x i) + phi (νp j) (x i) (y j)) := by
    intro i T
    have h1 : ∀ j, D i j * chiR p (y j - x i) =
        -(D i j) * (mchi (νp j) (x i) + phi (νp j) (x i) (y j)) := by
      intro j
      rw [← chiR_eq_mchi_add_phi, show y j - x i = -(x i - y j) by ring, chiR_neg hp]
      ring
    rw [Finset.prod_congr rfl fun j _ => h1 j, Finset.prod_mul_distrib, Finset.prod_neg]
    unfold coefA
    ring
  have hcol : ∀ j (S : Finset X), ∏ i ∈ S, (D i j * chiR p (y j - x i)) =
      coefB D j S * ∏ i ∈ S, (mchi (νp i) (y j) + phi (νp i) (y j) (x i)) := by
    intro j S
    rw [Finset.prod_congr rfl fun i _ => by rw [chiR_eq_mchi_add_phi (νp i)],
      Finset.prod_mul_distrib]
    rfl
  unfold starKernel pureKernel meanKernel
  simp only [hrow, hcol]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

omit [DecidableEq X] in
theorem bform_add (νp νq : X → FiniteLaw (ZMod p)) [DecidableEq X]
    (K₁ K₂ : (X → ZMod p) → (X → ZMod p) → ℝ) (f g : (X → ZMod p) → ℝ) :
    bform νp νq (fun x y => K₁ x y + K₂ x y) f g = bform νp νq K₁ f g + bform νp νq K₂ f g := by
  unfold bform
  rw [← FiniteLaw.expect_add]
  refine FiniteLaw.expect_congr _ fun x => ?_
  rw [← FiniteLaw.expect_add]
  exact FiniteLaw.expect_congr _ fun y => by ring

/-- `⟨U, K V⟩_λ` (`FiveType.kf`) is `bform` for `λ = ⊗ν_i`. -/
theorem kf_eq_bform (νp : X → FiniteLaw (ZMod p)) (K : (X → ZMod p) → (X → ZMod p) → ℝ)
    (f g : (X → ZMod p) → ℝ) : kf (blockLaw νp) K f g = bform νp νp K f g := by
  unfold kf bform FiniteLaw.expect
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **`T_⋆ = κ r 𝓕 M(Φ̂) 𝓕^* + T_mean`** for one row (`prop:conditional-star`(b)), as forms on
mean-zero functions. -/
theorem star_form_decomp (hp : p % 4 = 3) (νp : X → FiniteLaw (ZMod p)) (D : X → X → ℝ)
    (𝒮 : Finset (Finset X)) {κ : ℝ} (hκ : 0 < κ) {f g : (X → ZMod p) → ℝ}
    (hf : (blockLaw νp).expect f = 0) (hg : (blockLaw νp).expect g = 0) :
    kf (blockLaw νp) (starKernel D 𝒮) f g =
      κ * (Real.sqrt p)⁻¹ * mForm D 𝒮 (coefA D) 𝒮 (coefB D) (featU νp κ f) (featW νp κ f)
        (featU νp κ g) (featW νp κ g) + kf (blockLaw νp) (meanKernel νp D 𝒮) f g := by
  rw [kf_eq_bform, kf_eq_bform]
  rw [show starKernel D 𝒮 = fun x y => pureKernel νp νp D 𝒮 (coefA D) 𝒮 (coefB D) x y +
      meanKernel νp D 𝒮 x y from funext fun x => funext fun y => starKernel_eq hp νp D 𝒮 x y,
    bform_add, pure_block_identity νp νp D 𝒮 (coefA D) 𝒮 (coefB D) hκ f g hf hg]

/-- The joint form of the mean kernels, `𝕋_mean` at `v` (centred components). -/
noncomputable def qmeanStar (νp : X → FiniteLaw (ZMod p)) (DE DF : X → X → ℝ)
    (𝒮 : Finset (Finset X)) (v : EuclideanSpace ℝ ((X → ZMod p) ⊕ (X → ZMod p))) : ℝ :=
  RowsA.stForm (blockLaw νp) (meanKernel νp DE 𝒮) (meanKernel νp DF 𝒮)
    (cen (blockLaw νp) (Restrict.dewL (blockLaw νp) v))
    (cen (blockLaw νp) (Restrict.dewR (blockLaw νp) v))

/-- The joint feature map `v ↦ (𝓕 ⊕ 𝓕)^*(P₀ v_L, P₀ v_R)`. -/
noncomputable def starFeat (νp : X → FiniteLaw (ZMod p)) (κ : ℝ) (𝒮 : Finset (Finset X))
    (v : EuclideanSpace ℝ ((X → ZMod p) ⊕ (X → ZMod p))) :
    PiLp 2 (fun _ : (X ⊕ X) ⊕ (𝒮 ⊕ 𝒮) => sumZero p) :=
  jointFeat νp κ 𝒮 (cen (blockLaw νp) (Restrict.dewL (blockLaw νp) v))
    (cen (blockLaw νp) (Restrict.dewR (blockLaw νp) v))

theorem expect_cen {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω') (g : Ω' → ℝ) :
    μ.expect (cen μ g) = 0 := by
  unfold cen
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const, sub_self]

/-- **`hdec`** (`lem:joint-rows`(a), "Pure stars"): `𝕋 = κ r 𝕄 ∘ (𝓕 ⊕ 𝓕)^* + 𝕋_mean`. -/
theorem qTc_star_decomp (hp : p % 4 = 3) (νp : X → FiniteLaw (ZMod p)) {DE DF : X → X → ℝ}
    (hDE : ∀ i j, DE i j = -DE j i) (𝒮 : Finset (Finset X)) {κ : ℝ} (hκ : 0 < κ)
    (v : EuclideanSpace ℝ ((X → ZMod p) ⊕ (X → ZMod p))) :
    Restrict.qTc (blockLaw νp) (starKernel DE 𝒮) (starKernel DF 𝒮) v =
      κ * (Real.sqrt p)⁻¹ * Sector.qMat (jointZ DE DF) (jointA DE DF 𝒮) (paleyJ hp)
        (starFeat νp κ 𝒮 v) + qmeanStar νp DE DF 𝒮 v := by
  set f := cen (blockLaw νp) (Restrict.dewL (blockLaw νp) v) with hfdef
  set h := cen (blockLaw νp) (Restrict.dewR (blockLaw νp) v) with hhdef
  have hf : (blockLaw νp).expect f = 0 := expect_cen _ _
  have hh : (blockLaw νp).expect h = 0 := expect_cen _ _
  unfold Restrict.qTc qmeanStar starFeat RowsA.stForm
  rw [← hfdef, ← hhdef, qMat_jointFeat hp νp κ 𝒮 hDE hf hh, star_form_decomp hp νp DE 𝒮 hκ hf hf,
    star_form_decomp hp νp DF 𝒮 hκ hf hh, star_form_decomp hp νp DE 𝒮 hκ hh hh]
  ring

/-- `‖v_L/√λ‖²_λ + ‖v_R/√λ‖²_λ ≤ ‖v‖²`. -/
theorem ip_dew_le {Ω' : Type*} [Fintype Ω'] (lam : FiniteLaw Ω') (v : EuclideanSpace ℝ (Ω' ⊕ Ω')) :
    ip lam (Restrict.dewL lam v) (Restrict.dewL lam v) +
        ip lam (Restrict.dewR lam v) (Restrict.dewR lam v) ≤ ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Fintype.sum_sum_type]
  have key : ∀ (a : ℝ) (w : ℝ), 0 ≤ w → w * (a / Real.sqrt w * (a / Real.sqrt w)) ≤ ‖a‖ ^ 2 := by
    intro a w hw
    rw [Real.norm_eq_abs, sq_abs]
    rcases hw.lt_or_eq with hw' | hw'
    · have hs : Real.sqrt w * Real.sqrt w = w := Real.mul_self_sqrt hw
      have hs0 : Real.sqrt w ≠ 0 := (Real.sqrt_pos.mpr hw').ne'
      field_simp
      rw [Real.sq_sqrt hw]
      field_simp
      exact le_refl _
    · rw [← hw', zero_mul]; exact sq_nonneg _
  unfold ip FiniteLaw.expect Restrict.dewL Restrict.dewR
  exact add_le_add (Finset.sum_le_sum fun x _ => key _ _ (lam.nonneg x))
    (Finset.sum_le_sum fun x _ => key _ _ (lam.nonneg x))

/-- **`hV`**: `‖(𝓕 ⊕ 𝓕)^* v‖ ≤ ‖v‖`, for coordinate laws with densities at most `κ` and sets
`S ∈ 𝒮` with at least two elements. -/
theorem norm_starFeat_le (hp : p % 4 = 3) (νp : X → FiniteLaw (ZMod p)) {κ : ℝ} (hκ : 0 < κ)
    (hdens : ∀ i a, (νp i).weight a ≤ κ / p) (𝒮 : Finset (Finset X))
    (h𝒮 : ∀ S ∈ 𝒮, 2 ≤ S.card) (v : EuclideanSpace ℝ ((X → ZMod p) ⊕ (X → ZMod p))) :
    ‖starFeat νp κ 𝒮 v‖ ≤ ‖v‖ := by
  set f := cen (blockLaw νp) (Restrict.dewL (blockLaw νp) v) with hfdef
  set h := cen (blockLaw νp) (Restrict.dewR (blockLaw νp) v) with hhdef
  have hf : (blockLaw νp).expect f = 0 := expect_cen _ _
  have hh : (blockLaw νp).expect h = 0 := expect_cen _ _
  have hsq : ‖starFeat νp κ 𝒮 v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    unfold starFeat
    rw [← hfdef, ← hhdef, Sector.norm_sq_split]
    unfold jointFeat
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    simp only [inner_embC (expect_featU νp κ hf _) (expect_featU νp κ hf _),
      inner_embC (expect_featU νp κ hh _) (expect_featU νp κ hh _),
      inner_embC (expect_featW νp κ f _) (expect_featW νp κ f _),
      inner_embC (expect_featW νp κ h _) (expect_featW νp κ h _)]
    have hcs : ∀ F : Finset X → ℝ, ∑ S : 𝒮, F S = ∑ S ∈ 𝒮, F S :=
      fun F => Finset.sum_coe_sort 𝒮 F
    have h1 := featStar_norm_le hp νp hκ hdens 𝒮 h𝒮 hf
    have h2 := featStar_norm_le hp νp hκ hdens 𝒮 h𝒮 hh
    rw [← hcs] at h1 h2
    have h3 : ip (blockLaw νp) f f + ip (blockLaw νp) h h ≤ ‖v‖ ^ 2 := by
      have hcf := Star.nrm_cen_le (blockLaw νp) (Restrict.dewL (blockLaw νp) v)
      have hch := Star.nrm_cen_le (blockLaw νp) (Restrict.dewR (blockLaw νp) v)
      have hd := ip_dew_le (blockLaw νp) v
      rw [ip_self_eq, ip_self_eq] at hd
      rw [ip_self_eq, ip_self_eq]
      have := FiveType.nrm_nonneg (blockLaw νp) f
      have := FiveType.nrm_nonneg (blockLaw νp) h
      nlinarith
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp hsq

end Sarkozy.JointRows.StarOps
