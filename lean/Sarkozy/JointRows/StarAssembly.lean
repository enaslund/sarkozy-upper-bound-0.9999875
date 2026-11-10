module

public import Sarkozy.JointRows.StarNorms

/-!
# The contractions and the conclusion of `prop:conditional-star`(b)

Source: `paper/sections/16_extraction.tex`, `prop:conditional-star`(b) and its proof, Step 1 ("the
contractions `𝓕_X, 𝓕_Y`") and the conclusion "Hence `‖T_⋆‖ ≤ κ r(‖M(i)‖ + 𝖾_⋆)`".

* `contraction_of_orthogonal`: **Step 1, the assembly.** If the maps `L_α` (the centred
  evaluations `U_i` and the feature maps `W_S`) have pairwise orthogonal ranges (the Hoeffding
  components `H_{{i}}`, `H_S` of the product law) and `‖L_α h‖ ≤ c_α ‖h‖`, then
  `𝓕((h_α)_α) = ∑_α L_α h_α / c_α` is a contraction: `‖𝓕 h‖² ≤ ∑_α ‖h_α‖²`. With
  `c_i = √κ` (`‖U_ν‖ ≤ √κ`) and `c_S = √κ r` (`‖W_S‖ ≤ √κ r`) this is `𝓕_X`.
* `star_norm_bound`: **(b), the conclusion.** If `T_⋆ = κ r 𝓕_X M(Φ̂) 𝓕_Y* + T_mean` (as forms),
  `𝓕_Y*` and `𝓕_X*` are contractions, `‖M(Φ̂)‖ ≤ m` and `‖T_mean‖ ≤ κ r 𝖾_⋆`, then
  `‖T_⋆‖ ≤ κ r (m + 𝖾_⋆)`; with `m = ‖M(i)‖` (Step 3) this is `‖T_⋆‖ ≤ κ r(‖M(i)‖ + 𝖾_⋆)`, and
  under (a) `κ r(𝗄 + 𝖾_⋆)`.
* `joint_star_inputs`: **the inputs of `lem:joint-rows`(a).** For the two rows `E`, `F` with the
  same contractions (both rows have the law `λ`), the decompositions of (b) for `T^E_⋆`, `T^F_⋆`
  give exactly the hypotheses `hdec`, `hV`, `hmean` of `RowsA.joint_rows_a_gate`
  (`lean/Sarkozy/JointRows/RowsAGate.lean`) on `E = L²₀(λ) ⊕ L²₀(λ)` (`WithLp 2`), with
  `qT` the form of the joint block `𝕋`, `V = 𝓕* ⊕ 𝓕*`, `qM` the form of `𝕄` and `qmean` that of
  `𝕋_mean`, `‖𝕋_mean‖ ≤ κ₀ r(e_F + e_E)`.
-/

@[expose] public section

open scoped BigOperators RealInnerProductSpace

namespace Sarkozy.JointRows.Star

/-! ## Step 1: the contraction -/

section Contraction

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H]

/-- Pythagoras for a finite family of pairwise orthogonal vectors. -/
theorem norm_sum_sq_of_orthogonal {I : Type*} (s : Finset I) (v : I → E)
    (horth : ∀ α ∈ s, ∀ β ∈ s, α ≠ β → ⟪v α, v β⟫ = 0) :
    ‖∑ α ∈ s, v α‖ ^ 2 = ∑ α ∈ s, ‖v α‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [inner_sum, Finset.sum_eq_single α (fun β hβ hne => horth α hα β hβ (Ne.symm hne))
    (fun h => absurd hα h), real_inner_self_eq_norm_sq]

/-- **Step 1, the assembled contraction**: maps with pairwise orthogonal ranges and norms at most
`c_α` give the contraction `𝓕 h = ∑_α L_α h_α / c_α`. -/
theorem contraction_of_orthogonal {I : Type*} (s : Finset I) (L : I → H →ₗ[ℝ] E) (c : I → ℝ)
    (hc : ∀ α ∈ s, 0 < c α) (hL : ∀ α ∈ s, ∀ h, ‖L α h‖ ≤ c α * ‖h‖)
    (horth : ∀ α ∈ s, ∀ β ∈ s, α ≠ β → ∀ h h', ⟪L α h, L β h'⟫ = 0) (h : I → H) :
    ‖∑ α ∈ s, (c α)⁻¹ • L α (h α)‖ ^ 2 ≤ ∑ α ∈ s, ‖h α‖ ^ 2 := by
  rw [norm_sum_sq_of_orthogonal s _ fun α hα β hβ hne => by
    rw [inner_smul_left, inner_smul_right, horth α hα β hβ hne]; simp]
  refine Finset.sum_le_sum fun α hα => ?_
  have hcα := hc α hα
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcα), mul_pow]
  have h1 := hL α hα (h α)
  have h2 : ‖L α (h α)‖ ^ 2 ≤ c α ^ 2 * ‖h α‖ ^ 2 := by
    have := norm_nonneg (L α (h α))
    nlinarith
  calc (c α)⁻¹ ^ 2 * ‖L α (h α)‖ ^ 2 ≤ (c α)⁻¹ ^ 2 * (c α ^ 2 * ‖h α‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = ‖h α‖ ^ 2 := by field_simp

end Contraction

/-! ## (b): the conclusion -/

section Conclusion

variable {EX EY G : Type*} [NormedAddCommGroup EX] [NormedAddCommGroup EY] [NormedAddCommGroup G]

/-- **`prop:conditional-star`(b), the conclusion**: `‖T_⋆‖ ≤ κ r(‖M‖ + 𝖾_⋆)`. -/
theorem star_norm_bound (tStar tMean : EX → EY → ℝ) (mForm : G → G → ℝ) (FX : EX → G)
    (FY : EY → G) {κr m es : ℝ} (hκr : 0 ≤ κr) (hm0 : 0 ≤ m)
    (hdec : ∀ x y, tStar x y = κr * mForm (FX x) (FY y) + tMean x y)
    (hFX : ∀ x, ‖FX x‖ ≤ ‖x‖) (hFY : ∀ y, ‖FY y‖ ≤ ‖y‖)
    (hM : ∀ u w, |mForm u w| ≤ m * ‖u‖ * ‖w‖) (hmean : ∀ x y, |tMean x y| ≤ κr * es * ‖x‖ * ‖y‖)
    (x : EX) (y : EY) : |tStar x y| ≤ κr * (m + es) * ‖x‖ * ‖y‖ := by
  rw [hdec]
  have h1 := hM (FX x) (FY y)
  have h2 : m * ‖FX x‖ * ‖FY y‖ ≤ m * ‖x‖ * ‖y‖ := by
    have := mul_le_mul (hFX x) (hFY y) (norm_nonneg _) (norm_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left this hm0]
  calc |κr * mForm (FX x) (FY y) + tMean x y|
      ≤ |κr * mForm (FX x) (FY y)| + |tMean x y| := abs_add_le _ _
    _ ≤ κr * (m * ‖x‖ * ‖y‖) + κr * es * ‖x‖ * ‖y‖ := by
        rw [abs_mul, abs_of_nonneg hκr]
        have := mul_le_mul_of_nonneg_left (h1.trans h2) hκr
        linarith [hmean x y]
    _ = κr * (m + es) * ‖x‖ * ‖y‖ := by ring

end Conclusion

/-! ## The inputs of `lem:joint-rows`(a) -/

section Joint

variable {E0 G : Type*} [NormedAddCommGroup E0] [NormedAddCommGroup G]

/-- The form of the joint block `(T_E T_F; T_F* T_E)` at `z = (z₁, z₂)`. -/
noncomputable def jointForm {X : Type*} (tE tF : X → X → ℝ) (z : WithLp 2 (X × X)) : ℝ :=
  tE z.fst z.fst + 2 * tF z.fst z.snd + tE z.snd z.snd

/-- `V = 𝓕* ⊕ 𝓕*`. -/
noncomputable def pairMap (Fs : E0 → G) (z : WithLp 2 (E0 × E0)) : WithLp 2 (G × G) :=
  WithLp.toLp 2 (Fs z.fst, Fs z.snd)

omit [NormedAddCommGroup E0] [NormedAddCommGroup G] in
theorem pairMap_fst (Fs : E0 → G) (z : WithLp 2 (E0 × E0)) : (pairMap Fs z).fst = Fs z.fst := rfl

omit [NormedAddCommGroup E0] [NormedAddCommGroup G] in
theorem pairMap_snd (Fs : E0 → G) (z : WithLp 2 (E0 × E0)) : (pairMap Fs z).snd = Fs z.snd := rfl

/-- **The inputs `hdec`, `hV`, `hmean` of `RowsA.joint_rows_a_gate`** from
`prop:conditional-star`(b) for the two rows: if `T^•_⋆ = κ₀ r 𝓕 M_•(Φ̂) 𝓕* + T^•_mean` (as forms
on `L²₀(λ)`, with the same contraction `𝓕*` for both rows), `‖T^•_mean‖ ≤ κ₀ r e_•`, then on
`L²₀(λ) ⊕ L²₀(λ)`, `qT = κ₀ r qM ∘ V + qmean`, `‖V z‖ ≤ ‖z‖` and
`|qmean z| ≤ κ₀ r (e_F + e_E) ‖z‖²`. -/
theorem joint_star_inputs (tE tF aE aF : E0 → E0 → ℝ) (mE mF : G → G → ℝ) (Fs : E0 → G)
    {κr eE eF : ℝ} (hκr : 0 ≤ κr) (heF : 0 ≤ eF)
    (hE : ∀ x y, tE x y = κr * mE (Fs x) (Fs y) + aE x y)
    (hF : ∀ x y, tF x y = κr * mF (Fs x) (Fs y) + aF x y)
    (hFs : ∀ x, ‖Fs x‖ ≤ ‖x‖)
    (haE : ∀ x y, |aE x y| ≤ κr * eE * ‖x‖ * ‖y‖) (haF : ∀ x y, |aF x y| ≤ κr * eF * ‖x‖ * ‖y‖) :
    (∀ z, jointForm tE tF z = κr * jointForm mE mF (pairMap Fs z) + jointForm aE aF z) ∧
    (∀ z, ‖pairMap Fs z‖ ≤ ‖z‖) ∧
    (∀ z, |jointForm aE aF z| ≤ κr * (eF + eE) * ‖z‖ ^ 2) := by
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_⟩
  · simp only [jointForm, pairMap_fst, pairMap_snd, hE, hF]
    ring
  · have h1 := WithLp.prod_norm_sq_eq_of_L2 (pairMap Fs z)
    have h2 := WithLp.prod_norm_sq_eq_of_L2 z
    simp only [pairMap] at h1
    have hz1 := hFs z.fst
    have hz2 := hFs z.snd
    have hsq : ‖pairMap Fs z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
      simp only [pairMap]
      rw [h1, h2]
      have := norm_nonneg (Fs z.fst)
      have := norm_nonneg (Fs z.snd)
      have := norm_nonneg z.fst
      have := norm_nonneg z.snd
      change ‖Fs z.fst‖ ^ 2 + ‖Fs z.snd‖ ^ 2 ≤ ‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp hsq
  · have h2 := WithLp.prod_norm_sq_eq_of_L2 z
    set a := ‖z.fst‖
    set b := ‖z.snd‖
    have ha := norm_nonneg z.fst
    have hb := norm_nonneg z.snd
    have e1 := haE z.fst z.fst
    have e2 := haF z.fst z.snd
    have e3 := haE z.snd z.snd
    have hab : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
    simp only [jointForm]
    rw [h2]
    calc |aE z.fst z.fst + 2 * aF z.fst z.snd + aE z.snd z.snd|
        ≤ |aE z.fst z.fst| + 2 * |aF z.fst z.snd| + |aE z.snd z.snd| := by
          have := abs_add_le (aE z.fst z.fst + 2 * aF z.fst z.snd) (aE z.snd z.snd)
          have := abs_add_le (aE z.fst z.fst) (2 * aF z.fst z.snd)
          rw [abs_mul, abs_two] at *
          linarith
      _ ≤ κr * eE * a * a + 2 * (κr * eF * a * b) + κr * eE * b * b := by linarith
      _ ≤ κr * (eF + eE) * (a ^ 2 + b ^ 2) := by
          have h3 := mul_le_mul_of_nonneg_left hab (mul_nonneg hκr heF)
          nlinarith [h3]

end Joint

end Sarkozy.JointRows.Star
