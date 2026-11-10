module

public import Sarkozy.SpectralD.SmallExtractionCounts

/-! Scalar bounds for singleton extraction on an eighteen-vertex half. -/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.Extraction Sarkozy.ExtractionK Sarkozy.Labellings

variable {p : ℕ} {U : Type*} [Fintype U] [DecidableEq U]

theorem small_count_error (G : OrientedGraph U) (hn : Fintype.card U ≤ 18)
    (hp : 2 ^ 512 ≤ p) (i : U) : coarseError (rowsDeg0 G i) p 18 ≤ 1 / 100 :=
  (coarseError_tail hp ((small_rowsDeg G hn i).trans (by norm_num))
    (by norm_num)).trans (by norm_num)

theorem small_rowsR (G : OrientedGraph U) (hn : Fintype.card U ≤ 18)
    (hp : 2 ^ 512 ≤ p) : rowsR G p 18 univ ≤ 2 ^ 18 := by
  have he := small_count_error G hn hp
  calc rowsR G p 18 univ ≤ ∏ _i : U, (2 : ℝ) := by
          simp only [rowsR, Nat.cast_ofNat]
          apply prod_le_prod₀
          · intro i _
            exact div_nonneg (by
              linarith [coarseError_nonneg (q := (p : ℝ)) (n := 18)
                (by norm_num) (rowsDeg0 G i)])
              (by linarith [he i])
          · intro i _
            apply (div_le_iff₀ (by linarith [he i])).mpr
            linarith [he i]
    _ = (2 : ℝ) ^ Fintype.card U := by rw [prod_const, card_univ]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hn

theorem small_count_product_lower (G : OrientedGraph U) (hn : Fintype.card U ≤ 18)
    (hp : 2 ^ 512 ≤ p) :
    (1 / 2 : ℝ) ^ 18 ≤ ∏ i : U, (1 - coarseError (rowsDeg0 G i) p 18) := by
  calc (1 / 2 : ℝ) ^ 18 ≤ (1 / 2 : ℝ) ^ Fintype.card U :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    _ = ∏ _i : U, (1 / 2 : ℝ) := by rw [prod_const, card_univ]
    _ ≤ _ := prod_le_prod₀ (fun _ _ => by norm_num)
          (fun i _ => by linarith [small_count_error G hn hp i])

theorem small_Jsp_exp (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U ≤ 18) (hp : 2 ^ 512 ≤ p) :
    Real.exp ((Real.sqrt p)⁻¹ ^ 2 * cmpJsp G ς) ≤ 4 := by
  have hr := pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg p)) (tail_rp_le hp) 2
  have hj := mul_le_mul_of_nonneg_left (small_cmpJsp G ς hn)
    (sq_nonneg ((Real.sqrt p)⁻¹))
  have ha : (Real.sqrt p)⁻¹ ^ 2 * cmpJsp G ς ≤ 1 := by
    calc _ ≤ (Real.sqrt p)⁻¹ ^ 2 * 2 ^ 82 := hj
      _ ≤ ((2 : ℝ)⁻¹ ^ 256) ^ 2 * 2 ^ 82 :=
          mul_le_mul_of_nonneg_right hr (by positivity)
      _ ≤ _ := by norm_num
  exact (Real.exp_le_exp.mpr ha).trans (Real.exp_one_lt_three.le.trans (by norm_num))

theorem small_cmpLambda (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U ≤ 18) (hp : 2 ^ 512 ≤ p) :
    cmpLambda0 G ς p 18 (1 / 100) 2 ≤ 2 ^ 58 := by
  have he : ∀ i, coarseError (rowsDeg0 G i) p 18 < 1 :=
    fun i => (small_count_error G hn hp i).trans_lt (by norm_num)
  have hR0 : 0 ≤ rowsR G p 18 univ := zero_le_one.trans (rowsR_univ_ge_one G he)
  have hR := pow_le_pow_left₀ hR0 (small_rowsR G hn hp) 2
  have hprod := small_count_product_lower G hn hp
  have hprod0 : 0 ≤ ∏ i : U, (1 - coarseError (rowsDeg0 G i) p 18) :=
    (by norm_num : (0 : ℝ) ≤ (1 / 2) ^ 18).trans hprod
  have hden : (1 / 2 : ℝ) ^ 20 ≤
      (1 - 1 / 100) ^ 2 * ∏ i : U, (1 - coarseError (rowsDeg0 G i) p 18) := by
    calc _ = (1 / 2 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ 18 := by norm_num
      _ ≤ _ := mul_le_mul (by norm_num) hprod (by positivity) (by norm_num)
  unfold cmpLambda0
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hden)).mpr
  calc _ ≤ ((2 : ℝ) ^ 18) ^ 2 * 4 :=
          mul_le_mul hR (small_Jsp_exp G ς hn hp) (Real.exp_pos _).le (by positivity)
    _ = (2 : ℝ) ^ 58 * (1 / 2 : ℝ) ^ 20 := by norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

theorem small_occupancy_exp (G : OrientedGraph U) (hn : Fintype.card U ≤ 18)
    (hp : 2 ^ 512 ≤ p) (V W : Finset U) :
    Real.exp (cmpGamma p 18 36 * cmpOc G ∅ V W (univ \ V) (univ \ W)) ≤ 4 := by
  have hr0 : 0 ≤ (Real.sqrt p)⁻¹ := by positivity
  have hr := tail_rp_le hp
  have hr1 : (Real.sqrt p)⁻¹ ≤ 1 := hr.trans (by norm_num)
  have hr2 : (Real.sqrt p)⁻¹ ^ 2 ≤ (Real.sqrt p)⁻¹ := by nlinarith
  have hg0 : 0 ≤ cmpGamma p 18 36 := by unfold cmpGamma; positivity
  have hg : cmpGamma p 18 36 ≤ 27 * (Real.sqrt p)⁻¹ := by
    unfold cmpGamma
    norm_num only [Nat.cast_ofNat]
    linarith
  have ha : cmpGamma p 18 36 * cmpOc G ∅ V W (univ \ V) (univ \ W) ≤ 1 := by
    calc _ ≤ cmpGamma p 18 36 * 2 ^ 25 :=
            mul_le_mul_of_nonneg_left (small_cmpOc_empty G hn V W) hg0
      _ ≤ (27 * (Real.sqrt p)⁻¹) * 2 ^ 25 :=
            mul_le_mul_of_nonneg_right hg (by positivity)
      _ ≤ (27 * ((2 : ℝ)⁻¹ ^ 256)) * 2 ^ 25 := by gcongr
      _ ≤ _ := by norm_num
  exact (Real.exp_le_exp.mpr ha).trans (Real.exp_one_lt_three.le.trans (by norm_num))

end Sarkozy.SpectralD
