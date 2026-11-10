module

public import Sarkozy.L20Cap.RectangleCertificate.Records
public import Sarkozy.L20Cap.RectangleCertificate.Factors

/-! The checked rectangle certificate has total coefficient less than 282. -/

@[expose] public section

namespace Sarkozy.L20Cap.RectangleCertificate

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

theorem product_small (c : ClassDatum) (R : LeafRecordData (Fin 6)) (hs : smallCounts c R) :
    leafProd G6 D20Z anchor 6 (leafEhat G6 anchor 6) (Ex8 \ (c.1 ∪ c.2))
      (witV R.w) (witW R.w) R.Cx R.Cz R.ordX R.ordZ ≤ (10001 / 10000 : ℝ) ^ 8 := by
  obtain ⟨h1, h2, h3, h4, hcard⟩ := hs
  let fm := leafFm G6 D20Z anchor 6 (leafEhat G6 anchor 6)
  let fr := leafFrho G6 D20Z anchor 6 (leafEhat G6 anchor 6)
  let Fr := Ex8 \ (c.1 ∪ c.2)
  have b1 : (∏ u ∈ univ \ (witV R.w ∪ R.Cx), fm (intS G6 R.ordX Fr u)) ≤
      (10001 / 10000 : ℝ) ^ (univ \ (witV R.w ∪ R.Cx)).card := by
    rw [← prod_const]
    exact prod_le_prod₀ (fun u _ => leafFm_nonneg G6 D20Z ehat_lt_one _)
      (fun u hu => fm_small _ (h1 u hu))
  have b2 : (∏ b ∈ R.Cz, fr (coverRowS G6 R.Cz R.ordZ (Fr.filter fun e => e.2 ∈ R.Cz) b)) ≤
      (10001 / 10000 : ℝ) ^ R.Cz.card := by
    rw [← prod_const]
    exact prod_le_prod₀ (fun b _ => leafFrho_nonneg G6 D20Z ehat_lt_one _)
      (fun b hb => frho_small _ (h2 b hb))
  have b3 : (∏ u ∈ univ \ (witW R.w ∪ R.Cz), fm (intS G6 R.ordZ (Fr.image Prod.swap) u)) ≤
      (10001 / 10000 : ℝ) ^ (univ \ (witW R.w ∪ R.Cz)).card := by
    rw [← prod_const]
    exact prod_le_prod₀ (fun u _ => leafFm_nonneg G6 D20Z ehat_lt_one _)
      (fun u hu => fm_small _ (h3 u hu))
  have b4 : (∏ b ∈ R.Cx, fr (coverRowS G6 R.Cx R.ordX
      ((Fr.image Prod.swap).filter fun e => e.2 ∈ R.Cx) b)) ≤
      (10001 / 10000 : ℝ) ^ R.Cx.card := by
    rw [← prod_const]
    exact prod_le_prod₀ (fun b _ => leafFrho_nonneg G6 D20Z ehat_lt_one _)
      (fun b hb => frho_small _ (h4 b hb))
  have p2 : 0 ≤ ∏ b ∈ R.Cz, fr (coverRowS G6 R.Cz R.ordZ
      (Fr.filter fun e => e.2 ∈ R.Cz) b) :=
    prod_nonneg fun b _ => leafFrho_nonneg G6 D20Z ehat_lt_one _
  have p3 : 0 ≤ ∏ u ∈ univ \ (witW R.w ∪ R.Cz),
      fm (intS G6 R.ordZ (Fr.image Prod.swap) u) :=
    prod_nonneg fun u _ => leafFm_nonneg G6 D20Z ehat_lt_one _
  have p4 : 0 ≤ ∏ b ∈ R.Cx, fr (coverRowS G6 R.Cx R.ordX
      ((Fr.image Prod.swap).filter fun e => e.2 ∈ R.Cx) b) :=
    prod_nonneg fun b _ => leafFrho_nonneg G6 D20Z ehat_lt_one _
  have hb := mul_le_mul (mul_le_mul (mul_le_mul b1 b2 p2 (by positivity)) b3 p3
    (by positivity)) b4 p4 (by positivity)
  simp only [← pow_add, hcard] at hb
  exact hb

theorem coefficient_small (i : Fin 42) :
    leafCoef G6 D20Z anchor 6 Ex8 (datum i) (record i) ≤
      (1001 / 1000 : ℝ) * Real.sqrt (2 ^ exponent i) := by
  have hp := product_small (datum i) (record i) (records_small i)
  have hs : Real.sqrt ((2 : ℝ) ^ exponent i *
      leafProd G6 D20Z anchor 6 (leafEhat G6 anchor 6) (Ex8 \ ((datum i).1 ∪ (datum i).2))
        (witV (record i).w) (witW (record i).w) (record i).Cx (record i).Cz
        (record i).ordX (record i).ordZ) ≤
      Real.sqrt (2 ^ exponent i) * (10001 / 10000 : ℝ) ^ 4 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hR0 : 0 ≤ rowsR G6 anchor 6 univ := (by norm_num : (0 : ℝ) ≤ 1).trans
    (rowsR_univ_ge_one G6 (fun j => (coarseError_le_leafEhat G6 anchor 6 j).trans_lt ehat_lt_one))
  have hR2 := pow_le_pow_left₀ hR0 rows_ratio_small 2
  unfold leafCoef
  rw [records_exponent]
  conv_lhs => arg 2; rw [records_size]
  calc
    _ ≤ (Real.sqrt (2 ^ exponent i) * (10001 / 10000 : ℝ) ^ 4) *
        (10001 / 10000 : ℝ) ^ 2 / (1 - leafEhat G6 anchor 6) ^ 2 := by
      exact div_le_div_of_nonneg_right (mul_le_mul hs hR2 (sq_nonneg _) (by positivity))
        (sq_nonneg _)
    _ = Real.sqrt (2 ^ exponent i) *
        ((10001 / 10000 : ℝ) ^ 6 / (1 - leafEhat G6 anchor 6) ^ 2) := by ring
    _ ≤ _ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left coefficient_prefactor
        (Real.sqrt_nonneg ((2 : ℝ) ^ exponent i))

theorem sqrt_exponent_le_price (i : Fin 42) :
    Real.sqrt ((2 : ℝ) ^ exponent i) ≤ (rationalPrice i : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact_mod_cast rationalPrice_nonneg i
  · exact_mod_cast rationalPrice_sq i

theorem coefficient_sum :
    ∑ i, leafCoef G6 D20Z anchor 6 Ex8 (datum i) (record i) ≤ (282 : ℝ) := by
  calc
    _ ≤ ∑ i, (1001 / 1000 : ℝ) * (rationalPrice i : ℝ) := by
      apply sum_le_sum
      intro i _
      exact (coefficient_small i).trans (mul_le_mul_of_nonneg_left (sqrt_exponent_le_price i)
        (by norm_num))
    _ = (1001 / 1000 : ℝ) * (6998 / 25) := by
      rw [← mul_sum, ← Rat.cast_sum, rationalPrice_sum]
      norm_num
    _ ≤ _ := by norm_num

end Sarkozy.L20Cap.RectangleCertificate
