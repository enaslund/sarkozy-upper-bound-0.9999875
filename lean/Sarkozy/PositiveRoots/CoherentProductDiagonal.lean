module

public import Sarkozy.PositiveRoots.CoherentStarProductTrace
public import Sarkozy.Cuts.NormSums

/-! Mean-zero diagonal input bounds for normalized core-star products. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering
open scoped symmDiff

variable {p : ℕ} [Fact p.Prime] [Nonempty (CoreT (ZMod p))]

theorem core_rawStar_mean_zero_norm_any (hp3 : p % 4 = 3)
    (S : Finset (Fin 4)) (F : ZMod p → ℝ) (hF : (fieldLaw p).expect F = 0) :
    nrm coreLaw (fun c : CoreT (ZMod p) => rawStarMap S F c.val) ≤
      rp p * nrm (fieldLaw p) F := by
  by_cases hS : S.Nonempty
  · exact core_rawStar_mean_zero_norm hp3 S hS F hF
  · rw [not_nonempty_iff_eq_empty.mp hS]
    simp only [rawStarMap, StarMatrix.psi, prod_empty, one_mul, hF]
    simpa only [nrm, Recentering.ip, zero_mul, FiniteLaw.expect_const, Real.sqrt_zero] using
      mul_nonneg (rp_nonneg (p := p)) (nrm_nonneg (fieldLaw p) F)

theorem core_deleted_product_norm (hp3 : p % 4 = 3)
    (S T : Finset (Fin 4)) (F : ZMod p → ℝ) :
    nrm coreLaw (fun c : CoreT (ZMod p) =>
      ∑ j ∈ S ∩ T, StarMatrix.psi (S ∆ T) (c.val j) c.val * F (c.val j)) ≤
        ((S ∩ T).card : ℝ) * nrm (fieldLaw p) F := by
  refine (nrm_sum_le coreLaw (S ∩ T)
    (fun j (c : CoreT (ZMod p)) => StarMatrix.psi (S ∆ T) (c.val j) c.val * F (c.val j))).trans ?_
  calc
    _ ≤ ∑ _j ∈ S ∩ T, nrm (fieldLaw p) F := by
      apply sum_le_sum
      intro j _
      have h := nrm_mul_le coreLaw
        (fun c : CoreT (ZMod p) => StarMatrix.psi (S ∆ T) (c.val j) c.val)
        (fun c => F (c.val j)) (by norm_num : (0 : ℝ) ≤ 1)
        (fun c => abs_prod_chiRe_le (S ∆ T) c.val (c.val j))
      simpa only [one_mul, core_coordinate_norm hp3] using h
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

theorem core_centeredProductImage_norm (hp3 : p % 4 = 3)
    (S T : Finset (Fin 4)) (F : ZMod p → ℝ) (hF : (fieldLaw p).expect F = 0)
    {bS bT : ℝ} (hbS : 0 ≤ bS) (hbT : 0 ≤ bT)
    (hS : ∀ c : CoreT (ZMod p), |starMean S c.val| ≤ bS)
    (hT : ∀ c : CoreT (ZMod p), |starMean T c.val| ≤ bT) :
    nrm coreLaw (fun c : CoreT (ZMod p) => centeredProductImage S T F c.val) ≤
      (rp p + ((S ∩ T).card : ℝ) * (p : ℝ)⁻¹ + (bS + bT) * rp p) *
        nrm (fieldLaw p) F := by
  let A := fun c : CoreT (ZMod p) => rawStarMap (S ∆ T) F c.val
  let B := fun c : CoreT (ZMod p) => (p : ℝ)⁻¹ *
    ∑ j ∈ S ∩ T, StarMatrix.psi (S ∆ T) (c.val j) c.val * F (c.val j)
  let C := fun c : CoreT (ZMod p) => starMean S c.val * rawStarMap T F c.val
  let D := fun c : CoreT (ZMod p) => starMean T c.val * rawStarMap S F c.val
  have he : (fun c : CoreT (ZMod p) => centeredProductImage S T F c.val) =
      fun c => A c - B c - C c - D c := by
    funext c
    exact centeredProductImage_mean_zero S T F hF c.val c.property.1.injOn
  have hA := core_rawStar_mean_zero_norm_any hp3 (S ∆ T) F hF
  have hB : nrm coreLaw B ≤
      (p : ℝ)⁻¹ * (((S ∩ T).card : ℝ) * nrm (fieldLaw p) F) := by
    dsimp [B]
    rw [nrm_smul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ)⁻¹)]
    exact mul_le_mul_of_nonneg_left (core_deleted_product_norm hp3 S T F) (by positivity)
  have hC : nrm coreLaw C ≤ bS * (rp p * nrm (fieldLaw p) F) :=
    (nrm_mul_le coreLaw _ _ hbS hS).trans
      (mul_le_mul_of_nonneg_left (core_rawStar_mean_zero_norm_any hp3 T F hF) hbS)
  have hD : nrm coreLaw D ≤ bT * (rp p * nrm (fieldLaw p) F) :=
    (nrm_mul_le coreLaw _ _ hbT hT).trans
      (mul_le_mul_of_nonneg_left (core_rawStar_mean_zero_norm_any hp3 S F hF) hbT)
  rw [he]
  calc
    _ ≤ nrm coreLaw (fun c => A c - B c - C c) + nrm coreLaw D := nrm_sub_le _ _ _
    _ ≤ (nrm coreLaw (fun c => A c - B c) + nrm coreLaw C) + nrm coreLaw D :=
      add_le_add (nrm_sub_le _ _ _) le_rfl
    _ ≤ ((nrm coreLaw A + nrm coreLaw B) + nrm coreLaw C) + nrm coreLaw D :=
      add_le_add (add_le_add (nrm_sub_le _ _ _) le_rfl) le_rfl
    _ ≤ _ := by dsimp [A] at *; nlinarith

theorem core_projectedDiagonal_product_norm (hp3 : p % 4 = 3)
    (S T : Finset (Fin 4)) (F : ZMod p → ℝ) (hF : (fieldLaw p).expect F = 0)
    {bS bT : ℝ} (hbS : 0 ≤ bS) (hbT : 0 ≤ bT)
    (hS : ∀ c : CoreT (ZMod p), |starMean S c.val| ≤ bS)
    (hT : ∀ c : CoreT (ZMod p), |starMean T c.val| ≤ bT) :
    nrm coreLaw (fun c : CoreT (ZMod p) =>
      normalizedStarProduct S T (fun z => projectedDiagonal F z.1 z.2) c.val) ≤
        (p : ℝ) * (rp p + ((S ∩ T).card : ℝ) * (p : ℝ)⁻¹ + (bS + bT) * rp p) *
          nrm (fieldLaw p) F := by
  simp_rw [normalizedStarProduct_projectedDiagonal]
  rw [nrm_smul, abs_of_nonneg (Nat.cast_nonneg p)]
  exact (mul_le_mul_of_nonneg_left
    (core_centeredProductImage_norm hp3 S T F hF hbS hbT hS hT) (Nat.cast_nonneg p)).trans_eq
      (by ring)

end Sarkozy.PositiveRoots.CoherentFrame
