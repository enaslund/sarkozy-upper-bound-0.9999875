module

public import Sarkozy.PositiveRoots.CoherentProductInputs

/-! Weighted raw-star product identities, with exact deleted-coordinate terms. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD Sarkozy.Cuts
open scoped symmDiff

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] in
theorem psi_product_deleted (S T : Finset U) (x : U → ZMod p) (z : ZMod p) :
    StarMatrix.psi S z x * StarMatrix.psi T z x = StarMatrix.psi (S ∆ T) z x -
      if z ∈ (S ∩ T).image x then StarMatrix.psi (S ∆ T) z x else 0 := by
  unfold StarMatrix.psi
  rw [prod_mul_prod_eq, prod_chiRe_sq]
  split_ifs <;> ring

omit [Fintype U] in
theorem weighted_star_product (S T : Finset U) (F : ZMod p → ℝ) (x : U → ZMod p)
    (hx : Set.InjOn x (S ∩ T)) :
    (fieldLaw p).expect (fun z => StarMatrix.psi S z x * StarMatrix.psi T z x * F z) =
      rawStarMap (S ∆ T) F x - (p : ℝ)⁻¹ *
        ∑ j ∈ S ∩ T, StarMatrix.psi (S ∆ T) (x j) x * F (x j) := by
  have he (z : ZMod p) : StarMatrix.psi S z x * StarMatrix.psi T z x * F z =
      StarMatrix.psi (S ∆ T) z x * F z -
      if z ∈ (S ∩ T).image x then StarMatrix.psi (S ∆ T) z x * F z else 0 := by
    rw [psi_product_deleted]
    split_ifs <;> ring
  simp_rw [he]
  rw [FiniteLaw.expect_sub]
  unfold rawStarMap
  congr 1
  rw [fieldLaw, FiniteLaw.expect_uniform, ZMod.card, sum_ite_mem, univ_inter,
    sum_image (fun a ha b hb h => hx (by simpa using ha) (by simpa using hb) h)]
  ring

noncomputable def centeredProductImage (S T : Finset U) (F : ZMod p → ℝ) (x : U → ZMod p) : ℝ :=
  (fieldLaw p).expect fun z => (StarMatrix.psi S z x - starMean S x) *
    (StarMatrix.psi T z x - starMean T x) * F z

omit [Fintype U] [DecidableEq U] in
theorem centeredProductImage_expand (S T : Finset U) (F : ZMod p → ℝ) (x : U → ZMod p) :
    centeredProductImage S T F x =
      (fieldLaw p).expect (fun z => StarMatrix.psi S z x * StarMatrix.psi T z x * F z) -
      starMean S x * rawStarMap T F x - starMean T x * rawStarMap S F x +
      (starMean S x * starMean T x) * (fieldLaw p).expect F := by
  have he (z : ZMod p) : (StarMatrix.psi S z x - starMean S x) *
      (StarMatrix.psi T z x - starMean T x) * F z =
      StarMatrix.psi S z x * StarMatrix.psi T z x * F z -
        starMean S x * (StarMatrix.psi T z x * F z) -
        starMean T x * (StarMatrix.psi S z x * F z) +
        (starMean S x * starMean T x) * F z := by ring
  unfold centeredProductImage
  simp_rw [he, FiniteLaw.expect_add, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul]
  rfl

omit [Fintype U] in
theorem centeredProductImage_mean_zero (S T : Finset U) (F : ZMod p → ℝ)
    (hF : (fieldLaw p).expect F = 0) (x : U → ZMod p) (hx : Set.InjOn x (S ∩ T)) :
    centeredProductImage S T F x =
      rawStarMap (S ∆ T) F x - (p : ℝ)⁻¹ *
        ∑ j ∈ S ∩ T, StarMatrix.psi (S ∆ T) (x j) x * F (x j) -
      starMean S x * rawStarMap T F x - starMean T x * rawStarMap S F x := by
  rw [centeredProductImage_expand, weighted_star_product S T F x hx, hF, mul_zero, add_zero]

omit [Fintype U] [DecidableEq U] in
theorem normalizedStarProduct_projectedDiagonal (S T : Finset U) (F : ZMod p → ℝ)
    (x : U → ZMod p) :
    normalizedStarProduct S T (fun z => projectedDiagonal F z.1 z.2) x =
      (p : ℝ) * centeredProductImage S T F x := by
  change (p : ℝ) * (fieldLaw p).expect (fun u => (fieldLaw p).expect
    (fun v => StarMatrix.psi S u x * StarMatrix.psi T v x * projectedDiagonal F u v)) = _
  rw [← FiniteLaw.expect_product (fieldLaw p) (fieldLaw p)
    (fun z => StarMatrix.psi S z.1 x * StarMatrix.psi T z.2 x * projectedDiagonal F z.1 z.2)]
  congr 1
  change Recentering.ip ((FiniteLaw.uniform (ZMod p)).product (FiniteLaw.uniform (ZMod p)))
    (fun z => StarMatrix.psi S z.1 x * StarMatrix.psi T z.2 x)
    (fun z => projectedDiagonal F z.1 z.2) = _
  rw [Recentering.ip_comm,
    projectedDiagonal_tensor F (fun u => StarMatrix.psi S u x) (fun v => StarMatrix.psi T v x)]
  change (fieldLaw p).expect (fun u => F u * StarMatrix.psi S u x * StarMatrix.psi T u x) -
    (fieldLaw p).expect (fun u => StarMatrix.psi T u x) *
      (fieldLaw p).expect (fun u => F u * StarMatrix.psi S u x) -
    (fieldLaw p).expect (fun u => StarMatrix.psi S u x) *
      (fieldLaw p).expect (fun u => F u * StarMatrix.psi T u x) +
    (fieldLaw p).expect F * (fieldLaw p).expect (fun u => StarMatrix.psi S u x) *
      (fieldLaw p).expect (fun u => StarMatrix.psi T u x) = _
  rw [starMean_expect_psi, starMean_expect_psi, centeredProductImage_expand]
  unfold rawStarMap
  have he (u : ZMod p) : F u * StarMatrix.psi S u x * StarMatrix.psi T u x =
      StarMatrix.psi S u x * StarMatrix.psi T u x * F u := by ring
  simp_rw [he, mul_comm (F _)]
  ring

end Sarkozy.PositiveRoots.CoherentFrame
