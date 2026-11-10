module

public import Sarkozy.JointRows.StarMeanBound

/-! Coarse full form bounds for star terms, including their constant images. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Finset Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.JointRows.PaleyGauss

variable {p : ℕ} [Fact p.Prime]
variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

theorem bform_left_only_bound (νp : X → FiniteLaw (ZMod p))
    (νq : Y → FiniteLaw (ZMod p)) (a f : (X → ZMod p) → ℝ)
    (g : (Y → ZMod p) → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (ha : ∀ x, (blockLaw νp).weight x ≠ 0 → |a x| ≤ b) :
    |bform νp νq (fun x _ => a x) f g| ≤
      b * nrm (blockLaw νp) f * nrm (blockLaw νq) g := by
  have h1 : nrm (blockLaw νp) (fun _ => 1) = 1 := by
    simp [nrm, ip, FiniteLaw.expect_const]
  have ha' : nrm (blockLaw νp) a ≤ b := by
    simpa only [mul_one, h1] using
      nrm_mul_le (blockLaw νp) a (fun _ => 1) hb ha
  have hf := (abs_ip_le (blockLaw νp) f a).trans
    (mul_le_mul_of_nonneg_left ha' (FiveType.nrm_nonneg _ _))
  have hg : |(blockLaw νq).expect g| ≤ nrm (blockLaw νq) g :=
    Cuts.abs_expect_le_nrm _ _
  simp only [bform, FiniteLaw.expect_const_mul, FiniteLaw.expect_mul_const, abs_mul]
  have h := mul_le_mul hf hg (abs_nonneg _)
    (mul_nonneg (FiveType.nrm_nonneg _ _) hb)
  unfold ip at h
  convert h using 1; ring

theorem row_star_full_bound (hp : p ≠ 2)
    (νp : X → FiniteLaw (ZMod p)) (νq : Y → FiniteLaw (ZMod p))
    (i : X) (T : Finset Y) (hT : T.Nonempty) {c κ β : ℝ}
    (hc : |c| ≤ 1) (hκ : 0 ≤ κ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hdensX : ∀ t, (νp i).weight t ≤ κ / p)
    (hdensY : ∀ j ∈ T, ∀ t, (νq j).weight t ≤ κ / p)
    (hm : ∀ j ∈ T, ∀ t, (νp i).weight t ≠ 0 → |mchi (νq j) t| ≤ β)
    (f : (X → ZMod p) → ℝ) (g : (Y → ZMod p) → ℝ) :
    |bform νp νq (fun x y => c * ∏ j ∈ T, chiR p (x i - y j)) f g| ≤
      2 ^ T.card * (κ * (Real.sqrt p)⁻¹ + β) *
        nrm (blockLaw νp) f * nrm (blockLaw νq) g := by
  have hnf := FiveType.nrm_nonneg (blockLaw νp) f
  have hng := FiveType.nrm_nonneg (blockLaw νq) g
  let C := (κ * (Real.sqrt p)⁻¹ + β) * nrm (blockLaw νp) f * nrm (blockLaw νq) g
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (add_nonneg (mul_nonneg hκ (by positivity)) hβ0)
      (FiveType.nrm_nonneg _ _)) (FiveType.nrm_nonneg _ _)
  have hexp : (fun (x : X → ZMod p) (y : Y → ZMod p) =>
      c * ∏ j ∈ T, chiR p (x i - y j)) = fun x y =>
      ∑ R ∈ T.powerset, (c * ∏ j ∈ T \ R, mchi (νq j) (x i)) *
        ∏ j ∈ R, phi (νq j) (x i) (y j) := by
    funext x y
    rw [prod_congr rfl fun j _ => chiR_eq_mchi_add_phi (νq j) (x i) (y j)]
    rw [Star.row_star_expand, mul_sum]
    exact sum_congr rfl fun R _ => by ring
  rw [hexp, bform_sum]
  have hterm (R : Finset Y) (hR : R ∈ T.powerset) :
      |bform νp νq (fun x y => (c * ∏ j ∈ T \ R, mchi (νq j) (x i)) *
        ∏ j ∈ R, phi (νq j) (x i) (y j)) f g| ≤ C := by
    by_cases h0 : R = ∅
    · subst R
      simp only [sdiff_empty, prod_empty, mul_one]
      have hh := bform_left_only_bound νp νq
        (fun x => c * ∏ j ∈ T, mchi (νq j) (x i)) f g hβ0 (fun x hx => by
          rw [abs_mul]
          have hp := abs_prod_le_small T hT (fun j => mchi (νq j) (x i)) hβ0 hβ1
            (fun j hj => hm j hj _ (block_coordinate_ne_zero νp x hx i))
          exact (mul_le_mul hc hp (abs_nonneg _) (by norm_num)).trans_eq (one_mul β))
      apply hh.trans
      dsimp [C]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_nonneg hκ
          (by positivity : (0 : ℝ) ≤ (Real.sqrt p)⁻¹))) hnf) hng
    · have hsub := mem_powerset.mp hR
      have hh := rowStar_multiplier_bound_support hp νp νq i R
        (nonempty_iff_ne_empty.mpr h0)
        (fun t => c * ∏ j ∈ T \ R, mchi (νq j) t) hκ (by norm_num : (0 : ℝ) ≤ 1)
        (fun t _ => by
          rw [abs_mul]
          have hm1 (j : Y) : |mchi (νq j) t| ≤ 1 :=
            (νq j).abs_expect_le_const fun a => abs_chiR_le_one (t - a)
          exact (mul_le_mul hc (abs_prod_le_one _ _ hm1) (abs_nonneg _)
            (by norm_num)).trans_eq (one_mul 1))
        hdensX (fun j hj => hdensY j (hsub hj)) f g
      apply hh.trans
      dsimp [C]
      simp only [mul_one]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hβ0) hnf) hng
  calc
    _ ≤ ∑ _R ∈ T.powerset, C :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_powerset, Nat.cast_pow,
        Nat.cast_ofNat, C]; ring

end Sarkozy.JointRows.StarOps
