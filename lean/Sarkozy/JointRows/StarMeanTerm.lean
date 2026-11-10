module

public import Sarkozy.JointRows.StarSupportBounds
public import Sarkozy.JointRows.StarExpansion

/-! Complementary-mean terms retain the Paley decay after centring. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Finset Sarkozy.FiveType Sarkozy.FiveType.Blocks

theorem prod_add_sub_pure {I : Type*} [DecidableEq I] (T : Finset I) (m φ : I → ℝ) :
    (∏ j ∈ T, (m j + φ j)) - ∏ j ∈ T, φ j =
      ∑ R ∈ T.powerset.erase T, (∏ j ∈ T \ R, m j) * ∏ j ∈ R, φ j := by
  have h := Star.row_star_expand T 1 m φ
  simp only [one_mul] at h
  rw [h, ← add_sum_erase T.powerset
    (fun R => (∏ j ∈ T \ R, m j) * ∏ j ∈ R, φ j) (mem_powerset.mpr (Subset.refl T))]
  simp

theorem abs_prod_le_small {I : Type*} [DecidableEq I] (S : Finset I) (hS : S.Nonempty)
    (m : I → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hm : ∀ j ∈ S, |m j| ≤ β) :
    |∏ j ∈ S, m j| ≤ β := by
  obtain ⟨j, hj⟩ := hS
  rw [abs_prod, ← mul_prod_erase S (fun j => |m j|) hj]
  have hrest : ∏ i ∈ S.erase j, |m i| ≤ 1 := by
    calc _ ≤ ∏ _i ∈ S.erase j, (1 : ℝ) :=
          prod_le_prod₀ (fun _ _ => abs_nonneg _)
            (fun i hi => (hm i (mem_of_mem_erase hi)).trans hβ1)
      _ = 1 := prod_const_one
  calc _ ≤ β * 1 := mul_le_mul (hm j hj) hrest (by positivity) hβ0
    _ = β := mul_one β

variable {p : ℕ} [Fact p.Prime]
variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

theorem bform_sum {I : Type*} (νp : X → FiniteLaw (ZMod p))
    (νq : Y → FiniteLaw (ZMod p)) (R : Finset I)
    (K : I → (X → ZMod p) → (Y → ZMod p) → ℝ)
    (f : (X → ZMod p) → ℝ) (g : (Y → ZMod p) → ℝ) :
    bform νp νq (fun x y => ∑ i ∈ R, K i x y) f g =
      ∑ i ∈ R, bform νp νq (K i) f g := by
  simp only [bform, mul_sum, sum_mul, expect_finset_sum]

theorem bform_left_only (νp : X → FiniteLaw (ZMod p))
    (νq : Y → FiniteLaw (ZMod p)) (a f : (X → ZMod p) → ℝ)
    (g : (Y → ZMod p) → ℝ) (hg : (blockLaw νq).expect g = 0) :
    bform νp νq (fun x _ => a x) f g = 0 := by
  simp only [bform, FiniteLaw.expect_const_mul, hg, mul_zero, FiniteLaw.expect_const]

theorem rowMean_term_bound (hp : p ≠ 2)
    (νp : X → FiniteLaw (ZMod p)) (νq : Y → FiniteLaw (ZMod p))
    (i : X) (T : Finset Y) {c κ β : ℝ} (hc : |c| ≤ 1) (hκ : 0 ≤ κ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hdensX : ∀ t, (νp i).weight t ≤ κ / p)
    (hdensY : ∀ j ∈ T, ∀ t, (νq j).weight t ≤ κ / p)
    (hm : ∀ j ∈ T, ∀ t, (νp i).weight t ≠ 0 → |mchi (νq j) t| ≤ β)
    (f : (X → ZMod p) → ℝ) (g : (Y → ZMod p) → ℝ)
    (hg : (blockLaw νq).expect g = 0) :
    |bform νp νq (fun x y => c *
      ((∏ j ∈ T, (mchi (νq j) (x i) + phi (νq j) (x i) (y j))) -
        ∏ j ∈ T, phi (νq j) (x i) (y j))) f g| ≤
      2 ^ T.card * κ * (Real.sqrt p)⁻¹ * β * nrm (blockLaw νp) f * nrm (blockLaw νq) g := by
  let C := κ * (Real.sqrt p)⁻¹ * β * nrm (blockLaw νp) f * nrm (blockLaw νq) g
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hκ (by positivity)) hβ0)
      (FiveType.nrm_nonneg _ _)) (FiveType.nrm_nonneg _ _)
  have hexp : (fun (x : X → ZMod p) (y : Y → ZMod p) => c *
      ((∏ j ∈ T, (mchi (νq j) (x i) + phi (νq j) (x i) (y j))) -
        ∏ j ∈ T, phi (νq j) (x i) (y j))) =
      (fun x y => ∑ R ∈ T.powerset.erase T,
        (c * ∏ j ∈ T \ R, mchi (νq j) (x i)) *
          ∏ j ∈ R, phi (νq j) (x i) (y j)) := by
    funext x y
    rw [prod_add_sub_pure, mul_sum]
    exact sum_congr rfl fun R _ => by ring
  rw [hexp, bform_sum]
  have hterm (R : Finset Y) (hR : R ∈ T.powerset.erase T) :
      |bform νp νq (fun x y => (c * ∏ j ∈ T \ R, mchi (νq j) (x i)) *
        ∏ j ∈ R, phi (νq j) (x i) (y j)) f g| ≤ C := by
    by_cases h0 : R = ∅
    · subst R
      simpa only [prod_empty, mul_one, bform_left_only νp νq _ f g hg, abs_zero] using hC
    · have hsub : R ⊆ T := mem_powerset.mp (mem_of_mem_erase hR)
      have hdiff : (T \ R).Nonempty := sdiff_nonempty.mpr (fun hTR =>
        (mem_erase.mp hR).1 (Subset.antisymm hsub hTR))
      apply rowStar_multiplier_bound_support hp νp νq i R (nonempty_iff_ne_empty.mpr h0)
        (fun t => c * ∏ j ∈ T \ R, mchi (νq j) t) hκ hβ0
      · intro t ht
        rw [abs_mul]
        have hb := abs_prod_le_small (T \ R) hdiff (fun j => mchi (νq j) t) hβ0 hβ1
          (fun j hj => hm j (mem_sdiff.mp hj).1 t ht)
        exact (mul_le_mul hc hb (abs_nonneg _) (by norm_num)).trans_eq (one_mul β)
      · exact hdensX
      · exact fun j hj t => hdensY j (hsub hj) t
  calc _ ≤ ∑ R ∈ T.powerset.erase T, C :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
    _ = ((T.powerset.erase T).card : ℝ) * C := by simp
    _ ≤ (2 : ℝ) ^ T.card * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast (card_erase_le (s := T.powerset) (a := T)).trans_eq (card_powerset T)
    _ = _ := by dsimp [C]; ring

end Sarkozy.JointRows.StarOps
