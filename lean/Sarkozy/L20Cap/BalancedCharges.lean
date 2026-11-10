module

public import Sarkozy.L20Cap.BalancedGeometry

/-!
# Actual incident weights and balanced row charges for L20

Identify the signed incident weights of the extraction theorem with the two
core charges and the private charge in `prop:l20-collisions`(a).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy.Extraction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def pinMinus (b₀ b₁ y : F) : ℝ :=
  (1 - chi (b₀ - y)) * (1 - chi (b₁ - y))

noncomputable def pinPlus (b₀ b₁ y : F) : ℝ :=
  (1 + chi (b₀ - y)) * (1 + chi (b₁ - y))

noncomputable def balancedIncident (x : Fin 6 → F) (i : Fin 6) (y : F) : ℝ :=
  ![pinMinus (x 2) (x 3) y, pinMinus (x 2) (x 3) y,
    Kz y ![x 0, x 1, x 4, x 5], Kz y ![x 0, x 1, x 4, x 5],
    pinPlus (x 2) (x 3) y, pinPlus (x 2) (x 3) y] i

theorem balancedW_signed (hm1 : quadraticChar F (-1) = -1)
    (x : Fin 6 → F) (i : Fin 6) (y : F) :
    collisionW D20Z x i y =
      ∏ k ∈ rowsN D20Z i, (1 + (D20Z k i : ℝ) * chi (y - x k)) := by
  unfold collisionW
  refine prod_congr rfl fun k hk => ?_
  have hs : D20Z k i = 1 ∨ D20Z k i = -1 :=
    (balanced_signs k i).resolve_left (mem_filter.mp hk).2
  rw [map_mul, collision_chi_sign hm1 hs]
  simp only [chi, Int.cast_mul]

theorem balancedW_eq (hm1 : quadraticChar F (-1) = -1)
    (x : Fin 6 → F) (i : Fin 6) (y : F) :
    collisionW D20Z x i y = balancedIncident x i y := by
  rw [balancedW_signed hm1, balanced_neighbours]
  have h2 := chi_sub_comm hm1 y (x 2)
  have h3 := chi_sub_comm hm1 y (x 3)
  fin_cases i <;>
    norm_num [balancedIncident, balancedPair, balancedCore, D20Z, pinMinus, pinPlus,
      Kz_four, h2, h3] <;> ring

theorem balancedAlpha_eq (hm1 : quadraticChar F (-1) = -1)
    (x : Fin 6 → F) (i j : Fin 6) :
    collisionAlphaTilde G6 D20Z x i j =
      if (i ∈ balancedPair ↔ j ∈ balancedPair) then balancedIncident x i (x j) else 0 := by
  unfold collisionAlphaTilde
  by_cases h : collisionGamma G6 D20Z i j
  · rw [ite_eq_left h, ite_eq_left ((balanced_gamma i j).mp h)]
    simp only [collisionAlpha, balanced_mg i j h, pow_zero, mul_one, balancedW_eq hm1]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((balanced_gamma i j).mpr h'))]

/-- The charge at either `a` coordinate. Here `Q` is the field size. -/
noncomputable def balancedA (Q : ℝ) (x : CoreT F × PairT F) : ℝ :=
  Q⁻¹ * ∑ k, pinMinus x.2.1.1 x.2.1.2 (x.1.1 k)

/-- The charge at either `c` coordinate. -/
noncomputable def balancedC (Q : ℝ) (x : CoreT F × PairT F) : ℝ :=
  Q⁻¹ * ∑ k, pinPlus x.2.1.1 x.2.1.2 (x.1.1 k)

/-- The common charge at the two private coordinates. -/
noncomputable def balancedB (Q : ℝ) (x : CoreT F × PairT F) : ℝ :=
  Q⁻¹ * (Kz x.2.1.1 x.1.1 + Kz x.2.1.2 x.1.1)

/-- All six actual row charges, with the sixteen impossible pin types removed. -/
theorem balancedRho_eq (hm1 : quadraticChar F (-1) = -1) {Q : ℝ} (hQ : 0 < Q)
    (x : CoreT F × PairT F) (i : Fin 6) :
    collisionRhoTilde G6 D20Z Q (labels x) i =
      ![balancedA Q x, balancedA Q x, balancedB Q x, balancedB Q x,
        balancedC Q x, balancedC Q x] i := by
  unfold collisionRhoTilde
  rw [coverRow_r_sq hQ]
  simp_rw [balancedAlpha_eq hm1]
  fin_cases i <;>
    simp [Fin.sum_univ_six, balancedPair, balancedIncident, labels, emb,
      balancedA, balancedB, balancedC, Fin.sum_univ_four, Kz_four]

theorem balancedA_nonneg (hm1 : quadraticChar F (-1) = -1) {Q : ℝ} (hQ : 0 < Q)
    (x : CoreT F × PairT F) : 0 ≤ balancedA Q x := by
  simpa only [balancedRho_eq hm1 hQ, Matrix.cons_val_zero] using
    collisionRhoTilde_nonneg G6 D20Z Q (labels x) 0

theorem balancedB_nonneg (hm1 : quadraticChar F (-1) = -1) {Q : ℝ} (hQ : 0 < Q)
    (x : CoreT F × PairT F) : 0 ≤ balancedB Q x := by
  simpa [balancedRho_eq hm1 hQ] using
    collisionRhoTilde_nonneg G6 D20Z Q (labels x) 2

theorem balancedC_nonneg (hm1 : quadraticChar F (-1) = -1) {Q : ℝ} (hQ : 0 < Q)
    (x : CoreT F × PairT F) : 0 ≤ balancedC Q x := by
  simpa [balancedRho_eq hm1 hQ] using
    collisionRhoTilde_nonneg G6 D20Z Q (labels x) 4

/-- The joint bound is stronger than bounding each core charge separately. -/
theorem balancedAC_le {Q : ℝ} (hQ : 0 < Q) (x : CoreT F × PairT F) (hx : Avoid x) :
    balancedA Q x + balancedC Q x ≤ 16 * Q⁻¹ := by
  have h := charges_core_le x.1.1 x.2.1.1 x.2.1.2 hx.1 hx.2
  have he : balancedA Q x + balancedC Q x = Q⁻¹ *
      ∑ k, (pinMinus x.2.1.1 x.2.1.2 (x.1.1 k) +
        pinPlus x.2.1.1 x.2.1.2 (x.1.1 k)) := by
    rw [sum_add_distrib, mul_add]
    rfl
  rw [he]
  simpa only [pinMinus, pinPlus, mul_comm] using
    mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hQ.le)

theorem balancedB_le (hm1 : quadraticChar F (-1) = -1) {Q : ℝ} (hQ : 0 < Q)
    (x : CoreT F × PairT F) : balancedB Q x ≤ 32 * Q⁻¹ :=
  pair_charge_le hm1 x.1.2 x.2.1.1 x.2.1.2 (inv_nonneg.mpr hQ.le)

end Sarkozy.L20Cap
