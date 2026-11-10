module

public import Sarkozy.SpectralD.CollisionOperators

/-!
# Collision bounds for halves of size at most thirty-six

The same coefficient 2^35/p bounds all the smaller tail cuts. Count
products are compared using the half size as an upper bound.
-/

@[expose] public section

namespace Sarkozy.SpectralD.AtMost

open Finset Sarkozy.Labellings Sarkozy.Extraction

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem collision_Lint_lower (G : OrientedGraph U) (hn : Fintype.card U ≤ 36)
    (hd : ∀ i, rowsDeg0 G i ≤ 10) {q : ℝ} (hq : 2 ^ 64 ≤ q) :
    (9999 / 10000 : ℝ) ^ 36 ≤ collisionLint G q 36 := by
  have he : ∀ i, coarseError (rowsDeg0 G i) q 36 ≤ 1 / 10000 := fun i =>
    (coarseError_mono (by norm_num) (hd i)).trans (collision_error10 hq)
  calc (9999 / 10000 : ℝ) ^ 36 ≤ ∏ _i : U, (9999 / 10000 : ℝ) := by
        simp only [prod_const, card_univ]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    _ ≤ collisionLint G q 36 := prod_le_prod₀ (fun _ _ => by norm_num) (fun i _ => by
      dsimp
      linarith [he i])

theorem collision_Ups_upper (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U ≤ 36) (hd : ∀ i, rowsDeg0 G i ≤ 10)
    (hr : ∀ i, collisionR ς i ≤ 12) {q : ℝ} (hq : 2 ^ 64 ≤ q) :
    collisionUps G ς q 36 ≤ (101 / 100 : ℝ) ^ 36 := by
  have he : ∀ i, coarseError (rowsDeg0 G i + collisionR ς i) q 72 ≤ 1 / 100 := fun i =>
    (coarseError_mono (by norm_num) (by have := hd i; have := hr i; omega)).trans
      (collision_error22 hq)
  calc collisionUps G ς q 36 ≤ ∏ _i : U, (101 / 100 : ℝ) :=
        prod_le_prod₀ (fun i _ => by
          have := coarseError_nonneg (q := q) (by norm_num : (0 : ℝ) ≤ 72)
            (rowsDeg0 G i + collisionR ς i)
          norm_num only [Nat.cast_ofNat, show (2 : ℝ) * 36 = 72 by norm_num]
          linarith) (fun i _ => by
            norm_num only [Nat.cast_ofNat, show (2 : ℝ) * 36 = 72 by norm_num]
            linarith [he i])
    _ ≤ (101 / 100 : ℝ) ^ 36 := by
        simp only [prod_const, card_univ]
        exact pow_le_pow_right₀ (by norm_num) hn

theorem collision_count_ratio (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U ≤ 36) (hd : ∀ i, rowsDeg0 G i ≤ 10)
    (hr : ∀ i, collisionR ς i ≤ 12) {q : ℝ} (hq : 2 ^ 64 ≤ q) :
    collisionUps G ς q 36 / collisionLint G q 36 ≤ 2 := by
  have hL := collision_Lint_lower G hn hd hq
  have hU := collision_Ups_upper G ς hn hd hr hq
  have hL0 : 0 < collisionLint G q 36 := lt_of_lt_of_le (by positivity) hL
  apply (div_le_iff₀ hL0).mpr
  have hnum : (101 / 100 : ℝ) ^ 36 ≤ 2 * (9999 / 10000 : ℝ) ^ 36 := by norm_num
  linarith


theorem collision_weight_sum (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U ≤ 36) (hd : ∀ i, rowsDeg0 G i ≤ 10)
    (hr : ∀ i, collisionR ς i ≤ 12) :
    ∑ i, ∑ j, collisionA G ς i j ≤ 2 ^ 33 := by
  calc ∑ i, ∑ j, collisionA G ς i j ≤ ∑ _i : U, ∑ _j : U, (2 : ℝ) ^ 22 :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => collision_weight_bound G ς hd hr i j
    _ ≤ 2 ^ 33 := by
        simp only [sum_const, card_univ, nsmul_eq_mul]
        have hnR : (Fintype.card U : ℝ) ≤ 36 := by exact_mod_cast hn
        have hn0 : (0 : ℝ) ≤ Fintype.card U := Nat.cast_nonneg _
        nlinarith

theorem collisionXi_uniform (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U ≤ 36) (hd : ∀ i, rowsDeg0 G i ≤ 10)
    (hr : ∀ i, collisionR ς i ≤ 12) {q : ℝ} (hq : 0 < q) :
    0 ≤ collisionXi G ς q ∧ collisionXi G ς q ≤ 2 ^ 43 / q := by
  have hA : 0 ≤ ∑ i, ∑ j, collisionA G ς i j :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => by unfold collisionA; positivity
  have hΔ : collisionDeltaPlus G ≤ 10 := Finset.sup_le fun i _ => hd i
  have hs : Real.sqrt 2 ^ collisionDeltaPlus G ≤ (2 : ℝ) ^ 10 :=
    (pow_le_pow_left₀ (Real.sqrt_nonneg _) (by norm_num : Real.sqrt 2 ≤ (2 : ℝ)) _).trans
      (pow_le_pow_right₀ (by norm_num) hΔ)
  constructor
  · unfold collisionXi
    exact mul_nonneg (mul_nonneg (by positivity) (inv_nonneg.mpr hq.le)) hA
  · unfold collisionXi
    calc Real.sqrt 2 ^ collisionDeltaPlus G * q⁻¹ * ∑ i, ∑ j, collisionA G ς i j
        ≤ 2 ^ 10 * q⁻¹ * (2 ^ 33 : ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr hq.le))
            (collision_weight_sum G ς hn hd hr) hA (by positivity)
      _ = 2 ^ 43 / q := by norm_num [div_eq_mul_inv]; ring

theorem collision_exp_uniform (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U ≤ 36) (hd : ∀ i, rowsDeg0 G i ≤ 10)
    (hr : ∀ i, collisionR ς i ≤ 12) {q : ℝ} (hq : 2 ^ 64 ≤ q) :
    Real.exp (collisionXi G ς q) - 1 - collisionXi G ς q ≤ 2 ^ 33 / q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  obtain ⟨hX0, hX⟩ := collisionXi_uniform G ς hn hd hr hq0
  have hX1 : collisionXi G ς q ≤ 1 := hX.trans ((div_le_one hq0).mpr (by
    norm_num at hq ⊢
    linarith))
  refine (exp_remainder_le_square hX0 hX1).trans
    ((pow_le_pow_left₀ hX0 hX 2).trans ?_)
  have hnum : ((2 : ℝ) ^ 43) ^ 2 ≤ 2 ^ 33 * q := by
    norm_num at hq ⊢
    linarith
  rw [div_pow]
  calc ((2 : ℝ) ^ 43) ^ 2 / q ^ 2 ≤ (2 ^ 33 * q) / q ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = 2 ^ 33 / q := by field_simp

theorem collisionDnat_uniform (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U ≤ 36) (hd : ∀ i, rowsDeg0 G i ≤ 10)
    (hr : ∀ i, collisionR ς i ≤ 12) {q : ℝ} (hq : 2 ^ 64 ≤ q) :
    collisionDnat G ς q 36 ≤ 2 ^ 35 / q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hsum : q⁻¹ * ∑ i, ∑ j, collisionA G ς i j ≤ 2 ^ 33 / q := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (collision_weight_sum G ς hn hd hr)
      (inv_nonneg.mpr hq0.le)
  have hsum0 : 0 ≤ q⁻¹ * ∑ i, ∑ j, collisionA G ς i j :=
    mul_nonneg (inv_nonneg.mpr hq0.le)
      (sum_nonneg fun i _ => sum_nonneg fun j _ => by unfold collisionA; positivity)
  have hexp0 : 0 ≤ Real.exp (collisionXi G ς q) - 1 - collisionXi G ς q := by
    linarith [Real.add_one_le_exp (collisionXi G ς q)]
  unfold collisionDnat
  calc _ ≤ 2 * (2 ^ 33 / q + 2 ^ 33 / q) :=
        mul_le_mul (collision_count_ratio G ς hn hd hr hq)
          (add_le_add hsum (collision_exp_uniform G ς hn hd hr hq))
          (add_nonneg hsum0 hexp0) (by norm_num)
    _ = 2 ^ 35 / q := by norm_num; ring


theorem collisionDnat_nonneg (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U ≤ 36) (hd : ∀ i, rowsDeg0 G i ≤ 10)
    {q : ℝ} (hq : 2 ^ 64 ≤ q) : 0 ≤ collisionDnat G ς q 36 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hL : 0 < collisionLint G q 36 :=
    lt_of_lt_of_le (by positivity) (collision_Lint_lower G hn hd hq)
  have hU : 0 ≤ collisionUps G ς q 36 := prod_nonneg fun i _ => by
    exact add_nonneg zero_le_one (coarseError_nonneg (by positivity) _)
  unfold collisionDnat
  apply mul_nonneg (div_nonneg hU hL.le)
  apply add_nonneg
  · exact mul_nonneg (inv_nonneg.mpr hq0.le)
      (sum_nonneg fun i _ => sum_nonneg fun j _ => by unfold collisionA; positivity)
  · linarith [Real.add_one_le_exp (collisionXi G ς q)]

variable {p : ℕ} [Fact p.Prime]

theorem collOp_uniform {V : Type*} [Fintype V] [DecidableEq V] (D : Cuts.SpecData V)
    (hW : WeilBound (ZMod p)) (hp : 2 ^ 64 ≤ p)
    (hne : (injLabellings (ZMod p) D.G).Nonempty)
    (hn : Fintype.card D.cut.Half ≤ 36) (hd : ∀ i, rowsDeg0 D.halfGraph i ≤ 10)
    (hr : ∀ i, collisionR D.sgn i ≤ 12)
    (v : EuclideanSpace ℝ (D.cut.Half → ZMod p)) :
    ‖Cx.collOp D hne v‖ ≤ (2 ^ 35 / (p : ℝ)) * ‖v‖ := by
  have hp' : (2 : ℝ) ^ 64 ≤ p := by exact_mod_cast hp
  let rank : D.cut.Half → ℕ := fun i => (D.order.symm i).val
  have hi : Function.Injective rank := fun _ _ h => D.order.symm.injective (Fin.ext h)
  have hs : ∀ i, coarseError (rowsDeg0 D.halfGraph i) (Fintype.card (ZMod p)) 36 < 1 := by
    intro i
    rw [ZMod.card]
    exact lt_of_le_of_lt ((coarseError_mono (by norm_num) (hd i)).trans
      (collision_error10 hp')) (by norm_num)
  have hsign : ∀ j k, D.sgn j k = 0 ∨ D.sgn j k = 1 ∨ D.sgn j k = -1 := by
    intro j k
    unfold Cuts.SpecData.sgn
    split_ifs <;> simp
  have hb := collision_opBound_natural hW D.halfGraph D.sgn hsign D.sgn_antisymm
    (D.half_nonempty hne) hn hs (fun _ _ => rank) (fun _ _ _ _ _ _ h => hi h)
    (fun _ => rank) (fun _ => hi)
  rw [ZMod.card] at hb
  have hb' := hb.mono (collisionDnat_nonneg D.halfGraph D.sgn hn hd hp')
    (collisionDnat_uniform D.halfGraph D.sgn hn hd hr hp')
  have hk : Cx.collKer (p := p) D = collisionKernelColl D.sgn := by
    funext x y
    exact Cx.collKer_eq D x y
  unfold Cx.collOp
  rw [hk]
  exact Cx.kernelOp_norm_le_of_opBound D.halfGraph (D.half_nonempty hne) _
    (by positivity) hb' v


end Sarkozy.SpectralD.AtMost
