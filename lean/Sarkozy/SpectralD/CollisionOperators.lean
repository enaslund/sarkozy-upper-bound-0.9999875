module

public import Sarkozy.SpectralD.CollisionUniform
public import Sarkozy.SpectralD.CxBridge
public import Sarkozy.SpectralD.CxExpansion
public import Sarkozy.SpectralD.RootChecks

/-!
# Collision bounds on the actual LL20 and LL22 operators

The natural collision theorem and the uniform scalar estimate give 2^35/p
at every prime p ≥ 2^64, for both prime classes. At tail primes this is at
most 2^(-200)/sqrt(p). The vertex orders are supplied explicitly.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.Labellings Sarkozy.Extraction

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem rowsDeg0_eq_full_nbrCount (G : OrientedGraph U) (i : U) :
    rowsDeg0 G i = nbrCount G (univ.erase i) i := by
  unfold rowsDeg0 rowsAdj nbrCount
  congr 1
  ext j
  by_cases h : j = i
  · subst j
    simp [G.loopless]
  · simp [h]

theorem collisionDnat_nonneg (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U = 36) (hd : ∀ i, rowsDeg0 G i ≤ 10)
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
    (hn : Fintype.card D.cut.Half = 36) (hd : ∀ i, rowsDeg0 D.halfGraph i ≤ 10)
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
    (D.half_nonempty hne) hn.le hs (fun _ _ => rank) (fun _ _ _ _ _ _ h => hi h)
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

theorem LL20_collOp_bound (hW : WeilBound (ZMod p)) (hp : 2 ^ 64 ≤ p)
    (hne : (injLabellings (ZMod p) Root.LL20.G).Nonempty)
    (v : EuclideanSpace ℝ (Root.LL20.cut.Half → ZMod p)) :
    ‖Cx.collOp Root.LL20 hne v‖ ≤ (2 ^ 35 / (p : ℝ)) * ‖v‖ :=
  collOp_uniform Root.LL20 hW hp hne Root.LL20_card_half
    (fun i => by rw [rowsDeg0_eq_full_nbrCount]; exact Root.LL20_d0_le i) Root.LL20_r_le v

theorem LL22_collOp_bound (hW : WeilBound (ZMod p)) (hp : 2 ^ 64 ≤ p)
    (hne : (injLabellings (ZMod p) Root.LL22.G).Nonempty)
    (v : EuclideanSpace ℝ (Root.LL22.cut.Half → ZMod p)) :
    ‖Cx.collOp Root.LL22 hne v‖ ≤ (2 ^ 35 / (p : ℝ)) * ‖v‖ :=
  collOp_uniform Root.LL22 hW hp hne Root.LL22_card_half
    (fun i => by rw [rowsDeg0_eq_full_nbrCount]; exact Root.LL22_d0_le i)
    (fun i => (Root.LL22_r_le i).trans (by norm_num)) v

theorem collision_tail_scalar {q : ℕ} (hq : 2 ^ 512 ≤ q) :
    2 ^ 35 / (q : ℝ) ≤ 2⁻¹ ^ 200 * (Real.sqrt q)⁻¹ := by
  have hs : (2 : ℝ) ^ 256 ≤ Real.sqrt q := by
    have h := Real.sqrt_le_sqrt (show (2 : ℝ) ^ 512 ≤ q by exact_mod_cast hq)
    rwa [show 512 = 256 * 2 by rfl, pow_mul, Real.sqrt_sq (by positivity)] at h
  have hcoef : (2 : ℝ) ^ 35 * (Real.sqrt q)⁻¹ ≤ 2⁻¹ ^ 200 := by
    refine (mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hs) (by positivity)).trans ?_
    norm_num
  calc 2 ^ 35 / (q : ℝ) = (2 ^ 35 * (Real.sqrt q)⁻¹) * (Real.sqrt q)⁻¹ := by
        rw [mul_assoc, ← pow_two, inv_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
        rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem LL20_collOp_tail (hW : WeilBound (ZMod p)) (hp : 2 ^ 512 ≤ p)
    (hne : (injLabellings (ZMod p) Root.LL20.G).Nonempty)
    (v : EuclideanSpace ℝ (Root.LL20.cut.Half → ZMod p)) :
    ‖Cx.collOp Root.LL20 hne v‖ ≤ 2⁻¹ ^ 200 * (Real.sqrt p)⁻¹ * ‖v‖ :=
  (LL20_collOp_bound hW (by omega) hne v).trans
    (mul_le_mul_of_nonneg_right (collision_tail_scalar hp) (norm_nonneg _))

theorem LL22_collOp_tail (hW : WeilBound (ZMod p)) (hp : 2 ^ 512 ≤ p)
    (hne : (injLabellings (ZMod p) Root.LL22.G).Nonempty)
    (v : EuclideanSpace ℝ (Root.LL22.cut.Half → ZMod p)) :
    ‖Cx.collOp Root.LL22 hne v‖ ≤ 2⁻¹ ^ 200 * (Real.sqrt p)⁻¹ * ‖v‖ :=
  (LL22_collOp_bound hW (by omega) hne v).trans
    (mul_le_mul_of_nonneg_right (collision_tail_scalar hp) (norm_nonneg _))

end Sarkozy.SpectralD
