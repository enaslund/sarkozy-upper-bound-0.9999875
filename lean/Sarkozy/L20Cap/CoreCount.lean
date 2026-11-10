module

public import Sarkozy.L20Cap.HalfCount
public import Sarkozy.SpectralC.StarProductCube

/-! Exact core cardinality and comparison with four independent labels. -/

@[expose] public section

namespace Sarkozy.L20Cap

open Finset Sarkozy.Variance.WeightedMoment
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

def fourEquiv : (Fin 4 → ZMod p) ≃ ZMod p × ZMod p × ZMod p × ZMod p where
  toFun x := (x 0, x 1, x 2, x 3)
  invFun y := ![y.1, y.2.1, y.2.2.1, y.2.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

theorem adm_iff_isAdm (x : Fin 4 → ZMod p) :
    Adm x ↔ IsAdm p (x 0) (x 1) (x 2) (x 3) := by
  constructor
  · rintro ⟨hi, h02, h03, h12, h13⟩
    exact ⟨fun h => by have := hi h; norm_num at this,
      fun h => by have := hi h; norm_num at this, h02, h03, h12, h13⟩
  · rintro ⟨h01, h23, h02, h03, h12, h13⟩
    refine ⟨?_, h02, h03, h12, h13⟩
    have hn02 := weightedMoment_ne_of_chi p h02
    have hn03 := weightedMoment_ne_of_chi p h03
    have hn12 := weightedMoment_ne_of_chi p h12
    have hn13 := weightedMoment_ne_of_chi p h13
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

theorem card_coreT_eq_nAdm : (Fintype.card (CoreT (ZMod p)) : ℤ) = nAdm p := by
  have hc : (Fintype.card (CoreT (ZMod p)) : ℤ) =
      ∑ x : Fin 4 → ZMod p, if Adm x then (1 : ℤ) else 0 := by
    rw [sum_boole]
    congr 1
    exact Fintype.card_subtype _
  rw [hc]
  calc
    _ = ∑ y : ZMod p × ZMod p × ZMod p × ZMod p,
        if IsAdm p y.1 y.2.1 y.2.2.1 y.2.2.2 then (1 : ℤ) else 0 := by
      apply Fintype.sum_equiv fourEquiv
      intro x
      change (if Adm x then (1 : ℤ) else 0) =
        if IsAdm p (x 0) (x 1) (x 2) (x 3) then 1 else 0
      simp only [adm_iff_isAdm]
    _ = nAdm p := by simp only [Fintype.sum_prod_type, nAdm]

theorem card_coreT (hp3 : p % 4 = 3) :
    16 * (Fintype.card (CoreT (ZMod p)) : ℝ) =
      (p : ℝ) * (p - 1) * (p - 3) * (p - 7) := by
  have h := weightedMoment_nAdm p hp3
  rw [← card_coreT_eq_nAdm] at h
  exact_mod_cast h

noncomputable def coreCubeDensity (p : ℕ) : ℝ :=
  16 / ((1 - 1 / p) * (1 - 3 / p) * (1 - 7 / p))

omit [Fact p.Prime] in
theorem coreCubeDensity_pos (h7 : 7 < p) : 0 < coreCubeDensity p := by
  have hp : (7 : ℝ) < p := by exact_mod_cast h7
  unfold coreCubeDensity
  apply div_pos (by norm_num)
  apply mul_pos
  · apply mul_pos <;> apply sub_pos.mpr <;> rw [div_lt_one (by linarith)] <;> linarith
  · apply sub_pos.mpr
    rw [div_lt_one (by linarith)]
    exact hp

theorem coreLaw_cube_comparison [Nonempty (CoreT (ZMod p))]
    (hp3 : p % 4 = 3) (hp7 : 7 < p) (f : (Fin 4 → ZMod p) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (coreLaw (F := ZMod p)).expect (fun c => f c.val) ≤
      coreCubeDensity p * (SpectralC.TwoLabel.cube p (Fin 4)).expect f := by
  have hp : (7 : ℝ) < p := by exact_mod_cast hp7
  have hc : (0 : ℝ) < Fintype.card (CoreT (ZMod p)) := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ c : CoreT (ZMod p), f c.val) ≤ ∑ x, f x := by
    rw [← sum_subtype (univ.filter (fun x : Fin 4 → ZMod p => Adm x)) (by simp) f]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun x _ _ => hf x)
  have hw : (SpectralC.TwoLabel.cube p (Fin 4)).expect f = (∑ x, f x) / (p : ℝ) ^ 4 := by
    unfold FiniteLaw.expect SpectralC.TwoLabel.cube FiveType.Blocks.blockLaw
      SpectralC.TwoLabel.fieldLaw FiniteLaw.uniform
    simp only [ZMod.card, prod_const, card_univ, Fintype.card_fin, ← mul_sum]
    rw [inv_pow]
    ring
  rw [coreLaw, FiniteLaw.expect_uniform, hw]
  calc
    _ ≤ (∑ x, f x) / (Fintype.card (CoreT (ZMod p)) : ℝ) :=
      div_le_div_of_nonneg_right hsum hc.le
    _ = _ := by
      have hn := card_coreT hp3
      unfold coreCubeDensity
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hp3' : (p : ℝ) - 3 ≠ 0 := by linarith
      have hp7' : (p : ℝ) - 7 ≠ 0 := by linarith
      field_simp
      linear_combination -(∑ x, f x) * hn

end Sarkozy.L20Cap
