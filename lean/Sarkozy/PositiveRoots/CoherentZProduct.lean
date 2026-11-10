module

public import Sarkozy.PositiveRoots.CoherentProductActual

/-! A core-star product with the complete signed Z feature has residual norm at most 22. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering

theorem abs_coreSign (S : Finset (Fin 4)) : |sig S| = 1 := by
  have hs (i : Fin 4) : |sgn i| = 1 := by fin_cases i <;> norm_num [sgn]
  unfold sig
  rw [abs_prod]
  simp only [hs, prod_const_one]

theorem core_product_cost_sum {S : Finset (Fin 4)} (hS : S.Nonempty) :
    (∑ T ∈ nonemptySets (Fin 4), (if S = T then (9 : ℝ) else 5)) = 79 := by
  have hmem : S ∈ nonemptySets (Fin 4) := mem_filter.mpr ⟨mem_univ _, hS⟩
  have hcard : (nonemptySets (Fin 4)).card = 15 := by decide +kernel
  have he (T : Finset (Fin 4)) : (if S = T then (9 : ℝ) else 5) =
      5 + if S = T then 4 else 0 := by split_ifs <;> norm_num
  simp only [he, sum_add_distrib, sum_const, nsmul_eq_mul, hcard, sum_ite_eq, hmem, ite_true]
  norm_num

variable {p : ℕ} [Fact p.Prime]

noncomputable def coreZProduct (S : Finset (Fin 4)) (F : ZMod p × ZMod p → ℝ)
    (x : Fin 4 → ZMod p) : ℝ :=
  (Real.sqrt 15)⁻¹ * ∑ T ∈ nonemptySets (Fin 4), sig T * normalizedStarProduct S T F x

noncomputable def coreZExceptional (S : Finset (Fin 4)) (F : ZMod p × ZMod p → ℝ) : ℝ :=
  (sig S / Real.sqrt 15) * entangledCoefficient F * ((p : ℝ) / Real.sqrt (p - 1))

theorem coreZProduct_residual {S : Finset (Fin 4)} (hS : S.Nonempty)
    (F : ZMod p × ZMod p → ℝ) (x : Fin 4 → ZMod p) :
    coreZProduct S F x - coreZExceptional S F =
      (Real.sqrt 15)⁻¹ * ∑ T ∈ nonemptySets (Fin 4), sig T * reducedStarProduct S T F x := by
  have hmem : S ∈ nonemptySets (Fin 4) := mem_filter.mpr ⟨mem_univ _, hS⟩
  have he : (∑ T ∈ nonemptySets (Fin 4), sig T * productExceptional S T F) =
      sig S * (entangledCoefficient F * ((p : ℝ) / Real.sqrt (p - 1))) := by
    simp only [productExceptional, mul_ite, mul_zero, sum_ite_eq, hmem, ite_true]
  unfold coreZProduct coreZExceptional reducedStarProduct
  simp only [mul_sub, sum_sub_distrib, he]
  ring

variable [Nonempty (CoreT (ZMod p))]

theorem coreZProduct_residual_norm (hW : Labellings.WeilBound (ZMod p))
    (hDLK : Target.FourCycle) (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p)
    (S : Finset (Fin 4)) (hS : 2 ≤ S.card) (F : ZMod p × ZMod p → ℝ)
    (hrow : ∀ u, (fieldLaw p).expect (fun v => F (u, v)) = 0)
    (hcol : ∀ v, (fieldLaw p).expect (fun u => F (u, v)) = 0) :
    nrm coreLaw (fun c : CoreT (ZMod p) => coreZProduct S F c.val - coreZExceptional S F) ≤
      22 * nrm ((fieldLaw p).product (fieldLaw p)) F := by
  have hSne : S.Nonempty := card_pos.mp (by omega)
  have hsum : nrm coreLaw (fun c : CoreT (ZMod p) =>
      ∑ T ∈ nonemptySets (Fin 4), sig T * reducedStarProduct S T F c.val) ≤
        79 * nrm ((fieldLaw p).product (fieldLaw p)) F := by
    refine (nrm_sum_le coreLaw (nonemptySets (Fin 4))
      (fun T (c : CoreT (ZMod p)) => sig T * reducedStarProduct S T F c.val)).trans ?_
    calc
      _ ≤ ∑ T ∈ nonemptySets (Fin 4),
          (if S = T then 9 else 5) * nrm ((fieldLaw p).product (fieldLaw p)) F := by
        apply sum_le_sum
        intro T hT
        rw [nrm_smul, abs_coreSign, one_mul]
        exact core_reducedStarProduct_norm_9_5 hW hDLK hp3 hp40 S T hSne (mem_filter.mp hT).2
          (hS.trans (card_le_card subset_union_left)) F hrow hcol
      _ = _ := by rw [← sum_mul, core_product_cost_sum hSne]
  simp_rw [coreZProduct_residual hSne]
  rw [nrm_smul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt 15)⁻¹)]
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans ?_
  have hs : (19 / 5 : ℝ) ≤ Real.sqrt 15 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hn : (Real.sqrt 15)⁻¹ * 79 ≤ (22 : ℝ) := by
    rw [mul_comm, ← div_eq_mul_inv, div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 15)]
    linarith
  calc
    _ = ((Real.sqrt 15)⁻¹ * 79) * nrm ((fieldLaw p).product (fieldLaw p)) F := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hn (nrm_nonneg _ _)

end Sarkozy.PositiveRoots.CoherentFrame
