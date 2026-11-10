module

public import Sarkozy.SpectralC.TwoLabelMaps
public import Sarkozy.JointRows.CubeCoordinates

/-! Isolating the two output coordinates that control a product of raw stars. -/

@[expose] public section

namespace Sarkozy.SpectralC.TwoLabel

open Finset Sarkozy.FiveType Sarkozy.FiveType.Blocks
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [DecidableEq ι]

noncomputable def starProduct (S T : Finset ι) (F : ZMod p → ZMod p → ℝ)
    (x : ι → ZMod p) : ℝ :=
  (fieldLaw p).expect (fun u => (fieldLaw p).expect (fun v =>
    (∏ i ∈ S, chiRe (u - x i)) * (∏ j ∈ T, chiRe (v - x j)) * F u v))

theorem character_product_update (S : Finset ι) (x : ι → ZMod p) (i : ι)
    (a u : ZMod p) :
    (∏ k ∈ S, chiRe (u - Function.update x i a k)) =
      (if i ∈ S then chiRe (u - a) else 1) * ∏ k ∈ S.erase i, chiRe (u - x k) := by
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi, ← mul_prod_erase S _ hi, Function.update_self]
    congr 1
    exact prod_congr rfl fun k hk => by rw [Function.update_of_ne (ne_of_mem_erase hk)]
  · rw [ite_eq_right hi, one_mul, erase_eq_of_notMem hi]
    apply prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hi)]

theorem character_product_update_two (S : Finset ι) (x : ι → ZMod p)
    {i j : ι} (hij : i ≠ j) (a b u : ZMod p) :
    (∏ k ∈ S, chiRe (u - Function.update (Function.update x i a) j b k)) =
      (if i ∈ S then chiRe (u - a) else 1) *
      (if j ∈ S then chiRe (u - b) else 1) *
        ∏ k ∈ (S.erase i).erase j, chiRe (u - x k) := by
  rw [character_product_update, character_product_update]
  have he : (S.erase j).erase i = (S.erase i).erase j := erase_right_comm
  rw [he]
  have hm : i ∈ S.erase j ↔ i ∈ S := mem_erase.trans ⟨fun h => h.2, fun h => ⟨hij, h⟩⟩
  rw [if_congr hm rfl rfl]
  ring

noncomputable def productRest (S T : Finset ι) (i j : ι) (x : ι → ZMod p)
    (u v : ZMod p) : ℝ :=
  (∏ k ∈ (S.erase i).erase j, chiRe (u - x k)) *
    (∏ k ∈ (T.erase i).erase j, chiRe (v - x k))

theorem productRest_sq (S T : Finset ι) (i j : ι) (x : ι → ZMod p) (u v : ZMod p) :
    productRest S T i j x u v ^ 2 ≤ 1 := by
  have h (A : Finset ι) (z : ZMod p) : |∏ k ∈ A, chiRe (z - x k)| ≤ 1 := by
    rw [abs_prod]
    exact prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_chiRe_le _)
  apply (sq_le_one_iff_abs_le_one _).mpr
  rw [productRest, abs_mul]
  exact (mul_le_mul (h _ _) (h _ _) (abs_nonneg _) (by norm_num)).trans (by norm_num)

theorem starProduct_distinct_coordinates (S T : Finset ι) {i j : ι}
    (hiS : i ∈ S) (hiT : i ∉ T) (hjT : j ∈ T) (F : ZMod p → ZMod p → ℝ)
    (x : ι → ZMod p) (a b : ZMod p) :
    starProduct S T F (Function.update (Function.update x i a) j b) =
      distinctMap (decide (j ∈ S)) (fun u v => productRest S T i j x u v * F u v) a b := by
  have hij : i ≠ j := fun h => hiT (h ▸ hjT)
  unfold starProduct distinctMap productRest
  apply FiniteLaw.expect_congr
  intro u
  apply FiniteLaw.expect_congr
  intro v
  rw [character_product_update_two S x hij, character_product_update_two T x hij]
  simp only [ite_eq_left hiS, ite_eq_right hiT, ite_eq_left hjT, one_mul, decide_eq_true_eq]
  ring

theorem starProduct_equal_coordinates (S : Finset ι) {i j : ι}
    (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) (F : ZMod p → ZMod p → ℝ)
    (x : ι → ZMod p) (a b : ZMod p) :
    (if a = b then 0 else starProduct S S F (Function.update (Function.update x i a) j b)) =
      equalMap (fun u v => productRest S S i j x u v * F u v) a b := by
  unfold equalMap
  split_ifs
  · rfl
  · unfold starProduct productRest
    apply FiniteLaw.expect_congr
    intro u
    apply FiniteLaw.expect_congr
    intro v
    rw [character_product_update_two S x hij, character_product_update_two S x hij]
    simp only [ite_eq_left hi, ite_eq_left hj]
    ring

end Sarkozy.SpectralC.TwoLabel
