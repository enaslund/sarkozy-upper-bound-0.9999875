module

public import Sarkozy.SpectralC.StarProductCoordinates

/-! The actual raw-star product bounds on an independent cube. -/

@[expose] public section

namespace Sarkozy.SpectralC.TwoLabel

open Finset Sarkozy.FiveType Sarkozy.FiveType.Blocks
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def cube (p : ℕ) [Fact p.Prime] (ι : Type*) [Fintype ι] [DecidableEq ι] :
    FiniteLaw (ι → ZMod p) := blockLaw (fun _ : ι => fieldLaw p)

omit [Fintype ι] in
theorem productRest_energy (S T : Finset ι) (i j : ι) (x : ι → ZMod p)
    (F : ZMod p → ZMod p → ℝ) :
    (fieldLaw p).expect (fun u => (fieldLaw p).expect
      (fun v => (productRest S T i j x u v * F u v) ^ 2)) ≤
        (fieldLaw p).expect (fun u => (fieldLaw p).expect (fun v => F u v ^ 2)) := by
  apply FiniteLaw.expect_mono
  intro u
  apply FiniteLaw.expect_mono
  intro v
  rw [mul_pow]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (productRest_sq S T i j x u v) (sq_nonneg (F u v))

theorem starProduct_sq_of_mem (hp : p ≠ 2) (S T : Finset ι) {i j : ι}
    (hiS : i ∈ S) (hiT : i ∉ T) (hjT : j ∈ T) (F : ZMod p → ZMod p → ℝ) :
    (cube p ι).expect (fun x => starProduct S T F x ^ 2) ≤
      (p : ℝ)⁻¹ ^ 2 * (fieldLaw p).expect (fun u => (fieldLaw p).expect (fun v => F u v ^ 2)) := by
  apply JointRows.Star.expect_two_coordinate_bound (fun _ : ι => fieldLaw p) i j
  intro x
  simp_rw [starProduct_distinct_coordinates S T hiS hiT hjT]
  exact (distinctMap_sq hp (decide (j ∈ S))
    (fun u v => productRest S T i j x u v * F u v)).trans
      (mul_le_mul_of_nonneg_left (productRest_energy S T i j x F) (sq_nonneg _))

omit [Fintype ι] [DecidableEq ι] in
theorem starProduct_swap (S T : Finset ι) (F : ZMod p → ZMod p → ℝ) (x : ι → ZMod p) :
    starProduct S T F x = starProduct T S (fun u v => F v u) x := by
  unfold starProduct
  rw [Cuts.expect_comm]
  apply FiniteLaw.expect_congr
  intro v
  apply FiniteLaw.expect_congr
  intro u
  ring

/-- Different nonempty supports cost `q`, without a four-cycle input. -/
theorem starProduct_distinct_sq (hp : p ≠ 2) (S T : Finset ι)
    (hS : S.Nonempty) (hT : T.Nonempty) (hne : S ≠ T) (F : ZMod p → ZMod p → ℝ) :
    (cube p ι).expect (fun x => starProduct S T F x ^ 2) ≤
      (p : ℝ)⁻¹ ^ 2 * (fieldLaw p).expect (fun u => (fieldLaw p).expect (fun v => F u v ^ 2)) := by
  by_cases hST : S ⊆ T
  · have hTS : ¬T ⊆ S := fun h => hne (Subset.antisymm hST h)
    obtain ⟨i, hiT, hiS⟩ := not_subset.mp hTS
    obtain ⟨j, hjS⟩ := hS
    have h := starProduct_sq_of_mem hp T S hiT hiS hjS (fun u v => F v u)
    simp_rw [← starProduct_swap S T F] at h
    rwa [Cuts.expect_comm] at h
  · obtain ⟨i, hiS, hiT⟩ := not_subset.mp hST
    obtain ⟨j, hjT⟩ := hT
    exact starProduct_sq_of_mem hp S T hiS hiT hjT F

/-- Equal supports cost `2q`, after deleting the two output-label coincidences. -/
theorem starProduct_equal_sq (hDLK : Target.FourCycle) (hp : p ≠ 2)
    (S : Finset ι) {i j : ι} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j)
    (F : ZMod p → ZMod p → ℝ) (hF : ∀ u, F u u = 0) :
    (cube p ι).expect (fun x => (if x i = x j then 0 else starProduct S S F x) ^ 2) ≤
      4 * (p : ℝ)⁻¹ ^ 2 *
        (fieldLaw p).expect (fun u => (fieldLaw p).expect (fun v => F u v ^ 2)) := by
  apply JointRows.Star.expect_two_coordinate_bound (fun _ : ι => fieldLaw p) i j
  intro x
  simp only [Function.update_self, Function.update_of_ne hij]
  simp_rw [starProduct_equal_coordinates S hi hj hij]
  have hd (u : ZMod p) : productRest S S i j x u u * F u u = 0 := by rw [hF, mul_zero]
  exact (equalMap_sq hDLK hp (fun u v => productRest S S i j x u v * F u v) hd).trans
    (mul_le_mul_of_nonneg_left (productRest_energy S S i j x F) (by positivity))

end Sarkozy.SpectralC.TwoLabel
