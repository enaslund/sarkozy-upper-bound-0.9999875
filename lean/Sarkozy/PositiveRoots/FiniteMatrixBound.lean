module

public import Sarkozy.PositiveRoots.CoherentMatrixAlgebra

/-! Transfer exact matrix certificates through positive scaling and inactive coordinates. -/

@[expose] public section

namespace Sarkozy.PositiveRoots

open Finset Sarkozy.SpectralD Sarkozy.SpectralC
open scoped ComplexConjugate

variable {U K : Type*} [Fintype U] [DecidableEq U] [Fintype K]

theorem lower_bound_of_scaled_nonneg (A : U → U → ℂ) (R I : U → U → ℤ)
    {s g : ℝ} (hs : 0 < s)
    (hmodel : ∀ i j, gaussian (R i j) (I i j) =
      (s : ℂ) * ((if i = j then (g : ℂ) else 0) + A i j))
    (hpos : ∀ x, 0 ≤ (qform (fun i j => gaussian (R i j) (I i j)) x).re)
    (x : U → ℂ) : -g * ∑ i, ‖x i‖ ^ 2 ≤ (qform A x).re := by
  have h := hpos x
  simp_rw [hmodel] at h
  rw [CoherentMatrix.qform_scalar, Complex.re_ofReal_mul] at h
  have hb := (mul_nonneg_iff_of_pos_left hs).mp h
  have he := qform_shift (fun i j => -A i j) g x
  simp only [sub_neg_eq_add, CoherentMatrix.qform_neg, Complex.neg_re] at he
  rw [he] at hb
  linarith

omit [DecidableEq U] in
theorem qform_restrict (A : U → U → ℂ) (e : K ↪ U)
    (hzero : ∀ i j, (i ∉ univ.map e ∨ j ∉ univ.map e) → A i j = 0)
    (x : U → ℂ) :
    qform A x = qform (fun i j => A (e i) (e j)) (fun i => x (e i)) := by
  unfold qform
  calc
    _ = ∑ i ∈ univ.map e, ∑ j, conj (x i) * A i j * x j := by
      symm
      apply sum_subset (subset_univ _)
      intro i _ hi
      apply sum_eq_zero
      intro j _
      simp only [hzero i j (Or.inl hi), mul_zero, zero_mul]
    _ = ∑ i ∈ univ.map e, ∑ j ∈ univ.map e, conj (x i) * A i j * x j := by
      apply sum_congr rfl
      intro i _
      symm
      apply sum_subset (subset_univ _)
      intro j _ hj
      simp only [hzero i j (Or.inr hj), mul_zero, zero_mul]
    _ = _ := by simp only [sum_map]

omit [DecidableEq U] in
theorem energy_restrict_le (e : K ↪ U) (x : U → ℂ) :
    (∑ i, ‖x (e i)‖ ^ 2) ≤ ∑ i, ‖x i‖ ^ 2 := by
  rw [← sum_map univ e (fun i => ‖x i‖ ^ 2)]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)

omit [DecidableEq U] in
theorem lower_bound_of_restriction (A : U → U → ℂ) (e : K ↪ U) {g : ℝ} (hg : 0 ≤ g)
    (hzero : ∀ i j, (i ∉ univ.map e ∨ j ∉ univ.map e) → A i j = 0)
    (hbound : ∀ x, -g * ∑ i, ‖x i‖ ^ 2 ≤ (qform (fun i j => A (e i) (e j)) x).re)
    (x : U → ℂ) : -g * ∑ i, ‖x i‖ ^ 2 ≤ (qform A x).re := by
  rw [qform_restrict A e hzero]
  exact (mul_le_mul_of_nonpos_left (energy_restrict_le e x) (neg_nonpos.mpr hg)).trans
    (hbound (fun i => x (e i)))

end Sarkozy.PositiveRoots
