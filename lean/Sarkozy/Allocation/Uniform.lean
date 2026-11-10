module

public import Sarkozy.Allocation.Multiaffine
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic.IntervalCases

/-!
# Universal joint-allocation constants

For coordinates in [0, 1/2], the product of (1 + zᵢ) controls the first
elementary symmetric sum with coefficient 9/4, and its excess over one
controls the second with coefficient 211/80. The proof checks the vertices
and establishes the resulting inequalities for every natural degree.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Allocation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def firstSum (z : ι → ℝ) : ℝ := ∑ i, z i
noncomputable def secondSum (z : ι → ℝ) : ℝ := ((firstSum z) ^ 2 - ∑ i, z i ^ 2) / 2
noncomputable def onePlusProduct (z : ι → ℝ) : ℝ := ∏ i, (1 + z i)

/-- The quadratic formula is exactly half the sum over distinct ordered pairs,
so each unordered pair contributes once. -/
theorem secondSum_eq_offDiag (z : ι → ℝ) :
    secondSum z = (∑ p ∈ (Finset.univ : Finset ι).offDiag, z p.1 * z p.2) / 2 := by
  have h := Finset.sum_union (f := fun p : ι × ι => z p.1 * z p.2)
    (Finset.disjoint_diag_offDiag (s := Finset.univ))
  rw [Finset.diag_union_offDiag, Finset.sum_diag, Finset.sum_product] at h
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ← pow_two] at h
  unfold secondSum firstSum
  linarith

theorem firstSum_multiaffine : MultiAffine (firstSum (ι := ι)) := by
  intro i z a b t
  unfold firstSum
  simp only [Finset.sum_update_of_mem (Finset.mem_univ i)]
  ring

theorem secondSum_multiaffine : MultiAffine (secondSum (ι := ι)) := by
  intro i z a b t
  have he (q : ℝ) : (fun j => Function.update z i q j ^ 2) =
      Function.update (fun j => z j ^ 2) i (q ^ 2) := Function.comp_update (fun x : ℝ => x ^ 2) z i q
  unfold secondSum firstSum
  simp only [he, Finset.sum_update_of_mem (Finset.mem_univ i)]
  ring

theorem onePlusProduct_multiaffine : MultiAffine (onePlusProduct (ι := ι)) := by
  have he : onePlusProduct (ι := ι) = (fun z => ∏ i, (z i + 1)) := by
    funext z
    simp only [onePlusProduct, add_comm]
  rw [he]
  exact (MultiAffine.monomial (Finset.univ : Finset ι)).translate (fun _ => 1)

def zeroVertex (s : Finset ι) (u : ℝ) : ι → ℝ := fun i => if i ∈ s then u else 0

theorem exists_zeroVertex {z : ι → ℝ} {u : ℝ} (hz : ∀ i, z i = 0 ∨ z i = u) :
    ∃ s : Finset ι, z = zeroVertex s u := by
  classical
  refine ⟨Finset.univ.filter (fun i => z i ≠ 0), ?_⟩
  funext i
  by_cases hi : z i = 0
  · simp [zeroVertex, hi]
  · simp only [zeroVertex, Finset.mem_filter, Finset.mem_univ, true_and,
      ite_eq_left hi]
    exact (hz i).resolve_left hi

theorem firstSum_zeroVertex (s : Finset ι) (u : ℝ) :
    firstSum (zeroVertex s u) = (s.card : ℝ) * u := by
  simp [firstSum, zeroVertex]

theorem onePlusProduct_zeroVertex (s : Finset ι) (u : ℝ) :
    onePlusProduct (zeroVertex s u) = (1 + u) ^ s.card := by
  simp only [onePlusProduct, zeroVertex, add_ite, add_zero]
  rw [Fintype.prod_ite_mem]
  simp only [Finset.prod_const]

theorem secondSum_zeroVertex (s : Finset ι) (u : ℝ) :
    secondSum (zeroVertex s u) = (s.card : ℝ) * (s.card - 1) * u ^ 2 / 2 := by
  unfold secondSum
  rw [firstSum_zeroVertex]
  have he : (fun i => zeroVertex s u i ^ 2) = zeroVertex s (u ^ 2) := by
    funext i
    simp [zeroVertex, ite_pow]
  rw [he]
  change (((s.card : ℝ) * u) ^ 2 - firstSum (zeroVertex s (u ^ 2))) / 2 = _
  rw [firstSum_zeroVertex]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem zeta_vertex_bound (k : ℕ) : (9 / 8 : ℝ) * k ≤ (3 / 2 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    by_cases hk : k < 2
    · interval_cases k <;> norm_num
    · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      rw [pow_succ, Nat.cast_add_one]
      have h := mul_le_mul_of_nonneg_right ih (by norm_num : (0 : ℝ) ≤ 3 / 2)
      nlinarith

omit [Fintype ι] [DecidableEq ι] in
theorem eta_vertex_bound (k : ℕ) :
    1 + (211 / 640 : ℝ) * (k : ℝ) * (k - 1) ≤ (3 / 2 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    by_cases hk : k < 5
    · interval_cases k <;> norm_num
    · have hk5 : (5 : ℝ) ≤ k := by exact_mod_cast (show 5 ≤ k by omega)
      rw [pow_succ, Nat.cast_add_one]
      have h := mul_le_mul_of_nonneg_right ih (by norm_num : (0 : ℝ) ≤ 3 / 2)
      have hh : 0 ≤ (k : ℝ) * ((k : ℝ) - 5) :=
        mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hk5)
      nlinarith

/-- The paper's universal first-degree allocation constant, in every dimension. -/
theorem zeta_uniform {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 / 2) :
    (9 / 4 : ℝ) * firstSum z ≤ onePlusProduct z := by
  have hf := (onePlusProduct_multiaffine (ι := ι)).sub
    (firstSum_multiaffine.const_mul (9 / 4))
  apply sub_nonneg.mp (hf.nonneg_of_vertices (by norm_num : (0 : ℝ) ≤ 1 / 2) ?_ hz)
  intro v hv
  obtain ⟨s, rfl⟩ := exists_zeroVertex hv
  rw [onePlusProduct_zeroVertex, firstSum_zeroVertex]
  have h := zeta_vertex_bound s.card
  norm_num only [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num]
  linarith

/-- The paper's universal second-degree allocation constant, in every dimension. -/
theorem eta_uniform {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 / 2) :
    (211 / 80 : ℝ) * secondSum z ≤ onePlusProduct z - 1 := by
  have hf := ((onePlusProduct_multiaffine (ι := ι)).sub (MultiAffine.const 1)).sub
    (secondSum_multiaffine.const_mul (211 / 80))
  apply sub_nonneg.mp (hf.nonneg_of_vertices (by norm_num : (0 : ℝ) ≤ 1 / 2) ?_ hz)
  intro v hv
  obtain ⟨s, rfl⟩ := exists_zeroVertex hv
  rw [onePlusProduct_zeroVertex, secondSum_zeroVertex]
  have h := eta_vertex_bound s.card
  norm_num only [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num]
  nlinarith

end Sarkozy.Allocation
