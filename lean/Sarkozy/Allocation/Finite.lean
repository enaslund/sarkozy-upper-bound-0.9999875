module

public import Sarkozy.Allocation.Uniform

/-!
# Finite vertex tests for sharper allocation constants

Vertices are grouped by the number of lower coordinates. Their first and
second elementary symmetric sums are calculated exactly. Thus only n + 1
rational tests are needed in degree n, rather than a test for every vertex.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Allocation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def twoVertex (s : Finset ι) (l u : ℝ) : ι → ℝ := fun i => if i ∈ s then l else u

theorem exists_twoVertex {z : ι → ℝ} {l u : ℝ} (hz : ∀ i, z i = l ∨ z i = u) :
    ∃ s : Finset ι, z = twoVertex s l u := by
  classical
  refine ⟨Finset.univ.filter (fun i => z i = l), ?_⟩
  funext i
  by_cases hi : z i = l
  · simp [twoVertex, hi]
  · simp only [twoVertex, Finset.mem_filter, Finset.mem_univ, true_and,
      ite_eq_right hi]
    exact (hz i).resolve_left hi

noncomputable def vertexProduct (n k : ℕ) (l u : ℝ) : ℝ :=
  (1 + l) ^ k * (1 + u) ^ (n - k)

noncomputable def vertexFirst (n k : ℕ) (l u : ℝ) : ℝ :=
  (k : ℝ) * l + ((n : ℝ) - k) * u

noncomputable def vertexSecond (n k : ℕ) (l u : ℝ) : ℝ :=
  ((vertexFirst n k l u) ^ 2 - ((k : ℝ) * l ^ 2 + ((n : ℝ) - k) * u ^ 2)) / 2

theorem firstSum_twoVertex (s : Finset ι) (l u : ℝ) :
    firstSum (twoVertex s l u) = vertexFirst (Fintype.card ι) s.card l u := by
  have hleft : Finset.univ.filter (fun i : ι => i ∈ s) = s := by ext i; simp
  have hright : Finset.univ.filter (fun i : ι => i ∉ s) = Finset.univ \ s := by ext i; simp
  simp only [firstSum, twoVertex, Finset.sum_ite, hleft, hright, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ,
    Nat.cast_sub (Finset.card_le_univ s)]
  rfl

theorem onePlusProduct_twoVertex (s : Finset ι) (l u : ℝ) :
    onePlusProduct (twoVertex s l u) = vertexProduct (Fintype.card ι) s.card l u := by
  have hleft : Finset.univ.filter (fun i : ι => i ∈ s) = s := by ext i; simp
  have hright : Finset.univ.filter (fun i : ι => i ∉ s) = Finset.univ \ s := by ext i; simp
  simp only [onePlusProduct, twoVertex, add_ite, Finset.prod_ite, hleft, hright,
    Finset.prod_const]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ]
  rfl

theorem secondSum_twoVertex (s : Finset ι) (l u : ℝ) :
    secondSum (twoVertex s l u) = vertexSecond (Fintype.card ι) s.card l u := by
  unfold secondSum
  rw [firstSum_twoVertex]
  have he : (fun i => twoVertex s l u i ^ 2) = twoVertex s (l ^ 2) (u ^ 2) := by
    funext i
    simp only [twoVertex, ite_pow]
  rw [he]
  change ((vertexFirst (Fintype.card ι) s.card l u) ^ 2 -
    firstSum (twoVertex s (l ^ 2) (u ^ 2))) / 2 = _
  rw [firstSum_twoVertex]
  rfl

/-- First-degree allocation follows from the n + 1 grouped vertex tests. -/
theorem first_allocation_of_vertices {l u C : ℝ} (hlu : l ≤ u)
    (hv : ∀ k : ℕ, k ≤ Fintype.card ι →
      C * vertexFirst (Fintype.card ι) k l u ≤ vertexProduct (Fintype.card ι) k l u)
    {z : ι → ℝ} (hz : ∀ i, l ≤ z i ∧ z i ≤ u) : C * firstSum z ≤ onePlusProduct z := by
  have hf := (onePlusProduct_multiaffine (ι := ι)).sub (firstSum_multiaffine.const_mul C)
  apply sub_nonneg.mp (hf.nonneg_of_vertices hlu ?_ hz)
  intro v hv'
  obtain ⟨s, rfl⟩ := exists_twoVertex hv'
  rw [onePlusProduct_twoVertex, firstSum_twoVertex]
  exact sub_nonneg.mpr (hv s.card (Finset.card_le_univ s))

/-- Second-degree allocation follows from the n + 1 grouped vertex tests. -/
theorem second_allocation_of_vertices {l u C : ℝ} (hlu : l ≤ u)
    (hv : ∀ k : ℕ, k ≤ Fintype.card ι →
      C * vertexSecond (Fintype.card ι) k l u ≤ vertexProduct (Fintype.card ι) k l u - 1)
    {z : ι → ℝ} (hz : ∀ i, l ≤ z i ∧ z i ≤ u) :
    C * secondSum z ≤ onePlusProduct z - 1 := by
  have hf := ((onePlusProduct_multiaffine (ι := ι)).sub (MultiAffine.const 1)).sub
    (secondSum_multiaffine.const_mul C)
  apply sub_nonneg.mp (hf.nonneg_of_vertices hlu ?_ hz)
  intro v hv'
  obtain ⟨s, rfl⟩ := exists_twoVertex hv'
  rw [onePlusProduct_twoVertex, secondSum_twoVertex]
  exact sub_nonneg.mpr (hv s.card (Finset.card_le_univ s))

end Sarkozy.Allocation
