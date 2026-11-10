module

public import Sarkozy.Moments.Normalization
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Centered expansions and unit moment bounds

A product term with at least two centered inputs is controlled by the deficit
of the product of the means. Thus sufficiently small centered coefficients
give a unit bound for the full positive multilinear form.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

theorem product_deficit_bound {V : Type*} [Fintype V] [DecidableEq V]
    (m v : V → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (hsq : ∀ i, m i ^ 2 + v i ^ 2 ≤ 1)
    (S : Finset V) (hS : 2 ≤ S.card) :
    (∏ i ∈ S, v i) * (∏ i ∈ Sᶜ, m i) ≤ 1 - ∏ i, m i := by
  have hm1 (i : V) : m i ≤ 1 := by nlinarith [hsq i, sq_nonneg (v i)]
  have hv1 (i : V) : v i ≤ 1 := by nlinarith [hsq i, sq_nonneg (m i)]
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hpair : v i * v j ≤ 1 - m i * m j := by
    nlinarith [hsq i, hsq j, sq_nonneg (v i - v j), sq_nonneg (m i - m j)]
  have hsubset : ({i, j} : Finset V) ⊆ S :=
    Finset.insert_subset_iff.mpr ⟨hi, Finset.singleton_subset_iff.mpr hj⟩
  have hnot : i ∉ ({j} : Finset V) := by simpa only [Finset.mem_singleton] using hij
  have hpv : ∏ k ∈ S, v k ≤ v i * v j := by
    have h := Finset.prod_le_prod_of_subset_of_le_one₀ hsubset
      (fun k _ => hv k) (fun k _ _ => hv1 k)
    simpa only [Finset.prod_insert hnot, Finset.prod_singleton] using h
  have hpm : (∏ k, m k) ≤ m i * m j := by
    have h := Finset.prod_le_prod_of_subset_of_le_one₀
      (Finset.subset_univ ({i, j} : Finset V))
      (fun k _ => hm k) (fun k _ _ => hm1 k)
    simpa only [Finset.prod_insert hnot, Finset.prod_singleton] using h
  have hrest : ∏ k ∈ Sᶜ, m k ≤ 1 := Finset.prod_le_one₀ (fun k _ => hm k) (fun k _ => hm1 k)
  calc
    (∏ k ∈ S, v k) * (∏ k ∈ Sᶜ, m k) ≤ (∏ k ∈ S, v k) * 1 :=
      mul_le_mul_of_nonneg_left hrest (Finset.prod_nonneg (fun k _ => hv k))
    _ ≤ 1 - ∏ k, m k := by rw [mul_one]; linarith

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Nonempty X]

noncomputable def centeredInput (f : X → ℝ) (x : X) : ℝ :=
  f x - (FiniteLaw.uniform X).expect f

noncomputable def centeredForm (μ : FiniteLaw (V → X)) (f : V → X → ℝ) (S : Finset V) : ℝ :=
  μ.expect (fun z => ∏ v ∈ S, centeredInput (f v) (z v))

@[simp] theorem centeredForm_empty (μ : FiniteLaw (V → X)) (f : V → X → ℝ) :
    centeredForm μ f ∅ = 1 := by simp only [centeredForm, Finset.prod_empty, FiniteLaw.expect_const]

theorem centeredForm_singleton {μ : FiniteLaw (V → X)} (hm : HasUniformMarginals μ)
    (f : V → X → ℝ) (v : V) : centeredForm μ f {v} = 0 := by
  simp only [centeredForm, Finset.prod_singleton, centeredInput]
  rw [FiniteLaw.expect_sub, hm v (f v), FiniteLaw.expect_const, sub_self]

theorem centered_product_expansion (μ : FiniteLaw (V → X)) (f : V → X → ℝ) :
    μ.expect (fun z => ∏ v, f v (z v)) =
      ∑ S : Finset V, centeredForm μ f S * ∏ v ∈ Sᶜ, (FiniteLaw.uniform X).expect (f v) := by
  have he (z : V → X) : (∏ v, f v (z v)) =
      ∑ S : Finset V, (∏ v ∈ S, centeredInput (f v) (z v)) *
        ∏ v ∈ Sᶜ, (FiniteLaw.uniform X).expect (f v) := by
    rw [← Fintype.prod_add]
    simp only [centeredInput, sub_add_cancel]
  simp only [he]
  rw [FiniteLaw.expect_sum]
  simp only [FiniteLaw.expect_mul_const, centeredForm]

def centeredSets (V : Type*) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.filter (fun S => 2 ≤ S.card)

theorem centered_product_expansion_high {μ : FiniteLaw (V → X)} (hm : HasUniformMarginals μ)
    (f : V → X → ℝ) :
    μ.expect (fun z => ∏ v, f v (z v)) = (∏ v, (FiniteLaw.uniform X).expect (f v)) +
      ∑ S ∈ centeredSets V, centeredForm μ f S * ∏ v ∈ Sᶜ, (FiniteLaw.uniform X).expect (f v) := by
  rw [centered_product_expansion]
  let T : Finset V → ℝ := fun S => centeredForm μ f S * ∏ v ∈ Sᶜ, (FiniteLaw.uniform X).expect (f v)
  change (∑ S, T S) = _
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun S : Finset V => 2 ≤ S.card) T]
  have hlow : ∑ S ∈ Finset.univ.filter (fun S : Finset V => ¬2 ≤ S.card), T S =
      ∏ v, (FiniteLaw.uniform X).expect (f v) := by
    rw [Finset.sum_eq_single ∅]
    · simp only [T, centeredForm_empty, Finset.compl_empty, one_mul]
    · intro S hS hne
      have hc : S.card = 1 := by
        have hsmall := (Finset.mem_filter.mp hS).2
        have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
        omega
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
      simp only [T, centeredForm_singleton hm, zero_mul]
    · simp
  rw [hlow, add_comm]
  rfl

/-- A normalized centered-radius inequality and a small sum of centered
coefficients imply a unit mixed norm. The centered radii need not arise from
independent random variables. -/
theorem mixedLpBound_of_centered_small (μ : FiniteLaw (V → X)) (hm : HasUniformMarginals μ)
    {p : ℝ} (hp : 0 < p) (B : (X → ℝ) → ℝ) (hB : ∀ f, 0 ≤ B f)
    (hvariance : ∀ f : X → ℝ, (∀ x, 0 ≤ f x) → (FiniteLaw.uniform X).lpNorm p f = 1 →
      ((FiniteLaw.uniform X).expect f) ^ 2 + B f ^ 2 ≤ 1)
    (c : Finset V → ℝ) (hc : ∀ S ∈ centeredSets V, 0 ≤ c S)
    (hsum : ∑ S ∈ centeredSets V, c S ≤ 1)
    (hcenter : ∀ f : V → X → ℝ, ∀ S ∈ centeredSets V,
      |centeredForm μ f S| ≤ c S * ∏ v ∈ S, B (f v)) : MixedLpBound μ p 1 := by
  apply mixedLpBound_of_normalized μ hp
  intro f hf hn
  let m : V → ℝ := fun v => (FiniteLaw.uniform X).expect (f v)
  let b : V → ℝ := fun v => B (f v)
  have hm0 (v : V) : 0 ≤ m v := (FiniteLaw.uniform X).expect_nonneg (hf v)
  have hb0 (v : V) : 0 ≤ b v := hB (f v)
  have hsq (v : V) : m v ^ 2 + b v ^ 2 ≤ 1 := hvariance (f v) (hf v) (hn v)
  have hm1 (v : V) : m v ≤ 1 := by nlinarith [hsq v, sq_nonneg (b v)]
  have hprod : ∏ v, m v ≤ 1 := Finset.prod_le_one₀ (fun v _ => hm0 v) (fun v _ => hm1 v)
  have hterm (S : Finset V) (hS : S ∈ centeredSets V) :
      centeredForm μ f S * (∏ v ∈ Sᶜ, m v) ≤ c S * (1 - ∏ v, m v) := by
    have hcard := (Finset.mem_filter.mp hS).2
    calc
      centeredForm μ f S * (∏ v ∈ Sᶜ, m v) ≤
          (c S * ∏ v ∈ S, b v) * (∏ v ∈ Sᶜ, m v) :=
        mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hcenter f S hS))
          (Finset.prod_nonneg (fun v _ => hm0 v))
      _ = c S * ((∏ v ∈ S, b v) * ∏ v ∈ Sᶜ, m v) := mul_assoc _ _ _
      _ ≤ c S * (1 - ∏ v, m v) := mul_le_mul_of_nonneg_left
        (product_deficit_bound m b hm0 hb0 hsq S hcard) (hc S hS)
  rw [centered_product_expansion_high hm]
  change (∏ v, m v) + ∑ S ∈ centeredSets V, centeredForm μ f S * (∏ v ∈ Sᶜ, m v) ≤ 1
  calc
    _ ≤ (∏ v, m v) + ∑ S ∈ centeredSets V, c S * (1 - ∏ v, m v) := by
      exact add_le_add le_rfl (Finset.sum_le_sum hterm)
    _ = (∏ v, m v) + (∑ S ∈ centeredSets V, c S) * (1 - ∏ v, m v) := by
      rw [Finset.sum_mul]
    _ ≤ (∏ v, m v) + 1 * (1 - ∏ v, m v) := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hprod))
    _ = 1 := by ring

end Sarkozy
