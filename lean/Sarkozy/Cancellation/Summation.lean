module

public import Mathlib

@[expose] public section

/-!
# Step 4 of `lem:record:density-can`: summation over the pair supports

`paper/sections/08_scale_comparison.tex`, proof of `lem:record:density-can`, Step 4:
distinct sets `U` of tail primes have distinct products `q_U = ∏_{p∈U} p`, and for
`0 < γ < 1/2`,
`∑_{q_U ≤ T₀} q_U^{-2γ} ≤ 1 + T₀^{1-2γ}/(1-2γ)`.

The sets `U` are encoded as in `Sarkozy.Mixing` (`lem:tr:pairsupport`): `l : K → Bool` over a
finite family of coordinates `K`, with the product `∏_j (if l j then q_j else 1)`; this is the
body of `Sarkozy.Mixing.supportConductor q l`, so the lemma applies verbatim to the sum in
`Sarkozy.Mixing.pair_support`.

New material for this paper.
-/

namespace Sarkozy.Cancellation

open Finset

/-- The natural-number product `q_U = ∏_{j ∈ U} q_j`. -/
def natConductor {K : Type*} [Fintype K] (q : K → ℕ) (l : K → Bool) : ℕ :=
  ∏ j, if l j then q j else 1

lemma natConductor_cast {K : Type*} [Fintype K] (q : K → ℕ) (l : K → Bool) :
    ((natConductor q l : ℕ) : ℝ) = ∏ j, (if l j then (q j : ℝ) else 1) := by
  unfold natConductor
  push_cast
  apply prod_congr rfl
  intro j _
  split_ifs <;> simp

lemma natConductor_pos {K : Type*} [Fintype K] (q : K → ℕ) (hq : ∀ j, 0 < q j) (l : K → Bool) :
    0 < natConductor q l := by
  unfold natConductor
  apply prod_pos
  intro j _
  split_ifs
  · exact hq j
  · exact one_pos

/-- Distinct sets of distinct primes have distinct products. -/
lemma natConductor_injective {K : Type*} [Fintype K] [DecidableEq K] (q : K → ℕ)
    (hq : ∀ j, (q j).Prime) (hinj : Function.Injective q) :
    Function.Injective (natConductor q) := by
  intro l l' h
  funext j
  have key : ∀ l : K → Bool, (q j ∣ natConductor q l ↔ l j = true) := by
    intro l
    constructor
    · intro hdvd
      unfold natConductor at hdvd
      obtain ⟨i, _, hi⟩ := (Prime.dvd_finsetProd_iff (hq j).prime _).mp hdvd
      by_cases hli : l i = true
      · rw [ite_eq_left hli] at hi
        have : q j = q i := (Nat.prime_dvd_prime_iff_eq (hq j) (hq i)).mp hi
        rw [← hinj this] at hli
        exact hli
      · rw [ite_eq_right hli] at hi
        exact absurd (Nat.eq_one_of_dvd_one hi) (hq j).one_lt.ne'
    · intro hlj
      unfold natConductor
      exact (dvd_of_eq (ite_eq_left hlj).symm).trans (dvd_prod_of_mem _ (mem_univ j))
  have h1 := key l
  have h2 := key l'
  rw [h] at h1
  cases hl : l j <;> cases hl' : l' j
  · rfl
  · exact absurd (h1.mp (h2.mpr hl')) (by simp [hl])
  · exact absurd (h2.mp (h1.mpr hl)) (by simp [hl'])
  · rfl

/-- `∑_{n=1}^{M} n^{-s} ≤ 1 + M^{1-s}/(1-s)` for `0 ≤ s < 1`. -/
lemma sum_rpow_neg_le (M : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∑ n ∈ Icc 1 M, ((n : ℕ) : ℝ) ^ (-s) ≤ 1 + (M : ℝ) ^ (1 - s) / (1 - s) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp only [Icc_eq_empty_of_lt zero_lt_one, sum_empty, Nat.cast_zero]
    have : (0 : ℝ) ≤ (0 : ℝ) ^ (1 - s) / (1 - s) :=
      div_nonneg (Real.rpow_nonneg le_rfl _) (by linarith)
    linarith
  have hsplit : ∑ n ∈ Icc 1 M, ((n : ℕ) : ℝ) ^ (-s) =
      1 + ∑ i ∈ Ico 1 M, (((i + 1 : ℕ) : ℝ)) ^ (-s) := by
    have hI : Icc 1 M = insert 1 ((Ico 1 M).image (· + 1)) := by
      ext n
      simp only [mem_Icc, mem_insert, mem_image, mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge 1 n with h | h
        · right; exact ⟨n - 1, ⟨by omega, by omega⟩, by omega⟩
        · left; omega
      · rintro (h | ⟨i, ⟨h1, h2⟩, rfl⟩)
        · omega
        · omega
    rw [hI, sum_insert, sum_image]
    · simp
    · intro a _ b _ h; simpa using h
    · simp
  rw [hsplit]
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc ((1 : ℕ) : ℝ) ((M : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := by
      have := hx.1; push_cast at this; linarith
    exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have hint := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x ^ (-s)) hM hanti
  push_cast at hint
  have hval : ∫ x in (1 : ℝ)..(M : ℝ), x ^ (-s) = ((M : ℝ) ^ (1 - s) - 1) / (1 - s) := by
    rw [integral_rpow (Or.inl (by linarith))]
    rw [show -s + 1 = 1 - s by ring, Real.one_rpow]
  rw [hval] at hint
  have hfin : ((M : ℝ) ^ (1 - s) - 1) / (1 - s) ≤ (M : ℝ) ^ (1 - s) / (1 - s) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    linarith
  have hsum : ∑ i ∈ Ico 1 M, (((i + 1 : ℕ) : ℝ)) ^ (-s) =
      ∑ i ∈ Ico 1 M, ((i : ℝ) + 1) ^ (-s) := by
    apply sum_congr rfl
    intro i _
    push_cast
    rfl
  rw [hsum]
  linarith

/-- **Step 4 of `lem:record:density-can`.** For distinct primes `q_j` and `0 < γ < 1/2`,
`T₀ ≥ 1`: `∑_{U : q_U ≤ T₀} q_U^{-2γ} ≤ 1 + T₀^{1-2γ}/(1-2γ)`, with `q_U = ∏_{j ∈ U} q_j`. -/
theorem sum_supportConductor_rpow_le {K : Type*} [Fintype K] [DecidableEq K] (q : K → ℕ)
    (hq : ∀ j, (q j).Prime) (hinj : Function.Injective q) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1 / 2) {T₀ : ℝ} (hT₀ : 1 ≤ T₀) :
    ∑ l ∈ univ.filter (fun l : K → Bool => (∏ j, (if l j then (q j : ℝ) else 1)) ≤ T₀),
        (∏ j, (if l j then (q j : ℝ) else 1)) ^ (-2 * γ) ≤
      1 + T₀ ^ (1 - 2 * γ) / (1 - 2 * γ) := by
  classical
  set M := ⌊T₀⌋₊ with hM
  have hcast : ∀ l : K → Bool, (∏ j, (if l j then (q j : ℝ) else 1)) = (natConductor q l : ℝ) :=
    fun l => (natConductor_cast q l).symm
  simp_rw [hcast]
  -- reindex by the products, which are distinct
  have hmaps : ∀ l ∈ univ.filter (fun l : K → Bool => ((natConductor q l : ℕ) : ℝ) ≤ T₀),
      natConductor q l ∈ Icc 1 M := by
    intro l hl
    rw [mem_filter] at hl
    rw [mem_Icc]
    exact ⟨natConductor_pos q (fun j => (hq j).pos) l, Nat.le_floor hl.2⟩
  have hinj' := natConductor_injective q hq hinj
  calc ∑ l ∈ univ.filter (fun l : K → Bool => ((natConductor q l : ℕ) : ℝ) ≤ T₀),
        ((natConductor q l : ℕ) : ℝ) ^ (-2 * γ)
      = ∑ n ∈ (univ.filter (fun l : K → Bool => ((natConductor q l : ℕ) : ℝ) ≤ T₀)).image
          (natConductor q), ((n : ℕ) : ℝ) ^ (-2 * γ) := by
        rw [sum_image (fun a _ b _ h => hinj' h)]
    _ ≤ ∑ n ∈ Icc 1 M, ((n : ℕ) : ℝ) ^ (-2 * γ) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨l, hl, rfl⟩ := mem_image.mp hn
          exact hmaps l hl
        · intro n _ _
          exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    _ ≤ 1 + (M : ℝ) ^ (1 - 2 * γ) / (1 - 2 * γ) := by
        have := sum_rpow_neg_le M (2 * γ) (by linarith) (by linarith)
        simpa [neg_mul] using this
    _ ≤ 1 + T₀ ^ (1 - 2 * γ) / (1 - 2 * γ) := by
        have hMT : (M : ℝ) ≤ T₀ := Nat.floor_le (by linarith)
        have h1 : (M : ℝ) ^ (1 - 2 * γ) ≤ T₀ ^ (1 - 2 * γ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hMT (by linarith)
        have h2 : 0 < 1 - 2 * γ := by linarith
        have := div_le_div_of_nonneg_right h1 h2.le
        linarith

end Sarkozy.Cancellation
