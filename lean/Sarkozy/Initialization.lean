module

public import Sarkozy.Induction
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Finite initialization without an assumed base-case estimate

At any fixed finite collection of scales there are finitely many subsets of
the relevant integer intervals. A single positive constant therefore bounds
all nonempty-set energy ratios. The empty set is treated separately.
-/

@[expose] public section

namespace Sarkozy

theorem density_pos_of_nonempty {N : ℕ} {A : Finset ℤ}
    (hN : 0 < N) (hA : A.Nonempty) : 0 < density N A := by
  exact div_pos (by exact_mod_cast Finset.card_pos.mpr hA) (by exact_mod_cast hN)

@[simp] theorem density_empty (N : ℕ) : density N ∅ = 0 := by
  simp [density]

/-- Every finite initial segment has a uniform constant; no estimates on
nonempty sets need to be supplied by the caller. -/
theorem exists_initialization_constant (Y : ℕ → Finset ℤ → ℝ)
    (hzero : ∀ L : ℕ, 1 ≤ L → Y L ∅ ≤ 0) (L₀ : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ L : ℕ, 1 ≤ L → L < L₀ → EnergyUpperBoundAt Y C L := by
  classical
  let S := (Finset.range L₀).product (Finset.Icc 1 ((blockScale * L₀ : ℕ) : ℤ)).powerset
  let ratio : ℕ × Finset ℤ → ℝ := fun p =>
    Y p.1 p.2 / ((p.1 : ℝ) ^ (-decay) * density (blockScale * p.1) p.2 ^ densityExponent)
  obtain ⟨B, hB⟩ := (S.finite_toSet.image ratio).bddAbove
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro L hL hsmall A hA
  by_cases hempty : A = ∅
  · subst A
    have he : (0 : ℝ) ^ densityExponent = 0 :=
      Real.zero_rpow (by norm_num [densityExponent])
    simpa only [density_empty, he, mul_zero] using hzero L hL
  have hApos : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hKN : 0 < blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hweight : 0 < (L : ℝ) ^ (-decay) *
      density (blockScale * L) A ^ densityExponent :=
    mul_pos (Real.rpow_pos_of_pos hLpos _)
      (Real.rpow_pos_of_pos (density_pos_of_nonempty hKN hApos) _)
  have hsub : A ⊆ Finset.Icc 1 ((blockScale * L₀ : ℕ) : ℤ) := by
    intro z hz
    obtain ⟨hz₁, hzL⟩ := Finset.mem_Icc.mp (hA.1 hz)
    refine Finset.mem_Icc.mpr ⟨hz₁, hzL.trans ?_⟩
    exact_mod_cast Nat.mul_le_mul_left blockScale hsmall.le
  have hmem : (L, A) ∈ S :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr hsmall, Finset.mem_powerset.mpr hsub⟩
  have hratio : ratio (L, A) ≤ max 1 B :=
    (hB (Set.mem_image_of_mem ratio hmem)).trans (le_max_right _ _)
  have hb := (div_le_iff₀ hweight).mp hratio
  simpa only [mul_assoc] using hb

/-- The recurrence needs to be uniform in the induction constant, as it is
in the paper. Then finite initialization is a theorem rather than an input. -/
theorem scaledEnergyEstimate_of_uniform_contraction
    {Y : ℕ → Finset ℤ → ℝ} {q : ℝ} {L₀ : ℕ}
    {error : ℕ → Finset ℤ → ℝ}
    (hzero : ∀ L : ℕ, 1 ≤ L → Y L ∅ ≤ 0)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hrec : ∀ C : ℝ, 1 ≤ C → ∀ L : ℕ, 1 ≤ L → L₀ ≤ L →
      (∀ k : ℕ, 1 ≤ k → k < L → EnergyUpperBoundAt Y C k) →
      ∀ A : Finset ℤ, Admissible (blockScale * L) A →
        C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent < Y L A →
        Y L A ≤ (q + error L A) * Y L A)
    (hmargin : ∀ L : ℕ, 1 ≤ L → L₀ ≤ L →
      ∀ A : Finset ℤ, Admissible (blockScale * L) A → q + error L A < 1) :
    ScaledEnergyEstimate Y := by
  obtain ⟨C, hC, hinit⟩ := exists_initialization_constant Y hzero L₀
  exact scaledEnergyEstimate_of_contraction (lt_of_lt_of_le zero_lt_one hC)
    hreflection hinit (hrec C hC) hmargin

end Sarkozy
