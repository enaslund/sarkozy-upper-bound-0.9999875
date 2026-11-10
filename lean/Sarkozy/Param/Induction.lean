module

public import Sarkozy.Param.Params
public import Sarkozy.PowerBounds
public import Sarkozy.Initialization
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

@[expose] public section

/-!
# The scalar induction and the passage to cardinalities, for general exponents

Parametrized copies of `Sarkozy/Induction.lean`, `Sarkozy/PowerBounds.lean` and
`Sarkozy/Initialization.lean`: the scalar induction at the end of `thm:density:induction`
(`paper/sections/31_density_induction_upgrade.tex`), the finite initialization, and the
conversion `α^{72} ≤ Y ≤ C L^{-a} α^ϑ ⟹ s(N) ≤ C' N^{1 − a/(72 − ϑ)}`, for exponents
`P : Params` instead of the hard-coded `(decay, densityExponent, blockScale)`.

The proofs are those of the hard-coded files. The only side conditions used are fields of
`Params.Valid`: `ϑ ≠ 0` (initialization at the empty set), `72 − ϑ > 0` (the root) and `K ≥ 1`
(the interval embedding). The general real-root lemmas `Sarkozy.density_root_bound`,
`Sarkozy.density_bound_of_energy` and `Sarkozy.card_bound_of_density` are reused.
-/

namespace Sarkozy.Param

variable (P : Params)

/-- `Sarkozy.EnergyUpperBoundAt` at the exponents `P`: `Y(L, A) ≤ C L^{-a} α^ϑ` for every
square-difference-free `A ⊆ [1, K L]` (the bound proved by `thm:density:induction`). -/
def EnergyUpperBoundAt (Y : ℕ → Finset ℤ → ℝ) (C : ℝ) (L : ℕ) : Prop :=
  ∀ A : Finset ℤ, Admissible (P.blockScale * L) A →
    Y L A ≤ C * (L : ℝ) ^ (-P.decay) * density (P.blockScale * L) A ^ P.densityExponent

/-- `s(N) ≤ C N^{1 − a/(72 − ϑ)}`, the conclusion of `thm:density:induction` at the exponents
`P` (`Sarkozy.PowerSavingBound` at the record exponents). -/
def PowerSavingBound : Prop := CardinalityBound (1 - P.saving)

/-- The energy bounds of `thm:density:induction` at the exponents `P`: reflection
`α^{72} ≤ Y` and `Y ≤ C L^{-a} α^ϑ` (`Sarkozy.ScaledEnergyEstimate`). -/
def ScaledEnergyEstimate (Y : ℕ → Finset ℤ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
    Admissible (P.blockScale * L) A →
      density (P.blockScale * L) A ^ slots ≤ Y L A ∧
      Y L A ≤ C * (L : ℝ) ^ (-P.decay) * density (P.blockScale * L) A ^ P.densityExponent

/-- **The least-counterexample step** of `thm:density:induction` (scalar part), at the
exponents `P`; `Sarkozy.energyUpperBound_of_contraction` in general. -/
theorem energyUpperBound_of_contraction
    {Y : ℕ → Finset ℤ → ℝ} {C q : ℝ} {L₀ : ℕ}
    {error : ℕ → Finset ℤ → ℝ}
    (hC : 0 ≤ C)
    (hinit : ∀ L : ℕ, 1 ≤ L → L < L₀ → EnergyUpperBoundAt P Y C L)
    (hrec : ∀ L : ℕ, 1 ≤ L → L₀ ≤ L →
      (∀ l : ℕ, 1 ≤ l → l < L → EnergyUpperBoundAt P Y C l) →
      ∀ A : Finset ℤ, Admissible (P.blockScale * L) A →
        C * (L : ℝ) ^ (-P.decay) * density (P.blockScale * L) A ^ P.densityExponent < Y L A →
        Y L A ≤ (q + error L A) * Y L A)
    (hmargin : ∀ L : ℕ, 1 ≤ L → L₀ ≤ L →
      ∀ A : Finset ℤ, Admissible (P.blockScale * L) A → q + error L A < 1) :
    ∀ L : ℕ, 1 ≤ L → EnergyUpperBoundAt P Y C L := by
  intro L
  induction L using Nat.strong_induction_on with
  | h L ih =>
    intro hL A hA
    by_cases hsmall : L < L₀
    · exact hinit L hL hsmall A hA
    have hlarge : L₀ ≤ L := Nat.le_of_not_gt hsmall
    by_contra! hbad
    have hnonneg : 0 ≤ C * (L : ℝ) ^ (-P.decay) *
        density (P.blockScale * L) A ^ P.densityExponent :=
      mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg (density_nonneg _ _) _)
    have hy : 0 < Y L A := hnonneg.trans_lt hbad
    have hc := hrec L hL hlarge (fun l hl hlt => ih l hlt hl) A hA hbad
    have hm := hmargin L hL hlarge A hA
    have hstrict := mul_lt_mul_of_pos_right hm hy
    linarith

/-- Reflection and the scalar induction give the energy bounds at the exponents `P`
(`Sarkozy.scaledEnergyEstimate_of_contraction` in general). -/
theorem scaledEnergyEstimate_of_contraction
    {Y : ℕ → Finset ℤ → ℝ} {C q : ℝ} {L₀ : ℕ}
    {error : ℕ → Finset ℤ → ℝ}
    (hC : 0 < C)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (P.blockScale * L) A → density (P.blockScale * L) A ^ slots ≤ Y L A)
    (hinit : ∀ L : ℕ, 1 ≤ L → L < L₀ → EnergyUpperBoundAt P Y C L)
    (hrec : ∀ L : ℕ, 1 ≤ L → L₀ ≤ L →
      (∀ l : ℕ, 1 ≤ l → l < L → EnergyUpperBoundAt P Y C l) →
      ∀ A : Finset ℤ, Admissible (P.blockScale * L) A →
        C * (L : ℝ) ^ (-P.decay) * density (P.blockScale * L) A ^ P.densityExponent < Y L A →
        Y L A ≤ (q + error L A) * Y L A)
    (hmargin : ∀ L : ℕ, 1 ≤ L → L₀ ≤ L →
      ∀ A : Finset ℤ, Admissible (P.blockScale * L) A → q + error L A < 1) :
    ScaledEnergyEstimate P Y := by
  refine ⟨C, hC, ?_⟩
  intro L hL A hA
  exact ⟨hreflection L hL A hA,
    energyUpperBound_of_contraction P hC.le hinit hrec hmargin L hL A hA⟩

variable {P}

/-- `ScaledEnergyEstimate P` only sees the functional on admissible sets
(`Sarkozy.TheoremC.ScaledEnergyEstimate.transfer` in general). -/
theorem ScaledEnergyEstimate.transfer {Y Y' : ℕ → Finset ℤ → ℝ}
    (h : ∀ L A, Admissible (P.blockScale * L) A → Y L A = Y' L A)
    (hY : ScaledEnergyEstimate P Y) : ScaledEnergyEstimate P Y' := by
  obtain ⟨C, hC, hb⟩ := hY
  refine ⟨C, hC, fun L hL A hA => ?_⟩
  rw [← h L A hA]
  exact hb L hL A hA

/-- The energy bounds give the density saving `α ≤ D L^{-a/(72 − ϑ)}` at every physical scale
(`Sarkozy.scaled_density_bound` in general; needs `72 − ϑ > 0`). -/
theorem scaled_density_bound (hP : P.Valid) {Y : ℕ → Finset ℤ → ℝ}
    (hY : ScaledEnergyEstimate P Y) :
    ∃ D : ℝ, 0 < D ∧ ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (P.blockScale * L) A →
        density (P.blockScale * L) A ≤ D * (L : ℝ) ^ (-P.saving) := by
  obtain ⟨C, hC, hY⟩ := hY
  refine ⟨C ^ ((slots : ℝ) - P.densityExponent)⁻¹,
    Real.rpow_pos_of_pos hC _, ?_⟩
  intro L hL A hA
  obtain ⟨hl, hu⟩ := hY L hL A hA
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hh : density (P.blockScale * L) A ^ (slots : ℝ) ≤
      C * (L : ℝ) ^ (-P.decay) * density (P.blockScale * L) A ^ P.densityExponent := by
    simpa only [Real.rpow_natCast] using hl.trans hu
  exact density_bound_of_energy (density_nonneg _ _) hC.le hLpos hP.degree_gap_pos hh

/-- **The passage to cardinalities** (end of the proof of `thm:density:induction`): the energy
bounds at the exponents `P` give `s(N) ≤ C' N^{1 − a/(72 − ϑ)}` for every `N`, by the interval
embedding `[1, N] ⊆ [1, K N]` (`Sarkozy.powerSavingBound_of_scaledEnergyEstimate` in general). -/
theorem powerSavingBound_of_scaledEnergyEstimate (hP : P.Valid) {Y : ℕ → Finset ℤ → ℝ}
    (hY : ScaledEnergyEstimate P Y) : PowerSavingBound P := by
  obtain ⟨D, hD, h⟩ := scaled_density_bound hP hY
  have hK : (0 : ℝ) < P.blockScale := hP.blockScale_real_pos
  refine ⟨(P.blockScale : ℝ) * D, mul_pos hK hD, ?_⟩
  intro N hN A hA
  have hKN : N ≤ P.blockScale * N := by
    simpa using Nat.mul_le_mul_right N hP.one_le_blockScale
  have hlarge : Admissible (P.blockScale * N) A := by
    refine ⟨?_, hA.2⟩
    intro z hz
    obtain ⟨hz₁, hzN⟩ := Finset.mem_Icc.mp (hA.1 hz)
    exact Finset.mem_Icc.mpr ⟨hz₁, hzN.trans (by exact_mod_cast hKN)⟩
  have hb := h N hN A hlarge
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hden : density N A = (P.blockScale : ℝ) * density (P.blockScale * N) A := by
    unfold density
    push_cast
    field_simp
  apply card_bound_of_density hN
  rw [hden]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hK.le

/-- **Finite initialization** (proof of `thm:density:induction`: "at the finitely many earlier
scales … enlarge `C₀` to initialize the induction") at the exponents `P`
(`Sarkozy.exists_initialization_constant` in general; needs `ϑ ≠ 0` and `K ≥ 1`). -/
theorem exists_initialization_constant (hP : P.Valid) (Y : ℕ → Finset ℤ → ℝ)
    (hzero : ∀ L : ℕ, 1 ≤ L → Y L ∅ ≤ 0) (L₀ : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ L : ℕ, 1 ≤ L → L < L₀ → EnergyUpperBoundAt P Y C L := by
  classical
  let S := (Finset.range L₀).product
    (Finset.Icc 1 ((P.blockScale * L₀ : ℕ) : ℤ)).powerset
  let ratio : ℕ × Finset ℤ → ℝ := fun p =>
    Y p.1 p.2 / ((p.1 : ℝ) ^ (-P.decay) *
      density (P.blockScale * p.1) p.2 ^ P.densityExponent)
  obtain ⟨B, hB⟩ := (S.finite_toSet.image ratio).bddAbove
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro L hL hsmall A hA
  by_cases hempty : A = ∅
  · subst A
    have he : (0 : ℝ) ^ P.densityExponent = 0 := Real.zero_rpow hP.densityExponent_ne_zero
    simpa only [density_empty, he, mul_zero] using hzero L hL
  have hApos : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hKN : 0 < P.blockScale * L := Nat.mul_pos hP.blockScale_pos (by omega)
  have hweight : 0 < (L : ℝ) ^ (-P.decay) *
      density (P.blockScale * L) A ^ P.densityExponent :=
    mul_pos (Real.rpow_pos_of_pos hLpos _)
      (Real.rpow_pos_of_pos (density_pos_of_nonempty hKN hApos) _)
  have hsub : A ⊆ Finset.Icc 1 ((P.blockScale * L₀ : ℕ) : ℤ) := by
    intro z hz
    obtain ⟨hz₁, hzL⟩ := Finset.mem_Icc.mp (hA.1 hz)
    refine Finset.mem_Icc.mpr ⟨hz₁, hzL.trans ?_⟩
    exact_mod_cast Nat.mul_le_mul_left P.blockScale hsmall.le
  have hmem : (L, A) ∈ S :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr hsmall, Finset.mem_powerset.mpr hsub⟩
  have hratio : ratio (L, A) ≤ max 1 B :=
    (hB (Set.mem_image_of_mem ratio hmem)).trans (le_max_right _ _)
  have hb := (div_le_iff₀ hweight).mp hratio
  simpa only [mul_assoc] using hb

/-- With a recurrence uniform in the induction constant, finite initialization is a theorem
(`Sarkozy.scaledEnergyEstimate_of_uniform_contraction` in general). -/
theorem scaledEnergyEstimate_of_uniform_contraction (hP : P.Valid)
    {Y : ℕ → Finset ℤ → ℝ} {q : ℝ} {L₀ : ℕ}
    {error : ℕ → Finset ℤ → ℝ}
    (hzero : ∀ L : ℕ, 1 ≤ L → Y L ∅ ≤ 0)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (P.blockScale * L) A → density (P.blockScale * L) A ^ slots ≤ Y L A)
    (hrec : ∀ C : ℝ, 1 ≤ C → ∀ L : ℕ, 1 ≤ L → L₀ ≤ L →
      (∀ k : ℕ, 1 ≤ k → k < L → EnergyUpperBoundAt P Y C k) →
      ∀ A : Finset ℤ, Admissible (P.blockScale * L) A →
        C * (L : ℝ) ^ (-P.decay) * density (P.blockScale * L) A ^ P.densityExponent < Y L A →
        Y L A ≤ (q + error L A) * Y L A)
    (hmargin : ∀ L : ℕ, 1 ≤ L → L₀ ≤ L →
      ∀ A : Finset ℤ, Admissible (P.blockScale * L) A → q + error L A < 1) :
    ScaledEnergyEstimate P Y := by
  obtain ⟨C, hC, hinit⟩ := exists_initialization_constant hP Y hzero L₀
  exact scaledEnergyEstimate_of_contraction P (lt_of_lt_of_le zero_lt_one hC)
    hreflection hinit (hrec C hC) hmargin

end Sarkozy.Param
